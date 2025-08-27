///! This implementation is based on `cargo-miri`
///! https://github.com/rust-lang/miri/blob/master/src/bin/cargo-miri.rs
#[macro_use]
extern crate log as log_crate;

use std::env;
use std::fmt::Display;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use wait_timeout::ChildExt;

use rustc_version::VersionMeta;

use typepulse::log::{self, Verbosity};
use typepulse::{progress_error, progress_info};

const CARGO_TYPEPULSE_HELP: &str = r#"Tests crates with TypePulse
Usage:
    cargo typepulse [<cargo options>] [--] [<rustc/typepulse options>...]

Common options:
    -h, --help               Print this message

Other [options] are the same as `cargo check`. Everything after the first "--" is
passed verbatim to TypePulse.
"#;

fn show_help() {
    println!("{}", CARGO_TYPEPULSE_HELP);
}

fn main() {
    // Check for version and help flags even when invoked as `cargo-typepulse`.
    if std::env::args().any(|a| a == "--help" || a == "-h") {
        show_help();
        return;
    }

    log::setup_logging(Verbosity::Normal).expect("TypePulse failed to initialize");
    
    let rustc_sysroot = std::env::var("RUSTC_SYSROOT").expect("Couldn't find the env variable `RUSTC_SYSROOT`");

    if let Some("typepulse") = std::env::args().nth(1).as_ref().map(AsRef::as_ref) {
        progress_info!("Running cargo typepulse");
        // This arm is for when `cargo typepulse` is called. We call `cargo rustc` for each applicable target,
        // but with the `RUSTC` env var set to the `cargo-typepulse` binary so that we come back in the other branch,
        // and dispatch the invocations to `rustc` and `typepulse`, respectively.
        in_cargo_typepulse();
        progress_info!("cargo typepulse finished");
    } else if let Some("/root/.rustup/toolchains/nightly-2023-06-02-x86_64-unknown-linux-gnu/bin/rustc") = std::env::args().nth(1).as_ref().map(AsRef::as_ref) {
        // This arm is executed when `cargo-typepulse` runs `cargo rustc` with the `RUSTC_WRAPPER` env var set to itself:
        // dependencies get dispatched to `rustc`, the final test/binary to `typepulse`.
        inside_cargo_rustc();
    } else {
        show_error(
            "`cargo-typepulse` must be called with either `typepulse` or `rustc` as first argument.",
        );
    }
}

fn show_error(msg: impl AsRef<str>) -> ! {
    progress_error!("{}", msg.as_ref());
    std::process::exit(1)
}

// Determines whether a `--flag` is present.
fn has_arg_flag(name: &str) -> bool {
    // Stop searching at `--`.
    let mut args = std::env::args().take_while(|val| val != "--");
    args.any(|val| val == name)
}

/// Returns the path to the `typepulse` binary
fn find_typepulse() -> PathBuf {
    let mut path = std::env::current_exe().expect("current executable path invalid");
    path.set_file_name("typepulse");
    path
}

/// Make sure that the `typepulse` and `rustc` binary are from the same sysroot.
/// This can be violated e.g. when typepulse is locally built and installed with a different
/// toolchain than what is used when `cargo typepulse` is run.
fn test_sysroot_consistency() {
    fn get_sysroot(mut cmd: Command) -> PathBuf {
        let out = cmd
            .arg("--print")
            .arg("sysroot")
            .output()
            .expect("Failed to run rustc to get sysroot info");
        let stdout = String::from_utf8(out.stdout).expect("stdout is not valid UTF-8");
        let stderr = String::from_utf8(out.stderr).expect("stderr is not valid UTF-8");
        let stdout = stdout.trim();
        assert!(
            out.status.success(),
            "Bad status code when getting sysroot info.\nstdout:\n{}\nstderr:\n{}",
            stdout,
            stderr
        );
        PathBuf::from(stdout)
            .canonicalize()
            .unwrap_or_else(|_| panic!("Failed to canonicalize sysroot: {}", stdout))
    }

    let rustc_sysroot = get_sysroot(Command::new("rustc"));
    let typepulse_sysroot = get_sysroot(Command::new(find_typepulse()));

    if rustc_sysroot != typepulse_sysroot {
        show_error(format!(
            "typepulse was built for a different sysroot than the rustc in your current toolchain.\n\
             Make sure you use the same toolchain to run typepulse that you used to build it!\n\
             rustc sysroot: `{}`\n\
             typepulse sysroot: `{}`",
            rustc_sysroot.display(),
            typepulse_sysroot.display()
        ));
    }
}

/// Gets the value of a `--flag`.
fn get_arg_flag_value(name: &str) -> Option<String> {
    // Stop searching at `--`.
    let mut args = std::env::args().take_while(|val| val != "--");
    loop {
        let arg = match args.next() {
            Some(arg) => arg,
            None => return None,
        };
        if !arg.starts_with(name) {
            continue;
        }
        // Strip leading `name`.
        let suffix = &arg[name.len()..];
        if suffix.is_empty() {
            // This argument is exactly `name`; the next one is the value.
            return args.next();
        } else if suffix.starts_with('=') {
            // This argument is `name=value`; get the value.
            // Strip leading `=`.
            return Some(suffix[1..].to_owned());
        }
    }
}

fn cargo_package() -> cargo_metadata::Package {
    // We need to get the manifest, and then the metadata, to enumerate targets.
    let manifest_path =
        get_arg_flag_value("--manifest-path").map(|m| Path::new(&m).canonicalize().unwrap());

    let mut cmd = cargo_metadata::MetadataCommand::new();
    if let Some(manifest_path) = &manifest_path {
        cmd.manifest_path(manifest_path);
    }
    let mut metadata = match cmd.exec() {
        Ok(metadata) => metadata,
        Err(e) => show_error(format!("Could not obtain Cargo metadata\n{}", e)),
    };

    let current_dir = std::env::current_dir();

    let package_index = metadata
        .packages
        .iter()
        .position(|package| {
            let package_manifest_path = Path::new(&package.manifest_path);
            if let Some(manifest_path) = &manifest_path {
                package_manifest_path == manifest_path
            } else {
                let current_dir = current_dir
                    .as_ref()
                    .expect("could not read current directory");
                let package_manifest_directory = package_manifest_path
                    .parent()
                    .expect("could not find parent directory of package manifest");
                package_manifest_directory == current_dir
            }
        })
        .unwrap_or_else(|| {
            show_error("This seems to be a workspace, which is not supported by cargo-typepulse");
        });

    metadata.packages.remove(package_index)
}

fn in_cargo_typepulse() {
    let verbose = has_arg_flag("-v");

    // Some basic sanity checks
    test_sysroot_consistency();

    // Now run the command.
    let package = cargo_package();
    let mut targets: Vec<_> = package.targets.into_iter().collect();

    // Ensure `lib` is compiled before `bin`
    targets.sort_by_key(|target| TargetKind::from(target) as u8);

    for target in targets {
        // Skip `cargo typepulse`
        let mut args = std::env::args().skip(2);
        let kind = TargetKind::from(&target);

        // Now we run `cargo check $FLAGS $ARGS`, giving the user the
        // change to add additional arguments. `FLAGS` is set to identify
        // this target. The user gets to control what gets actually passed to typepulse.
        let mut cmd = Command::new("cargo");
        cmd.arg("check");

        // Allow an option to use `xargo check` instead of `cargo`, this is used
        // for analyzing the rust standard library.
        if std::env::var_os("TYPEPULSE_USE_XARGO_INSTEAD_OF_CARGO").is_some() {
            cmd = Command::new("xargo-check");
        }

        match kind {
            TargetKind::Bin => {
                // Analyze all the binaries.
                cmd.arg("--bin").arg(&target.name);
            }
            TargetKind::Library => {
                // There can be only one lib in a crate.
                cmd.arg("--lib");
                // Clean the result to disable Cargo's freshness check
                clean_package(&package.name);
            }
            TargetKind::Unknown => {
                warn!(
                    "Target {}:{} is not supported",
                    target.kind.as_slice().join("/"),
                    &target.name
                );
                continue;
            }
        }

        if !cfg!(debug_assertions) && !verbose {
            cmd.arg("-q");
        }

        // Forward user-defined `cargo` args until first `--`.
        while let Some(arg) = args.next() {
            if arg == "--" {
                break;
            }
            cmd.arg(arg);
        }

        // We want to always run `cargo` with `--target`. This later helps us detect
        // which crates are proc-macro/build-script (host crates) and which crates are
        // needed for the program itself.
        if get_arg_flag_value("--target").is_none() {
            // When no `--target` is given, default to the host.
            cmd.arg("--target");
            cmd.arg(version_info().host);
        }

        // Add suffix to TYPEPULSE_REPORT_PATH
        if let Ok(report) = env::var("TYPEPULSE_REPORT_PATH") {
            cmd.env(
                "TYPEPULSE_REPORT_PATH",
                format!("{}-{}-{}", report, kind, &target.name),
            );
        }

        // Serialize the remaining args into a special environment variable.
        // This will be read by `inside_cargo_rustc` when we go to invoke
        // our actual target crate (the binary or the test we are running).
        // Since we're using "cargo check", we have no other way of passing
        // these arguments.
        let args_vec: Vec<String> = args.collect();
        cmd.env(
            "TYPEPULSE_ARGS",
            serde_json::to_string(&args_vec).expect("failed to serialize args"),
        );

        // Set `RUSTC_WRAPPER` to ourselves.  Cargo will prepend that binary to its usual invocation,
        // i.e., the first argument is `rustc` -- which is what we use in `main` to distinguish
        // the two codepaths.
        if env::var_os("RUSTC_WRAPPER").is_some() {
            println!("WARNING: Ignoring existing `RUSTC_WRAPPER` environment variable, typepulse does not support wrapping.");
        }

        let path = std::env::current_exe().expect("current executable path invalid");
        cmd.env("RUSTC_WRAPPER", path);
        if verbose {
            cmd.env("TYPEPULSE_VERBOSE", ""); // this makes `inside_cargo_rustc` verbose.
            eprintln!("+ {:?}", cmd);
        }

        progress_info!("Running typepulse for target {}:{}", kind, &target.name);
        let mut child = cmd.spawn().expect("could not run cargo check");
        // 1 hour timeout
        match child
            .wait_timeout(Duration::from_secs(60 * 60))
            .expect("failed to wait for subprocess")
        {
            Some(exit_status) => {
                if !exit_status.success() {
                    show_error("Finished with non-zero exit code");
                }
            }
            None => {
                child.kill().expect("failed to kill subprocess");
                child.wait().expect("failed to wait for subprocess");
                show_error("Killed due to timeout");
            }
        };
    }
}

#[repr(u8)]
enum TargetKind {
    Library = 0,
    Bin,
    Unknown,
}

impl TargetKind {
    fn is_lib_str(s: &str) -> bool {
        s == "lib" || s == "rlib" || s == "staticlib"
    }
}

impl From<&cargo_metadata::Target> for TargetKind {
    fn from(target: &cargo_metadata::Target) -> Self {
        if target.kind.iter().any(|s| TargetKind::is_lib_str(s)) {
            TargetKind::Library
        } else if let Some("bin") = target.kind.get(0).map(|s| s.as_ref()) {
            TargetKind::Bin
        } else {
            TargetKind::Unknown
        }
    }
}

impl Display for TargetKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TargetKind::Library => "lib",
                TargetKind::Bin => "bin",
                TargetKind::Unknown => "unknown",
            }
        )
    }
}

fn clean_package(package_name: &str) {
    let mut cmd = Command::new("cargo");
    cmd.arg("clean");

    cmd.arg("-p");
    cmd.arg(package_name);

    cmd.arg("--target");
    cmd.arg(version_info().host);

    let exit_status = cmd
        .spawn()
        .expect("could not run cargo clean")
        .wait()
        .expect("failed to wait for cargo?");

    if !exit_status.success() {
        show_error(format!("cargo clean failed"));
    }
}

fn version_info() -> VersionMeta {
    VersionMeta::for_command(Command::new(find_typepulse()))
        .expect("failed to determine underlying rustc version of TypePulse")
}

/// Finds the first argument ends with `.rs`.
fn get_first_arg_with_rs_suffix() -> Option<String> {
    // Stop searching at `--`.
    let mut args = std::env::args().take_while(|val| val != "--");
    args.find(|arg| arg.ends_with(".rs"))
}

fn any_arg_flag<F>(name: &str, mut check: F) -> bool
where
    F: FnMut(&str) -> bool,
{
    // Stop searching at `--`.
    let mut args = std::env::args().take_while(|val| val != "--");
    loop {
        let arg = match args.next() {
            Some(arg) => arg,
            None => return false,
        };
        if !arg.starts_with(name) {
            continue;
        }

        // Strip leading `name`.
        let suffix = &arg[name.len()..];
        let value = if suffix.is_empty() {
            // This argument is exactly `name`; the next one is the value.
            match args.next() {
                Some(arg) => arg,
                None => return false,
            }
        } else if suffix.starts_with('=') {
            // This argument is `name=value`; get the value.
            // Strip leading `=`.
            suffix[1..].to_owned()
        } else {
            return false;
        };

        if check(&value) {
            return true;
        }
    }
}

// This will construct a cmd like:
// `typepulse --crate-name a_crate_name src/lib.rs --crate-type lib`
fn inside_cargo_rustc() {
    /// Determines if we are being invoked (as rustc) to build a crate for
    /// the "target" architecture, in contrast to the "host" architecture.
    /// Host crates are for build scripts and proc macros and still need to
    /// be built like normal; target crates need to be built for or interpreted
    /// by TypePulse.
    ///
    /// Currently, we detect this by checking for "--target=", which is
    /// never set for host crates. This matches what rustc bootstrap does,
    /// which hopefully makes it "reliable enough". This relies on us always
    /// invoking cargo itself with `--target`, which `in_cargo_typepulse` ensures.
    fn contains_target_flag() -> bool {
        get_arg_flag_value("--target").is_some()
    }

    /// Returns whether we are building the target crate.
    /// Cargo passes the file name as a relative address when building the local crate,
    /// such as `crawl/src/bin/unsafe-counter.rs` when building the target crate.
    /// This might not be a stable behavior, but let's rely on this for now.
    fn is_target_crate() -> bool {
        let entry_path_arg = match get_first_arg_with_rs_suffix() {
            Some(arg) => arg,
            None => return false,
        };
        let entry_path: &Path = entry_path_arg.as_ref();

        entry_path.is_relative()
    }

    fn is_crate_type_lib() -> bool {
        any_arg_flag("--crate-type", TargetKind::is_lib_str)
    }

    fn run_command(mut cmd: Command) {
        // Run it.
        let verbose = std::env::var_os("TYPEPULSE_VERBOSE").is_some();
        if verbose {
            eprintln!("+ {:?}", cmd);
        }

        match cmd.status() {
            Ok(exit) => {
                if !exit.success() {
                    std::process::exit(exit.code().unwrap_or(42));
                }
            }
            Err(e) => panic!("error running {:?}:\n{:?}", cmd, e),
        }
    }

    // TODO: Miri sets custom sysroot here, check if it is needed for us (typepulse-30)

    let is_direct_target = contains_target_flag() && is_target_crate();
    let mut is_additional_target = false;

    // Perform analysis if the crate being compiled is in the typepulse_ALSO_ANALYZE
    // environment variable.
    if let (Ok(cargo_pkg_name), Ok(typepulse_also_analyze_crates)) =
        (env::var("CARGO_PKG_NAME"), env::var("TYPEPULSE_ALSO_ANALYZE"))
    {
        if typepulse_also_analyze_crates
            .split(',')
            .any(|x| x.to_lowercase() == cargo_pkg_name.to_lowercase())
        {
            is_additional_target = true;
        }
    }

    if is_direct_target || is_additional_target {
        let mut cmd = Command::new(find_typepulse());
        cmd.args(std::env::args().skip(2)); // skip `cargo-typepulse rustc`

        if let Ok(report) = env::var("TYPEPULSE_REPORT_PATH") {
            cmd.env(
                "TYPEPULSE_REPORT_PATH",
                format!(
                    "{}-{}",
                    report,
                    env::var("CARGO_PKG_NAME").unwrap_or(String::from("unknown"))
                ),
            );
        }

        // This is the local crate that we want to analyze with TYPEPULSE.
        // (Testing `target_crate` is needed to exclude build scripts.)
        // We deserialize the arguments that are meant for TypePulse from the special
        // environment variable "TYPEPULSE_ARGS", and feed them to the 'typepulse' binary.
        //
        // `env::var` is okay here, well-formed JSON is always UTF-8.
        let magic = std::env::var("TYPEPULSE_ARGS").expect("missing TYPEPULSE_ARGS");
        let typepulse_args: Vec<String> =
            serde_json::from_str(&magic).expect("failed to deserialize TYPEPULSE_ARGS");
        cmd.args(typepulse_args);

        run_command(cmd);
    }

    // TypePulse does not build anything.
    // We need to run rustc (or sccache) to build dependencies.
    if !is_direct_target || is_crate_type_lib() {
        let cmd = match which::which("sccache") {
            Ok(sccache_path) => {
                let mut cmd = Command::new(&sccache_path);
                // ["cargo-typepulse", "rustc", ...]
                cmd.args(std::env::args().skip(1));
                cmd
            }
            Err(_) => {
                // sccache was not found, use vanilla rustc
                let mut cmd = Command::new("rustc");
                // ["cargo-typepulse", "rustc", ...]
                cmd.args(std::env::args().skip(2));
                cmd
            }
        };
        //println!("final cmd: {:?}", cmd);
        run_command(cmd);
    }
}
