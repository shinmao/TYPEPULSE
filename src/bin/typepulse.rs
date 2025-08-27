#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;

#[macro_use]
extern crate log;

use std::env;

use rustc_driver::Compilation;
use rustc_interface::{interface::Compiler, Queries};

// to use lib crate from bin crate, use crate name rather than `crate`
use typepulse::log::Verbosity;
use typepulse::report::{default_report_logger, init_report_logger, ReportLevel};
use typepulse::{TypePulseConfig, compile_time_sysroot, progress_info, analyze, TYPEPULSE_DEFAULT_ARGS};

struct TypePulseCompilerCalls {
    config: TypePulseConfig,
}

impl TypePulseCompilerCalls {
    fn new(config: TypePulseConfig) -> TypePulseCompilerCalls {
        TypePulseCompilerCalls { config }
    }
}

impl rustc_driver::Callbacks for TypePulseCompilerCalls {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();

        typepulse::log::setup_logging(self.config.verbosity).expect("TypePulse failed to initialize");

        // debug!(
        //     "Input file name: {}",
        //     compiler.input().source_name().prefer_local()
        // );
        //debug!("Crate name: {}", queries.crate_name().unwrap().peek_mut());

        progress_info!("TypePulse started");
        queries.global_ctxt().unwrap().enter(|tcx| {
            debug!(
                "Input file name: {}",
                tcx.sess.io.input.filestem().to_string()
            );
            analyze(tcx, self.config);
        });
        progress_info!("TypePulse finished");

        compiler.session().abort_if_errors();
        Compilation::Stop
    }
}

fn parse_config() -> (TypePulseConfig, Vec<String>) {
    let mut config = TypePulseConfig::default();

    let mut rustc_args = vec![];
    for arg in std::env::args() {
        match arg.as_str() {
            "-Ztypepulse-enable-broken-layout" => config.broken_layout_enabled = true,
            "-Ztypepulse-disable-broken-layout" => config.broken_layout_enabled = false,
            "-Ztypepulse-enable-uninit-exposure" => config.uninit_exposure_enabled = true,
            "-Ztypepulse-disable-uninit-exposure" => config.uninit_exposure_enabled = false,
            "-Ztypepulse-enable-broken-bitpatterns" => config.broken_bitpatterns_enabled = true,
            "-Ztypepulse-disable-broken-bitpatterns" => config.broken_bitpatterns_enabled = false,
            "-v" => config.verbosity = Verbosity::Verbose,
            "-vv" => config.verbosity = Verbosity::Trace,
            "-Zsensitivity-high" => config.report_level = ReportLevel::Error,
            "-Zsensitivity-med" => config.report_level = ReportLevel::Warning,
            "-Zsensitivity-low" => config.report_level = ReportLevel::Info,
            "-Zenable-optimize" => config.optimize_enabled = true,
            "-Zdisable-optimize" => config.optimize_enabled = false,
            "-Zdisable-inter" => config.type_check = false,
            _ => {
                rustc_args.push(arg);
            }
        }
    }

    (config, rustc_args)
}

/// Execute a compiler with the given CLI arguments and callbacks.
fn run_compiler(
    mut args: Vec<String>,
    callbacks: &mut (dyn rustc_driver::Callbacks + Send),
) -> i32 {
    // Make sure we use the right default sysroot. The default sysroot is wrong,
    // because `get_or_default_sysroot` in `librustc_session` bases that on `current_exe`.
    //
    // Make sure we always call `compile_time_sysroot` as that also does some sanity-checks
    // of the environment we were built in.
    // FIXME: Ideally we'd turn a bad build env into a compile-time error via CTFE or so.
    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        if !args.iter().any(|e| e == sysroot_flag) {
            // We need to overwrite the default that librustc_session would compute.
            args.push(sysroot_flag.to_owned());
            args.push(sysroot);
        }
    }

    // Some options have different defaults in TypePulse than in plain rustc; apply those by making
    // them the first arguments after the binary name (but later arguments can overwrite them).
    args.splice(
        1..1,
        typepulse::TYPEPULSE_DEFAULT_ARGS.iter().map(ToString::to_string),
    );

    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&args, callbacks).run()
    });

    exit_code
}

fn main() {
    rustc_driver::install_ice_hook(
        "https://github.com/xxx/TypePulse/issues/new",
        |_| ()
    );

    let exit_code = {
        // initialize the report logger
        // `logger_handle` must be nested because it flushes the logs when it goes out of the scope
        let (config, mut rustc_args) = parse_config();
        // if report path is provided, write to file
        // if not, output to stderr
        let _logger_handle = init_report_logger(default_report_logger());

        // init rustc logger
        if env::var_os("RUSTC_LOG").is_some() {
            rustc_driver::init_rustc_env_logger();
        }

        // --sysroot
        if let Some(sysroot) = compile_time_sysroot() {
            let sysroot_flag = "--sysroot";
            if !rustc_args.iter().any(|e| e == sysroot_flag) {
                // We need to overwrite the default that librustc would compute.
                rustc_args.push(sysroot_flag.to_owned());
                rustc_args.push(sysroot);
            }
        }

        // Finally, add the default flags all the way in the beginning, but after the binary name.
        rustc_args.splice(1..1, TYPEPULSE_DEFAULT_ARGS.iter().map(ToString::to_string));

        debug!("rustc arguments: {:?}", &rustc_args);
        run_compiler(rustc_args, &mut TypePulseCompilerCalls::new(config))
    };

    std::process::exit(exit_code)
}
