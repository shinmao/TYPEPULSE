#![feature(box_patterns)]
#![feature(rustc_private)]
#![feature(try_blocks)]
#![feature(never_type)]
#![feature(let_chains)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

#[macro_use]
extern crate bitflags;

#[macro_use]
extern crate if_chain;

#[macro_use]
extern crate log as log_crate;

#[macro_use]
mod macros;

// so that we can call than from lib.rs
mod analysis;
pub mod log;
pub mod report;
pub mod utils;
pub mod context;
pub mod visitor;
pub mod ir;
pub mod graph;
pub mod iter;
pub mod paths;
pub mod prelude;
pub mod call_graph;

use rustc_middle::ty::TyCtxt;

use crate::analysis::{BrokenLayoutChecker, UninitExposureChecker, BrokenBitPatternsChecker};
use crate::log::Verbosity;
use crate::report::ReportLevel;
use crate::context::TypePulseCtxtOwner;

// Insert rustc arguments at the beginning of the argument list that TypePulse wants to be
// set per default, for maximal validation power.
pub static TYPEPULSE_DEFAULT_ARGS: &[&str] =
    &["-Zalways-encode-mir", "-Zmir-opt-level=0", "--cfg=typepulse"];

#[derive(Debug, Clone, Copy)]
pub struct TypePulseConfig {
    pub verbosity: Verbosity,
    pub report_level: ReportLevel,
    pub broken_layout_enabled: bool,
    pub uninit_exposure_enabled: bool,
    pub broken_bitpatterns_enabled: bool,
    pub unsafe_dataflow_enabled: bool,
    pub optimize_enabled: bool,
    pub type_check: bool,
}

impl Default for TypePulseConfig {
    fn default() -> Self {
        TypePulseConfig {
            verbosity: Verbosity::Normal,
            report_level: ReportLevel::Info,
            broken_layout_enabled: true,
            uninit_exposure_enabled: true,
            broken_bitpatterns_enabled: true,
            unsafe_dataflow_enabled: true,
            optimize_enabled: true,
            type_check: true,
        }
    }
}

/// Returns the "default sysroot" that TypePulse will use if no `--sysroot` flag is set.
/// Should be a compile-time constant.
pub fn compile_time_sysroot() -> Option<String> {
    // option_env! is replaced to a constant at compile time
    if option_env!("RUSTC_STAGE").is_some() {
        // This is being built as part of rustc, and gets shipped with rustup.
        // We can rely on the sysroot computation in librustc.
        return None;
    }

    // For builds outside rustc, we need to ensure that we got a sysroot
    // that gets used as a default. The sysroot computation in librustc would
    // end up somewhere in the build dir.
    // Taken from PR <https://github.com/Manishearth/rust-clippy/pull/911>.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("To build TypePulse without rustup, set the `RUST_SYSROOT` env var at build time")
            .to_owned(),
    })
}

fn run_analysis<F, R>(name: &str, f: F) -> R
where
    F: FnOnce() -> R,
{
    // progress_info!("{} analysis started", name);
    let result = f();
    // progress_info!("{} analysis finished", name);
    result
}

pub fn analyze<'tcx>(tcx: TyCtxt<'tcx>, config: TypePulseConfig) {
    // workaround to mimic arena lifetime
    let rcx_owner = TypePulseCtxtOwner::new(
        tcx, 
        config.report_level, 
        config.optimize_enabled,
        config.type_check
    );
    let rcx = &*Box::leak(Box::new(rcx_owner));

    // shadow the variable tcx
    #[allow(unused_variables)]
    let tcx = ();

    // Broken layout analysis
    if config.broken_layout_enabled {
        run_analysis("BrokenLayout", || {
            let checker = BrokenLayoutChecker::new(rcx);
            checker.analyze();
        })
    }

    // Uninit Exposure analysis
    if config.uninit_exposure_enabled {
        run_analysis("UninitExposure", || {
            let checker = UninitExposureChecker::new(rcx);
            checker.analyze();
        })
    }

    // Broken Bit patterns analysis
    if config.broken_bitpatterns_enabled {
        run_analysis("BrokenBitPatterns", || {
            let checker = BrokenBitPatternsChecker::new(rcx);
            checker.analyze();
        })
    }
}
