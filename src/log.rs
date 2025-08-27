use std::env;
use std::io;

use log::LevelFilter;

#[derive(Debug, Clone, Copy)]
pub enum Verbosity {
    Normal,
    Verbose,
    Trace,
}

pub fn setup_logging(verbosity: Verbosity) -> Result<(), fern::InitError> {
    let mut base_config = fern::Dispatch::new();

    base_config = match verbosity {
        Verbosity::Normal => base_config.level(LevelFilter::Info),
        Verbosity::Verbose => base_config.level(LevelFilter::Debug),
        Verbosity::Trace => base_config.level(LevelFilter::Trace),
    }
    .level_for(
        // log >= debug on debug build and >= info on release build
        "typepulse-progress",
        if cfg!(debug_assertions) {
            LevelFilter::Debug
        } else {
            LevelFilter::Info
        },
    );

    if let Some(log_file_path) = env::var_os("TYPEPULSE_LOG_PATH") {
        let file_config = fern::Dispatch::new()
            .filter(|metadata| metadata.target() == "typepulse-progress")
            .format(|out, message, record| {
                out.finish(format_args!(
                    "{} |PROGRESS-{:5}| {}",
                    chrono::Local::now().format("%Y-%m-%d %H:%M:%S%.6f"),
                    record.level(),
                    message
                ))
            })
            .chain(fern::log_file(log_file_path)?);

        base_config = base_config.chain(file_config);
    }

    // stderr is captured and cached by Cargo, which leads to confusing output when used as `cargo typepulse`
    let stdout_config = fern::Dispatch::new()
        .format(|out, message, record| {
            out.finish(format_args!(
                "{} |{:5}| [{}] {}",
                chrono::Local::now().format("%Y-%m-%d %H:%M:%S%.6f"),
                record.level(),
                record.target(),
                message
            ))
        })
        .chain(io::stdout());

    base_config.chain(stdout_config).apply()?;

    Ok(())
}

#[macro_export]
macro_rules! progress_trace {
    ($($arg:tt)+) => (
        ::log::trace!(target: "typepulse-progress", $($arg)+)
    )
}

#[macro_export]
macro_rules! progress_debug {
    ($($arg:tt)+) => (
        ::log::debug!(target: "typepulse-progress", $($arg)+)
    )
}

#[macro_export]
macro_rules! progress_info {
    ($($arg:tt)+) => (
        ::log::info!(target: "typepulse-progress", $($arg)+)
    )
}

#[macro_export]
macro_rules! progress_warn {
    ($($arg:tt)+) => (
        ::log::warn!(target: "typepulse-progress", $($arg)+)
    )
}

#[macro_export]
macro_rules! progress_error {
    ($($arg:tt)+) => (
        ::log::error!(target: "typepulse-progress", $($arg)+)
    )
}