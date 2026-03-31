//! Foundry-inspired [`tracing`] setup and coarse compile-phase logging for the batch compiler.
//!
//! `-v` … `-vvvvv` on `ur-compile` map to default `RUST_LOG`-style filters for the `ur` crate only
//! when `RUST_LOG` is unset. With `RUST_LOG` set, [`tracing_subscriber::EnvFilter`] follows the environment.

use std::io::IsTerminal as _;
use std::sync::Once;

use tracing_subscriber::EnvFilter;

/// Maximum meaningful repetition for Forge-style `-v` flags (five levels beyond quiet).
pub const MAX_COMPILER_VERBOSITY: u8 = 5;

static INIT_TRACING_SUBSCRIBER: Once = Once::new();

/// Build default `ur=…` filter from CLI verbosity when `RUST_LOG` / `RUST_LOG_FORMAT` are not controlling output.
fn default_filter_for_verbosity(verbosity: u8) -> EnvFilter {
    let level = verbosity.min(MAX_COMPILER_VERBOSITY);
    let directive = match level {
        0 => "off",
        1 => "ur=warn",
        2 => "ur=info",
        3 => "ur=debug",
        _ => "ur=trace",
    };
    EnvFilter::new(directive)
}

/// Install stderr [`tracing`] output once per process (`try_init` is safe across repeated calls).
///
/// Honors `RUST_LOG` when set; otherwise uses [`Settings::verbosity`](crate::settings::Settings::verbosity)
/// from the **first** successful initialization (typical single `compile` / `compile_to_outputs` run).
///
/// # Arguments
///
/// * `settings` — Live settings after CLI / job flags are merged.
pub fn init_compiler_tracing(settings: &crate::settings::Settings) {
    let verbosity = settings.verbosity;
    let show_thread = verbosity >= MAX_COMPILER_VERBOSITY;
    let ansi = std::io::stderr().is_terminal();
    INIT_TRACING_SUBSCRIBER.call_once(|| {
        let filter = EnvFilter::try_from_default_env()
            .unwrap_or_else(|_| default_filter_for_verbosity(verbosity));
        let init_result = match verbosity >= 3 {
            true => tracing_subscriber::fmt()
                .with_env_filter(filter)
                .with_writer(std::io::stderr)
                .with_target(true)
                .with_timer(tracing_subscriber::fmt::time::SystemTime)
                .with_thread_ids(show_thread)
                .with_ansi(ansi)
                .try_init(),
            false => tracing_subscriber::fmt()
                .with_env_filter(filter)
                .with_writer(std::io::stderr)
                .with_target(true)
                .without_time()
                .with_thread_ids(show_thread)
                .with_ansi(ansi)
                .try_init(),
        };
        let _ = init_result;
    });
}

/// Log phase completion and optionally print a Forge-style timing line on stderr.
///
/// # Arguments
///
/// * `settings` — Drives human-readable timing via [`Settings::emit_phase_timing`] and verbosity.
/// * `phase` — Stable phase name (for example `"parse"`).
/// * `started` — [`std::time::Instant`] taken at phase start.
pub fn log_phase_complete(
    settings: &crate::settings::Settings,
    phase: &'static str,
    started: std::time::Instant,
) {
    let ms = started.elapsed().as_millis();
    tracing::debug!(phase, elapsed_ms = ms, "phase complete");
    if settings.emit_phase_timing || settings.verbosity >= 4 {
        eprintln!("  · {phase}: {ms} ms");
    }
}
