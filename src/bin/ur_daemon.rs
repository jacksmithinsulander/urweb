//! Placeholder for a future inter-process communication development daemon (`ur-daemon`).
//!
//! A real implementation would likely use an operating-system socket path (for example a Unix-domain socket file on Unix-like systems).

use std::process;

use ur::cli_common::{self, cli_diagnostic_text, diagnostic_locale_for_cli, writeln_stdout_line};
use ur::diagnostics::DiagnosticId;

/// Filesystem path marker for a future socket file (`stop` removes it best-effort).
const SOCKET_PATH: &str = ".ur_daemon";

/// Handle `start` and `stop` for the stub daemon (`args` is argv after the program name).
///
/// Returns `0` for `stop` or the placeholder `start`, `1` on bad usage.
fn daemon_command(args: &[String]) -> i32 {
    let locale = diagnostic_locale_for_cli(None);
    match args.first().map(|token| token.as_str()) {
        Some("stop") => {
            let _ = std::fs::remove_file(SOCKET_PATH);
            let msg = cli_diagnostic_text(DiagnosticId::CliDaemonStopped, vec![], locale);
            writeln_stdout_line(&msg);
            0
        }
        Some("start") => {
            let msg = cli_diagnostic_text(DiagnosticId::CliDaemonNotImplemented, vec![], locale);
            cli_common::writeln_stderr_display(msg);
            0
        }
        _ => {
            let usage = cli_diagnostic_text(DiagnosticId::CliDaemonUsage, vec![], locale);
            ur::cli_common::writeln_stderr_display(usage);
            1
        }
    }
}

/// Run [`daemon_command`] on argv after the executable, then exit with its code.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = daemon_command(&args[1..]);
    process::exit(code);
}
