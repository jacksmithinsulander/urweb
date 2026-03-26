//! Placeholder for a future inter-process communication development daemon (`ur-daemon`).
//!
//! A real implementation would likely use an operating-system socket path (for example a Unix-domain socket file on Unix-like systems).

use std::process;

/// Filesystem path marker for a future socket file (`stop` removes it best-effort).
const SOCKET_PATH: &str = ".ur_daemon";

/// Handle `start` and `stop` for the stub daemon (`args` is argv after the program name).
///
/// Returns `0` for `stop` or the placeholder `start`, `1` on bad usage.
fn daemon_command(args: &[String]) -> i32 {
    match args.first().map(|s| s.as_str()) {
        Some("stop") => {
            // Best-effort removal of the socket file; ignore errors if absent.
            let _ = std::fs::remove_file(SOCKET_PATH);
            println!("Daemon stopped.");
            0
        }
        Some("start") => {
            // Placeholder until a real daemon process is implemented.
            eprintln!("note: daemon not yet implemented");
            0
        }
        _ => {
            eprintln!("usage: ur-daemon [start|stop]");
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
