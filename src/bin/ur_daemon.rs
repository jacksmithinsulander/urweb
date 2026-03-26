//! ur-daemon — Start or stop Ur/Web daemon.

use std::process;

const SOCKET_PATH: &str = ".ur_daemon";

fn daemon_command(args: &[String]) -> i32 {
    match args.first().map(|s| s.as_str()) {
        Some("stop") => {
            let _ = std::fs::remove_file(SOCKET_PATH);
            println!("Daemon stopped.");
            0
        }
        Some("start") => {
            eprintln!("note: daemon not yet implemented");
            0
        }
        _ => {
            eprintln!("usage: ur-daemon [start|stop]");
            1
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = daemon_command(&args[1..]);
    process::exit(code);
}
