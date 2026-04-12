//! Integration tests for `ur-debugger` argument dispatch (`src/bin/ur_debugger.rs`).

#[path = "common/proc.rs"]
mod proc;
#[path = "common/require_ok.rs"]
mod require_ok;
#[path = "common/ur_bins.rs"]
mod ur_bins;

use proc::command_output;
use ur_bins::ur_package_binary;

use std::process::Command;

use ur_package_binary as cargo_bin;

fn gdb_available() -> bool {
    Command::new("gdb")
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|status| status.success())
        .unwrap_or(false)
}

#[test]
fn ur_debugger_help_prints_modes_and_succeeds() {
    let exe = cargo_bin("ur-debugger");
    let mut command = Command::new(&exe);
    command.arg("--help");
    let output = command_output(&mut command, "run ur-debugger --help");
    assert!(
        output.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let err = String::from_utf8_lossy(&output.stderr);
    assert!(
        err.contains("--dap") && (err.contains("Modes") || err.contains("gdb")),
        "usage must describe modes: {err:?}"
    );
}

#[test]
fn ur_debugger_short_help_succeeds() {
    let exe = cargo_bin("ur-debugger");
    let mut command = Command::new(&exe);
    command.arg("-h");
    let output = command_output(&mut command, "run ur-debugger -h");
    assert!(output.status.success());
}

#[test]
fn ur_debugger_positional_without_mode_fails() {
    let exe = cargo_bin("ur-debugger");
    let mut command = Command::new(&exe);
    command.arg("not-a-subcommand");
    let output = command_output(
        &mut command,
        "run ur-debugger with bare positional argument",
    );
    assert!(
        !output.status.success(),
        "bare positional must error (run -> Ok(()) mutant would exit 0): {:?}",
        output.status
    );
}

#[test]
fn ur_debugger_no_args_prints_usage_and_succeeds() {
    let exe = cargo_bin("ur-debugger");
    let mut command = Command::new(&exe);
    let output = command_output(&mut command, "run ur-debugger without arguments");
    assert!(output.status.success());
    let err = String::from_utf8_lossy(&output.stderr);
    assert!(err.contains("ur-debugger") || err.contains("--dap"));
}

#[test]
fn ur_debugger_unknown_dash_flag_fails() {
    let exe = cargo_bin("ur-debugger");
    let mut command = Command::new(&exe);
    command.args(["--not-a-real-cli-flag-xyz"]);
    let output = command_output(&mut command, "run ur-debugger with unknown flag");
    assert!(!output.status.success());
    let err = String::from_utf8_lossy(&output.stderr);
    assert!(
        err.contains("not-a-real-cli-flag-xyz"),
        "unknown flags should name the token: {err:?}"
    );
}

#[test]
fn ur_debugger_tty_without_program_fails() {
    let exe = cargo_bin("ur-debugger");
    let mut command = Command::new(&exe);
    command.arg("--tty");
    let output = command_output(&mut command, "run ur-debugger --tty without a program");
    assert!(
        !output.status.success(),
        "--tty without program must error (gdb_tty Ok mutant would hide this)"
    );
}

#[test]
fn ur_debugger_gdb_mi_batch_quit_ok_when_gdb_installed() {
    if !gdb_available() {
        return;
    }
    let exe = cargo_bin("ur-debugger");
    let mut command = Command::new(&exe);
    command.args(["--gdb", "--", "-batch", "-ex", "quit"]);
    let output = command_output(&mut command, "run ur-debugger --gdb -- -batch -ex quit");
    assert!(
        output.status.success(),
        "gdb -batch -ex quit should be success; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}
