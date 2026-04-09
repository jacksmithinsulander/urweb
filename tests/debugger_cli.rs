//! Integration tests for `ur-debugger` argument dispatch (`src/bin/ur_debugger.rs`).

mod common;

use std::process::Command;

use common::ur_package_binary as cargo_bin;

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
    let output = Command::new(&exe)
        .arg("--help")
        .output()
        .expect("ur-debugger --help");
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
    let output = Command::new(&exe).arg("-h").output().expect("-h");
    assert!(output.status.success());
}

#[test]
fn ur_debugger_positional_without_mode_fails() {
    let exe = cargo_bin("ur-debugger");
    let output = Command::new(&exe)
        .arg("not-a-subcommand")
        .output()
        .expect("positional");
    assert!(
        !output.status.success(),
        "bare positional must error (run -> Ok(()) mutant would exit 0): {:?}",
        output.status
    );
}

#[test]
fn ur_debugger_no_args_prints_usage_and_succeeds() {
    let exe = cargo_bin("ur-debugger");
    let output = Command::new(&exe).output().expect("no args");
    assert!(output.status.success());
    let err = String::from_utf8_lossy(&output.stderr);
    assert!(err.contains("ur-debugger") || err.contains("--dap"));
}

#[test]
fn ur_debugger_unknown_dash_flag_fails() {
    let exe = cargo_bin("ur-debugger");
    let output = Command::new(&exe)
        .args(["--not-a-real-cli-flag-xyz"])
        .output()
        .expect("bad flag");
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
    let output = Command::new(&exe)
        .arg("--tty")
        .output()
        .expect("--tty alone");
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
    let output = Command::new(&exe)
        .args(["--gdb", "--", "-batch", "-ex", "quit"])
        .output()
        .expect("--gdb batch");
    assert!(
        output.status.success(),
        "gdb -batch -ex quit should be success; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}
