//! Integration tests for `ur-fmt` (`src/bin/ur_fmt.rs`).

mod common;

use std::fs;
use std::process::Command;

use common::ur_package_binary as cargo_bin;
use tempfile::tempdir;

#[test]
fn ur_fmt_parse_failure_prints_error_detail() {
    let tmp = tempdir().unwrap();
    let path = tmp.path().join("bad.ur");
    fs::write(&path, "fun main () = )))\n").unwrap();
    let output = Command::new(cargo_bin("ur-fmt"))
        .arg(path.to_str().unwrap())
        .output()
        .expect("ur-fmt bad.ur");
    assert!(
        !output.status.success(),
        "invalid syntax must fail (print_errors noop mutant drops detail-only output)"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("format") || stderr.contains("parse") || stderr.contains("error"),
        "expected format error preamble: {stderr:?}"
    );
    assert!(
        stderr.lines().count() >= 2,
        "print_errors should list diagnostics (multi-line stderr), got {stderr:?}"
    );
}

#[test]
fn ur_fmt_check_unchanged_file_exits_zero() {
    let tmp = tempdir().unwrap();
    let path = tmp.path().join("ok.ur");
    fs::write(&path, "val x = 1\n").unwrap();
    let output = Command::new(cargo_bin("ur-fmt"))
        .args(["--check", path.to_str().unwrap()])
        .output()
        .expect("ur-fmt --check");
    assert!(
        output.status.success(),
        "formatted == orig guard: --check should pass for stable text, stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}
