//! Integration tests for `ur-fmt` (`src/bin/ur_fmt.rs`).

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use tempfile::tempdir;

fn cargo_bin(name: &str) -> PathBuf {
    let underscored = name.replace('-', "_");
    let key = format!("CARGO_BIN_EXE_{underscored}");
    if let Some(p) = std::env::var_os(&key) {
        return PathBuf::from(p);
    }
    let profile = std::env::var("PROFILE").unwrap_or_else(|_| "debug".into());
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join(&profile)
        .join(name);
    assert!(path.exists(), "missing {name}: set {key} — {:?}", path);
    path
}

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
