//! Integration tests for `ur-fmt` (`src/bin/ur_fmt.rs`).

#[path = "common/proc.rs"]
mod proc;
#[path = "common/require_ok.rs"]
mod require_ok;
#[path = "common/require_some.rs"]
mod require_some;
#[path = "common/tempdir.rs"]
mod tempdir;
#[path = "common/ur_bins.rs"]
mod ur_bins;
#[path = "common/write_file.rs"]
mod write_file;

use proc::command_output;
use require_some::require_some;
use tempdir::tempdir;
use ur_bins::ur_package_binary;
use write_file::write_file;

use std::process::Command;

use ur_package_binary as cargo_bin;

#[test]
fn ur_fmt_parse_failure_prints_error_detail() {
    let tmp = tempdir("fmt_cli parse failure tempdir");
    let path = tmp.path().join("bad.ur");
    write_file(
        &path,
        "fun main () = )))\n",
        "write malformed formatter fixture",
    );
    let path_arg = require_some(path.to_str(), "formatter fixture path must be UTF-8");
    let mut command = Command::new(cargo_bin("ur-fmt"));
    command.arg(path_arg);
    let output = command_output(&mut command, "run ur-fmt on malformed file");
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
    let tmp = tempdir("fmt_cli check tempdir");
    let path = tmp.path().join("ok.ur");
    write_file(&path, "val x = 1\n", "write stable formatter fixture");
    let path_arg = require_some(path.to_str(), "formatter fixture path must be UTF-8");
    let mut command = Command::new(cargo_bin("ur-fmt"));
    command.args(["--check", path_arg]);
    let output = command_output(&mut command, "run ur-fmt --check on stable file");
    assert!(
        output.status.success(),
        "formatted == orig guard: --check should pass for stable text, stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}
