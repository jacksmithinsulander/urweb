//! Run dev binaries so `main` cannot be emptied without failing tests.

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

#[test]
fn test_pp_prints_context() {
    let mut command = Command::new(cargo_bin("test_pp"));
    command.current_dir(env!("CARGO_MANIFEST_DIR"));
    let out = command_output(&mut command, "spawn test_pp");
    assert!(
        out.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("Preprocessor window (debug):"),
        "expected test_pp preprocessor debug line (CliTestPpContextOk), got {stdout:?}"
    );
}

#[test]
fn test_parse_prints_status() {
    let mut command = Command::new(cargo_bin("test_parse"));
    command.current_dir(env!("CARGO_MANIFEST_DIR"));
    let out = command_output(&mut command, "spawn test_parse");
    assert!(
        out.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("Reporter reports errors:") && stdout.contains("declaration count"),
        "unexpected test_parse stdout (catalog-backed CliTestParse*): {stdout:?}"
    );
    assert!(
        stdout.contains("Second sample") && stdout.contains("declaration count: 2"),
        "test_parse second sample must report declaration count 2: {stdout:?}"
    );
}

#[test]
fn compile_thread_stack_bytes_matches_compiler_thread() {
    assert_eq!(ur::COMPILE_THREAD_STACK_BYTES, 512 * 1024 * 1024);
}

#[test]
fn ur_prints_subcommand_help() {
    let mut command = Command::new(cargo_bin("ur"));
    command.arg("--help");
    let out = command_output(&mut command, "spawn ur --help");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("ur build") && stdout.contains("ur fmt"),
        "expected orchestrator usage on stdout, got {stdout:?}"
    );
}

#[test]
fn ur_fmt_help_on_stdout() {
    let mut command = Command::new(cargo_bin("ur-fmt"));
    command.arg("--help");
    let out = command_output(&mut command, "spawn ur-fmt --help");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("ur-fmt") && stdout.contains("-check"),
        "expected formatter help, got {stdout:?}"
    );
}

#[test]
fn ur_fmt_missing_file_is_error() {
    let mut command = Command::new(cargo_bin("ur-fmt"));
    command.arg("/nonexistent/path/to/file.ur");
    let out = command_output(&mut command, "spawn ur-fmt with missing file");
    assert!(
        !out.status.success(),
        "missing .ur file should be exit != 0, stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn ur_new_app_usage_without_name() {
    let mut command = Command::new(cargo_bin("ur-new"));
    let out = command_output(&mut command, "spawn ur-new");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("ur-new") && stderr.contains("<project-name>"),
        "expected CliUrNewUsageApp on stderr, got {stderr:?}"
    );
    assert!(
        !stderr.contains("--lib"),
        "app usage must not mention --lib: {stderr:?}"
    );
}

#[test]
fn ur_new_lib_usage_without_name() {
    let mut command = Command::new(cargo_bin("ur-new"));
    command.arg("--lib");
    let out = command_output(&mut command, "spawn ur-new --lib");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("ur-new --lib") && stderr.contains("<library-name>"),
        "expected CliUrNewUsageLib on stderr, got {stderr:?}"
    );
}
