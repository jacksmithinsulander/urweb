//! Run dev binaries so `main` cannot be emptied without failing tests.

mod common;

use std::process::Command;

use common::ur_package_binary as cargo_bin;

#[test]
fn test_pp_prints_context() {
    let out = Command::new(cargo_bin("test_pp"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("spawn test_pp");
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
    let out = Command::new(cargo_bin("test_parse"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("spawn test_parse");
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
    let out = Command::new(cargo_bin("ur"))
        .arg("--help")
        .output()
        .expect("spawn ur");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("ur build") && stdout.contains("ur fmt"),
        "expected orchestrator usage on stdout, got {stdout:?}"
    );
}

#[test]
fn ur_fmt_help_on_stdout() {
    let out = Command::new(cargo_bin("ur-fmt"))
        .arg("--help")
        .output()
        .expect("spawn ur-fmt");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("ur-fmt") && stdout.contains("-check"),
        "expected formatter help, got {stdout:?}"
    );
}

#[test]
fn ur_fmt_missing_file_is_error() {
    let out = Command::new(cargo_bin("ur-fmt"))
        .arg("/nonexistent/path/to/file.ur")
        .output()
        .expect("spawn ur-fmt");
    assert!(
        !out.status.success(),
        "missing .ur file should be exit != 0, stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn ur_new_app_usage_without_name() {
    let out = Command::new(cargo_bin("ur-new"))
        .output()
        .expect("spawn ur-new");
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
    let out = Command::new(cargo_bin("ur-new"))
        .arg("--lib")
        .output()
        .expect("spawn ur-new --lib");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("ur-new --lib") && stderr.contains("<library-name>"),
        "expected CliUrNewUsageLib on stderr, got {stderr:?}"
    );
}
