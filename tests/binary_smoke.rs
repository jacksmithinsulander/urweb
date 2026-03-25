//! Run dev binaries so `main` cannot be emptied without failing tests.

use std::path::PathBuf;
use std::process::Command;

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
    assert!(
        path.exists(),
        "missing binary {name}: set {key} or build with cargo test — looked for {:?}",
        path
    );
    path
}

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
        stdout.starts_with("Context:"),
        "expected Context line, got {stdout:?}"
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
        stdout.contains("Errors:")
            && (stdout.contains("Parsed") || stdout.contains("Parse failed")),
        "unexpected stdout: {stdout:?}"
    );
    assert!(
        stdout.contains("two_decls: 2") || stdout.contains("two_decls: parse failed"),
        "test_parse must count two val decls or report parse failure (not a wrong count): {stdout:?}"
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
        stderr.contains("usage: ur-new <name>"),
        "expected app usage, got {stderr:?}"
    );
    assert!(
        !stderr.contains("--lib"),
        "app usage must not use the --lib template: {stderr:?}"
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
        stderr.contains("usage: ur-new --lib <name>"),
        "expected library usage, got {stderr:?}"
    );
}
