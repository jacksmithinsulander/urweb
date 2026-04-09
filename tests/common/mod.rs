//! Shared helpers for integration tests: bounded compile helper (cargo-mutants) and `ur` `[[bin]]` paths.
//!
//! Each integration test crate declares `mod common;` but only calls a **subset** of these helpers, so
//! allow dead-code at module scope instead of splitting into many tiny files.
#![allow(dead_code)]

use std::path::PathBuf;
use std::process::Command;
use std::process::Output;
use std::sync::mpsc;
use std::sync::OnceLock;
use std::thread;
use std::time::Duration;

use ur::compiler;
use ur::settings::Settings;

/// Single `cargo build` that materializes [`ur_package_binary`] targets when tests skip them.
static ENSURE_UR_PACKAGE_BINS: OnceLock<()> = OnceLock::new();

/// Per-invocation wall clock limit so a broken / pathological compiler mutant fails fast
/// instead of running until cargo-mutants' whole-crate test timeout (~108s).
pub const COMPILE_TO_OUTPUTS_TEST_TIMEOUT: Duration = Duration::from_secs(45);

/// Stack size for the compile worker thread (bytes).
///
/// [`compiler::compile_to_outputs`] runs the whole pipeline; debug builds can recurse deeply enough
/// to overflow the default per-thread stack (often ~2 MiB), especially on macOS.
const COMPILE_THREAD_STACK_SIZE: usize = 16 * 1024 * 1024;

/// Run [`compile_to_outputs`](compiler::compile_to_outputs) in a joinable context with a hard
/// timeout. Preserves `Ok` / `Err` from the compiler; maps hangs to `Err`.
pub fn compile_to_outputs_bounded(
    urp: PathBuf,
    configure: impl FnOnce(&mut Settings) + Send + 'static,
) -> anyhow::Result<(String, String)> {
    type R = anyhow::Result<(String, String)>;
    let urp_display = urp.display().to_string();
    let (tx, rx) = mpsc::channel::<R>();
    // Larger stack avoids stack overflow in full pipeline + boot-linked Basis under `--test`.
    thread::Builder::new()
        .stack_size(COMPILE_THREAD_STACK_SIZE)
        .spawn(move || {
            let mut settings = Settings::new();
            configure(&mut settings);
            let r = compiler::compile_to_outputs(&urp, &mut settings);
            let _ = tx.send(r);
        })
        .map_err(|e| anyhow::anyhow!("failed to spawn compile thread: {e}"))?;
    match rx.recv_timeout(COMPILE_TO_OUTPUTS_TEST_TIMEOUT) {
        Ok(r) => r,
        Err(mpsc::RecvTimeoutError::Timeout) => Err(anyhow::anyhow!(
            "compile_to_outputs exceeded {:?} (hung or pathologically slow) for {urp_display}",
            COMPILE_TO_OUTPUTS_TEST_TIMEOUT,
        )),
        Err(mpsc::RecvTimeoutError::Disconnected) => Err(anyhow::anyhow!(
            "compile_to_outputs panicked or aborted for {urp_display}",
        )),
    }
}

/// Run [`compiler::elaborate_project`] in a joinable context with a hard timeout.
///
/// Preserves `Ok` / `Err` from the compiler; maps hangs to `Err`.
pub fn elaborate_project_bounded(
    urp: PathBuf,
    configure: impl FnOnce(&mut Settings) + Send + 'static,
) -> anyhow::Result<()> {
    type R = anyhow::Result<()>;
    let urp_display = urp.display().to_string();
    let (tx, rx) = mpsc::channel::<R>();
    thread::Builder::new()
        .stack_size(COMPILE_THREAD_STACK_SIZE)
        .spawn(move || {
            let mut settings = Settings::new();
            configure(&mut settings);
            let r = compiler::elaborate_project(&urp, &mut settings);
            let _ = tx.send(r);
        })
        .map_err(|e| anyhow::anyhow!("failed to spawn elaboration thread: {e}"))?;
    match rx.recv_timeout(COMPILE_TO_OUTPUTS_TEST_TIMEOUT) {
        Ok(r) => r,
        Err(mpsc::RecvTimeoutError::Timeout) => Err(anyhow::anyhow!(
            "elaborate_project exceeded {:?} (hung or pathologically slow) for {urp_display}",
            COMPILE_TO_OUTPUTS_TEST_TIMEOUT,
        )),
        Err(mpsc::RecvTimeoutError::Disconnected) => Err(anyhow::anyhow!(
            "elaborate_project panicked or aborted for {urp_display}",
        )),
    }
}

/// Unwrap a `Result` in tests with a contextual panic that keeps the original error visible.
pub fn require_ok<T, E: std::fmt::Display>(result: Result<T, E>, context: &str) -> T {
    match result {
        Ok(value) => value,
        Err(error) => panic!("{context}: {error}"),
    }
}

/// Unwrap an `Option` in tests with a contextual panic when the value is missing.
pub fn require_some<T>(value: Option<T>, context: &str) -> T {
    match value {
        Some(inner) => inner,
        None => panic!("{context}: expected Some(..), got None"),
    }
}

/// Unwrap the error side of a `Result` in tests with a contextual panic on unexpected success.
pub fn require_err<T, E>(result: Result<T, E>, context: &str) -> E {
    match result {
        Ok(_) => panic!("{context}: expected Err(..), got Ok(..)"),
        Err(error) => error,
    }
}

/// Create an isolated temp directory for a test, panicking with context on failure.
pub fn tempdir(context: &str) -> tempfile::TempDir {
    require_ok(tempfile::tempdir(), context)
}

/// Write one test fixture file with contextual panic text on failure.
pub fn write_file(path: &std::path::Path, contents: impl AsRef<[u8]>, context: &str) {
    match std::fs::write(path, contents) {
        Ok(()) => {}
        Err(error) => panic!("{context} ({}): {error}", path.display()),
    }
}

/// Create a directory tree for test fixtures with contextual panic text on failure.
pub fn create_dir_all(path: &std::path::Path, context: &str) {
    match std::fs::create_dir_all(path) {
        Ok(()) => {}
        Err(error) => panic!("{context} ({}): {error}", path.display()),
    }
}

/// Run a child process and surface spawn errors with contextual panic text.
pub fn command_output(command: &mut Command, context: &str) -> Output {
    match command.output() {
        Ok(output) => output,
        Err(error) => panic!("{context}: {error}"),
    }
}

/// Same as Cargo’s default `target/` when `CARGO_TARGET_DIR` is unset.
fn cargo_target_root() -> PathBuf {
    std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
}

/// Filesystem path for `cargo build -p ur --bin <name>` (honours `PROFILE` and Windows `.exe`).
fn built_bin_path(name: &str) -> PathBuf {
    let profile = std::env::var("PROFILE").unwrap_or_else(|_| "debug".into());
    #[cfg(windows)]
    {
        let mut path = cargo_target_root().join(profile).join(name);
        path.set_extension("exe");
        path
    }
    #[cfg(not(windows))]
    {
        cargo_target_root().join(profile).join(name)
    }
}

/// Invoked once when a needed `[[bin]]` was not scheduled by the current `cargo test` graph.
fn ensure_ur_bins_built_once() {
    ENSURE_UR_PACKAGE_BINS.get_or_init(|| {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let mut cmd = Command::new(std::env::var("CARGO").unwrap_or_else(|_| "cargo".into()));
        cmd.current_dir(manifest_dir);
        if let Ok(target_dir) = std::env::var("CARGO_TARGET_DIR") {
            cmd.env("CARGO_TARGET_DIR", target_dir);
        }
        let status = require_ok(
            cmd.args([
                "build",
                "-p",
                "ur",
                "--bin",
                "ur",
                "--bin",
                "ur-compile",
                "--bin",
                "ur-fmt",
                "--bin",
                "ur-new",
                "--bin",
                "ur-install",
                "--bin",
                "ur-daemon",
                "--bin",
                "ur-debugger",
                "--bin",
                "ur-lsp",
                "--bin",
                "test_pp",
                "--bin",
                "test_parse",
            ])
            .status(),
            "spawn cargo build for integration-test peer binaries",
        );
        assert!(
            status.success(),
            "cargo build for integration-test peer binaries exited with {status}",
        );
    });
}

/// Absolute path to a root-package binary (`ur`, `ur-fmt`, `ur-debugger`, …).
///
/// Cargo exposes `CARGO_BIN_EXE_<NAME>` with `<NAME>` = target name, dashes → underscores, **ASCII uppercase**
/// (see Cargo book: environment variables Cargo sets for crates).
pub fn ur_package_binary(name: &str) -> PathBuf {
    let for_env_key = name.replace('-', "_").to_ascii_uppercase();
    let key = format!("CARGO_BIN_EXE_{for_env_key}");
    if let Some(path) = std::env::var_os(&key) {
        return PathBuf::from(path);
    }
    let direct = built_bin_path(name);
    if direct.is_file() {
        return direct;
    }
    ensure_ur_bins_built_once();
    if let Some(path) = std::env::var_os(&key) {
        return PathBuf::from(path);
    }
    assert!(
        direct.is_file(),
        "missing binary {name}: set {key} or run `cargo build -p ur --bin {name}` — looked for {:?}",
        direct
    );
    direct
}

/// Directory containing root-package executables (`ur`, `ur-compile`, …) for `PATH`.
pub fn ur_package_bin_dir() -> PathBuf {
    require_some(
        ur_package_binary("ur").parent(),
        "ur binary path must have a parent directory",
    )
    .to_path_buf()
}
