//! Locate `ur` workspace `[[bin]]` executables for integration tests.

use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;

use super::require_ok::require_ok;

/// Same as Cargo’s default `target/` when `CARGO_TARGET_DIR` is unset.
fn cargo_target_root() -> PathBuf {
    std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
}

/// Single `cargo build` that materializes [`ur_package_binary`] targets when tests skip them.
static ENSURE_UR_PACKAGE_BINS: OnceLock<()> = OnceLock::new();

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
