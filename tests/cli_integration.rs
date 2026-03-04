//! CLI integration tests: run the urweb binary and assert on exit codes.
//! Catches mutants in main.rs (dispatch, new_project, build_project, etc.).

use std::process::Command;
use std::sync::Mutex;

static CWD_LOCK: Mutex<()> = Mutex::new(());

fn urweb() -> Command {
    Command::new(env!("CARGO_BIN_EXE_urweb"))
}

#[test]
fn cli_no_args_fails() {
    let out = urweb().output().unwrap();
    assert!(!out.status.success());
}

#[test]
fn cli_help_succeeds() {
    let out = urweb().arg("-help").output().unwrap();
    assert!(out.status.success());
}

#[test]
fn cli_version_succeeds() {
    let out = urweb().arg("-version").output().unwrap();
    assert!(out.status.success());
}

#[test]
fn cli_new_requires_name() {
    let out = urweb().args(["new"]).output().unwrap();
    assert!(!out.status.success());
}

#[test]
fn cli_new_creates_project() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    let out = urweb().args(["new", "testproj"]).output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    assert!(out.status.success());
    assert!(dir.path().join("testproj/testproj.urp").exists());
}

#[test]
fn cli_build_requires_urweb_toml() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    let out = urweb().arg("build").output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    assert!(!out.status.success());
}

#[test]
fn cli_build_with_toml_does_not_say_not_found() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    std::fs::write(
        "urweb.toml",
        "[package]\nname=\"x\"\n[build]\nentry=\"x\"\n",
    )
    .unwrap();
    std::fs::write("x.urp", "x.ur").unwrap();
    std::fs::write("x.ur", "val x = 1").unwrap();
    let out = urweb().arg("build").output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !stderr.contains("not found"),
        "with urweb.toml present, stderr must not say 'not found': {}",
        stderr
    );
    // Catches build_project -> 1 mutant: mutant returns 1 immediately, never reaches run_compiler_args
    assert!(
        stderr.contains("would compile"),
        "build must reach compiler (catches build_project -> 1 mutant): {}",
        stderr
    );
}

#[test]
fn cli_help_prints_usage() {
    let out = urweb().arg("-help").output().unwrap();
    let out_str = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out_str.contains("usage:"));
}

#[test]
fn cli_new_lib_flag_creates_library() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    let out = urweb().args(["new", "--lib", "mylib"]).output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    assert!(out.status.success());
    assert!(dir.path().join("mylib/mylib.urs").exists());
}

#[test]
fn cli_new_minus_lib_creates_library() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    let out = urweb().args(["new", "-lib", "mylib2"]).output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    assert!(out.status.success());
    assert!(dir.path().join("mylib2/mylib2.urs").exists());
}

#[test]
fn cli_bare_project_name_routes_to_compiler() {
    let out = urweb().args(["myproj"]).output().unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("myproj"));
}

#[test]
fn cli_unknown_flag_prints_error() {
    let out = urweb().args(["-badflag", "myproj"]).output().unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("unknown flag"),
        "expected 'unknown flag' in stderr: {}",
        stderr
    );
}

#[test]
fn cli_compiler_flag_parses_project_correctly() {
    let out = urweb()
        .args(["-ccompiler", "gcc", "myproj"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("myproj"),
        "stderr should mention project 'myproj', got: {}",
        stderr
    );
}

#[test]
fn cli_fmt_help_returns_zero() {
    let out = urweb().args(["fmt", "-help"]).output().unwrap();
    assert!(out.status.success(), "fmt -help must return 0");
}

#[test]
fn cli_fmt_with_unknown_flag_in_project_treats_as_warning_not_file() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    std::fs::write(
        "urweb.toml",
        "[package]\nname=\"x\"\n[build]\nentry=\"x\"\n",
    )
    .unwrap();
    std::fs::write("x.urp", "x.ur").unwrap();
    std::fs::write("x.ur", "val x = 1").unwrap();
    let out = urweb().args(["fmt", "-unknownflag"]).output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    // With correct is_file_arg guard, -unknownflag is warning only; project mode finds files, returns 0.
    // Mutant (guard true) would treat -unknownflag as file, fail .ur/.urs check, return 1.
    assert!(
        out.status.success(),
        "fmt -unknownflag in project: expected success (warning only), got: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn cli_limit_valid_number_not_rejected() {
    let out = urweb()
        .args(["-limit", "Class", "5", "proj"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !stderr.contains("invalid limit number"),
        "valid limit 5 must not be rejected: {}",
        stderr
    );
}

#[test]
fn cli_limit_negative_rejected() {
    let out = urweb()
        .args(["-limit", "Class", "-5", "proj"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("invalid limit number"),
        "negative limit -5 must be rejected (catches is_valid_limit mutant): {}",
        stderr
    );
}

#[test]
fn cli_build_with_scss_compiles_when_sass_available() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    let bin_dir = dir.path().join("bin");
    std::fs::create_dir_all(&bin_dir).unwrap();
    // Fake sass that exits 0 (catches has_sass_or_sassc -> false mutant)
    let sass_path = bin_dir.join("sass");
    #[cfg(unix)]
    std::fs::write(&sass_path, "#!/bin/sh\nexit 0\n").unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = std::fs::metadata(&sass_path).unwrap().permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&sass_path, perms).unwrap();
    }
    #[cfg(not(unix))]
    std::fs::write(&sass_path, "").unwrap(); // Windows: skip this test or use bat
    std::fs::write(
        "urweb.toml",
        "[package]\nname=\"x\"\n[build]\nentry=\"x\"\n\n[style]\nscss=\"style/main.scss\"\ncss=\"style/main.css\"\n",
    )
    .unwrap();
    std::fs::create_dir_all("style").unwrap();
    std::fs::write("style/main.scss", "body {}").unwrap();
    std::fs::write("x.urp", "x.ur").unwrap();
    std::fs::write("x.ur", "val x = 1").unwrap();
    let path_env = if cfg!(unix) {
        format!(
            "{}:{}",
            bin_dir.display(),
            std::env::var("PATH").unwrap_or_default()
        )
    } else {
        std::env::var("PATH").unwrap_or_default()
    };
    let out = if cfg!(unix) {
        urweb().env("PATH", path_env).arg("build").output().unwrap()
    } else {
        return; // Skip on Windows - no executable script
    };
    std::env::set_current_dir(&cwd).unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stdout.contains("Compiling SCSS") || stderr.contains("Compiling SCSS"),
        "when sass is in PATH, must compile SCSS (catches has_sass_or_sassc mutant): stdout={} stderr={}",
        stdout,
        stderr
    );
}

#[test]
fn cli_build_with_scss_fails_when_sass_exits_nonzero() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    let bin_dir = dir.path().join("bin");
    std::fs::create_dir_all(&bin_dir).unwrap();
    let sass_path = bin_dir.join("sass");
    #[cfg(unix)]
    std::fs::write(&sass_path, "#!/bin/sh\nexit 1\n").unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = std::fs::metadata(&sass_path).unwrap().permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&sass_path, perms).unwrap();
    }
    std::fs::write(
        "urweb.toml",
        "[package]\nname=\"x\"\n[build]\nentry=\"x\"\n\n[style]\nscss=\"style/main.scss\"\ncss=\"style/main.css\"\n",
    )
    .unwrap();
    std::fs::create_dir_all("style").unwrap();
    std::fs::write("style/main.scss", "body {}").unwrap();
    std::fs::write("x.urp", "x.ur").unwrap();
    std::fs::write("x.ur", "val x = 1").unwrap();
    let path_env = if cfg!(unix) {
        format!(
            "{}:{}",
            bin_dir.display(),
            std::env::var("PATH").unwrap_or_default()
        )
    } else {
        std::env::var("PATH").unwrap_or_default()
    };
    let out = if cfg!(unix) {
        urweb().env("PATH", path_env).arg("build").output().unwrap()
    } else {
        return;
    };
    std::env::set_current_dir(&cwd).unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success(),
        "when sass exits 1, build must fail (exit code)"
    );
    assert!(
        stderr.contains("SCSS compilation failed"),
        "when sass fails, must report SCSS error (catches ! in build_project): {}",
        stderr
    );
}

#[test]
fn cli_install_from_project_dir_does_not_say_toml_not_found() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    std::fs::write(
        "urweb.toml",
        "[package]\nname=\"x\"\n[build]\nentry=\"x\"\n",
    )
    .unwrap();
    let out = urweb()
        .args(["install", "nonexistent/nonexistent"])
        .output()
        .unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !stderr.contains("urweb.toml not found"),
        "when urweb.toml exists, install must not say 'not found' (catches delete ! mutant): {}",
        stderr
    );
    // When git submodule add fails, install must return 1 (catches delete ! in command_succeeded)
    assert!(
        !out.status.success(),
        "install with invalid spec must fail (git fails): {}",
        stderr
    );
    assert!(
        stderr.contains("git submodule add failed"),
        "install failure must report git error: {}",
        stderr
    );
}

#[test]
fn cli_fmt_accepts_ur_file_explicit() {
    // Catches delete ! at line 641: !f.ends_with(".ur") - mutant would reject .ur files
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    std::fs::write(
        "urweb.toml",
        "[package]\nname=\"x\"\n[build]\nentry=\"x\"\n",
    )
    .unwrap();
    std::fs::write("x.ur", "val x = 1").unwrap();
    let out = urweb().args(["fmt", "x.ur"]).output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !stderr.contains("is not a .ur or .urs file"),
        "fmt with explicit .ur file must not reject it: {}",
        stderr
    );
}

#[test]
fn cli_fmt_accepts_urs_file_explicit() {
    // Catches delete ! at line 641: !f.ends_with(".urs") - mutant would reject .urs files
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    std::fs::write(
        "urweb.toml",
        "[package]\nname=\"x\"\n[build]\nentry=\"x\"\n",
    )
    .unwrap();
    std::fs::write("x.urs", "val x : int").unwrap();
    let out = urweb().args(["fmt", "x.urs"]).output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !stderr.contains("is not a .ur or .urs file"),
        "fmt with explicit .urs file must not reject it: {}",
        stderr
    );
}

#[test]
fn cli_fmt_project_mode_succeeds_when_toml_exists() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    std::fs::write(
        "urweb.toml",
        "[package]\nname=\"x\"\n[build]\nentry=\"x\"\n",
    )
    .unwrap();
    std::fs::write("x.urp", "x.ur").unwrap();
    std::fs::write("x.ur", "val x = 1").unwrap();
    let out = urweb().args(["fmt"]).output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    assert!(
        out.status.success(),
        "fmt in project dir with urweb.toml must succeed (catches file_exists ! mutant): {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn cli_build_with_scss_skips_sass_when_unavailable() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir.path()).unwrap();
    std::fs::write(
        "urweb.toml",
        "[package]\nname=\"x\"\n[build]\nentry=\"x\"\n\n[style]\nscss=\"style/main.scss\"\ncss=\"style/main.css\"\n",
    )
    .unwrap();
    std::fs::create_dir_all("style").unwrap();
    std::fs::write("style/main.scss", "body {}").unwrap();
    std::fs::write("x.urp", "x.ur").unwrap();
    std::fs::write("x.ur", "val x = 1").unwrap();
    let out = urweb().env("PATH", "").arg("build").output().unwrap();
    std::env::set_current_dir(&cwd).unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);
    // has_sass_or_sassc is false when sass/sassc not in PATH. We skip SCSS block.
    // Mutant (replace with true) would enter block, try to run sass, print "Compiling SCSS" and fail.
    assert!(
        !stdout.contains("Compiling SCSS") && !stderr.contains("Compiling SCSS"),
        "when sass not in PATH, must skip SCSS (no 'Compiling SCSS'): stdout={} stderr={}",
        stdout,
        stderr
    );
}
