//! `ur.toml` `[build].db` must match the resolved project `dbms`.

use std::fs;
use std::sync::Mutex;
use tempfile::tempdir;
use ur::compiler;
use ur::settings::Settings;

static CWD_LOCK: Mutex<()> = Mutex::new(());

#[test]
fn ur_toml_db_mismatch_with_urp_errors() {
    let _g = CWD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = tempdir().unwrap();
    let dir_path = dir.path();
    fs::write(
        dir_path.join("ur.toml"),
        "[package]\nname = \"t\"\n[build]\nentry = \"m.ur\"\ndb = \"tigerbeetle\"\n",
    )
    .unwrap();
    fs::write(dir_path.join("app.urp"), "dbms postgres\ndatabase x\n\nm\n").unwrap();
    fs::write(dir_path.join("m.ur"), "val x = 1").unwrap();
    std::env::set_current_dir(dir_path).unwrap();
    let err =
        compiler::compile_to_outputs(&dir_path.join("app.urp"), &mut Settings::new()).unwrap_err();
    let msg = format!("{err:#}");
    assert!(
        msg.contains("ur.toml") && msg.contains("tigerbeetle") && msg.contains("postgres"),
        "{msg}"
    );
}
