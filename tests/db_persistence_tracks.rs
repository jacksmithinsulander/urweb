//! `ur.toml` `[build].db` must match the resolved project `dbms`.

#[path = "common/compile_bounded.rs"]
mod compile_bounded;
#[path = "common/require_err.rs"]
mod require_err;
#[path = "common/tempdir.rs"]
mod tempdir;
#[path = "common/write_file.rs"]
mod write_file;

use compile_bounded::compile_to_outputs_bounded;
use require_err::require_err;
use tempdir::tempdir;
use write_file::write_file;

#[test]
fn ur_toml_db_mismatch_with_urp_errors() {
    let dir = tempdir("db_persistence_tracks tempdir");
    let dir_path = dir.path();
    write_file(
        &dir_path.join("ur.toml"),
        "[package]\nname = \"t\"\n[build]\nentry = \"m.ur\"\ndb = \"tigerbeetle\"\n",
        "write ur.toml for db mismatch test",
    );
    write_file(
        &dir_path.join("app.urp"),
        "dbms postgres\ndatabase x\n\nm\n",
        "write app.urp for db mismatch test",
    );
    write_file(
        &dir_path.join("m.ur"),
        "val x = 1",
        "write m.ur for db mismatch test",
    );
    let err = require_err(
        compile_to_outputs_bounded(dir_path.join("app.urp"), |_| {}),
        "compile_to_outputs should reject mismatched ur.toml db",
    );
    let msg = format!("{err:#}");
    assert!(
        msg.contains("ur.toml") && msg.contains("tigerbeetle") && msg.contains("postgres"),
        "{msg}"
    );
}
