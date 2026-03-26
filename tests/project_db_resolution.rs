//! Compiler vs LSP must resolve the same effective [`ur::db::ProjectDb`] for a tree.

mod common;

use std::fs;
use tempfile::tempdir;
use ur::compiler;
use ur::db::ProjectDb;
use ur::lsp_analysis::ProjectState;

#[test]
fn lsp_and_compiler_agree_on_manifest_db() {
    let dir = tempdir().unwrap();
    let root = dir.path();
    fs::write(
        root.join("ur.toml"),
        "[package]\n\n[build]\nentry = \"m\"\ndb = \"rocksdb\"\n",
    )
    .unwrap();
    fs::write(root.join("app.urp"), "dbms rocksdb\ndatabase ./data\n\nm\n").unwrap();
    fs::write(root.join("m.ur"), "val x = 1\n").unwrap();

    let state = ProjectState::open(root).expect("LSP project open");
    assert_eq!(
        ur::db::effective_project_db(&state.settings),
        ProjectDb::Rocksdb
    );

    let urp = root.join("app.urp");
    let (_, settings) = compiler::resolve_project_job_and_settings(&urp).expect("compiler resolve");
    assert_eq!(ur::db::effective_project_db(&settings), ProjectDb::Rocksdb);

    assert_eq!(
        compiler::effective_project_db_for_workspace_root(root).expect("workspace db"),
        ProjectDb::Rocksdb
    );
}

#[test]
fn compile_to_outputs_native_sql_is_placeholder() {
    let dir = tempdir().unwrap();
    let root = dir.path();
    fs::write(
        root.join("app.urp"),
        "dbms tigerbeetle\ndatabase ./tb\n\nm\n",
    )
    .unwrap();
    fs::write(root.join("m.ur"), "val x = 1\n").unwrap();
    let urp = root.join("app.urp");
    std::env::set_current_dir(root).unwrap();
    let (_, sql) = common::compile_to_outputs_bounded(urp.clone(), |_| {}).expect("compile");
    assert!(
        sql.contains("tigerbeetle") && !sql.contains("CREATE TABLE"),
        "SQL sidecar: {sql}"
    );
}
