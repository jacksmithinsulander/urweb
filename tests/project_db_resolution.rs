//! Compiler vs LSP must resolve the same effective [`ur::db::ProjectDb`] for a tree.

#[path = "common/compile_bounded.rs"]
mod compile_bounded;
#[path = "common/require_err.rs"]
mod require_err;
#[path = "common/require_ok.rs"]
mod require_ok;
#[path = "common/tempdir.rs"]
mod tempdir;
#[path = "common/write_file.rs"]
mod write_file;

use compile_bounded::compile_to_outputs_bounded;
use require_err::require_err;
use require_ok::require_ok;
use tempdir::tempdir;
use write_file::write_file;

use ur::cli_common::diagnostic_locale_from_manifest_path;
use ur::compiler;
use ur::db::ProjectDb;
use ur::lsp_analysis::ProjectState;

#[test]
fn lsp_and_compiler_agree_on_manifest_db() {
    let dir = tempdir("project_db_resolution manifest db tempdir");
    let root = dir.path();
    write_file(
        &root.join("ur.toml"),
        "[package]\n\n[build]\nentry = \"m\"\ndb = \"rocksdb\"\n",
        "write ur.toml for manifest db resolution test",
    );
    write_file(
        &root.join("app.urp"),
        "dbms rocksdb\ndatabase ./data\n\nm\n",
        "write app.urp for manifest db resolution test",
    );
    write_file(
        &root.join("m.ur"),
        "val x = 1\n",
        "write m.ur for manifest db resolution test",
    );

    let locale = diagnostic_locale_from_manifest_path(&root.join("ur.toml"));
    let state = require_ok(
        ProjectState::open(root, locale),
        "open LSP project for manifest db resolution test",
    );
    assert_eq!(
        ur::db::effective_project_db(&state.settings),
        ProjectDb::Rocksdb
    );

    let urp = root.join("app.urp");
    let (_, settings) = require_ok(
        compiler::resolve_project_job_and_settings(&urp),
        "resolve compiler project job and settings",
    );
    assert_eq!(ur::db::effective_project_db(&settings), ProjectDb::Rocksdb);

    assert_eq!(
        require_ok(
            compiler::effective_project_db_for_workspace_root(root),
            "resolve workspace db",
        ),
        ProjectDb::Rocksdb
    );
}

#[test]
fn workspace_discovery_no_urp_is_swedish_when_ur_toml_language_sv() {
    let dir = tempdir("project_db_resolution no-urp tempdir");
    let root = dir.path();
    write_file(
        &root.join("ur.toml"),
        "[package]\nlanguage = \"sv\"\n\n[build]\nentry = \"m\"\n",
        "write ur.toml for Swedish no-urp test",
    );
    let locale = diagnostic_locale_from_manifest_path(&root.join("ur.toml"));
    let discovery_error = require_err(
        ur::lsp_workspace::discover_unique_urp(root),
        "workspace discovery should fail when no .urp exists",
    );
    let message = discovery_error.to_diagnostic_text(locale);
    assert!(
        message.contains("Ingen") && message.contains(".urp"),
        "expected Swedish workspace discovery catalog text: {message}"
    );
}

#[test]
fn compile_to_outputs_native_sql_is_placeholder() {
    let dir = tempdir("project_db_resolution native sql tempdir");
    let root = dir.path();
    write_file(
        &root.join("app.urp"),
        "dbms tigerbeetle\ndatabase ./tb\n\nm\n",
        "write app.urp for native sql placeholder test",
    );
    write_file(
        &root.join("m.ur"),
        "val x = 1\n",
        "write m.ur for native sql placeholder test",
    );
    let urp = root.join("app.urp");
    let (_, sql) = require_ok(
        compile_to_outputs_bounded(urp, |_| {}),
        "compile native sql placeholder project",
    );
    assert!(
        sql.contains("tigerbeetle") && !sql.contains("CREATE TABLE"),
        "SQL sidecar: {sql}"
    );
}
