//! Compiler vs LSP must resolve the same effective [`ur::db::ProjectDb`] for a tree.

mod common;

use std::fs;
use std::path::PathBuf;
use tempfile::tempdir;
use ur::cli_common::diagnostic_locale_from_manifest_path;
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

    // Temporary trees have no `lib/ur`; resolution still needs a boot root when `-boot` is in effect.
    let boot_tree = PathBuf::from(env!("CARGO_MANIFEST_DIR")); // Repo root contains `lib/ur/basis.urs`.
    let previous_boot_root = std::env::var_os("URWEB_BOOT_ROOT"); // Snapshot for isolation after the test.
    std::env::set_var("URWEB_BOOT_ROOT", &boot_tree); // Point boot discovery at this workspace.

    let locale = diagnostic_locale_from_manifest_path(&root.join("ur.toml"));
    let state = ProjectState::open(root, locale).expect("LSP project open");
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

    match previous_boot_root {
        None => std::env::remove_var("URWEB_BOOT_ROOT"), // Drop override so other tests see default discovery.
        Some(value) => std::env::set_var("URWEB_BOOT_ROOT", value), // Restore whatever the harness had set.
    }
}

#[test]
fn workspace_discovery_no_urp_is_swedish_when_ur_toml_language_sv() {
    let dir = tempdir().unwrap();
    let root = dir.path();
    fs::write(
        root.join("ur.toml"),
        "[package]\nlanguage = \"sv\"\n\n[build]\nentry = \"m\"\n",
    )
    .unwrap();
    let locale = diagnostic_locale_from_manifest_path(&root.join("ur.toml"));
    let discovery_error =
        ur::lsp_workspace::discover_unique_urp(root).expect_err("expected no urp");
    let message = discovery_error.to_diagnostic_text(locale);
    assert!(
        message.contains("Ingen") && message.contains(".urp"),
        "expected Swedish workspace discovery catalog text: {message}"
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
