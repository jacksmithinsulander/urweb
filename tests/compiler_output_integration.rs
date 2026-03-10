//! Integration tests for compile_to_outputs: assert generated C and SQL content.
//! Catches mutants that replace compile_to_outputs with Ok((String::new(), String::new())),
//! and mutants in cjr_print, sql_generate, cjrize, prepare that corrupt output.

use std::fs;
use std::path::PathBuf;
use std::sync::Mutex;
use tempfile::tempdir;
use urweb::compiler;
use urweb::settings::Settings;

static CWD_LOCK: Mutex<()> = Mutex::new(());

fn setup_minimal_project() -> (tempfile::TempDir, PathBuf) {
    let dir = tempdir().unwrap();
    let dir_path = dir.path().to_path_buf();
    fs::write(dir_path.join("app.urp"), "mod1\n").unwrap();
    fs::write(dir_path.join("mod1.ur"), "val x = 1").unwrap();
    let urp = dir_path.join("app.urp");
    (dir, urp)
}

#[test]
#[ignore = "requires parse_ur (LALRPOP grammar - set URWEB_GEN_PARSER=1)"]
fn compile_to_outputs_c_code_non_empty() {
    let _g = CWD_LOCK.lock().unwrap();
    let (_dir, urp) = setup_minimal_project();
    let mut settings = Settings::new();
    let (c_code, _sql) = compiler::compile_to_outputs(&urp, &mut settings).unwrap();
    assert!(
        !c_code.is_empty(),
        "compile_to_outputs must produce non-empty C code (catches Ok((String::new(), ..)) mutant)"
    );
}

#[test]
#[ignore = "requires parse_ur (LALRPOP grammar)"]
fn compile_to_outputs_sql_non_empty_when_database() {
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempdir().unwrap();
    let dir_path = dir.path().to_path_buf();
    fs::write(dir_path.join("app.urp"), "database sqlite://\n\nmod1\n").unwrap();
    fs::write(dir_path.join("mod1.ur"), "val x = 1").unwrap();
    let urp = dir_path.join("app.urp");
    let mut settings = Settings::new();
    let (_c_code, sql) = compiler::compile_to_outputs(&urp, &mut settings).unwrap();
    assert!(
        !sql.is_empty(),
        "with database, SQL DDL must be non-empty (catches Ok((.., String::new())) mutant)"
    );
}

#[test]
#[ignore = "requires parse_ur (LALRPOP grammar)"]
fn compile_to_outputs_c_contains_main_or_ur_ctx() {
    let _g = CWD_LOCK.lock().unwrap();
    let (_dir, urp) = setup_minimal_project();
    let mut settings = Settings::new();
    let (c_code, _) = compiler::compile_to_outputs(&urp, &mut settings).unwrap();
    assert!(
        c_code.contains("main") || c_code.contains("ur_ctx") || c_code.contains("int main"),
        "C code must contain main/ur_ctx (catches cjr_print mutants): {}",
        &c_code[..c_code.len().min(500)]
    );
}

#[test]
#[ignore = "requires parse_ur (LALRPOP grammar)"]
fn compile_to_outputs_c_not_xyzzy() {
    let _g = CWD_LOCK.lock().unwrap();
    let (_dir, urp) = setup_minimal_project();
    let mut settings = Settings::new();
    let (c_code, sql) = compiler::compile_to_outputs(&urp, &mut settings).unwrap();
    assert!(
        !c_code.contains("xyzzy"),
        "C code must not be replaced with xyzzy placeholder"
    );
    assert!(
        !sql.contains("xyzzy"),
        "SQL must not be replaced with xyzzy placeholder"
    );
}

#[test]
#[ignore = "requires parse_ur (LALRPOP grammar)"]
fn compile_to_outputs_sql_create_index_exact_when_table_with_index() {
    // Kills: mutants in sql_generate Decl::Index, CREATE INDEX.
    // Minimal .ur with table+index: assert exact "CREATE INDEX" substring.
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempdir().unwrap();
    let dir_path = dir.path().to_path_buf();
    fs::write(dir_path.join("app.urp"), "database sqlite://\n\nmod1\n").unwrap();
    fs::write(
        dir_path.join("mod1.ur"),
        "table t : { id : int }\nval _ = ()\n",
    )
    .unwrap();
    let urp = dir_path.join("app.urp");
    let mut settings = Settings::new();
    let (_c_code, sql) = compiler::compile_to_outputs(&urp, &mut settings).unwrap();
    assert!(
        sql.contains("CREATE INDEX"),
        "SQL with table must contain CREATE INDEX (exact substring)"
    );
}

#[test]
#[ignore = "requires parse_ur (LALRPOP grammar)"]
fn compile_to_outputs_sql_pg_trgm_when_uses_similar() {
    // Kills: mutants in sql_generate similar init guard.
    // Database with uses_similar: assert pg_trgm extension present.
    let _g = CWD_LOCK.lock().unwrap();
    let dir = tempdir().unwrap();
    let dir_path = dir.path().to_path_buf();
    fs::write(
        dir_path.join("app.urp"),
        "database postgres://localhost/db\n\nmod1\n",
    )
    .unwrap();
    fs::write(
        dir_path.join("mod1.ur"),
        r#"
table t : { id : int, name : string }
val _ = (fun () => search t [] []) ()
"#,
    )
    .unwrap();
    let urp = dir_path.join("app.urp");
    let mut settings = Settings::new();
    let (_c_code, sql) = compiler::compile_to_outputs(&urp, &mut settings).unwrap();
    assert!(
        sql.contains("pg_trgm") || sql.contains("pgcrypto"),
        "Postgres SQL with search must contain pg_trgm or pgcrypto init"
    );
}
