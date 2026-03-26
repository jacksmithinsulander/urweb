//! Integration tests for [`ur::db`] — every backend codegen path, unknown `dbms`, SQL wires, default Postgres.

mod common;

use std::fs;
use std::sync::Mutex;
use tempfile::tempdir;
use ur::db;

static CWD_LOCK: Mutex<()> = Mutex::new(());

/// Native `-dbms` values emit vendor headers (not `sqlite3.h`).
#[test]
fn compile_to_outputs_each_native_backend_emits_vendor_client() {
    let needle_for: &[(&str, &str)] = &[
        ("persy", "persy_handle"),
        ("rocksdb", "rocksdb/c.h"),
        ("ndb", "urweb_ndb_open"),
        ("tigerbeetle", "tb_client.h"),
    ];
    for (canon, needle) in needle_for {
        let _g = CWD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let dir = tempdir().unwrap();
        let dir_path = dir.path().to_path_buf();
        let urp_body = format!("dbms {canon}\ndatabase :memory:\n\nm\n");
        fs::write(dir_path.join("app.urp"), urp_body).unwrap();
        fs::write(dir_path.join("m.ur"), "val x = 1").unwrap();
        let urp = dir_path.join("app.urp");

        std::env::set_current_dir(&dir_path).unwrap();
        let (c, _) = common::compile_to_outputs_bounded(urp.clone(), |_| {}).unwrap();
        assert!(
            c.contains(needle),
            "dbms {canon} should mention {needle}: {}",
            &c[..c.len().min(500)]
        );
        assert!(
            !c.contains("sqlite3.h"),
            "dbms {canon} must not use sqlite3.h"
        );
    }
}

/// TigerBeetle `urweb_tb_transfer` lowers to a blocking `tb_client_submit` + `CREATE_TRANSFERS`.
#[test]
fn compile_to_outputs_tigerbeetle_emits_transfer_submit() {
    let _g = CWD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = tempdir().unwrap();
    let dir_path = dir.path().to_path_buf();
    fs::write(
        dir_path.join("app.urp"),
        "dbms tigerbeetle\ndatabase 127.0.0.1:3000\n\nm\n",
    )
    .unwrap();
    fs::write(dir_path.join("m.ur"), "val x = 1").unwrap();
    let urp = dir_path.join("app.urp");
    std::env::set_current_dir(&dir_path).unwrap();
    let (c, _) = common::compile_to_outputs_bounded(urp.clone(), |_| {}).unwrap();
    assert!(
        c.contains("tb_client_submit") && c.contains("TB_OPERATION_CREATE_TRANSFERS"),
        "expected TigerBeetle transfer submit in C: {}",
        &c[..c.len().min(700)]
    );
}

#[test]
fn compile_to_outputs_rejects_unknown_dbms_name() {
    let _g = CWD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = tempdir().unwrap();
    let dir_path = dir.path().to_path_buf();
    fs::write(dir_path.join("app.urp"), "dbms oracle\ndatabase x\n\nm\n").unwrap();
    fs::write(dir_path.join("m.ur"), "val x = 1").unwrap();
    let urp = dir_path.join("app.urp");

    std::env::set_current_dir(&dir_path).unwrap();
    let err = common::compile_to_outputs_bounded(urp.clone(), |_| {}).unwrap_err();
    let msg = format!("{err:#}");
    assert!(
        msg.contains("unknown dbms") || msg.contains("oracle"),
        "expected unknown dbms, got: {msg}"
    );
}

/// `compile_to_outputs` includes DB client headers for each SQL wire.
fn compile_dbms_urp_minimal_c(urp_body: &str) -> String {
    let _g = CWD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = tempdir().unwrap();
    let dir_path = dir.path().to_path_buf();
    fs::write(dir_path.join("app.urp"), urp_body).unwrap();
    fs::write(dir_path.join("m.ur"), "val x = 1").unwrap();
    let urp = dir_path.join("app.urp");
    std::env::set_current_dir(&dir_path).unwrap();
    let (c_code, _) = common::compile_to_outputs_bounded(urp.clone(), |_| {}).unwrap_or_else(|e| {
        panic!("compile_to_outputs must succeed for minimal SQL URP ({urp_body:?}): {e:#}")
    });
    assert!(
        !c_code.trim().is_empty(),
        "expected non-empty generated C for {urp_body:?}"
    );
    c_code
}

#[test]
fn functional_compile_sqlite_includes_sqlite3_header() {
    let c = compile_dbms_urp_minimal_c("dbms sqlite\ndatabase :memory:\n\nm\n");
    assert!(
        c.contains("sqlite3.h"),
        "sqlite: {}",
        &c[..c.len().min(400)]
    );
}

#[test]
fn functional_compile_mysql_includes_mysql_header() {
    let c = compile_dbms_urp_minimal_c("dbms mysql\ndatabase dbname=test host=localhost\n\nm\n");
    assert!(c.contains("mysql.h"), "mysql: {}", &c[..c.len().min(400)]);
}

#[test]
fn functional_compile_postgres_includes_libpq_header() {
    let c = compile_dbms_urp_minimal_c("dbms postgres\ndatabase postgres://localhost/db\n\nm\n");
    assert!(
        c.contains("libpq-fe.h"),
        "postgres: {}",
        &c[..c.len().min(400)]
    );
}

#[test]
fn functional_compile_omitted_dbms_uses_postgres_libpq_header() {
    let c = compile_dbms_urp_minimal_c("database postgres://localhost/db\n\nm\n");
    assert!(
        c.contains("libpq-fe.h"),
        "default backend must emit libpq: {}",
        &c[..c.len().min(400)]
    );
}

#[test]
fn public_db_api_lists_alternate_backends() {
    assert!(db::NON_SQL_BACKENDS.contains(&"persy"));
    assert!(db::NON_SQL_BACKENDS.contains(&"rocksdb"));
    assert!(db::NON_SQL_BACKENDS.contains(&"ndb"));
    assert!(db::NON_SQL_BACKENDS.contains(&"tigerbeetle"));
    assert!(db::KV_BACKENDS.contains(&"tigerbeetle"));
    assert!(!db::SQL_BACKENDS.contains(&"tigerbeetle"));
}

#[test]
fn parse_tigerbeetle_case_insensitive() {
    assert_eq!(
        db::ProjectDb::parse_user_input("TigerBeetle").unwrap(),
        db::ProjectDb::Tigerbeetle
    );
}
