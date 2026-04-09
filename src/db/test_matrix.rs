//! Exhaustive unit tests for every backend and [`ProjectDbCtx`].

use super::{
    apply_urp_job_db_fields, canonical_dbms, link_library_flag_from_option, mangle_sql_ident,
    mangle_sql_table, merge_optional_dbms_token, require_sql_codegen_from_option, resolved_backend,
    set_backend_from_cli_token, validate_manifest_db_engine, DatabaseBackend, LangsecParseProfile,
    ProjectDb, ProjectDbCtx, SqlFlavor, KNOWN_DB_NAMES, NON_SQL_BACKENDS, SQL_BACKENDS,
};
use crate::settings::Settings;
use std::sync::atomic::Ordering;

fn string_result<T>(result: std::result::Result<T, String>) -> anyhow::Result<T> {
    result.map_err(anyhow::Error::msg)
}

fn all_project_db_variants() -> Vec<ProjectDb> {
    vec![
        ProjectDb::sqlite(),
        ProjectDb::mysql(),
        ProjectDb::postgres(),
        ProjectDb::Persy,
        ProjectDb::Rocksdb,
        ProjectDb::Ndb,
        ProjectDb::Tigerbeetle,
    ]
}

#[test]
fn known_db_names_match_sql_plus_non_sql_lists() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let mut expected: Vec<&str> = SQL_BACKENDS.to_vec();
    expected.extend_from_slice(NON_SQL_BACKENDS);
    assert_eq!(
        KNOWN_DB_NAMES.len(),
        expected.len(),
        "KNOWN_DB_NAMES must list each SQL and non-SQL name exactly once"
    );
    for name in KNOWN_DB_NAMES {
        assert!(expected.contains(name), "{name} not in merged list");
    }
    Ok(()) // return success to the test harness
}

#[test]
fn parse_roundtrip_lowercase_known_names() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    for name in KNOWN_DB_NAMES {
        let db = string_result(ProjectDb::parse_user_input(name))?;
        assert_eq!(db.canonical_name(), *name);
    }
    Ok(()) // return success to the test harness
}

#[test]
fn parse_case_insensitive_each_known() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    for name in KNOWN_DB_NAMES {
        let mixed: String = name
            .chars()
            .enumerate()
            .map(|(i, c)| {
                if i % 2 == 0 {
                    c.to_ascii_uppercase()
                } else {
                    c.to_ascii_lowercase()
                }
            })
            .collect();
        let db = string_result(ProjectDb::parse_user_input(&mixed))?;
        assert_eq!(db.canonical_name(), *name, "from mixed-case {mixed:?}");
    }
    Ok(()) // return success to the test harness
}

#[test]
fn parse_rejects_empty_and_unknown() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    assert!(ProjectDb::parse_user_input("").is_err());
    assert!(ProjectDb::parse_user_input("oracle").is_err());
    let err = match ProjectDb::parse_user_input("mssql") {
        Ok(db) => {
            return Err(anyhow::anyhow!(
                "expected parse error for unknown dbms, got {:?}",
                db
            ));
        }
        Err(error) => error,
    };
    assert!(err.contains("unknown dbms"), "{err}");
    Ok(()) // return success to the test harness
}

#[test]
fn canonical_dbms_matches_parse() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    assert_eq!(string_result(canonical_dbms("MySQL"))?, "mysql");
    Ok(()) // return success to the test harness
}

#[test]
fn sql_wire_names_match_relational_emission() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    assert_eq!(ProjectDb::sqlite().sql_wire_name(), Some("sqlite"));
    assert_eq!(ProjectDb::mysql().sql_wire_name(), Some("mysql"));
    assert_eq!(ProjectDb::postgres().sql_wire_name(), Some("postgres"));
    for r in [
        ProjectDb::Persy,
        ProjectDb::Rocksdb,
        ProjectDb::Ndb,
        ProjectDb::Tigerbeetle,
    ] {
        assert_eq!(r.sql_wire_name(), None, "{r:?}");
    }
    Ok(()) // return success to the test harness
}

#[test]
fn sql_flavor_wire_name_const() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    assert_eq!(SqlFlavor::Sqlite.wire_name(), "sqlite");
    assert_eq!(SqlFlavor::Mysql.wire_name(), "mysql");
    assert_eq!(SqlFlavor::Postgresql.wire_name(), "postgres");
    Ok(()) // return success to the test harness
}

#[test]
fn dialect_helpers_per_sql_flavor() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let sl = ProjectDb::sqlite();
    assert!(sl.is_sqlite());
    assert!(!sl.is_mysql());
    assert!(!sl.is_postgres_family());

    let my = ProjectDb::mysql();
    assert!(!my.is_sqlite());
    assert!(my.is_mysql());
    assert!(!my.is_postgres_family());

    let pg = ProjectDb::postgres();
    assert!(!pg.is_sqlite());
    assert!(!pg.is_mysql());
    assert!(pg.is_postgres_family());
    Ok(()) // return success to the test harness
}

#[test]
fn native_dbms_are_not_sqlite_dialect_flags() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    for db in [
        ProjectDb::Persy,
        ProjectDb::Rocksdb,
        ProjectDb::Ndb,
        ProjectDb::Tigerbeetle,
    ] {
        assert!(!db.is_sqlite(), "{db:?}");
        assert!(!db.is_mysql(), "{db:?}");
        assert!(!db.is_postgres_family(), "{db:?}");
        assert!(!db.emits_foreign_relational_sql_ddl(), "{db:?}");
    }
    Ok(()) // return success to the test harness
}

#[test]
fn langsec_profile_groups_native_backends() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    assert_eq!(
        ProjectDb::postgres().langsec_parse_profile(),
        LangsecParseProfile::RelationalSql
    );
    assert_eq!(
        ProjectDb::Rocksdb.langsec_parse_profile(),
        LangsecParseProfile::KeyValueStore
    );
    assert_eq!(
        ProjectDb::Tigerbeetle.langsec_parse_profile(),
        LangsecParseProfile::Ledger
    );
    Ok(()) // return success to the test harness
}

#[test]
fn require_sql_accepts_all_known_backends() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    for db in all_project_db_variants() {
        assert!(
            db.require_sql_code_generation().is_ok(),
            "codegen must run for {db:?}"
        );
    }
    Ok(()) // return success to the test harness
}

#[test]
fn link_library_flag_matrix() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let expected: &[(&str, &str)] = &[
        ("sqlite", "-lsqlite3"),
        ("mysql", "-lmysqlclient"),
        ("postgres", "-lpq"),
        ("persy", "-lurweb_persy"),
        ("rocksdb", "-lrocksdb -lstdc++"),
        ("ndb", "-lurweb_ndb"),
        ("tigerbeetle", "-ltb_client"),
    ];
    for (name, flag) in expected {
        let db = string_result(ProjectDb::parse_user_input(name))?;
        assert_eq!(db.link_library_flag(), *flag, "{name}");
    }
    Ok(()) // return success to the test harness
}

#[test]
fn resolved_none_is_postgres_family() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let none: Option<ProjectDb> = None;
    assert!(resolved_backend(&none).is_postgres_family());
    assert_eq!(resolved_backend(&none).link_library_flag(), "-lpq");
    let ctx = ProjectDbCtx::new(&none);
    assert!(ctx.is_postgres_family());
    assert_eq!(ctx.link_library_flag(), "-lpq");
    Ok(()) // return success to the test harness
}

#[test]
fn project_db_ctx_matches_resolved_backend_for_each_variant() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    for db in all_project_db_variants() {
        let opt = Some(db);
        let ctx = ProjectDbCtx::new(&opt);
        assert_eq!(ctx.resolved(), db);
        assert_eq!(ctx.link_library_flag(), db.link_library_flag());
        assert_eq!(ctx.is_mysql(), db.is_mysql());
        assert_eq!(ctx.is_sqlite(), db.is_sqlite());
        assert_eq!(ctx.is_postgres_family(), db.is_postgres_family());
    }
    Ok(()) // return success to the test harness
}

#[test]
fn link_and_require_helpers_from_option() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let none: Option<ProjectDb> = None;
    assert_eq!(link_library_flag_from_option(&none), "-lpq");
    assert!(require_sql_codegen_from_option(&none).is_ok());

    let rocks = Some(ProjectDb::Rocksdb);
    assert_eq!(link_library_flag_from_option(&rocks), "-lrocksdb -lstdc++");
    assert!(require_sql_codegen_from_option(&rocks).is_ok());
    Ok(()) // return success to the test harness
}

/// Mutants that replace [`require_sql_codegen_from_option`] with a bare `Ok(())` skip the invocation counter.
#[test]
fn require_sql_codegen_from_option_runs_real_body() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    super::REQUIRE_SQL_CODEGEN_FROM_OPTION_INVOCATIONS.store(0, Ordering::SeqCst);
    require_sql_codegen_from_option(&Some(ProjectDb::sqlite()))?;
    assert!(
        super::REQUIRE_SQL_CODEGEN_FROM_OPTION_INVOCATIONS.load(Ordering::SeqCst) >= 1,
        "wrapper must call into ProjectDbCtx (not empty body)"
    );
    Ok(()) // return success to the test harness
}

#[test]
fn merge_optional_only_when_unset() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let mut slot = None;
    string_result(merge_optional_dbms_token(&mut slot, Some("mysql")))?;
    assert_eq!(slot, Some(ProjectDb::mysql()));
    string_result(merge_optional_dbms_token(&mut slot, Some("sqlite")))?;
    assert_eq!(slot, Some(ProjectDb::mysql()));

    let mut slot2: Option<ProjectDb> = Some(ProjectDb::postgres());
    string_result(merge_optional_dbms_token(&mut slot2, Some("mysql")))?;
    assert_eq!(slot2, Some(ProjectDb::postgres()));
    Ok(()) // return success to the test harness
}

#[test]
fn merge_optional_none_token_leaves_unset() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let mut slot: Option<ProjectDb> = None;
    string_result(merge_optional_dbms_token(&mut slot, None))?;
    assert!(slot.is_none());
    Ok(()) // return success to the test harness
}

#[test]
fn mangle_sql_ident_each_sql_flavor_when_mangle_true() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let my = ProjectDb::mysql();
    assert_eq!(mangle_sql_ident(&my, true, "Foo"), "uw_foo");

    let pg = ProjectDb::postgres();
    assert_eq!(mangle_sql_ident(&pg, true, "Foo"), "uw_Foo");

    let sl = ProjectDb::sqlite();
    assert_eq!(mangle_sql_ident(&sl, true, "Foo"), "uw_Foo");
    Ok(()) // return success to the test harness
}

#[test]
fn mangle_sql_table_sqlite_matches_postgres_capitalization() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let sl = ProjectDb::sqlite();
    let pg = ProjectDb::postgres();
    assert_eq!(mangle_sql_table(&sl, true, "users"), "uw_Users");
    assert_eq!(mangle_sql_table(&pg, true, "users"), "uw_Users");
    Ok(()) // return success to the test harness
}

#[test]
fn non_sql_lists_disjoint_from_sql_backends() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    for n in NON_SQL_BACKENDS {
        assert!(
            !SQL_BACKENDS.contains(n),
            "{n} must not be listed as SQL backend"
        );
    }
    Ok(()) // return success to the test harness
}

#[test]
fn validate_manifest_db_engine_accepts_known_names() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    for name in KNOWN_DB_NAMES {
        string_result(validate_manifest_db_engine(name))?;
    }
    Ok(()) // return success to the test harness
}

#[test]
fn validate_manifest_db_engine_rejects_unknown() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    assert!(validate_manifest_db_engine("oracle").is_err());
    Ok(()) // return success to the test harness
}

#[test]
fn set_backend_from_cli_token_overwrites() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let mut s = Settings::new();
    string_result(set_backend_from_cli_token(&mut s, "mysql"))?;
    assert_eq!(s.db_backend, Some(ProjectDb::mysql()));
    string_result(set_backend_from_cli_token(&mut s, "sqlite"))?;
    assert_eq!(s.db_backend, Some(ProjectDb::sqlite()));
    Ok(()) // return success to the test harness
}

#[test]
fn apply_urp_job_db_fields_fills_when_unset() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let mut s = Settings::new();
    string_result(apply_urp_job_db_fields(
        &mut s,
        Some("mysql"),
        Some("host=x"),
    ))?;
    assert_eq!(s.db_backend, Some(ProjectDb::mysql()));
    assert_eq!(s.dbstring.as_deref(), Some("host=x"));
    Ok(()) // return success to the test harness
}

#[test]
fn apply_urp_respects_cli_precedence_dbms() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let mut s = Settings::new();
    string_result(set_backend_from_cli_token(&mut s, "sqlite"))?;
    string_result(apply_urp_job_db_fields(
        &mut s,
        Some("mysql"),
        Some("from.urp"),
    ))?;
    assert_eq!(s.db_backend, Some(ProjectDb::sqlite()));
    assert_eq!(s.dbstring.as_deref(), Some("from.urp"));
    Ok(()) // return success to the test harness
}

#[test]
fn apply_urp_does_not_overwrite_dbstring_from_cli() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let mut s = Settings::new();
    s.dbstring = Some("cli-conn".into());
    string_result(apply_urp_job_db_fields(
        &mut s,
        Some("postgres"),
        Some("urp-conn"),
    ))?;
    assert_eq!(s.dbstring.as_deref(), Some("cli-conn"));
    Ok(()) // return success to the test harness
}
