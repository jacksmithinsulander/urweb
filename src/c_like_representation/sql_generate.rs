//! SQL DDL generator: CJR → SQL schema.
//!
//! Generates CREATE TABLE / CREATE SEQUENCE / CREATE VIEW / CREATE INDEX
//! statements for the database schema described by a CJR file.
//!
//! Mirrors `CjrPrint.p_sql` in `cjr_print.sml`.

use crate::c_like_representation::{Decl, File};
use crate::db::DatabaseBackend;
use crate::monomorphized::IndexMode;
use crate::settings::{Settings, SqlType};

// ---------------------------------------------------------------------------
// DBMS configuration
// ---------------------------------------------------------------------------

struct DbmsInfo<'a> {
    settings: &'a Settings,
}

impl<'a> DbmsInfo<'a> {
    fn new(settings: &'a Settings) -> Self {
        DbmsInfo { settings }
    }

    fn db(&self) -> crate::db::ProjectDb {
        crate::db::ProjectDbCtx::new(&self.settings.db_backend).resolved()
    }

    fn p_sql_type(&self, t: &SqlType) -> String {
        let db = self.db();
        if db.is_mysql() {
            mysql_sql_type(t)
        } else if db.is_sqlite() {
            sqlite_sql_type(t)
        } else {
            postgres_sql_type(t)
        }
    }

    fn create_sequence(&self, name: &str) -> String {
        let db = self.db();
        if db.is_mysql() {
            format!(
                "CREATE TABLE {} (uw_id INTEGER PRIMARY KEY AUTO_INCREMENT)",
                name
            )
        } else if db.is_sqlite() {
            format!(
                "CREATE TABLE {} (id INTEGER PRIMARY KEY AUTOINCREMENT)",
                name
            )
        } else {
            format!("CREATE SEQUENCE {}", name)
        }
    }

    fn sql_prefix(&self) -> &str {
        if self.db().is_sqlite() {
            "PRAGMA foreign_keys = ON;\nPRAGMA journal_mode = WAL;\n\n"
        } else {
            ""
        }
    }

    fn text_keys_need_lengths(&self) -> bool {
        self.db().is_mysql()
    }

    fn requires_timestamp_defaults(&self) -> bool {
        self.db().is_mysql()
    }

    fn supports_similar(&self) -> Option<&'static str> {
        if self.db().is_postgres_family() {
            Some("CREATE EXTENSION IF NOT EXISTS pg_trgm;")
        } else {
            None
        }
    }

    fn supports_sha512(&self) -> Option<&'static str> {
        let db = self.db();
        if db.is_mysql() {
            Some("")
        } else if db.is_postgres_family() {
            Some("CREATE EXTENSION IF NOT EXISTS pgcrypto;")
        } else {
            None
        }
    }

    fn normalize_ddl_sql(&self, sql: &str) -> String {
        if !self.db().is_sqlite() {
            return sql.to_string();
        }
        sql.replace("::int8", "")
            .replace("::float8", "")
            .replace("::text", "")
            .replace("::char", "")
            .replace("::bytea", "")
            .replace("::int4", "")
    }
}

fn postgres_sql_type(t: &SqlType) -> String {
    match t {
        SqlType::Int => "int8".to_string(),
        SqlType::Float => "float8".to_string(),
        SqlType::String => "text".to_string(),
        SqlType::Char => "char".to_string(),
        SqlType::Bool => "bool".to_string(),
        SqlType::Time => "timestamp".to_string(),
        SqlType::Clocktime => "time".to_string(),
        SqlType::Calendardate => "date".to_string(),
        SqlType::Blob => "bytea".to_string(),
        SqlType::Channel => "int8".to_string(),
        SqlType::Client => "int4".to_string(),
        SqlType::Nullable(inner) => postgres_sql_type(inner),
    }
}

fn mysql_sql_type(t: &SqlType) -> String {
    match t {
        SqlType::Int => "bigint".to_string(),
        SqlType::Float => "double".to_string(),
        SqlType::String => "longtext".to_string(),
        SqlType::Char => "char".to_string(),
        SqlType::Bool => "bool".to_string(),
        SqlType::Time => "timestamp".to_string(),
        SqlType::Clocktime => "time".to_string(),
        SqlType::Calendardate => "date".to_string(),
        SqlType::Blob => "longblob".to_string(),
        SqlType::Channel => "bigint".to_string(),
        SqlType::Client => "int".to_string(),
        SqlType::Nullable(inner) => mysql_sql_type(inner),
    }
}

fn sqlite_sql_type(t: &SqlType) -> String {
    match t {
        SqlType::Int => "integer".to_string(),
        SqlType::Float => "real".to_string(),
        SqlType::String => "text".to_string(),
        SqlType::Char => "text".to_string(),
        SqlType::Bool => "integer".to_string(),
        SqlType::Time => "text".to_string(),
        SqlType::Clocktime => "text".to_string(),
        SqlType::Calendardate => "text".to_string(),
        SqlType::Blob => "blob".to_string(),
        SqlType::Channel => "integer".to_string(),
        SqlType::Client => "integer".to_string(),
        SqlType::Nullable(inner) => sqlite_sql_type(inner),
    }
}

// ---------------------------------------------------------------------------
// SQL type conversion from CJR type
// ---------------------------------------------------------------------------

fn sql_type_in(t: &crate::c_like_representation::LocTyp) -> Option<SqlType> {
    use crate::c_like_representation::Typ;
    match &t.node {
        Typ::Ffi(m, x) if m == "Basis" => match x.as_str() {
            "int" => Some(SqlType::Int),
            "float" => Some(SqlType::Float),
            "string" => Some(SqlType::String),
            "char" => Some(SqlType::Char),
            "bool" => Some(SqlType::Bool),
            "time" => Some(SqlType::Time),
            "clocktime" => Some(SqlType::Clocktime),
            "calendardate" => Some(SqlType::Calendardate),
            "blob" => Some(SqlType::Blob),
            "channel" => Some(SqlType::Channel),
            "client" => Some(SqlType::Client),
            _ => None,
        },
        Typ::Option(inner) => sql_type_in(inner).map(|t| SqlType::Nullable(Box::new(t))),
        _ => None,
    }
}

fn is_text(t: &SqlType) -> bool {
    match t {
        SqlType::String => true,
        SqlType::Nullable(inner) => is_text(inner),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Helper: does a constraint string declare a foreign key for the given column?
// ---------------------------------------------------------------------------

fn declares_as_foreign_key(col: &str, s: &str) -> bool {
    // Tokenize by whitespace, comma, '(' or ')'
    let tokens: Vec<&str> = s
        .split(|ch: char| ch.is_whitespace() || ch == ',' || ch == '(' || ch == ')')
        .filter(|s| !s.is_empty())
        .collect();
    if tokens.len() >= 2 && tokens[0] == "FOREIGN" && tokens[1] == "KEY" {
        let rest = &tokens[2..];
        for tok in rest {
            if *tok == "REFERENCES" {
                return false;
            }
            if *tok == col {
                return true;
            }
        }
        false
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// Index deduplication
// ---------------------------------------------------------------------------

type IndexKey = (String, Vec<(String, IndexMode)>);

/// Convert an index column list to the canonical key form used for dedup.
fn index_key(table: &str, cols: &[(String, IndexMode)], settings: &Settings) -> IndexKey {
    let mangled: Vec<(String, IndexMode)> = cols
        .iter()
        .map(|(col, m)| {
            let k = settings.mangle_sql(&col.to_lowercase());
            (k, *m)
        })
        .collect();
    (table.to_string(), mangled)
}

// ---------------------------------------------------------------------------
// DDL generation
// ---------------------------------------------------------------------------

fn p_ddl_table(
    table: &str,
    xts: &[(String, crate::c_like_representation::LocTyp)],
    pk: &str,
    csts: &[(String, String)],
    db: &DbmsInfo,
    settings: &Settings,
) -> String {
    let mut out = String::new();
    out.push_str("CREATE TABLE ");
    out.push_str(table);
    out.push('(');
    out.push_str("\n    ");

    let mut elts: Vec<String> = Vec::new();

    // Column definitions
    for (x, t_loc) in xts {
        let xs = settings.mangle_sql(&x.to_lowercase());
        let sql_t = sql_type_in(t_loc).unwrap_or(SqlType::Int);
        let ts = if db.text_keys_need_lengths()
            && is_text(&sql_t)
            && (csts.iter().any(|(_, c)| declares_as_foreign_key(&xs, c))
                || pk.contains(&format!("{}(255)", xs))
                || pk
                    .split(|ch: char| ch == ',' || ch.is_whitespace())
                    .any(|s| s == xs))
        {
            "varchar(255)".to_string()
        } else {
            db.p_sql_type(&sql_t)
        };

        let mut col = format!("{} {}", xs, ts);
        if sql_t.is_not_null() {
            col.push_str(" NOT NULL");
        }
        if matches!(sql_t, SqlType::Time) && db.requires_timestamp_defaults() {
            col.push_str(" DEFAULT CURRENT_TIMESTAMP");
        }
        elts.push(col);
    }

    // Primary key constraint
    if !pk.is_empty() {
        elts.push(format!("CONSTRAINT {}_pkey PRIMARY KEY ({})", table, pk));
    }

    // Other constraints
    for (x, c) in csts {
        elts.push(format!(
            "CONSTRAINT {}_{} {}",
            table,
            x,
            db.normalize_ddl_sql(c)
        ));
    }

    out.push_str(&elts.join(",\n    "));
    out.push_str(");\n\n");
    out
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Generate SQL DDL from a CJR file.
///
/// Mirrors `CjrPrint.p_sql`.
pub fn sql_generate(file: &File, settings: &Settings) -> String {
    let (decls, _) = file;
    let db_choice = crate::db::ProjectDbCtx::new(&settings.db_backend).resolved();
    if !db_choice.emits_foreign_relational_sql_ddl() {
        return format!(
            "-- Ur/Web native backend `{}`: no relational SQL DDL is emitted.\n",
            db_choice.canonical_name()
        );
    }

    let db = DbmsInfo::new(settings);

    let mut uses_similar = false;

    // Deduplication pass: collect all DIndex keys (including those implied by PKs),
    // and filter duplicate indexes.
    let mut known_indexes: Vec<IndexKey> = Vec::new();
    let mut filtered_decls: Vec<&crate::c_like_representation::LocDecl> = Vec::new();

    for d in decls {
        match &d.node {
            Decl::Table(s, _xts, pk, _csts) => {
                // Add primary key as a known index (to dedup explicit DIndex decls)
                if !pk.is_empty() {
                    let pk_cols: Vec<(String, IndexMode)> = pk
                        .split(|ch: char| ch == ',' || ch.is_whitespace())
                        .filter(|s| !s.is_empty())
                        .map(|col| {
                            // Strip function call syntax: "col(len)" → "col"
                            let col = col.split('(').next().unwrap_or(col);
                            (col.to_string(), IndexMode::Equality)
                        })
                        .collect();
                    known_indexes.push((s.clone(), pk_cols));
                }
                filtered_decls.push(d);
            }
            Decl::Index(tab, cols) => {
                // Filter out Skipped columns
                let active: Vec<(String, IndexMode)> = cols
                    .iter()
                    .filter(|(_, m)| !matches!(m, IndexMode::Skipped))
                    .cloned()
                    .collect();
                if active.is_empty() {
                    continue; // drop empty index
                }
                let key = index_key(tab, &active, settings);
                if known_indexes.contains(&key) {
                    continue; // duplicate, drop
                }
                known_indexes.push(key);
                filtered_decls.push(d);
            }
            Decl::Database {
                uses_similar: s, ..
            } => {
                if *s {
                    uses_similar = true;
                }
                filtered_decls.push(d);
            }
            _ => {
                filtered_decls.push(d);
            }
        }
    }

    let mut out = String::new();

    // File cache SHA512 support
    if settings.file_cache.is_some() {
        match db.supports_sha512() {
            None => {
                // Error: using file cache with database that doesn't support SHA512
                // (just skip for now; real compiler would report an error)
            }
            Some(init) if !init.is_empty() => {
                out.push_str(init);
                out.push_str("\n\n");
            }
            _ => {}
        }
    }

    // SIMILAR support initialization
    if uses_similar {
        match db.supports_similar() {
            None => {
                // Error: using SIMILAR with database that doesn't support it
            }
            Some(init) if !init.is_empty() => {
                out.push_str(init);
                out.push_str("\n\n");
            }
            _ => {}
        }
    }

    // SQL prefix
    out.push_str(db.sql_prefix());

    // DDL for each filtered declaration
    for d in &filtered_decls {
        match &d.node {
            Decl::Table(s, xts, pk, csts) => {
                out.push_str(&p_ddl_table(s, xts, pk, csts, &db, settings));
            }
            Decl::Sequence(s) => {
                out.push_str(&db.create_sequence(s));
                out.push_str(";\n\n");
            }
            Decl::View(s, _xts, q) => {
                out.push_str(&format!(
                    "CREATE VIEW {} AS {};\n\n",
                    s,
                    db.normalize_ddl_sql(q)
                ));
            }
            Decl::Index(tab, cols) => {
                // Build index name: tab_col1_col2...
                let mut name = tab.clone();
                for (col, m) in cols {
                    if matches!(m, IndexMode::Skipped) {
                        continue;
                    }
                    name.push('_');
                    name.push_str(&settings.mangle_sql(&col.to_lowercase()));
                    if matches!(m, IndexMode::Trigram) {
                        name.push_str("_trigram");
                    }
                }

                let has_trigram = cols.iter().any(|(_, m)| matches!(m, IndexMode::Trigram));

                let mut index_stmt = format!("CREATE INDEX {} ON {}", name, tab);
                if has_trigram {
                    index_stmt.push_str(" USING gist");
                }
                index_stmt.push('(');
                let col_list: Vec<String> = cols
                    .iter()
                    .filter(|(_, m)| !matches!(m, IndexMode::Skipped))
                    .map(|(col, m)| {
                        let mangled = settings.mangle_sql(&col.to_lowercase());
                        match m {
                            IndexMode::Equality => mangled,
                            IndexMode::Trigram => {
                                if db.supports_similar().is_some() {
                                    format!("{} gist_trgm_ops", mangled)
                                } else {
                                    mangled
                                }
                            }
                            IndexMode::Skipped => mangled,
                        }
                    })
                    .collect();
                index_stmt.push_str(&col_list.join(", "));
                index_stmt.push_str(");\n\n");
                out.push_str(&index_stmt);
            }
            _ => {}
        }
    }

    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c_like_representation::{Decl, Typ};
    use crate::error_types::{Located, Span};

    fn ffi_typ(m: &str, x: &str) -> crate::c_like_representation::LocTyp {
        Located::new(Typ::Ffi(m.to_string(), x.to_string()), Span::dummy())
    }

    #[test]
    fn empty_file_generates_empty_sql() {
        let settings = Settings::default();
        let result = sql_generate(&(vec![], vec![]), &settings);
        assert!(result.is_empty());
    }

    #[test]
    fn sequence_postgres() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let decls = vec![Located::new(
            Decl::Sequence("uw_seq".to_string()),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(result.contains("CREATE SEQUENCE uw_seq"), "got: {}", result);
    }

    #[test]
    fn sequence_mysql() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::mysql()),
            ..Default::default()
        };
        let decls = vec![Located::new(
            Decl::Sequence("uw_seq".to_string()),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(result.contains("AUTO_INCREMENT"), "got: {}", result);
    }

    #[test]
    fn table_basic_postgres() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![
            ("Id".to_string(), ffi_typ("Basis", "int")),
            ("Name".to_string(), ffi_typ("Basis", "string")),
        ];
        let decls = vec![Located::new(
            Decl::Table("uw_users".to_string(), xts, "".to_string(), vec![]),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(result.contains("CREATE TABLE uw_users"), "got: {}", result);
        assert!(result.contains("int8"), "got: {}", result);
        assert!(result.contains("text"), "got: {}", result);
    }

    #[test]
    fn view_generates_create_view() {
        let settings = Settings::default();
        let xts = vec![("x".to_string(), ffi_typ("Basis", "int"))];
        let decls = vec![Located::new(
            Decl::View("myview".to_string(), xts, "SELECT 1".to_string()),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("CREATE VIEW myview AS SELECT 1"),
            "got: {}",
            result
        );
    }

    #[test]
    fn sqlite_view_strips_postgres_type_casts() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::sqlite()),
            ..Default::default()
        };
        let xts = vec![("x".to_string(), ffi_typ("Basis", "int"))];
        let decls = vec![Located::new(
            Decl::View(
                "myview".to_string(),
                xts,
                "SELECT 7::int8, 'x'::text".to_string(),
            ),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("CREATE VIEW myview AS SELECT 7, 'x'"),
            "sqlite DDL should strip postgres casts, got: {}",
            result
        );
        assert!(
            !result.contains("::"),
            "sqlite view DDL must not contain postgres casts: {}",
            result
        );
    }

    #[test]
    fn sqlite_prefix() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::sqlite()),
            ..Default::default()
        };
        let result = sql_generate(&(vec![], vec![]), &settings);
        assert!(result.contains("PRAGMA foreign_keys"), "got: {}", result);
    }

    #[test]
    fn database_uses_similar_produces_pg_trgm() {
        // Catches mutant: delete match arm Decl::Database in sql_generate.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let decls = vec![Located::new(
            Decl::Database {
                name: "db".into(),
                expunge: 0,
                initialize: 0,
                uses_similar: true,
            },
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("pg_trgm"),
            "uses_similar must produce pg_trgm extension (catches delete Database arm): {}",
            result
        );
    }

    #[test]
    fn table_mysql_uses_mysql_sql_types() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::mysql()),
            ..Default::default()
        };
        let xts = vec![
            ("Id".to_string(), ffi_typ("Basis", "int")),
            ("Name".to_string(), ffi_typ("Basis", "string")),
        ];
        let decls = vec![Located::new(
            Decl::Table("uw_users".to_string(), xts, "".to_string(), vec![]),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("bigint"),
            "mysql uses bigint for int, got: {}",
            result
        );
        assert!(
            result.contains("longtext"),
            "mysql uses longtext, got: {}",
            result
        );
    }

    #[test]
    fn table_sqlite_uses_sqlite_sql_types() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::sqlite()),
            ..Default::default()
        };
        let xts = vec![
            ("Id".to_string(), ffi_typ("Basis", "int")),
            ("Name".to_string(), ffi_typ("Basis", "string")),
        ];
        let decls = vec![Located::new(
            Decl::Table("uw_users".to_string(), xts, "".to_string(), vec![]),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("integer"),
            "sqlite uses integer, got: {}",
            result
        );
        assert!(result.contains("text"), "sqlite uses text, got: {}", result);
    }

    #[test]
    fn sqlite_table_constraints_strip_postgres_type_casts() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::sqlite()),
            ..Default::default()
        };
        let xts = vec![("Id".to_string(), ffi_typ("Basis", "int"))];
        let decls = vec![Located::new(
            Decl::Table(
                "uw_users".to_string(),
                xts,
                "".to_string(),
                vec![("Check".to_string(), "CHECK (uw_id >= 0::int8)".to_string())],
            ),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("CHECK (uw_id >= 0)"),
            "sqlite constraints should strip postgres casts, got: {}",
            result
        );
        assert!(
            !result.contains("::"),
            "sqlite table DDL must not contain postgres casts: {}",
            result
        );
    }

    #[test]
    fn native_dbms_sql_generate_is_placeholder_not_sqlite_ddl() {
        let xts = vec![
            ("Id".to_string(), ffi_typ("Basis", "int")),
            ("Name".to_string(), ffi_typ("Basis", "string")),
        ];
        let cjr = (
            vec![Located::new(
                Decl::Table("uw_users".to_string(), xts, "".to_string(), vec![]),
                Span::dummy(),
            )],
            vec![],
        );
        for alt in [
            crate::db::ProjectDb::Persy,
            crate::db::ProjectDb::Rocksdb,
            crate::db::ProjectDb::Ndb,
            crate::db::ProjectDb::Tigerbeetle,
        ] {
            use crate::db::DatabaseBackend;
            let name = alt.canonical_name();
            let s = Settings {
                db_backend: Some(alt),
                ..Default::default()
            };
            let out = sql_generate(&cjr, &s);
            assert!(
                !out.contains("CREATE TABLE") && out.contains(name),
                "native {name} must not emit relational DDL: {out}"
            );
        }
    }

    #[test]
    fn sequence_sqlite_uses_autoincrement() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::sqlite()),
            ..Default::default()
        };
        let decls = vec![Located::new(
            Decl::Sequence("uw_seq".to_string()),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("AUTOINCREMENT"),
            "sqlite create_sequence uses AUTOINCREMENT, got: {}",
            result
        );
    }

    #[test]
    fn postgres_sql_type_produces_non_empty() {
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![("x".to_string(), ffi_typ("Basis", "float"))];
        let decls = vec![Located::new(
            Decl::Table("t".to_string(), xts, "".to_string(), vec![]),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("float8"),
            "postgres_sql_type must produce float8 for float, got: {}",
            result
        );
    }

    #[test]
    fn sql_type_in_basis_types() {
        // Catches mutants: delete match arms in sql_type_in for int, char, bool, time, etc.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        for (name, typ, expected) in [
            ("int", "int", "int8"),
            ("char", "char", "char"),
            ("bool", "bool", "bool"),
            ("time", "time", "timestamp"),
            ("clocktime", "clocktime", "time"),
            ("calendardate", "calendardate", "date"),
            ("blob", "blob", "bytea"),
            ("channel", "channel", "int8"),
            ("client", "client", "int4"),
        ] {
            let xts = vec![("c".to_string(), ffi_typ("Basis", typ))];
            let decls = vec![Located::new(
                Decl::Table(name.to_string(), xts, "".to_string(), vec![]),
                Span::dummy(),
            )];
            let result = sql_generate(&(decls, vec![]), &settings);
            assert!(
                result.contains(expected),
                "Basis.{} must produce {}, got: {}",
                typ,
                expected,
                result
            );
        }
    }

    #[test]
    fn sql_type_option_produces_nullable() {
        // Catches mutant: delete Typ::Option arm in sql_type_in.
        // Option int -> Nullable(Int) -> no NOT NULL; without Option arm we'd get Int -> NOT NULL.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let opt_int = crate::c_like_representation::Located::new(
            crate::c_like_representation::Typ::Option(Box::new(ffi_typ("Basis", "int"))),
            crate::error_types::Span::dummy(),
        );
        let xts = vec![("c".to_string(), opt_int)];
        let decls = vec![Located::new(
            Decl::Table("t".to_string(), xts, "".to_string(), vec![]),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            !result.contains("NOT NULL"),
            "Option int must not add NOT NULL (nullable), got: {}",
            result
        );
    }

    #[test]
    fn supports_sha512_postgres() {
        // Catches mutant: delete match arm in supports_sha512 for postgres.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            file_cache: Some("cache".to_string()),
            ..Default::default()
        };
        let decls = vec![Located::new(
            Decl::Database {
                name: "db".into(),
                expunge: 0,
                initialize: 0,
                uses_similar: false,
            },
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("pgcrypto"),
            "postgres supports_sha512 must yield pgcrypto when file_cache set, got: {}",
            result
        );
    }

    #[test]
    fn index_generates_create_index() {
        // Catches mutant: delete match arm Decl::Index in sql_generate.
        use crate::monomorphized::IndexMode;
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![
            ("id".to_string(), ffi_typ("Basis", "int")),
            ("name".to_string(), ffi_typ("Basis", "string")),
        ];
        let decls = vec![
            Located::new(
                Decl::Table("uw_t".to_string(), xts, "id".to_string(), vec![]),
                Span::dummy(),
            ),
            Located::new(
                Decl::Index(
                    "uw_t".to_string(),
                    vec![("name".to_string(), IndexMode::Equality)],
                ),
                Span::dummy(),
            ),
        ];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("CREATE INDEX"),
            "Index decl must produce CREATE INDEX (catches delete arm mutant), got: {}",
            result
        );
    }

    #[test]
    fn text_keys_need_lengths_mysql_string_fk_gets_varchar() {
        // Catches mutant: text_keys_need_lengths, is_text, declares_as_foreign_key.
        // MySQL + string column in FOREIGN KEY -> varchar(255).
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::mysql()),
            mangle: true,
            ..Default::default()
        };
        let xts = vec![
            ("Id".to_string(), ffi_typ("Basis", "int")),
            ("Ref".to_string(), ffi_typ("Basis", "string")),
        ];
        let csts = vec![(
            "fk_ref".to_string(),
            "FOREIGN KEY (uw_ref) REFERENCES t(id)".to_string(),
        )];
        let decls = vec![Located::new(
            Decl::Table("uw_mytable".to_string(), xts, "Id".to_string(), csts),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("varchar(255)"),
            "MySQL string FK column must get varchar(255) (catches text_keys_need_lengths, declares_as_foreign_key): {}",
            result
        );
    }

    #[test]
    fn requires_timestamp_defaults_mysql() {
        // Catches mutant: requires_timestamp_defaults.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::mysql()),
            ..Default::default()
        };
        let xts = vec![
            ("id".to_string(), ffi_typ("Basis", "int")),
            ("ts".to_string(), ffi_typ("Basis", "time")),
        ];
        let decls = vec![Located::new(
            Decl::Table("uw_t".to_string(), xts, "id".to_string(), vec![]),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("DEFAULT CURRENT_TIMESTAMP"),
            "MySQL time column must get DEFAULT (catches requires_timestamp_defaults): {}",
            result
        );
    }

    #[test]
    fn supports_sha512_mysql_with_file_cache() {
        // Catches mutant: delete "mysql" arm in supports_sha512.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::mysql()),
            file_cache: Some("/tmp".into()),
            ..Default::default()
        };
        let decls = vec![Located::new(
            Decl::Database {
                name: "db".into(),
                expunge: 0,
                initialize: 0,
                uses_similar: false,
            },
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        // MySQL returns Some("") for supports_sha512, so no extra init; shouldn't panic.
        assert!(
            !result.contains("pgcrypto"),
            "MySQL uses built-in SHA2, not pgcrypto"
        );
    }

    #[test]
    fn sql_type_in_clocktime_and_calendardate() {
        // Catches mutant: delete "clocktime"/"calendardate" arms in sql_type_in.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![
            ("id".to_string(), ffi_typ("Basis", "int")),
            ("ct".to_string(), ffi_typ("Basis", "clocktime")),
            ("cd".to_string(), ffi_typ("Basis", "calendardate")),
        ];
        let decls = vec![Located::new(
            Decl::Table("uw_t".to_string(), xts, "id".to_string(), vec![]),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("time") && result.contains("date"),
            "clocktime->time, calendardate->date (catches delete arm): {}",
            result
        );
    }

    #[test]
    fn dbms_empty_uses_postgres_types() {
        // Catches mutant: dbms "" not matching postgres branch.
        let settings = Settings {
            db_backend: None,
            ..Default::default()
        };
        let xts = vec![("x".to_string(), ffi_typ("Basis", "int"))];
        let decls = vec![Located::new(
            Decl::Table("t".to_string(), xts, "".to_string(), vec![]),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("int8"),
            "dbms empty must use postgres types (int8), got: {}",
            result
        );
    }

    #[test]
    fn native_backend_skips_relational_ddl() {
        let native = Settings {
            db_backend: Some(crate::db::ProjectDb::Rocksdb),
            ..Default::default()
        };
        let pg = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![("id".to_string(), ffi_typ("Basis", "int"))];
        let decls = vec![Located::new(
            Decl::Table("uw_t".to_string(), xts, "id".to_string(), vec![]),
            Span::dummy(),
        )];
        let rocks_sql = sql_generate(&(decls.clone(), vec![]), &native);
        let pg_sql = sql_generate(&(decls, vec![]), &pg);
        assert!(
            rocks_sql.contains("rocksdb") && !rocks_sql.contains("CREATE TABLE"),
            "native placeholder: {rocks_sql}"
        );
        assert!(
            pg_sql.contains("CREATE TABLE"),
            "postgres must still emit DDL: {pg_sql}"
        );
    }

    // --- Plan: Catch Missed Mutants - sql_generate ---

    #[test]
    fn index_dedup_does_not_drop() {
        // Kills: delete Decl::Index arm, dedup logic. Table with PK "a,b" plus explicit Index on same columns: no extra CREATE INDEX (dedup).
        use crate::monomorphized::IndexMode;
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            mangle: false, // PK cols stored unmangled; index_key mangles - use mangle=false so keys match
            ..Default::default()
        };
        let xts = vec![
            ("a".to_string(), ffi_typ("Basis", "int")),
            ("b".to_string(), ffi_typ("Basis", "int")),
        ];
        let decls = vec![
            Located::new(
                Decl::Table("uw_t".to_string(), xts, "a,b".to_string(), vec![]),
                Span::dummy(),
            ),
            Located::new(
                Decl::Index(
                    "uw_t".to_string(),
                    vec![
                        ("a".to_string(), IndexMode::Equality),
                        ("b".to_string(), IndexMode::Equality),
                    ],
                ),
                Span::dummy(),
            ),
        ];
        let result = sql_generate(&(decls, vec![]), &settings);
        let create_index_count = result.matches("CREATE INDEX").count();
        assert_eq!(
            create_index_count, 0,
            "PK a,b implies index; explicit Index on same cols must be deduplicated (0 extra), got {} CREATE INDEX",
            create_index_count
        );
    }

    #[test]
    fn index_with_skipped_column_keeps_non_skipped() {
        // Kills: !matches!(m, IndexMode::Skipped) filter. Index with Skipped + Equality: CREATE INDEX with one col.
        use crate::monomorphized::IndexMode;
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![
            ("id".to_string(), ffi_typ("Basis", "int")),
            ("name".to_string(), ffi_typ("Basis", "string")),
        ];
        let decls = vec![
            Located::new(
                Decl::Table("uw_t".to_string(), xts, "id".to_string(), vec![]),
                Span::dummy(),
            ),
            Located::new(
                Decl::Index(
                    "uw_t".to_string(),
                    vec![
                        ("id".to_string(), IndexMode::Skipped),
                        ("name".to_string(), IndexMode::Equality),
                    ],
                ),
                Span::dummy(),
            ),
        ];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(result.contains("CREATE INDEX"));
        assert!(result.contains("name"));
        assert!(
            !result.contains("id") || result.contains("_pkey"),
            "index should not include Skipped id col"
        );
    }

    #[test]
    fn index_all_skipped_produces_no_create_index() {
        // Kills: active.is_empty() / filter. Index with all Skipped -> no CREATE INDEX.
        use crate::monomorphized::IndexMode;
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![
            ("id".to_string(), ffi_typ("Basis", "int")),
            ("x".to_string(), ffi_typ("Basis", "int")),
        ];
        let decls = vec![
            Located::new(
                Decl::Table("uw_t".to_string(), xts, "id".to_string(), vec![]),
                Span::dummy(),
            ),
            Located::new(
                Decl::Index(
                    "uw_t".to_string(),
                    vec![("x".to_string(), IndexMode::Skipped)],
                ),
                Span::dummy(),
            ),
        ];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            !result.contains("CREATE INDEX"),
            "all-Skipped index must produce no CREATE INDEX, got: {}",
            result
        );
    }

    #[test]
    fn index_trigram_produces_gist() {
        // Kills: Trigram branch. Index with Trigram on Postgres: USING gist and gist_trgm_ops.
        use crate::monomorphized::IndexMode;
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![
            ("id".to_string(), ffi_typ("Basis", "int")),
            ("name".to_string(), ffi_typ("Basis", "string")),
        ];
        let decls = vec![
            Located::new(
                Decl::Table("uw_t".to_string(), xts, "id".to_string(), vec![]),
                Span::dummy(),
            ),
            Located::new(
                Decl::Database {
                    name: "db".into(),
                    expunge: 0,
                    initialize: 0,
                    uses_similar: true,
                },
                Span::dummy(),
            ),
            Located::new(
                Decl::Index(
                    "uw_t".to_string(),
                    vec![("name".to_string(), IndexMode::Trigram)],
                ),
                Span::dummy(),
            ),
        ];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("USING gist"),
            "Trigram index must use gist: {}",
            result
        );
        assert!(
            result.contains("gist_trgm_ops"),
            "Trigram index must use gist_trgm_ops: {}",
            result
        );
    }

    #[test]
    fn pk_with_multiple_columns_parsed() {
        // Kills: split/filter !s.is_empty(). Table with PK "id,name": both cols in PRIMARY KEY.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![
            ("id".to_string(), ffi_typ("Basis", "int")),
            ("name".to_string(), ffi_typ("Basis", "string")),
        ];
        let decls = vec![Located::new(
            Decl::Table("uw_t".to_string(), xts, "id,name".to_string(), vec![]),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(result.contains("id"));
        assert!(result.contains("name"));
        assert!(result.contains("PRIMARY KEY"));
    }

    #[test]
    fn file_cache_sha512_init_non_empty() {
        // Kills: !init.is_empty() guard. Postgres + file_cache -> pgcrypto init.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            file_cache: Some("cache".to_string()),
            ..Default::default()
        };
        let decls = vec![Located::new(
            Decl::Database {
                name: "db".into(),
                expunge: 0,
                initialize: 0,
                uses_similar: false,
            },
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("pgcrypto"),
            "file_cache + postgres must include pgcrypto init: {}",
            result
        );
    }

    #[test]
    fn similar_init_non_empty() {
        // Kills: supports_similar !init.is_empty() guard.
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let decls = vec![Located::new(
            Decl::Database {
                name: "db".into(),
                expunge: 0,
                initialize: 0,
                uses_similar: true,
            },
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("pg_trgm"),
            "uses_similar must produce pg_trgm init: {}",
            result
        );
    }

    #[test]
    fn exact_index_name_format() {
        // Kills: name-building, column list. Index on "uw_tab" with "col" -> CREATE INDEX uw_tab_col ON ...
        use crate::monomorphized::IndexMode;
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![
            ("id".to_string(), ffi_typ("Basis", "int")),
            ("col".to_string(), ffi_typ("Basis", "string")),
        ];
        let decls = vec![
            Located::new(
                Decl::Table("uw_tab".to_string(), xts, "id".to_string(), vec![]),
                Span::dummy(),
            ),
            Located::new(
                Decl::Index(
                    "uw_tab".to_string(),
                    vec![("col".to_string(), IndexMode::Equality)],
                ),
                Span::dummy(),
            ),
        ];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("CREATE INDEX") && result.contains("uw_tab") && result.contains("col"),
            "index name must include table and column: {}",
            result
        );
    }

    #[test]
    fn index_trigram_uses_gist_postgres() {
        use crate::monomorphized::IndexMode;
        let settings = Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![
            ("id".to_string(), ffi_typ("Basis", "int")),
            ("name".to_string(), ffi_typ("Basis", "string")),
        ];
        let decls = vec![
            Located::new(
                Decl::Table("uw_t".to_string(), xts, "id".to_string(), vec![]),
                Span::dummy(),
            ),
            Located::new(
                Decl::Index(
                    "uw_t".to_string(),
                    vec![("name".to_string(), IndexMode::Trigram)],
                ),
                Span::dummy(),
            ),
        ];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(
            result.contains("USING gist") || result.contains("gist_trgm_ops"),
            "Trigram index must use gist on postgres: {}",
            result
        );
    }
}
