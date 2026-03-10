//! SQL DDL generator: CJR → SQL schema.
//!
//! Generates CREATE TABLE / CREATE SEQUENCE / CREATE VIEW / CREATE INDEX
//! statements for the database schema described by a CJR file.
//!
//! Mirrors `CjrPrint.p_sql` in `cjr_print.sml`.

use crate::c_like_representation::{Decl, File};
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

    fn dbms(&self) -> &str {
        &self.settings.dbms
    }

    fn p_sql_type(&self, t: &SqlType) -> String {
        match self.dbms() {
            "mysql" => mysql_sql_type(t),
            "sqlite" => sqlite_sql_type(t),
            _ => postgres_sql_type(t), // postgres default
        }
    }

    fn create_sequence(&self, name: &str) -> String {
        match self.dbms() {
            "mysql" => {
                format!(
                    "CREATE TABLE {} (uw_id INTEGER PRIMARY KEY AUTO_INCREMENT)",
                    name
                )
            }
            "sqlite" => {
                format!(
                    "CREATE TABLE {} (id INTEGER PRIMARY KEY AUTOINCREMENT)",
                    name
                )
            }
            _ => format!("CREATE SEQUENCE {}", name), // postgres
        }
    }

    fn sql_prefix(&self) -> &str {
        match self.dbms() {
            "sqlite" => "PRAGMA foreign_keys = ON;\nPRAGMA journal_mode = WAL;\n\n",
            _ => "",
        }
    }

    fn text_keys_need_lengths(&self) -> bool {
        self.dbms() == "mysql"
    }

    fn requires_timestamp_defaults(&self) -> bool {
        self.dbms() == "mysql"
    }

    fn supports_similar(&self) -> Option<&'static str> {
        match self.dbms() {
            "postgres" | "" => Some("CREATE EXTENSION IF NOT EXISTS pg_trgm;"),
            _ => None,
        }
    }

    fn supports_sha512(&self) -> Option<&'static str> {
        match self.dbms() {
            "mysql" => Some(""), // MySQL has SHA2 built-in, no init needed
            "postgres" | "" => Some("CREATE EXTENSION IF NOT EXISTS pgcrypto;"),
            _ => None,
        }
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
            (k, m.clone())
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
        elts.push(format!("CONSTRAINT {}_{} {}", table, x, c));
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
                out.push_str(&format!("CREATE VIEW {} AS {};\n\n", s, q));
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
                            IndexMode::Skipped => unreachable!(),
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
        let mut settings = Settings::default();
        settings.dbms = "postgres".to_string();
        let decls = vec![Located::new(
            Decl::Sequence("uw_seq".to_string()),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(result.contains("CREATE SEQUENCE uw_seq"), "got: {}", result);
    }

    #[test]
    fn sequence_mysql() {
        let mut settings = Settings::default();
        settings.dbms = "mysql".to_string();
        let decls = vec![Located::new(
            Decl::Sequence("uw_seq".to_string()),
            Span::dummy(),
        )];
        let result = sql_generate(&(decls, vec![]), &settings);
        assert!(result.contains("AUTO_INCREMENT"), "got: {}", result);
    }

    #[test]
    fn table_basic_postgres() {
        let mut settings = Settings::default();
        settings.dbms = "postgres".to_string();
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
    fn sqlite_prefix() {
        let mut settings = Settings::default();
        settings.dbms = "sqlite".to_string();
        let result = sql_generate(&(vec![], vec![]), &settings);
        assert!(result.contains("PRAGMA foreign_keys"), "got: {}", result);
    }
}
