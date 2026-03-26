//! SQL identifier mangling for emitted DDL and queries (MySQL vs Postgres/SQLite rules).

use super::{DatabaseBackend, ProjectDb};

/// Escape / prefix a SQL identifier (columns, etc.) for the active backend.
///
/// # Arguments
///
/// * `backend` — Resolved [`ProjectDb`] (MySQL lowercases; Postgres/SQLite keep case when not mangling).
/// * `mangle` — When true, apply `uw_` prefix per dialect rules.
/// * `s` — Logical identifier from the compiler.
///
/// # Returns
///
/// String safe to embed as an identifier in emitted SQL.
pub fn mangle_sql_ident(backend: &ProjectDb, mangle: bool, s: &str) -> String {
    if backend.is_mysql() {
        if mangle {
            format!("uw_{}", s.to_lowercase())
        } else {
            s.to_lowercase()
        }
    } else if mangle {
        format!("uw_{}", s)
    } else {
        lowercase(s)
    }
}

/// Table names: Postgres-style capitalizes the first letter when mangling; MySQL stays lowercase.
///
/// # Arguments
///
/// * `backend` — Same as [`mangle_sql_ident`].
/// * `mangle` — Same as [`mangle_sql_ident`].
/// * `s` — Logical table name.
///
/// # Returns
///
/// Mangled table identifier for DDL and queries.
pub fn mangle_sql_table(backend: &ProjectDb, mangle: bool, s: &str) -> String {
    if backend.is_mysql() {
        if mangle {
            format!("uw_{}", s.to_lowercase())
        } else {
            s.to_lowercase()
        }
    } else if mangle {
        let capitalized = capitalize(s);
        format!("uw_{}", capitalized)
    } else {
        lowercase(s)
    }
}

fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

fn lowercase(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_lowercase().collect::<String>() + chars.as_str(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::ProjectDb;

    #[test]
    fn table_postgres_mangle() {
        let pg = ProjectDb::postgres();
        assert_eq!(mangle_sql_table(&pg, true, "users"), "uw_Users");
    }

    #[test]
    fn table_mysql_mangle() {
        let my = ProjectDb::mysql();
        assert_eq!(mangle_sql_table(&my, true, "Users"), "uw_users");
    }

    #[test]
    fn ident_mysql_vs_postgres() {
        let s_mysql = ProjectDb::mysql();
        let s_pg = ProjectDb::postgres();
        assert_eq!(mangle_sql_ident(&s_mysql, true, "Foo"), "uw_foo");
        assert_eq!(mangle_sql_ident(&s_pg, true, "Foo"), "uw_Foo");
    }
}
