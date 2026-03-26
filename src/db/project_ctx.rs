//! Single entry type for “what is the project DB backend right now?”
//!
//! Pass `&settings.db_backend` (the `Option<ProjectDb>` from a [`crate::settings::Settings`]).
//! SQL mangling still takes the settings `mangle` flag explicitly to avoid pulling in `Settings`
//! (and a module cycle).

use anyhow::Result;

use super::{DatabaseBackend, ProjectDb};

/// View on the optional `-dbms` / `.urp` selection stored in [`crate::settings::Settings::db_backend`].
#[derive(Debug, Clone, Copy)]
pub struct ProjectDbCtx<'a> {
    choice: &'a Option<ProjectDb>,
}

impl<'a> ProjectDbCtx<'a> {
    #[inline]
    pub fn new(choice: &'a Option<ProjectDb>) -> Self {
        Self { choice }
    }

    /// Legacy unset `db_backend` → Postgres family (same as historical empty `dbms`).
    #[inline]
    pub fn resolved(&self) -> ProjectDb {
        super::resolved_backend(self.choice)
    }

    #[inline]
    pub fn link_library_flag(&self) -> &'static str {
        use DatabaseBackend;
        self.resolved().link_library_flag()
    }

    #[inline]
    pub fn require_sql_codegen(&self) -> Result<()> {
        use DatabaseBackend;
        self.resolved().require_sql_code_generation()
    }

    #[inline]
    pub fn is_mysql(&self) -> bool {
        use DatabaseBackend;
        self.resolved().is_mysql()
    }

    #[inline]
    pub fn is_sqlite(&self) -> bool {
        use DatabaseBackend;
        self.resolved().is_sqlite()
    }

    #[inline]
    pub fn is_postgres_family(&self) -> bool {
        use DatabaseBackend;
        self.resolved().is_postgres_family()
    }

    /// SQL identifier mangling (column names, etc.).
    #[inline]
    pub fn mangle_sql_ident(&self, mangle_cfg: bool, s: &str) -> String {
        super::mangle_sql_ident(&self.resolved(), mangle_cfg, s)
    }

    /// SQL table name mangling.
    #[inline]
    pub fn mangle_sql_table(&self, mangle_cfg: bool, s: &str) -> String {
        super::mangle_sql_table(&self.resolved(), mangle_cfg, s)
    }
}
