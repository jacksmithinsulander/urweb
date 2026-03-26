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
    /// Wrap the optional backend stored in settings (or elsewhere).
    ///
    /// # Arguments
    ///
    /// * `choice` — Typically `&settings.db_backend`.
    #[inline]
    pub fn new(choice: &'a Option<ProjectDb>) -> Self {
        Self { choice }
    }

    /// Legacy unset `db_backend` → Postgres family (same as historical empty `dbms`).
    ///
    /// # Returns
    ///
    /// [`super::resolved_backend`] of this context’s pointer.
    #[inline]
    pub fn resolved(&self) -> ProjectDb {
        super::resolved_backend(self.choice)
    }

    /// Linker flag for [`Self::resolved`].
    ///
    /// # Returns
    ///
    /// See [`DatabaseBackend::link_library_flag`].
    #[inline]
    pub fn link_library_flag(&self) -> &'static str {
        use DatabaseBackend;
        self.resolved().link_library_flag()
    }

    /// Enforce that relational SQL codegen is allowed for [`Self::resolved`].
    ///
    /// # Errors
    ///
    /// When [`DatabaseBackend::require_sql_code_generation`] fails.
    ///
    /// # Returns
    ///
    /// `Ok(())` on success.
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

    /// SQL identifier mangling (column names, etc.) for [`Self::resolved`].
    ///
    /// # Arguments
    ///
    /// * `mangle_cfg` — Typically [`crate::settings::Settings::mangle`] (when true, emit `uw_` prefixes per dialect).
    /// * `s` — Source identifier.
    ///
    /// # Returns
    ///
    /// Backend-specific mangled name.
    #[inline]
    pub fn mangle_sql_ident(&self, mangle_cfg: bool, s: &str) -> String {
        super::mangle_sql_ident(&self.resolved(), mangle_cfg, s)
    }

    /// SQL table name mangling for [`Self::resolved`].
    ///
    /// # Arguments
    ///
    /// * `mangle_cfg` — Same meaning as [`Self::mangle_sql_ident`].
    /// * `s` — Source table name.
    ///
    /// # Returns
    ///
    /// Backend-specific mangled table name (capitalization rules differ by dialect).
    #[inline]
    pub fn mangle_sql_table(&self, mangle_cfg: bool, s: &str) -> String {
        super::mangle_sql_table(&self.resolved(), mangle_cfg, s)
    }
}
