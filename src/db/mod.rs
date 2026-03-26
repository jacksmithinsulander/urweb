//! **Project database backend** — one module for parse, resolve, mangling, linker flags, and SQL codegen gates.
//!
//! ## Collaboration with the compiler
//!
//! - **`ur.toml`** — `[build] db` is the **engine** name (same strings as `-dbms` / `.urp` `dbms`).
//!   Validate with [`validate_manifest_db_engine`] before invoking `ur-compile` (see `ur` orchestrator).
//! - **CLI** — `-dbms` is applied with [`set_backend_from_cli_token`] (overwrites `Settings.db_backend`).
//! - **`.urp` / `Job`** — after parsing the project file, the compiler calls [`apply_urp_job_db_fields`]:
//!   merges `dbms` / `database` into `settings` only where the CLI left them unset (same precedence as historical SML).
//! - **Manifest vs build** — when `ur.toml` sits next to the `.urp`, [`reconcile_ur_manifest_with_resolved_db`]
//!   requires `[build].db` to match the resolved [`ProjectDb`] (CLI `-dbms` / `.urp` after merge).
//! ## Queries during codegen
//!
//! Use [`ProjectDbCtx::new`] on `&settings.db_backend` for resolved backend, linker flags, SQL gate, and mangling.
//!
//! - Parser: [`ProjectDb::parse_user_input`].

mod mangle;
mod project_ctx;
mod project_db;
mod project_resolution;

#[cfg(test)]
mod test_matrix;

pub use mangle::{mangle_sql_ident, mangle_sql_table};
pub use project_ctx::ProjectDbCtx;
pub use project_db::{
    canonical_dbms, DatabaseBackend, LangsecParseProfile, ProjectDb, SqlFlavor, KNOWN_DB_NAMES,
    KV_BACKENDS, NON_SQL_BACKENDS, NON_SQL_BACKEND_DOC_MARKERS, SQL_BACKENDS,
};
pub use project_resolution::{
    apply_urp_manifest_db_defaults, effective_project_db, read_manifest_project_db_next_to_urp,
};

use anyhow::Result;

/// Effective backend: `None` means legacy unset → Postgres family (same as empty `dbms`).
#[inline]
pub fn resolved_backend(db_backend: &Option<ProjectDb>) -> ProjectDb {
    db_backend.unwrap_or_default()
}

/// If `into` is unset, parse `token` from a `.urp` `dbms` line or job field.
pub fn merge_optional_dbms_token(
    into: &mut Option<ProjectDb>,
    token: Option<&str>,
) -> Result<(), String> {
    if into.is_none() {
        if let Some(d) = token {
            *into = Some(ProjectDb::parse_user_input(d)?);
        }
    }
    Ok(())
}

/// `ur.toml` `[build].db` — must be a recognized engine name (not the SQL connection string; that is `-db` / `.urp` `database`).
#[inline]
pub fn validate_manifest_db_engine(token: &str) -> Result<(), String> {
    ProjectDb::parse_user_input(token).map(|_| ())
}

/// When `ur.toml` sits next to the `.urp` file, `[build].db` must match the effective `ProjectDb`
/// (`-dbms` / `.urp` `dbms`, after CLI / job merge). Omit or ignore when no manifest file exists.
pub fn reconcile_ur_manifest_with_resolved_db(
    urp_path: &std::path::Path,
    settings: &crate::settings::Settings,
) -> Result<(), String> {
    let parent = urp_path
        .parent()
        .unwrap_or_else(|| std::path::Path::new("."));
    let manifest_path = parent.join(crate::cli_common::UR_MANIFEST_FILE);
    if !manifest_path.exists() {
        return Ok(());
    }
    let toml = std::fs::read_to_string(&manifest_path)
        .map_err(|e| format!("error reading {}: {}", manifest_path.display(), e))?;
    let cfg = crate::cli_common::parse_ur_toml_strict(&toml)
        .map_err(|e| format!("{}: {}", manifest_path.display(), e))?;
    let manifest_db = ProjectDb::parse_user_input(cfg.build.db.trim())?;
    let effective = resolved_backend(&settings.db_backend);
    if effective != manifest_db {
        return Err(format!(
            "ur.toml [build].db is `{}` but this build resolves to `{}` (-dbms / .urp `dbms` / default). They must match.",
            manifest_db.canonical_name(),
            effective.canonical_name(),
        ));
    }
    Ok(())
}

/// `-dbms` from the CLI: set the project backend (runs before `.urp` merge; merge only fills if this left `db_backend` unset).
pub fn set_backend_from_cli_token(
    settings: &mut crate::settings::Settings,
    token: &str,
) -> Result<(), String> {
    settings.db_backend = Some(ProjectDb::parse_user_input(token)?);
    Ok(())
}

/// Copy `.urp` `dbms` / `database` (and optional library project fields) into `settings` when the CLI did not set them.
pub fn apply_urp_job_db_fields(
    settings: &mut crate::settings::Settings,
    job_dbms: Option<&str>,
    job_database: Option<&str>,
) -> Result<(), String> {
    merge_optional_dbms_token(&mut settings.db_backend, job_dbms)?;
    if settings.dbstring.is_none() {
        if let Some(d) = job_database {
            settings.dbstring = Some(d.to_string());
        }
    }
    Ok(())
}

/// Linker `-l` flag for the resolved project backend.
#[inline]
pub fn link_library_flag_from_option(db_backend: &Option<ProjectDb>) -> &'static str {
    ProjectDbCtx::new(db_backend).link_library_flag()
}

/// Reserved for backends that cannot emit relational C/SQL (currently always succeeds for known engines).
#[inline]
pub fn require_sql_codegen_from_option(db_backend: &Option<ProjectDb>) -> Result<()> {
    ProjectDbCtx::new(db_backend).require_sql_codegen()
}
