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
//!
//! **Style:** new/edited Rust here follows [README.md](../../README.md) Rust code style (exceptions documented there).
//!
//! Public helpers document `# Arguments`, `# Returns`, and `# Errors` when the contract is not obvious.

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
    apply_urp_manifest_db_defaults, apply_urp_manifest_diagnostic_locale, effective_project_db,
    read_manifest_project_db_next_to_urp,
};

use anyhow::Result;

#[cfg(test)]
use std::sync::atomic::AtomicUsize;

/// Incremented inside [`require_sql_codegen_from_option`] under `cfg(test)` so mutants that replace the body with `Ok(())` skip the hook.
#[cfg(test)]
pub(crate) static REQUIRE_SQL_CODEGEN_FROM_OPTION_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);

/// Effective backend after treating `None` as legacy unset Postgres family (same as empty `.urp` `dbms`).
///
/// # Arguments
///
/// * `db_backend` — Optional value from [`crate::settings::Settings::db_backend`].
///
/// # Returns
///
/// [`ProjectDb`] stored in `db_backend`, or [`ProjectDb::default`].
#[inline]
pub fn resolved_backend(db_backend: &Option<ProjectDb>) -> ProjectDb {
    db_backend.unwrap_or_default()
}

/// If `into` is `None`, parse `token` and store it (typical merge from `.urp` `dbms`).
///
/// # Arguments
///
/// * `into` — Backend slot to fill only when presently unset.
/// * `token` — Raw `dbms` string, or `None` to leave `into` unchanged.
///
/// # Errors
///
/// Propagates [`ProjectDb::parse_user_input`] failures when `into` is `None` and `token` is `Some`.
///
/// # Returns
///
/// `Ok(())` after an optional assignment.
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

/// Validate `ur.toml` `[build].db`: must be a recognized engine name (not the SQL connection string; that is `-db` / `.urp` `database`).
///
/// # Arguments
///
/// * `token` — Trimmed `[build].db` value from the manifest.
///
/// # Errors
///
/// Same as [`ProjectDb::parse_user_input`] for unknown or empty names.
///
/// # Returns
///
/// `Ok(())` when the engine is known.
#[inline]
pub fn validate_manifest_db_engine(token: &str) -> Result<(), String> {
    ProjectDb::parse_user_input(token).map(|_| ())
}

/// When `ur.toml` sits next to the `.urp`, require `[build].db` to match the resolved backend.
///
/// Effective backend is `-dbms` / `.urp` `dbms` after CLI and job merge (see [`apply_urp_job_db_fields`]).
/// No-op when the manifest file is missing.
///
/// # Arguments
///
/// * `urp_path` — Path to the `.urp` file (manifest is sought in its parent).
/// * `settings` — Merged settings whose `db_backend` defines the build.
///
/// # Errors
///
/// Read/parse failures for the manifest, or a mismatch between manifest `[build].db` and `settings`.
///
/// # Returns
///
/// `Ok(())` when there is no manifest or names agree.
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

/// Apply `-dbms` from the CLI: sets [`crate::settings::Settings::db_backend`] unconditionally.
///
/// Runs before `.urp` merge; later [`apply_urp_job_db_fields`] only fills when this left the slot unset.
///
/// # Arguments
///
/// * `settings` — Settings to mutate.
/// * `token` — Engine name (same spellings as [`ProjectDb::parse_user_input`]).
///
/// # Errors
///
/// Invalid or unknown `token`.
///
/// # Returns
///
/// `Ok(())` after assignment.
pub fn set_backend_from_cli_token(
    settings: &mut crate::settings::Settings,
    token: &str,
) -> Result<(), String> {
    settings.db_backend = Some(ProjectDb::parse_user_input(token)?);
    Ok(())
}

/// Merge `.urp` job `dbms` / `database` into `settings` only where CLI did not already set values.
///
/// # Arguments
///
/// * `settings` — Compiler settings after CLI flags.
/// * `job_dbms` — Optional `dbms` line from the job (fills `db_backend` if unset).
/// * `job_database` — Optional `database` line (fills `dbstring` if unset).
///
/// # Errors
///
/// Bad `job_dbms` token when the backend slot is still empty.
///
/// # Returns
///
/// `Ok(())` after optional merges.
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

/// Linker `-l` (and related) flag string for the resolved project backend.
///
/// # Arguments
///
/// * `db_backend` — Optional backend; `None` uses legacy default (Postgres family).
///
/// # Returns
///
/// Static flag fragment suitable for the C link line.
#[inline]
pub fn link_library_flag_from_option(db_backend: &Option<ProjectDb>) -> &'static str {
    ProjectDbCtx::new(db_backend).link_library_flag()
}

/// Fail the build early if the backend cannot run the relational SQL codegen path.
///
/// Today this always succeeds for known engines; reserved for stricter gating.
///
/// # Arguments
///
/// * `db_backend` — Optional backend selection.
///
/// # Errors
///
/// Backend-specific codegen refusal (currently unused for all [`ProjectDb`] variants).
///
/// # Returns
///
/// `Ok(())` when codegen is allowed.
#[inline]
pub fn require_sql_codegen_from_option(db_backend: &Option<ProjectDb>) -> Result<()> {
    #[cfg(test)]
    REQUIRE_SQL_CODEGEN_FROM_OPTION_INVOCATIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    ProjectDbCtx::new(db_backend).require_sql_codegen()
}
