//! Shared resolution of effective [`ProjectDb`] from `ur.toml`, `.urp`, and CLI settings.
//!
//! Compiler, LSP, and other tools must use these helpers so `[build].db` in the manifest
//! participates in the same merge order as batch builds.

use std::path::Path;

use super::{resolved_backend, ProjectDb};
use crate::settings::Settings;

/// Load `[build].db` from `ur.toml` beside `urp_path` (parent directory of the `.urp`).
///
/// # Arguments
///
/// * `urp_path` — Absolute or relative path to the project file.
///
/// # Errors
///
/// Manifest exists but cannot be read or parsed, or `[build].db` is not a known engine.
///
/// # Returns
///
/// `Ok(None)` when there is no `ur.toml`; otherwise `Ok(Some(db))`.
pub fn read_manifest_project_db_next_to_urp(urp_path: &Path) -> Result<Option<ProjectDb>, String> {
    let parent = urp_path.parent().unwrap_or_else(|| Path::new("."));
    let manifest_path = parent.join(crate::cli_common::UR_MANIFEST_FILE);
    if !manifest_path.is_file() {
        return Ok(None);
    }
    let toml = std::fs::read_to_string(&manifest_path)
        .map_err(|e| format!("error reading {}: {}", manifest_path.display(), e))?;
    let cfg = crate::cli_common::parse_ur_toml_strict(&toml)
        .map_err(|e| format!("{}: {}", manifest_path.display(), e))?;
    Ok(Some(ProjectDb::parse_user_input(cfg.build.db.trim())?))
}

/// After CLI and `.urp` merge, set `settings.db_backend` from `ur.toml` when it is still `None`.
///
/// # Arguments
///
/// * `urp_path` — `.urp` path (manifest is resolved next to it).
/// * `settings` — Merged settings to update.
///
/// # Errors
///
/// Propagates [`read_manifest_project_db_next_to_urp`] when a manifest is present and invalid.
///
/// # Returns
///
/// `Ok(())` whether or not a default was applied.
pub fn apply_urp_manifest_db_defaults(
    urp_path: &Path,
    settings: &mut Settings,
) -> Result<(), String> {
    if settings.db_backend.is_some() {
        return Ok(());
    }
    if let Some(db) = read_manifest_project_db_next_to_urp(urp_path)? {
        settings.db_backend = Some(db)
    }
    Ok(())
}

/// Effective backend after merge (for tests and debugger tooling).
///
/// # Arguments
///
/// * `settings` — Settings whose `db_backend` may be unset.
///
/// # Returns
///
/// Same as [`resolved_backend`](crate::db::resolved_backend) with `&settings.db_backend`.
#[inline]
pub fn effective_project_db(settings: &Settings) -> ProjectDb {
    resolved_backend(&settings.db_backend)
}
