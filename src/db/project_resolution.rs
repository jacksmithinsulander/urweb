//! Shared resolution of effective [`ProjectDb`] from `ur.toml`, `.urp`, and CLI settings.
//!
//! Compiler, LSP, and other tools must use these helpers so `[build].db` in the manifest
//! participates in the same merge order as batch builds.

use std::path::Path;

use super::{resolved_backend, ProjectDb};
use crate::settings::Settings;

/// Load `[build].db` from `ur.toml` in the same directory as `urp_path` (the `.urp` parent).
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

/// After CLI and `.urp` have been merged into `settings`, fill `db_backend` from `ur.toml` when still unset.
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

/// Pure helper: effective backend after merge (for tests and debugger tooling).
#[inline]
pub fn effective_project_db(settings: &Settings) -> ProjectDb {
    resolved_backend(&settings.db_backend)
}
