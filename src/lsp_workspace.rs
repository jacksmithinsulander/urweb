//! Workspace roots and `file:` uniform resource identifiers for `ur-lsp`.
//!
//! Treat editor payloads as untrusted: validate before opening paths (language-based security style).
//! [`lsp_types::InitializeParams`] and document uniform resource identifier strings deserialize through `serde_json`;
//! only `file:` schemes become local filesystem paths here.
//!
//! ## Input surfaces
//!
//! - Workspace folder / root uniform resource identifiers: [`workspace_root_from_initialize`] then [`uri_to_file_path`];
//!   non-`file:` roots are not mapped to disk.
//! - Open document identifiers (`textDocument/*`): [`uri_to_file_path`] and [`uri_local_path_for_tooling`];
//!   analysis and formatting use paths derived from `file:` resources only.
//! - Discovering the project file: [`discover_unique_urp`] reads one directory level and returns an error instead of panicking.

use std::path::{Path, PathBuf};

use lsp_types::{InitializeParams, Uri};

/// Convert a `file:` Language Server Protocol [`Uri`] to a local path; other schemes yield `None`.
///
/// # Arguments
///
/// * `uri` — Editor-supplied uniform resource identifier.
///
/// # Returns
///
/// Local [`PathBuf`] when the scheme is `file:` and the path decodes; `None` for other schemes or parse failure.
pub fn uri_to_file_path(uri: &Uri) -> Option<PathBuf> {
    let scheme = uri.scheme()?;
    if !scheme.as_str().eq_ignore_ascii_case("file") {
        return None;
    }
    let path = uri.path().as_str();
    #[cfg(windows)]
    {
        let path = path.strip_prefix('/').unwrap_or(path);
        Some(PathBuf::from(path))
    }
    #[cfg(not(windows))]
    {
        Some(PathBuf::from(path))
    }
}

/// Local filesystem path string for `file:` resources only (formatting and virtual parse labels).
///
/// Returns `None` for other schemes so arbitrary uniform resource identifiers never become implicit disk paths.
///
/// # Arguments
///
/// * `uri` — Document or workspace uniform resource identifier.
///
/// # Returns
///
/// Lossy UTF-8 path string for `file:` locations; `None` if not a local `file:` URL.
pub fn uri_local_path_for_tooling(uri: &Uri) -> Option<String> {
    uri_to_file_path(uri).map(|p| p.to_string_lossy().into_owned())
}

/// Workspace root path: first entry in `workspaceFolders`, else deprecated `rootUri` when folders are absent.
///
/// # Arguments
///
/// * `params` — Payload from the `initialize` request after JSON deserialization.
///
/// # Returns
///
/// First folder’s path, else `rootUri`, converted with [`uri_to_file_path`]; `None` if neither yields a `file:` path.
pub fn workspace_root_from_initialize(params: &InitializeParams) -> Option<PathBuf> {
    if let Some(folders) = &params.workspace_folders {
        if let Some(f) = folders.first() {
            return uri_to_file_path(&f.uri);
        }
    }
    // Clients without `workspaceFolders` still send `rootUri` (deprecated in lsp-types but widely used).
    #[allow(deprecated)]
    {
        params.root_uri.as_ref().and_then(uri_to_file_path)
    }
}

/// Find exactly one `*.urp` in `root` (non-recursive), matching the legacy Standard ML language server behaviour.
///
/// # Arguments
///
/// * `root` — Workspace directory to scan (not recursive).
///
/// # Returns
///
/// The single `.urp` [`PathBuf`] when exactly one exists.
///
/// # Errors
///
/// Directory read failures, zero matches, or more than one `.urp` file (human-readable `String` messages).
pub fn discover_unique_urp(root: &Path) -> Result<PathBuf, String> {
    let mut found: Vec<PathBuf> = Vec::new();
    let rd = std::fs::read_dir(root).map_err(|e| format!("read workspace directory: {e}"))?;
    for ent in rd {
        let ent = ent.map_err(|e| format!("workspace dir entry: {e}"))?;
        let p = ent.path();
        if p.extension().and_then(|x| x.to_str()) == Some("urp") {
            found.push(p);
        }
    }
    match found.len() {
        0 => Err(
            "no .urp file in the workspace root (open a folder that contains exactly one .urp)"
                .into(),
        ),
        1 => found
            .pop()
            .ok_or_else(|| "workspace scan: missing .urp path".to_string()),
        _ => Err(
            "multiple .urp files in the workspace root; use a folder with a single project".into(),
        ),
    }
}

/// Path of `disk` relative to `root` with forward slashes, for comparing with [`crate::error_types::Span`] paths.
///
/// # Arguments
///
/// * `root` — Workspace root directory.
/// * `disk` — Absolute or rooted path under (or beside) that workspace.
///
/// # Returns
///
/// Relative path using `/` separators; if `disk` is not under `root`, returns `disk` unchanged (lossy, normalized slashes).
pub fn file_key_relative_to_root(root: &Path, disk: &Path) -> String {
    disk.strip_prefix(root)
        .unwrap_or(disk)
        .to_string_lossy()
        .replace('\\', "/")
}

/// Workspace-relative path key for a `file:` document [`Uri`] (for semantic lookup against [`Span::file`](crate::error_types::Span)).
///
/// # Arguments
///
/// * `workspace_root` — Editor workspace folder from initialize; `None` when no root is open.
/// * `uri` — Document uniform resource identifier.
///
/// # Returns
///
/// Forward-slash key under the root, or `None` when the root or local path is missing.
pub fn relative_file_key_for_uri(workspace_root: Option<&Path>, uri: &Uri) -> Option<String> {
    let root = workspace_root?;
    let disk = uri_to_file_path(uri)?;
    Some(file_key_relative_to_root(root, &disk))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relative_file_key_none_without_workspace() {
        let uri: Uri = "file:///tmp/a.ur".parse().expect("uri");
        assert!(relative_file_key_for_uri(None, &uri).is_none());
    }

    #[test]
    fn relative_file_key_under_root() {
        let tmp = tempfile::tempdir().unwrap();
        let only = tmp.path().join("Only.ur");
        std::fs::write(&only, "").unwrap();
        let path_for_uri = only.to_string_lossy().replace('\\', "/");
        let uri: Uri = format!("file://{path_for_uri}").parse().expect("uri");
        assert_eq!(
            relative_file_key_for_uri(Some(tmp.path()), &uri).as_deref(),
            Some("Only.ur")
        );
    }

    #[test]
    fn relative_file_key_non_file_uri() {
        let root = std::path::Path::new("/proj");
        let uri: Uri = "https://ex/x.ur".parse().expect("uri");
        assert!(relative_file_key_for_uri(Some(root), &uri).is_none());
    }
}
