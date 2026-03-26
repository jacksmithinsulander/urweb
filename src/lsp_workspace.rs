//! Workspace discovery and `file:` URI handling for ur-lsp (LangSec: validate before use).
//!
//! **Untrusted input:** [`InitializeParams`] JSON, `DocumentUri` strings. Deserialization is the
//! schema boundary; paths are normalized to the local filesystem only when the scheme is `file:`.
//!
//! ## LangSec inventory (ur-lsp)
//!
//! | Input | Recognizer | Notes |
//! |-------|------------|--------|
//! | `InitializeParams` workspace URIs | [`workspace_root_from_initialize`] → [`uri_to_file_path`] | Non-`file:` roots rejected (no path mapping). |
//! | `textDocument/*` document URIs | [`uri_to_file_path`], [`uri_local_path_for_tooling`] | Analysis and formatting use **only** local paths derived from `file:` URIs; other schemes are ignored or yield empty results. |
//! | Workspace `.urp` discovery | [`discover_unique_urp`] | Reads only directory entries; reports errors instead of panicking. |

use std::path::{Path, PathBuf};

use lsp_types::{InitializeParams, Uri};

/// Convert a `file:` LSP URI to a local path. Non-`file:` schemes return `None`.
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

/// Local filesystem path string for `file:` URIs only — used for formatting and virtual parse paths.
/// Non-`file:` schemes return `None` (LangSec: do not treat `Uri::path()` as a local path for arbitrary schemes).
pub fn uri_local_path_for_tooling(uri: &Uri) -> Option<String> {
    uri_to_file_path(uri).map(|p| p.to_string_lossy().into_owned())
}

/// Prefer first workspace folder, then `rootUri` (LSP 3.17 workspace folders).
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

/// List `*.urp` in a single directory (non-recursive), like the legacy SML LSP.
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

/// Path relative to workspace using `/`, for comparing with [`Span::file`](crate::error_types::Span).
pub fn file_key_relative_to_root(root: &Path, disk: &Path) -> String {
    disk.strip_prefix(root)
        .unwrap_or(disk)
        .to_string_lossy()
        .replace('\\', "/")
}
