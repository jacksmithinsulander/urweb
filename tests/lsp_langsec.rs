//! LangSec-focused tests for LSP untrusted surfaces: URI scheme/path validation and workspace root.

use lsp_types::{InitializeParams, Uri, WorkspaceFolder};

use ur::lsp_workspace::{
    uri_local_path_for_tooling, uri_to_file_path, workspace_root_from_initialize,
};

#[test]
fn uri_non_file_scheme_is_rejected() {
    let u: Uri = "https://example.com/x.ur".parse().expect("uri");
    assert!(uri_to_file_path(&u).is_none());
}

#[test]
fn uri_local_path_for_tooling_rejects_non_file() {
    let u: Uri = "https://example.com/x.ur".parse().expect("uri");
    assert!(uri_local_path_for_tooling(&u).is_none());
}

#[cfg(unix)]
#[test]
fn uri_local_path_for_tooling_accepts_file_uri() {
    let u: Uri = "file:///tmp/urweb-langsec-tooling.ur".parse().expect("uri");
    assert_eq!(
        uri_local_path_for_tooling(&u).as_deref(),
        Some("/tmp/urweb-langsec-tooling.ur")
    );
}

#[cfg(unix)]
#[test]
fn uri_file_scheme_maps_to_local_path() {
    let u: Uri = "file:///tmp/urweb-lsp-langsec.ur".parse().expect("uri");
    assert_eq!(
        uri_to_file_path(&u),
        Some(std::path::PathBuf::from("/tmp/urweb-lsp-langsec.ur"))
    );
}

#[test]
fn workspace_root_prefers_workspace_folder_over_root_uri() {
    #[allow(deprecated)]
    let params = InitializeParams {
        workspace_folders: Some(vec![WorkspaceFolder {
            uri: "file:///first/folder".parse().expect("uri"),
            name: "first".into(),
        }]),
        root_uri: Some("file:///other/root".parse().expect("uri")),
        ..Default::default()
    };

    let got = workspace_root_from_initialize(&params).expect("root");
    #[cfg(unix)]
    assert_eq!(got, std::path::PathBuf::from("/first/folder"));
    #[cfg(windows)]
    assert!(got.as_os_str().len() > 0);
}
