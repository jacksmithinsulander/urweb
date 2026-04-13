//! LangSec-focused tests for LSP untrusted surfaces: URI scheme/path validation and workspace root.

use lsp_types::{InitializeParams, Uri, WorkspaceFolder};

use ur::lsp_workspace::{
    uri_local_path_for_tooling, uri_to_file_path, workspace_root_from_initialize,
};

fn parse_uri(uri: &str) -> Uri {
    match uri.parse() {
        Ok(parsed) => parsed,
        Err(error) => panic!("parse URI {uri}: {error}"),
    }
}

#[test]
fn uri_non_file_scheme_is_rejected() {
    let u = parse_uri("https://example.com/x.ur");
    assert!(uri_to_file_path(&u).is_none());
}

#[test]
fn uri_local_path_for_tooling_rejects_non_file() {
    let u = parse_uri("https://example.com/x.ur");
    assert!(uri_local_path_for_tooling(&u).is_none());
}

#[cfg(unix)]
#[test]
fn uri_local_path_for_tooling_accepts_file_uri() {
    let u = parse_uri("file:///tmp/urweb-langsec-tooling.ur");
    assert_eq!(
        uri_local_path_for_tooling(&u).as_deref(),
        Some("/tmp/urweb-langsec-tooling.ur")
    );
}

#[cfg(unix)]
#[test]
fn uri_file_scheme_maps_to_local_path() {
    let u = parse_uri("file:///tmp/urweb-lsp-langsec.ur");
    assert_eq!(
        uri_to_file_path(&u),
        Some(std::path::PathBuf::from("/tmp/urweb-lsp-langsec.ur"))
    );
}

#[test]
fn workspace_root_resolves_first_workspace_folder() {
    let params = InitializeParams {
        workspace_folders: Some(vec![WorkspaceFolder {
            uri: parse_uri("file:///first/folder"),
            name: "first".into(),
        }]),
        ..Default::default()
    };

    let got = match workspace_root_from_initialize(&params) {
        Some(root) => root,
        None => panic!("workspace_root_from_initialize should resolve a root"),
    };
    #[cfg(unix)]
    assert_eq!(got, std::path::PathBuf::from("/first/folder"));
    #[cfg(windows)]
    assert!(got.as_os_str().len() > 0);
}
