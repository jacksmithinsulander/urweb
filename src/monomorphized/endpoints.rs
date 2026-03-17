//! endpoints — collect HTTP endpoint metadata from a Mono file.
//!
//! Ports `endpoints.sml`.  Scans `DExport` declarations (and, in the full
//! implementation, binary/JS static files registered in `Settings`) and
//! returns a list of `Endpoint` records describing the application's HTTP
//! interface.  The file itself is passed through unchanged.

use crate::export::ExportKind;
use crate::monomorphized::{Decl, File};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HttpMethod {
    Get,
    Post,
}

impl HttpMethod {
    pub fn as_str(&self) -> &'static str {
        match self {
            HttpMethod::Get => "GET",
            HttpMethod::Post => "POST",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Endpoint {
    pub method: HttpMethod,
    pub url: String,
    pub content_type: Option<String>,
}

/// Collect all endpoint records from `file` and return them alongside
/// the (unchanged) file.
pub fn collect(file: File) -> (File, Vec<Endpoint>) {
    let (decls, _exports) = &file;
    let mut endpoints: Vec<Endpoint> = Vec::new();

    for d in decls {
        if let Decl::Export(ek, url, _id, _ts, _rt, _b) = &d.node {
            let method = export_kind_to_method(ek);
            endpoints.push(Endpoint {
                method,
                url: url.clone(),
                content_type: None,
            });
        }
    }

    (file, endpoints)
}

fn export_kind_to_method(ek: &ExportKind) -> HttpMethod {
    match ek {
        ExportKind::Link(_) => HttpMethod::Get,
        ExportKind::Action(_) | ExportKind::Rpc(_) | ExportKind::Extern(_) => HttpMethod::Post,
    }
}

/// Render an endpoint list as a JSON report string (mirrors `p_report`).
pub fn to_json(endpoints: &[Endpoint]) -> String {
    let items: Vec<String> = endpoints
        .iter()
        .map(|ep| {
            let ct = match &ep.content_type {
                Some(ct) => format!("\"{}\"", ct),
                None => "null".into(),
            };
            format!(
                "{{\"method\": \"{}\", \"url\": \"{}\", \"content-type\": {}}}",
                ep.method.as_str(),
                ep.url,
                ct
            )
        })
        .collect();
    format!("{{\"endpoints\": [{}]}}", items.join(", "))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collect_empty_file_returns_empty_endpoints() {
        let file: File = Default::default();
        let (_, endpoints) = collect(file);
        assert!(endpoints.is_empty());
    }

    #[test]
    fn to_json_empty() {
        let json = to_json(&[]);
        assert_eq!(json, "{\"endpoints\": []}");
    }

    #[test]
    fn to_json_single_get() {
        let ep = Endpoint {
            method: HttpMethod::Get,
            url: "/foo".into(),
            content_type: None,
        };
        let json = to_json(&[ep]);
        assert!(json.contains("\"GET\""));
        assert!(json.contains("/foo"));
    }
}
