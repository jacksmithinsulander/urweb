//! Script classification pass.
//!
//! Classifies each exported function as `ServerOnly`, `ServerAndPull`
//! (uses client-pull / XMLHttpRequest), or `ServerAndPullAndPush` (uses
//! server push via channels).
//!
//! Mirrors `ScriptCheck.classify` in `scriptcheck.sml`.

use std::collections::{HashMap, HashSet};

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::error_types::ErrorReporter;
use crate::export::ExportKind;
use crate::monomorphized::{Decl, Exp, File, LocExp, Sidedness};
use crate::primitives::Prim;
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// rpcmap — trie keyed by "/" separated path components
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum RpcMap {
    Rpc(usize),
    Module(HashMap<String, RpcMap>),
}

impl RpcMap {
    fn empty_module() -> Self {
        RpcMap::Module(HashMap::new())
    }

    fn lookup(&self, key: &str) -> Option<usize> {
        let parts: Vec<&str> = key.split('/').collect();
        self.lookup_parts(&parts)
    }

    fn lookup_parts(&self, parts: &[&str]) -> Option<usize> {
        match self {
            RpcMap::Rpc(n) => Some(*n),
            RpcMap::Module(m) => {
                if let Some(first) = parts.first() {
                    m.get(*first)?.lookup_parts(&parts[1..])
                } else {
                    None
                }
            }
        }
    }

    fn insert(self, key: &str, val: usize) -> Self {
        let parts: Vec<&str> = key.split('/').collect();
        self.insert_parts(&parts, val)
    }

    fn insert_parts(self, parts: &[&str], val: usize) -> Self {
        match self {
            RpcMap::Rpc(_) => RpcMap::Rpc(val),
            RpcMap::Module(mut m) => {
                if let Some(first) = parts.first() {
                    let rest = &parts[1..];
                    let child = m.remove(*first).unwrap_or(RpcMap::Module(HashMap::new()));
                    m.insert(first.to_string(), child.insert_parts(rest, val));
                    RpcMap::Module(m)
                } else {
                    RpcMap::Rpc(val)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// has_client — check if expression contains client-side features
// ---------------------------------------------------------------------------

/// Basis functions that only matter for push (server-push / channels).
const PUSH_BASIS: &[&str] = &["new_channel", "self"];

/// Get the head string of a server-call URL (following EStrcat left spines).
fn server_call_head(e: &LocExp) -> Option<String> {
    match &e.node {
        Exp::Strcat(e1, _) => server_call_head(e1),
        Exp::Prim(Prim::String(_, s)) => Some(s.clone()),
        _ => None,
    }
}

/// Recursively check whether `e` has client-side features.
///
/// `push=false` → check for pull features (XMLHttpRequest / EJavaScript).
/// `push=true` → check for push features (ERecv, new_channel, self).
fn has_client_exp(
    e: &LocExp,
    basis: &HashSet<String>,
    rpcs: &RpcMap,
    funcs: &HashSet<usize>,
    push: bool,
) -> bool {
    match &e.node {
        Exp::Recv(_, _) => push,
        Exp::FfiApp(m, x, args) if m == "Basis" => {
            if basis.contains(x.as_str()) {
                return true;
            }
            args.iter()
                .any(|(a, _)| has_client_exp(a, basis, rpcs, funcs, push))
        }
        Exp::JavaScript(_, _) => !push,
        Exp::Named(n) => funcs.contains(n),
        Exp::ServerCall(e, _, _, _) => match server_call_head(e) {
            None => true,
            Some(fcall) => match rpcs.lookup(&fcall) {
                None => true,
                Some(n) => funcs.contains(&n),
            },
        },
        // Recurse into subexpressions
        Exp::App(f, arg) => {
            has_client_exp(f, basis, rpcs, funcs, push)
                || has_client_exp(arg, basis, rpcs, funcs, push)
        }
        Exp::Abs(_, _, _, body) => has_client_exp(body, basis, rpcs, funcs, push),
        Exp::Let(_, _, e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::Strcat(e1, e2)
        | Exp::Binop(_, _, e1, e2)
        | Exp::SignalBind(e1, e2)
        | Exp::Setval(e1, e2) => {
            has_client_exp(e1, basis, rpcs, funcs, push)
                || has_client_exp(e2, basis, rpcs, funcs, push)
        }
        Exp::Write(inner)
        | Exp::Unop(_, inner)
        | Exp::Field(inner, _)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner)
        | Exp::Nextval(inner)
        | Exp::Dml(inner, _) => has_client_exp(inner, basis, rpcs, funcs, push),
        Exp::FfiApp(_, _, args) => args
            .iter()
            .any(|(a, _)| has_client_exp(a, basis, rpcs, funcs, push)),
        Exp::Record(xets) => xets
            .iter()
            .any(|(_, a, _)| has_client_exp(a, basis, rpcs, funcs, push)),
        Exp::Case(disc, arms, _) => {
            has_client_exp(disc, basis, rpcs, funcs, push)
                || arms
                    .iter()
                    .any(|(_, ae)| has_client_exp(ae, basis, rpcs, funcs, push))
        }
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => {
            has_client_exp(inner, basis, rpcs, funcs, push)
        }
        Exp::Error(inner, _) | Exp::Redirect(inner, _) | Exp::Uurlify(inner, _, _) => {
            has_client_exp(inner, basis, rpcs, funcs, push)
        }
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            blob.as_ref()
                .is_some_and(|b| has_client_exp(b, basis, rpcs, funcs, push))
                || has_client_exp(mime_type, basis, rpcs, funcs, push)
        }
        Exp::Query(qm) => {
            has_client_exp(&qm.query, basis, rpcs, funcs, push)
                || has_client_exp(&qm.body, basis, rpcs, funcs, push)
                || has_client_exp(&qm.initial, basis, rpcs, funcs, push)
        }
        Exp::Closure(_, envs) => envs
            .iter()
            .any(|e| has_client_exp(e, basis, rpcs, funcs, push)),
        _ => false,
    }
}

fn has_client(
    e: &LocExp,
    basis: &HashSet<String>,
    rpcs: &RpcMap,
    funcs: &HashSet<usize>,
    push: bool,
) -> bool {
    has_client_exp(e, basis, rpcs, funcs, push)
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Classify sidedness of each exported function, updating `ps`.
///
/// Mirrors `ScriptCheck.classify`.
pub fn classify(file: File, settings: &Settings, errors: &mut ErrorReporter) -> File {
    let (decls, _) = &file;

    // Build rpcmap: walk DExport(Rpc, fcall, n) declarations
    let mut rpcs = RpcMap::empty_module();
    for d in decls {
        if let Decl::Export(ExportKind::Rpc(_), fcall, n, _, _, _) = &d.node {
            rpcs = rpcs.insert(fcall, *n);
        }
    }

    let push_basis: HashSet<String> = PUSH_BASIS.iter().map(|s| s.to_string()).collect();
    let empty_basis: HashSet<String> = HashSet::new();

    // Two-pass: compute pull_ids and push_ids
    let mut pull_ids: HashSet<usize> = HashSet::new();
    let mut push_ids: HashSet<usize> = HashSet::new();

    for d in decls {
        match &d.node {
            Decl::Val(_, n, _, e, _) => {
                if has_client(e, &empty_basis, &rpcs, &pull_ids, false) {
                    pull_ids.insert(*n);
                }
                if has_client(e, &push_basis, &rpcs, &push_ids, true) {
                    push_ids.insert(*n);
                }
            }
            Decl::ValRec(vis) => {
                let any_pull = vis
                    .iter()
                    .any(|(_, _, _, e, _)| has_client(e, &empty_basis, &rpcs, &pull_ids, false));
                let any_push = vis
                    .iter()
                    .any(|(_, _, _, e, _)| has_client(e, &push_basis, &rpcs, &push_ids, true));
                if any_pull {
                    for (_, n, _, _, _) in vis {
                        pull_ids.insert(*n);
                    }
                }
                if any_push {
                    for (_, n, _, _, _) in vis {
                        push_ids.insert(*n);
                    }
                }
            }
            _ => {}
        }
    }

    // Protocol persistent check: "cgi" is not persistent, others typically are
    let protocol_persistent = !settings.protocol.is_empty() && settings.protocol != "cgi";

    let all_ids: HashSet<usize> = pull_ids.union(&push_ids).cloned().collect();
    let mut found_bad = false;

    let new_ps: Vec<_> = all_ids
        .into_iter()
        .map(|n| {
            let side = if push_ids.contains(&n) {
                if !protocol_persistent && !found_bad {
                    found_bad = true;
                    errors.report_at_with_hint(
                        crate::error_types::Span::dummy(),
                        DiagnosticPayload::new(
                            DiagnosticId::ScriptPushProtocolNotPersistent,
                            vec![settings.protocol.clone()],
                        ),
                        DiagnosticId::HintScriptPushProtocolNotPersistent,
                        vec![],
                    );
                }
                Sidedness::ServerAndPullAndPush
            } else if pull_ids.contains(&n) {
                Sidedness::ServerAndPull
            } else {
                Sidedness::ServerOnly
            };
            (n, side, crate::monomorphized::DbMode::AnyDb)
        })
        .collect();

    let (decls, _) = file;
    (decls, new_ps)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_file_classify() {
        let settings = Settings::default();
        let mut errors = ErrorReporter::new();
        let result = classify((vec![], vec![]), &settings, &mut errors);
        assert!(result.0.is_empty());
        assert!(result.1.is_empty());
        assert!(!errors.has_errors());
    }

    #[test]
    fn rpc_map_lookup_and_insert() {
        let r = RpcMap::empty_module();
        let r = r.insert("foo/bar", 42);
        assert_eq!(r.lookup("foo/bar"), Some(42));
        assert_eq!(r.lookup("foo"), None); // partial path doesn't match
        assert_eq!(r.lookup("baz"), None);
    }
}
