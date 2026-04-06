//! Optional warnings for unused top-level bindings in the language server (reachable from export, table, or view roots).

use std::collections::HashSet;
use std::path::Path;

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::elaborated::{
    Declaration, ElaboratedDeclaration, Expression, File as ElabFile, LocatedExpression,
    LocatedSignature, Signature, SignatureItem, Structure,
};
use crate::error_types::ErrorReporter;
use crate::lsp_semantics::{paths_match_given_open_normalized, slash_normalized_cow};

fn collect_named_ids_expr(e: &LocatedExpression, s: &mut HashSet<usize>) {
    match &e.node {
        Expression::Named(id) => {
            s.insert(*id);
        }
        Expression::Rel(_) | Expression::Prim(_) => {}
        Expression::ModProj(_, _, _) => {}
        Expression::App(a, b) => {
            collect_named_ids_expr(a, s);
            collect_named_ids_expr(b, s);
        }
        Expression::Abs(_, _, _, b) => collect_named_ids_expr(b, s),
        Expression::CApp(a, _) => collect_named_ids_expr(a, s),
        Expression::CAbs(_, _, _, b) => collect_named_ids_expr(b, s),
        Expression::KAbs(_, b) => collect_named_ids_expr(b, s),
        Expression::KApp(b, _) => collect_named_ids_expr(b, s),
        Expression::Record(fs) => {
            for (_, e2, _) in fs {
                collect_named_ids_expr(e2, s);
            }
        }
        Expression::Field(e2, _, _) => collect_named_ids_expr(e2, s),
        Expression::Concat(a, _, b, _) => {
            collect_named_ids_expr(a, s);
            collect_named_ids_expr(b, s);
        }
        Expression::Cut(e2, _, _) => collect_named_ids_expr(e2, s),
        Expression::CutMulti(e2, _, _) => collect_named_ids_expr(e2, s),
        Expression::Case(disc, arms, _) => {
            collect_named_ids_expr(disc, s);
            for (_, ee) in arms {
                collect_named_ids_expr(ee, s);
            }
        }
        Expression::Error => {}
        Expression::Unif(r) => {
            if let Ok(g) = r.lock() {
                if let Some(inner) = g.as_ref() {
                    collect_named_ids_expr(inner, s);
                }
            }
        }
        Expression::Hole(_) => {}
        Expression::Let(bindings, body, _) => {
            for b in bindings {
                match &b.node {
                    ElaboratedDeclaration::Val(_, _, e2) => collect_named_ids_expr(e2, s),
                    ElaboratedDeclaration::ValRec(recs) => {
                        for (_, _, e2) in recs {
                            collect_named_ids_expr(e2, s);
                        }
                    }
                }
            }
            collect_named_ids_expr(body, s);
        }
    }
}

fn collect_named_from_structure_roots(
    strukt: &crate::elaborated::LocatedStructure,
    s: &mut HashSet<usize>,
) {
    match &strukt.node {
        Structure::Const(decls) => {
            for d in decls {
                collect_named_from_declaration_roots(&d.node, s);
            }
        }
        Structure::Var(_) => {}
        Structure::Proj(inner, _) => collect_named_from_structure_roots(inner, s),
        Structure::Fun(_, _, _, _, b) => collect_named_from_structure_roots(b, s),
        Structure::App(a, b) => {
            collect_named_from_structure_roots(a, s);
            collect_named_from_structure_roots(b, s);
        }
        Structure::Error => {}
    }
}

fn collect_named_from_signature_roots(sig: &LocatedSignature, s: &mut HashSet<usize>) {
    match &sig.node {
        Signature::Const(items) => {
            for it in items {
                collect_named_from_signature_item_roots(&it.node, s);
            }
        }
        Signature::Var(_) => {}
        Signature::Fun(_, _, _, b) => collect_named_from_signature_roots(b, s),
        Signature::Where(inner, _, _, _) => collect_named_from_signature_roots(inner, s),
        Signature::Proj(_, _, _) => {}
        Signature::Error => {}
    }
}

fn collect_named_from_signature_item_roots(item: &SignatureItem, s: &mut HashSet<usize>) {
    match item {
        SignatureItem::Structure(_, _, _, inner) | SignatureItem::Signature(_, _, inner) => {
            collect_named_from_signature_roots(inner, s);
        }
        _ => {}
    }
}

/// `Named` value references appearing in “root” declarations only (not inside ordinary `val` bodies).
fn collect_named_from_declaration_roots(decl: &Declaration, s: &mut HashSet<usize>) {
    match decl {
        Declaration::Val(_, _, _, _) | Declaration::ValRec(_) => {}
        Declaration::Constructor(_, _, _, _)
        | Declaration::Datatype(_)
        | Declaration::DatatypeImp { .. } => {}
        Declaration::Signature(_, _, sig) => collect_named_from_signature_roots(sig, s),
        Declaration::Structure(_, _, _, ls) => collect_named_from_structure_roots(ls, s),
        Declaration::FfiStr(_, _, sig) => collect_named_from_signature_roots(sig, s),
        Declaration::Constraint(_, _) => {}
        Declaration::Export(_, _, ls) => collect_named_from_structure_roots(ls, s),
        Declaration::Table { exp, pk_exp, .. } => {
            collect_named_ids_expr(exp, s);
            collect_named_ids_expr(pk_exp, s);
        }
        Declaration::Sequence(_, _, _) | Declaration::Database(_) | Declaration::Style(_, _, _) => {
        }
        Declaration::View(_, _, _, e, _) => collect_named_ids_expr(e, s),
        Declaration::Index(e1, e2) => {
            collect_named_ids_expr(e1, s);
            collect_named_ids_expr(e2, s);
        }
        Declaration::Cookie(_, _, _, _) => {}
        Declaration::Task(e1, e2) => {
            collect_named_ids_expr(e1, s);
            collect_named_ids_expr(e2, s);
        }
        Declaration::Policy(e) => collect_named_ids_expr(e, s),
        Declaration::OnError(_, _, _) => {}
        Declaration::Ffi(_, _, _, _) => {}
    }
}

fn expand_used_from_roots(elab: &ElabFile, roots: &mut HashSet<usize>) {
    let mut changed = true;
    while changed {
        changed = false;
        for d in elab {
            match &d.node {
                Declaration::Val(_, id, _, e) => {
                    if roots.contains(id) {
                        let before = roots.len();
                        collect_named_ids_expr(e, roots);
                        if roots.len() > before {
                            changed = true;
                        }
                    }
                }
                Declaration::ValRec(recs) => {
                    for (_, id, _, e) in recs {
                        if roots.contains(id) {
                            let before = roots.len();
                            collect_named_ids_expr(e, roots);
                            if roots.len() > before {
                                changed = true;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

/// Emit `WarningAt` for top-level `val` / `val rec` bindings that are not reachable from roots.
pub fn report_unused_top_level_values(
    elab: &ElabFile,
    open_file_key: &str,
    errors: &mut ErrorReporter,
) {
    let mut used = HashSet::new();
    for d in elab {
        collect_named_from_declaration_roots(&d.node, &mut used);
    }
    expand_used_from_roots(elab, &mut used);

    let open_norm = slash_normalized_cow(open_file_key);
    let oref = open_norm.as_ref();
    for d in elab {
        match &d.node {
            Declaration::Val(name, id, _, _) => {
                if paths_match_given_open_normalized(oref, &d.span.file) && !used.contains(id) {
                    errors.report_warning_at_with_hint(
                        d.span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::LspUnusedValueNeverUsedFromEntry,
                            vec![name.clone()],
                        ),
                        DiagnosticId::HintLspUnusedValueNeverUsedFromEntry,
                        vec![],
                    );
                }
            }
            Declaration::ValRec(recs) => {
                for (name, id, _, _) in recs {
                    if paths_match_given_open_normalized(oref, &d.span.file) && !used.contains(id) {
                        errors.report_warning_at_with_hint(
                            d.span.clone(),
                            DiagnosticPayload::new(
                                DiagnosticId::LspUnusedValRecNotReachable,
                                vec![name.clone()],
                            ),
                            DiagnosticId::HintLspUnusedValRecNotReachable,
                            vec![],
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

/// Workspace-relative key for the open buffer, same as LSP `file_key_relative_to_root`.
pub fn open_key_for_buffer(workspace_root: &Path, disk_ur_path: &Path) -> String {
    crate::lsp_workspace::file_key_relative_to_root(workspace_root, disk_ur_path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn open_key_helpers_consistent() {
        let root = PathBuf::from("/proj");
        let p = PathBuf::from("/proj/src/M.ur");
        assert_eq!(open_key_for_buffer(&root, &p), "src/M.ur");
    }
}
