//! Path uniqueness check pass.
//!
//! Verifies that no two declarations export the same URL path, and that
//! table/sequence/cookie/style names are unique.
//!
//! Mirrors `PathCheck.check` in `pathcheck.sml`.

use std::collections::HashSet;

use crate::error_types::ErrorReporter;
use crate::monomorphized::{Decl, Exp, File, LocExp};
use crate::primitives::Prim;

// ---------------------------------------------------------------------------
// constraints — walk a constraint expression collecting path strings
// ---------------------------------------------------------------------------

fn collect_constraints(
    e: &LocExp,
    table: &str,
    rels: &mut HashSet<String>,
    errors: &mut ErrorReporter,
) {
    match &e.node {
        Exp::Record(xets) if xets.len() == 1 => {
            let path = format!("{}_{}", table, xets[0].0);
            if rels.contains(&path) {
                errors.report_at(
                    e.span.clone(),
                    format!("Duplicate constraint path {}", path),
                );
            } else {
                rels.insert(path);
            }
        }
        Exp::Strcat(e1, e2) => {
            collect_constraints(e1, table, rels, errors);
            collect_constraints(e2, table, rels, errors);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Check for duplicate export / table / cookie / style paths.
///
/// Reports errors but does not modify the file.
/// Mirrors `PathCheck.check`.
pub fn check(file: &File, errors: &mut ErrorReporter) {
    let (decls, _) = file;

    let mut funcs: HashSet<String> = HashSet::new();
    let mut rels: HashSet<String> = HashSet::new();
    let mut cookies: HashSet<String> = HashSet::new();
    let mut styles: HashSet<String> = HashSet::new();

    for d in decls {
        let span = d.span.clone();
        match &d.node {
            Decl::Export(_, s, _, _, _, _) => {
                if funcs.contains(s) {
                    errors.report_at(span, format!("Duplicate function path {}", s));
                } else {
                    funcs.insert(s.clone());
                }
            }
            Decl::Table(s, _, pk_exp, ce) => {
                // Check table itself
                if rels.contains(s) {
                    errors.report_at(span.clone(), format!("Duplicate table/sequence path {}", s));
                } else {
                    rels.insert(s.clone());
                }
                // Check primary key constraint path (if non-empty string expression)
                let pk_empty =
                    matches!(&pk_exp.node, Exp::Prim(Prim::String(_, pk)) if pk.is_empty());
                if !pk_empty {
                    let pkey_path = format!("{}_Pkey", s);
                    if rels.contains(&pkey_path) {
                        errors.report_at(
                            span.clone(),
                            format!("Duplicate primary key constraint path {}", pkey_path),
                        );
                    } else {
                        rels.insert(pkey_path);
                    }
                }
                // Check additional constraints
                collect_constraints(ce, s, &mut rels, errors);
            }
            Decl::Sequence(s) => {
                if rels.contains(s) {
                    errors.report_at(span, format!("Duplicate table/sequence path {}", s));
                } else {
                    rels.insert(s.clone());
                }
            }
            Decl::Cookie(s) => {
                if cookies.contains(s) {
                    errors.report_at(span, format!("Duplicate cookie path {}", s));
                } else {
                    cookies.insert(s.clone());
                }
            }
            Decl::Style(s) => {
                if styles.contains(s) {
                    errors.report_at(span, format!("Duplicate style path {}", s));
                } else {
                    styles.insert(s.clone());
                }
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_file_no_errors() {
        let mut errors = ErrorReporter::new();
        check(&(vec![], vec![]), &mut errors);
        assert!(!errors.has_errors());
    }
}
