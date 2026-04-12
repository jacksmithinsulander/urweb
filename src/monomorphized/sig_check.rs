//! CSRF signature check pass.
//!
//! Identifies declarations that read the CSRF signature (via `Basis.sigString`
//! or accessing a `siggers` rel variable), then wraps non-function declarations
//! in a unit-arg lambda and rewrites call sites.
//!
//! Mirrors `SigCheck.check` in `sigcheck.sml`.

use std::collections::HashSet;

use crate::error_types::Located;
use crate::monomorphized::{utilities, Decl, Exp, File, LocDecl, LocExp, LocTyp, Typ};

// ---------------------------------------------------------------------------
// Helper: unit type (TRecord [])
// ---------------------------------------------------------------------------

fn unit_typ(span: &crate::error_types::Span) -> LocTyp {
    Located::new(Typ::Record(vec![]), span.clone())
}

fn unit_exp(span: &crate::error_types::Span) -> LocExp {
    Located::new(Exp::Record(vec![]), span.clone())
}

// ---------------------------------------------------------------------------
// is_siggy — does a declaration reference siggers or Basis.sigString?
// ---------------------------------------------------------------------------

fn is_siggy_decl(d: &LocDecl, siggers: &HashSet<usize>) -> bool {
    utilities::decl::exists(
        d,
        &|_| false,
        &|node| match node {
            Exp::Rel(n) => siggers.contains(n),
            Exp::FfiApp(m, x, _) => m == "Basis" && x == "sigString",
            _ => false,
        },
        &|_| false,
    )
}

// ---------------------------------------------------------------------------
// sigify — rewrite ENamed n → EApp(ENamed n, ERecord []) for n in sigdecs
// ---------------------------------------------------------------------------

fn sigify_node(node: Exp, sigdecs: &HashSet<usize>, span: &crate::error_types::Span) -> Exp {
    match node {
        Exp::Named(n) if sigdecs.contains(&n) => {
            let named = Located::new(Exp::Named(n), span.clone());
            let unit = unit_exp(span);
            Exp::App(Box::new(named), Box::new(unit))
        }
        other => other,
    }
}

fn sigify_decl(d: LocDecl, sigdecs: &HashSet<usize>) -> LocDecl {
    let span = d.span.clone();
    utilities::decl::map(
        d,
        &|t| t,
        &|node| sigify_node(node, sigdecs, &span),
        &|dn| dn,
    )
}

// ---------------------------------------------------------------------------
// is_fun — does an expression start with EAbs?
// ---------------------------------------------------------------------------

fn is_fun(e: &LocExp) -> bool {
    matches!(&e.node, Exp::Abs(_, _, _, _))
}

// ---------------------------------------------------------------------------
// do_decl — process one declaration
// ---------------------------------------------------------------------------

fn do_decl(d: LocDecl, siggers: &mut HashSet<usize>, sigdecs: &mut HashSet<usize>) -> LocDecl {
    let span = d.span.clone();

    match &d.node {
        Decl::Val(_x, n, _t, _e, _s) => {
            let n = *n;
            let is_sig = is_siggy_decl(&d, siggers);

            // Rewrite ENamed references in this decl
            let d_sigified = sigify_decl(d, sigdecs);

            if is_sig {
                siggers.insert(n);
                // Extract (mutably) the sigified val fields
                if let Decl::Val(x, n2, t, e, s) = d_sigified.node {
                    if is_fun(&e) {
                        // Already a function: just mark it
                        Located::new(Decl::Val(x, n2, t, e, s), span)
                    } else {
                        // Wrap e in a unit-arg lambda
                        sigdecs.insert(n2);
                        let unit_t = unit_typ(&span);
                        let new_t = Located::new(
                            Typ::Fun(Box::new(unit_t.clone()), Box::new(t.clone())),
                            span.clone(),
                        );
                        let new_e = Located::new(
                            Exp::Abs("_".to_string(), unit_t, t, Box::new(e)),
                            span.clone(),
                        );
                        Located::new(Decl::Val(x, n2, new_t, new_e, s), span)
                    }
                } else {
                    d_sigified
                }
            } else {
                d_sigified
            }
        }

        Decl::ValRec(_vis) => {
            let is_sig = is_siggy_decl(&d, siggers);
            let d_sigified = sigify_decl(d, sigdecs);

            if is_sig {
                if let Decl::ValRec(vis) = &d_sigified.node {
                    for (_, n, _, _, _) in vis {
                        siggers.insert(*n);
                    }
                }
            }
            d_sigified
        }

        _ => sigify_decl(d, sigdecs),
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Apply CSRF signature checking transformation.
///
/// Mirrors `SigCheck.check`.
pub fn check(file: File) -> File {
    let (decls, ps) = file;

    let mut siggers: HashSet<usize> = HashSet::new();
    let mut sigdecs: HashSet<usize> = HashSet::new();

    let new_decls = decls
        .into_iter()
        .map(|d| do_decl(d, &mut siggers, &mut sigdecs))
        .collect();

    (new_decls, ps)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_file() {
        let result = check((vec![], vec![]));
        assert!(result.0.is_empty());
    }
}
