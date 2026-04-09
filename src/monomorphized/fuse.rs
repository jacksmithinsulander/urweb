//! Fuse pass: convert string-returning functions into direct-write variants.
//!
//! For each function whose return type ends in `Basis.string` (possibly behind
//! multiple arrows), creates a parallel variant with a fresh id that instead
//! calls `EWrite` on the string expression directly.  Also rewrites
//! `EWrite(app-chain-over-ENamed n)` → the fused variant `ENamed funcs[n]` in
//! all expressions.
//!
//! Mirrors `fuse.sml`.

use std::collections::HashMap;

use crate::error_types::{Located, Span};
use crate::monomorphized::{utilities, Decl, Exp, File, LocDecl, LocExp, LocTyp, Typ};

// ---------------------------------------------------------------------------
// opt_exp — identity stub (mono_opt runs as a separate pass after fuse)
// ---------------------------------------------------------------------------

fn opt_exp(e: LocExp) -> LocExp {
    e
}

// ---------------------------------------------------------------------------
// returns_string — check if type ends in Basis.string
// ---------------------------------------------------------------------------

/// Recursively check if `t` ends in `Basis.string` (possibly behind arrows).
///
/// Returns `Some((args, t'))` where `args[0]` is the outermost domain and
/// `t'` is the type with the trailing `string` replaced by `TRecord([])`.
fn rs_inner(t: &LocTyp) -> Option<(Vec<LocTyp>, LocTyp)> {
    match &t.node {
        Typ::Ffi(m, x) if m == "Basis" && x == "string" => {
            Some((vec![], Located::new(Typ::Record(vec![]), t.span.clone())))
        }
        Typ::Fun(dom, ran) => rs_inner(ran).map(|(mut args, ran_p)| {
            args.insert(0, (**dom).clone());
            let t_p = Located::new(Typ::Fun(dom.clone(), Box::new(ran_p)), t.span.clone());
            (args, t_p)
        }),
        _ => None,
    }
}

/// Like `rs_inner` but requires the outermost constructor to be `TFun`.
///
/// Mirrors `returnsString` in `fuse.sml`.
fn returns_string(t: &LocTyp) -> Option<(Vec<LocTyp>, LocTyp)> {
    match &t.node {
        Typ::Fun(dom, ran) => rs_inner(ran).map(|(mut args, ran_p)| {
            args.insert(0, (**dom).clone());
            let t_p = Located::new(Typ::Fun(dom.clone(), Box::new(ran_p)), t.span.clone());
            (args, t_p)
        }),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// get_body — peel leading EAbs layers
// ---------------------------------------------------------------------------

/// Peel `count` leading `EAbs` layers off `e`.
///
/// Returns `Some((inner_body, binders))` where `binders[0]` is the outermost
/// binder `(name, domain_type)`.  Returns `None` if `e` does not have enough
/// leading `EAbs` nodes.
fn get_body(e: &LocExp, count: usize) -> Option<(LocExp, Vec<(String, LocTyp)>)> {
    if count == 0 {
        return Some((e.clone(), vec![]));
    }
    match &e.node {
        Exp::Abs(x, dom, _, body) => get_body(body, count - 1).map(|(inner, mut binders)| {
            binders.insert(0, (x.clone(), dom.clone()));
            (inner, binders)
        }),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// do_vi — build a fused variant for a value binding
// ---------------------------------------------------------------------------

/// Try to build a fused variant for binding `vi`.
///
/// Returns `Some(new_vi)` if the binding's type ends in `string` and the
/// expression has enough leading `EAbs` layers to peel.
fn do_vi(
    vi: &(String, usize, LocTyp, LocExp, String),
    fresh_id: usize,
    loc: &Span,
) -> Option<(String, usize, LocTyp, LocExp, String)> {
    let (x, _, t, e, s) = vi;
    let (args, t_prime) = returns_string(t)?;
    let (body, binders) = get_body(e, args.len())?;

    // Wrap the string body in EWrite, then optimise (stub: identity).
    let written = opt_exp(Located::new(Exp::Write(Box::new(body)), loc.clone()));

    // Rebuild abstraction stack from innermost (right of binders) to outermost.
    //
    // binders[0] is outermost; we iterate in reverse so innermost first.
    let unit_t = Located::new(Typ::Record(vec![]), loc.clone());
    let (final_body, _) =
        binders
            .iter()
            .rev()
            .fold((written, unit_t), |(acc_body, acc_ran), (bx, dom)| {
                let new_ran = Located::new(
                    Typ::Fun(Box::new(dom.clone()), Box::new(acc_ran.clone())),
                    loc.clone(),
                );
                let abs = Located::new(
                    Exp::Abs(bx.clone(), dom.clone(), acc_ran, Box::new(acc_body)),
                    loc.clone(),
                );
                (abs, new_ran)
            });

    Some((x.clone(), fresh_id, t_prime, final_body, s.clone()))
}

// ---------------------------------------------------------------------------
// unravel — find the fused replacement for an EWrite target
// ---------------------------------------------------------------------------

/// Given the inner expression of `EWrite(e)`, return the fused replacement.
///
/// Follows an app-chain `EApp(EApp(... ENamed n ...), ...)` and replaces the
/// inner `ENamed n` with `ENamed funcs[n]`, removing the outer `EWrite`.
fn unravel(e: &LocExp, funcs: &HashMap<usize, usize>) -> Option<LocExp> {
    match &e.node {
        Exp::Named(n) => funcs
            .get(n)
            .map(|n_prime| Located::new(Exp::Named(*n_prime), e.span.clone())),
        Exp::App(e1, e2) => unravel(e1, funcs)
            .map(|e1_prime| Located::new(Exp::App(Box::new(e1_prime), e2.clone()), e.span.clone())),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// max_name — maximum id used in a declaration list
// ---------------------------------------------------------------------------

fn max_name(decls: &[LocDecl]) -> usize {
    decls.iter().fold(0, |m, d| match &d.node {
        Decl::Datatype(dts) => dts.iter().fold(m, |m, dt| {
            dt.constrs
                .iter()
                .fold(m.max(dt.id), |m, (_, n, _)| m.max(*n))
        }),
        Decl::Val(_, n, _, _, _) => m.max(*n),
        Decl::ValRec(vis) => vis.iter().fold(m, |m, (_, n, _, _, _)| m.max(*n)),
        _ => m,
    })
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the fuse pass over a Mono file.
///
/// Mirrors `Fuse.fuse`.
pub fn fuse(file: File) -> File {
    let (decls, exports) = file;
    let mut funcs: HashMap<usize, usize> = HashMap::new();
    let mut next_id = max_name(&decls) + 1;

    let new_decls: Vec<LocDecl> = decls
        .into_iter()
        .map(|d| {
            let span = d.span.clone();

            // ----------------------------------------------------------
            // Step 1: optionally add fused variants; record id mappings.
            // ----------------------------------------------------------
            let (new_node, updates): (Decl, Vec<(usize, usize)>) = match d.node {
                Decl::Val(x, n, t, e, s) => {
                    let vi = (x, n, t, e, s);
                    match do_vi(&vi, next_id, &span) {
                        None => (Decl::Val(vi.0, vi.1, vi.2, vi.3, vi.4), vec![]),
                        Some(vi_prime) => {
                            let entry = (vi.1, next_id);
                            next_id += 1;
                            (Decl::ValRec(vec![vi, vi_prime]), vec![entry])
                        }
                    }
                }
                Decl::ValRec(vis) => {
                    let mut vis_prime: Vec<(String, usize, LocTyp, LocExp, String)> = vec![];
                    let mut updates: Vec<(usize, usize)> = vec![];
                    let mut fresh = next_id;
                    for vi in &vis {
                        if let Some(vi_p) = do_vi(vi, fresh, &span) {
                            updates.push((vi.1, fresh));
                            fresh += 1;
                            vis_prime.push(vi_p);
                        }
                    }
                    next_id = fresh;
                    if vis_prime.is_empty() {
                        (Decl::ValRec(vis), updates)
                    } else {
                        let mut combined = vis;
                        combined.extend(vis_prime);
                        (Decl::ValRec(combined), updates)
                    }
                }
                other => (other, vec![]),
            };

            // Apply id-mapping updates.
            for (n, n_prime) in updates {
                funcs.insert(n, n_prime);
            }

            // ----------------------------------------------------------
            // Step 2: rewrite EWrite(app-chain) → fused version.
            // ----------------------------------------------------------
            // NLL: the mutable uses of `funcs` above are finished, so we
            // can take an immutable borrow here.
            let funcs_ref: &HashMap<usize, usize> = &funcs;
            utilities::decl::map(
                Located::new(new_node, span),
                &|t| t,
                &|e| {
                    if let Exp::Write(ref inner) = e {
                        if let Some(replacement) = unravel(inner, funcs_ref) {
                            return replacement.node;
                        }
                    }
                    e
                },
                &|d_inner| d_inner,
            )
        })
        .collect();

    (new_decls, exports)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;
    use anyhow::Context as _; // .with_context() on Result in tests

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    fn string_typ() -> LocTyp {
        dummy(Typ::Ffi("Basis".into(), "string".into()))
    }

    fn int_typ() -> LocTyp {
        dummy(Typ::Ffi("Basis".into(), "int".into()))
    }

    #[test]
    fn fuse_empty_file() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let result = fuse((vec![], vec![]));
        assert!(result.0.is_empty());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn returns_string_plain_string_is_none() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(returns_string(&string_typ()).is_none());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn returns_string_int_to_string_is_some() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = dummy(Typ::Fun(Box::new(int_typ()), Box::new(string_typ())));
        let (args, t_prime) = returns_string(&t).with_context(|| "should match")?;
        assert_eq!(args.len(), 1);
        // t' should be int -> unit (TRecord [])
        assert!(matches!(t_prime.node, Typ::Fun(_, _)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn returns_string_non_string_return_is_none() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = dummy(Typ::Fun(Box::new(int_typ()), Box::new(int_typ())));
        assert!(returns_string(&t).is_none());
        Ok(()) // return success to the test harness
    }
}
