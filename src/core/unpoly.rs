//! Unpoly — specialize polymorphic Core functions by substituting closed constructor arguments.
//!
//! This pass repeats polymorphic function definitions, substituting in closed
//! constructor arguments at each call site. A call like `f [T1] [T2]` where
//! `T1` and `T2` are closed (no free `CRel` variables) is turned into a call
//! to a freshly generated specialization `f_unpoly` with `T1` and `T2` already
//! substituted away.
//!
//! Mirrors `unpoly.sml`.

#![allow(dead_code)]

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::HashMap;

use crate::core::local_reduction::reduce_con;
use crate::core::utilities::constructor as con_util;
use crate::core::utilities::file as file_util;
use crate::core::utilities::kind as kind_util;
use crate::core::*;
use crate::error_types::{Located, Span};

// ---------------------------------------------------------------------------
// Substitution helpers
// ---------------------------------------------------------------------------

/// Replace every occurrence of `Constructor::Rel(depth)` in `body` with `sub`,
/// without adjusting depth when entering binders.
///
/// This is correct because `sub` is always a *closed* constructor (checked by
/// `is_open`), so no capture can occur even when we pass under binders.
pub fn sub_con_in_con(
    depth: usize,
    sub: &LocatedConstructor,
    body: LocatedConstructor,
) -> LocatedConstructor {
    let span = body.span.clone();
    match body.node {
        Constructor::Rel(i) if i == depth => sub.clone(),
        Constructor::Rel(_)
        | Constructor::Named(_)
        | Constructor::Ffi(_, _)
        | Constructor::Name(_)
        | Constructor::Unit => body,

        Constructor::TFun(a, b) => Located::new(
            Constructor::TFun(
                Box::new(sub_con_in_con(depth, sub, *a)),
                Box::new(sub_con_in_con(depth, sub, *b)),
            ),
            span,
        ),
        Constructor::TCFun(x, k, b) => Located::new(
            Constructor::TCFun(x, k, Box::new(sub_con_in_con(depth, sub, *b))),
            span,
        ),
        Constructor::TRecord(inner) => Located::new(
            Constructor::TRecord(Box::new(sub_con_in_con(depth, sub, *inner))),
            span,
        ),
        Constructor::App(f, a) => Located::new(
            Constructor::App(
                Box::new(sub_con_in_con(depth, sub, *f)),
                Box::new(sub_con_in_con(depth, sub, *a)),
            ),
            span,
        ),
        Constructor::Abs(x, k, b) => Located::new(
            Constructor::Abs(x, k, Box::new(sub_con_in_con(depth, sub, *b))),
            span,
        ),
        Constructor::KAbs(x, b) => Located::new(
            Constructor::KAbs(x, Box::new(sub_con_in_con(depth, sub, *b))),
            span,
        ),
        Constructor::KApp(c, k) => Located::new(
            Constructor::KApp(Box::new(sub_con_in_con(depth, sub, *c)), k),
            span,
        ),
        Constructor::TKFun(x, b) => Located::new(
            Constructor::TKFun(x, Box::new(sub_con_in_con(depth, sub, *b))),
            span,
        ),
        Constructor::Record(k, pairs) => {
            let pairs_new = pairs
                .into_iter()
                .map(|(n, v)| (sub_con_in_con(depth, sub, n), sub_con_in_con(depth, sub, v)))
                .collect();
            Located::new(Constructor::Record(k, pairs_new), span)
        }
        Constructor::Concat(a, b) => Located::new(
            Constructor::Concat(
                Box::new(sub_con_in_con(depth, sub, *a)),
                Box::new(sub_con_in_con(depth, sub, *b)),
            ),
            span,
        ),
        Constructor::Map(k1, k2) => Located::new(Constructor::Map(k1, k2), span),
        Constructor::Tuple(cs) => Located::new(
            Constructor::Tuple(
                cs.into_iter()
                    .map(|c| sub_con_in_con(depth, sub, c))
                    .collect(),
            ),
            span,
        ),
        Constructor::Proj(c, i) => Located::new(
            Constructor::Proj(Box::new(sub_con_in_con(depth, sub, *c)), i),
            span,
        ),
    }
}

/// Replace every occurrence of `Constructor::Rel(depth)` inside an expression
/// with `sub`. As with `sub_con_in_con`, `sub` must be closed so no capture
/// adjustment is needed.
fn sub_con_in_exp(
    depth: usize,
    sub: &LocatedConstructor,
    body: LocatedExpression,
) -> LocatedExpression {
    let span = body.span.clone();
    match body.node {
        Expression::Prim(_) | Expression::Rel(_) | Expression::Named(_) | Expression::Ffi(_, _) => {
            body
        }
        Expression::Constructor(dk, pc, cs, arg) => {
            let cs_new = cs
                .into_iter()
                .map(|c| sub_con_in_con(depth, sub, c))
                .collect();
            let arg_new = arg.map(|e| Box::new(sub_con_in_exp(depth, sub, *e)));
            Located::new(Expression::Constructor(dk, pc, cs_new, arg_new), span)
        }
        Expression::FfiApp(m, f, args) => {
            let args_new = args
                .into_iter()
                .map(|(e, c)| (sub_con_in_exp(depth, sub, e), sub_con_in_con(depth, sub, c)))
                .collect();
            Located::new(Expression::FfiApp(m, f, args_new), span)
        }
        Expression::App(f, a) => Located::new(
            Expression::App(
                Box::new(sub_con_in_exp(depth, sub, *f)),
                Box::new(sub_con_in_exp(depth, sub, *a)),
            ),
            span,
        ),
        Expression::Abs(x, dom, ran, body) => Located::new(
            Expression::Abs(
                x,
                sub_con_in_con(depth, sub, dom),
                sub_con_in_con(depth, sub, ran),
                Box::new(sub_con_in_exp(depth, sub, *body)),
            ),
            span,
        ),
        Expression::CApp(f, c) => Located::new(
            Expression::CApp(
                Box::new(sub_con_in_exp(depth, sub, *f)),
                sub_con_in_con(depth, sub, c),
            ),
            span,
        ),
        Expression::CAbs(x, k, body) => Located::new(
            Expression::CAbs(x, k, Box::new(sub_con_in_exp(depth, sub, *body))),
            span,
        ),
        Expression::KAbs(x, body) => Located::new(
            Expression::KAbs(x, Box::new(sub_con_in_exp(depth, sub, *body))),
            span,
        ),
        Expression::KApp(f, k) => Located::new(
            Expression::KApp(Box::new(sub_con_in_exp(depth, sub, *f)), k),
            span,
        ),
        Expression::Record(fields) => {
            let fields_new = fields
                .into_iter()
                .map(|(name_c, val_e, ty_c)| {
                    (
                        sub_con_in_con(depth, sub, name_c),
                        sub_con_in_exp(depth, sub, val_e),
                        sub_con_in_con(depth, sub, ty_c),
                    )
                })
                .collect();
            Located::new(Expression::Record(fields_new), span)
        }
        Expression::Field(record, field_c, meta) => Located::new(
            Expression::Field(
                Box::new(sub_con_in_exp(depth, sub, *record)),
                sub_con_in_con(depth, sub, field_c),
                FieldMeta {
                    field: sub_con_in_con(depth, sub, meta.field),
                    rest: sub_con_in_con(depth, sub, meta.rest),
                },
            ),
            span,
        ),
        Expression::Concat(le, lc, re, rc) => Located::new(
            Expression::Concat(
                Box::new(sub_con_in_exp(depth, sub, *le)),
                sub_con_in_con(depth, sub, lc),
                Box::new(sub_con_in_exp(depth, sub, *re)),
                sub_con_in_con(depth, sub, rc),
            ),
            span,
        ),
        Expression::Cut(record, field_c, meta) => Located::new(
            Expression::Cut(
                Box::new(sub_con_in_exp(depth, sub, *record)),
                sub_con_in_con(depth, sub, field_c),
                FieldMeta {
                    field: sub_con_in_con(depth, sub, meta.field),
                    rest: sub_con_in_con(depth, sub, meta.rest),
                },
            ),
            span,
        ),
        Expression::CutMulti(record, field_c, rest_meta) => Located::new(
            Expression::CutMulti(
                Box::new(sub_con_in_exp(depth, sub, *record)),
                sub_con_in_con(depth, sub, field_c),
                RestMeta {
                    rest: sub_con_in_con(depth, sub, rest_meta.rest),
                },
            ),
            span,
        ),
        Expression::Case(disc, arms, meta) => {
            let disc_new = Box::new(sub_con_in_exp(depth, sub, *disc));
            let arms_new = arms
                .into_iter()
                .map(|(pat, arm_e)| {
                    (
                        sub_con_in_pat(depth, sub, pat),
                        sub_con_in_exp(depth, sub, arm_e),
                    )
                })
                .collect();
            let meta_new = CaseMeta {
                disc: sub_con_in_con(depth, sub, meta.disc),
                result: sub_con_in_con(depth, sub, meta.result),
            };
            Located::new(Expression::Case(disc_new, arms_new, meta_new), span)
        }
        Expression::Write(inner) => Located::new(
            Expression::Write(Box::new(sub_con_in_exp(depth, sub, *inner))),
            span,
        ),
        Expression::Closure(id, env) => {
            let env_new = env
                .into_iter()
                .map(|e| sub_con_in_exp(depth, sub, e))
                .collect();
            Located::new(Expression::Closure(id, env_new), span)
        }
        Expression::Let(x, ty, e1, e2) => Located::new(
            Expression::Let(
                x,
                sub_con_in_con(depth, sub, ty),
                Box::new(sub_con_in_exp(depth, sub, *e1)),
                Box::new(sub_con_in_exp(depth, sub, *e2)),
            ),
            span,
        ),
        Expression::ServerCall(id, args, result_ty, mode) => {
            let args_new = args
                .into_iter()
                .map(|e| sub_con_in_exp(depth, sub, e))
                .collect();
            Located::new(
                Expression::ServerCall(id, args_new, sub_con_in_con(depth, sub, result_ty), mode),
                span,
            )
        }
    }
}

fn sub_con_in_pat(depth: usize, sub: &LocatedConstructor, pat: LocatedPattern) -> LocatedPattern {
    let span = pat.span.clone();
    let node = match pat.node {
        Pattern::Var(x, ty) => Pattern::Var(x, sub_con_in_con(depth, sub, ty)),
        Pattern::Prim(p) => Pattern::Prim(p),
        Pattern::Constructor(dk, pc, cs, sub_pat) => {
            let cs_new = cs
                .into_iter()
                .map(|c| sub_con_in_con(depth, sub, c))
                .collect();
            let sub_pat_new = sub_pat.map(|p| Box::new(sub_con_in_pat(depth, sub, *p)));
            Pattern::Constructor(dk, pc, cs_new, sub_pat_new)
        }
        Pattern::Record(fields) => {
            let fields_new = fields
                .into_iter()
                .map(|(name, p, ty)| {
                    (
                        name,
                        sub_con_in_pat(depth, sub, p),
                        sub_con_in_con(depth, sub, ty),
                    )
                })
                .collect();
            Pattern::Record(fields_new)
        }
    };
    Located::new(node, span)
}

// ---------------------------------------------------------------------------
// is_open: check for free CRel variables
// ---------------------------------------------------------------------------

/// Returns `true` if the constructor has any free `CRel` variable (i.e. any
/// `Constructor::Rel(i)` with `i >= depth`, starting with `depth = 0`).
pub fn is_open(c: &LocatedConstructor) -> bool {
    is_open_at(c, 0)
}

fn is_open_at(c: &LocatedConstructor, depth: usize) -> bool {
    match &c.node {
        Constructor::Rel(i) => *i >= depth,
        Constructor::Named(_)
        | Constructor::Ffi(_, _)
        | Constructor::Name(_)
        | Constructor::Unit
        | Constructor::Map(_, _) => false,

        Constructor::TFun(a, b) => is_open_at(a, depth) || is_open_at(b, depth),
        Constructor::TCFun(_, _, b) => is_open_at(b, depth + 1),
        Constructor::TRecord(inner) => is_open_at(inner, depth),
        Constructor::App(f, a) => is_open_at(f, depth) || is_open_at(a, depth),
        Constructor::Abs(_, _, b) => is_open_at(b, depth + 1),
        Constructor::KAbs(_, b) => is_open_at(b, depth),
        Constructor::KApp(c, _) => is_open_at(c, depth),
        Constructor::TKFun(_, b) => is_open_at(b, depth),
        Constructor::Record(_, pairs) => pairs
            .iter()
            .any(|(n, v)| is_open_at(n, depth) || is_open_at(v, depth)),
        Constructor::Concat(a, b) => is_open_at(a, depth) || is_open_at(b, depth),
        Constructor::Tuple(cs) => cs.iter().any(|c| is_open_at(c, depth)),
        Constructor::Proj(c, _) => is_open_at(c, depth),
    }
}

// ---------------------------------------------------------------------------
// unravel_capp: peel off CApp layers to find (Named id, [c1, c2, ...])
// ---------------------------------------------------------------------------

/// Unravels `CApp(CApp(Named(f), c1), c2)` into `Some((f, [c1, c2]))`.
/// The constructor arguments are in application order (first applied first).
pub fn unravel_capp(e: &LocatedExpression) -> Option<(usize, Vec<LocatedConstructor>)> {
    fn go(e: &LocatedExpression, acc: &mut Vec<LocatedConstructor>) -> Option<usize> {
        match &e.node {
            Expression::CApp(inner, c) => {
                let n = go(inner, acc)?;
                acc.push(c.clone());
                Some(n)
            }
            Expression::Named(n) => Some(*n),
            _ => None,
        }
    }
    let mut cargs = Vec::new();
    let n = go(e, &mut cargs)?;
    Some((n, cargs))
}

// ---------------------------------------------------------------------------
// ConList — BTreeMap key for (constructor list → replacement id) maps
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct ConList(Vec<LocatedConstructor>);

impl PartialEq for ConList {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for ConList {}

impl PartialOrd for ConList {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ConList {
    fn cmp(&self, other: &Self) -> Ordering {
        let len_ord = self.0.len().cmp(&other.0.len());
        if len_ord != Ordering::Equal {
            return len_ord;
        }
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            let ord = con_util::compare(a, b);
            if ord != Ordering::Equal {
                return ord;
            }
        }
        Ordering::Equal
    }
}

// ---------------------------------------------------------------------------
// FuncInfo — what we know about a polymorphic function
// ---------------------------------------------------------------------------

/// Information stored about each polymorphic function definition.
#[derive(Clone)]
struct FuncInfo {
    /// The kinds of each outer `CAbs` binder, in order.
    kinds: Vec<LocatedKind>,
    /// The original (pre-specialization) definition group.
    /// Each entry is `(name, id, type, expr, tag)`.
    defs: Vec<(String, usize, LocatedConstructor, LocatedExpression, String)>,
    /// Map from concrete constructor argument list → replacement function id.
    replacements: BTreeMap<ConList, usize>,
}

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

struct State {
    /// Map from function id → info about that polymorphic function.
    funcs: HashMap<usize, FuncInfo>,
    /// Newly created specialization declarations accumulated during a single
    /// top-level declaration's processing (prepended before the original decl).
    new_decls: Vec<LocatedDeclaration>,
    /// Counter for freshly allocated globally-unique ids.
    next_name: usize,
}

// ---------------------------------------------------------------------------
// trim — peel TCFun/CAbs pairs while substituting cargs
// ---------------------------------------------------------------------------

/// Strips `len(cargs)` leading `TCFun`/`CAbs` binders from `(t, e)` while
/// substituting each constructor argument.  Returns `None` if the structure
/// does not match (e.g. not enough binders, or type/expr don't line up).
fn trim(
    mut t: LocatedConstructor,
    mut e: LocatedExpression,
    cargs: &[LocatedConstructor],
) -> Option<(LocatedConstructor, LocatedExpression)> {
    for carg in cargs {
        match (t.node.clone(), e.node.clone()) {
            (Constructor::TCFun(_, _, t_body), Expression::CAbs(_, _, e_body)) => {
                // The depth to substitute is (remaining cargs - 1) — but since
                // the SML uses a simple mapCon on the entire term after each
                // peel, and the depth is determined by how many binders are
                // still left to peel, we substitute at depth = cargs.len() - 1
                // *after* we have already peeled some binders.
                //
                // Actually the SML passes `length cargs` as the de Bruijn
                // level to substitute, where `cargs` shrinks as we peel.
                // At the first iteration cargs has all args; after peeling one
                // binder the remaining cargs list is used.  The substitution
                // replaces `CRel(length remaining_cargs)`.
                //
                // Let remaining = cargs from this element onwards (exclusive)
                // i.e. the ones NOT yet substituted.
                // In SML: `subConInCon (length cargs, carg) t`
                // where cargs at that point is the *tail* (cargs after this one).
                // We'll compute remaining_depth as the index into the tail.
                t = sub_con_in_con(cargs.len() - 1, carg, *t_body);
                e = sub_con_in_exp(cargs.len() - 1, carg, *e_body);
            }
            (_, _) if cargs.len() == 0 => {
                // No more to substitute — should not be reached inside loop
                break;
            }
            _ => return None,
        }
    }
    Some((t, e))
}

// ---------------------------------------------------------------------------
// trim (iterative, correct depth tracking)
// ---------------------------------------------------------------------------

/// Correct implementation: peel and substitute one binder at a time.
/// At each step the depth equals the number of remaining cargs *after* this one
/// (i.e. `remaining.len() - 1`).
fn trim_iter(
    t: LocatedConstructor,
    e: LocatedExpression,
    cargs: &[LocatedConstructor],
) -> Option<(LocatedConstructor, LocatedExpression)> {
    if cargs.is_empty() {
        return Some((t, e));
    }
    // Peel one binder
    let carg = &cargs[0];
    let remaining = &cargs[1..];
    match (t.node.clone(), e.node.clone()) {
        (Constructor::TCFun(_, _, t_body), Expression::CAbs(_, _, e_body)) => {
            // Substitute at depth = remaining.len() (the number of still-outer binders
            // after this substitution — which equals how many CRel indices from 0
            // upward are still bound by the CAbs binders we haven't peeled yet).
            //
            // SML: `subConInCon (length cargs (* == remaining.len()+1 before peel *), carg) t`
            // where `length cargs` at that call site is the length of the *remaining*
            // cargs *including* the current one, so = remaining.len() + 1.
            // But wait — SML passes `length cargs` where `cargs` is the tail after
            // taking `carg :: cargs`. Let's re-read:
            //
            //   fun trim (t, e, cargs) =
            //     case (t, e, cargs) of
            //       ((TCFun..., _), (ECAbs..., _), carg :: cargs) =>
            //         let val t = subConInCon (length cargs, carg) t
            //             val e = subConInExp (length cargs, carg) e
            //         in trim (t, e, cargs) end
            //
            // So after destructuring `carg :: cargs`, `length cargs` is the length
            // of the *tail*. In Rust that's `remaining.len()`.
            let depth = remaining.len();
            let t_new = sub_con_in_con(depth, carg, *t_body);
            let e_new = sub_con_in_exp(depth, carg, *e_body);
            trim_iter(t_new, e_new, remaining)
        }
        _ => {
            if cargs.is_empty() {
                Some((t, e))
            } else {
                None
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Irregularity check for mutual recursion
// ---------------------------------------------------------------------------

/// Returns the de Bruijn depth contribution from expression binders
/// encountered when walking *inside* the CAbs binders. We track how many
/// additional `CAbs` (type-level) binders we descend into beyond the outer
/// `nargs` ones that have been stripped.
///
/// The check: inside `deAbs(e, cargs)` (where we have stripped `nargs` outer
/// CAbs binders), a recursive call `Named(n) [c1] ... [cnargs]` is *irregular*
/// if any of the supplied constructor args is not exactly the expected
/// `CRel(nargs - pos + cn)` where `cn` counts additional CAbs binders entered
/// during the traversal and `pos` counts from 1.
fn is_irregular(
    e: &LocatedExpression,
    member_ids: &std::collections::HashSet<usize>,
    nargs: usize,
) -> bool {
    // cn = number of extra CAbs binders entered (starts at 0 for the de-abs'd body)
    is_irregular_at(e, member_ids, nargs, 0)
}

fn is_irregular_at(
    e: &LocatedExpression,
    member_ids: &std::collections::HashSet<usize>,
    nargs: usize,
    cn: usize,
) -> bool {
    match &e.node {
        Expression::CApp(_, _) => {
            // Try to unravel this as a recursive call
            if let Some((name_id, cargs)) = unravel_capp(e) {
                if member_ids.contains(&name_id) {
                    // Check each type argument
                    let n_applied = cargs.len();
                    for (pos_zero, c) in cargs.iter().enumerate() {
                        // pos is 1-indexed in SML: pos goes 1..nargs
                        // expected index: nargs - pos + cn  where pos = pos_zero + 1
                        // = nargs - (pos_zero + 1) + cn
                        let expected_idx = (nargs + cn).saturating_sub(pos_zero + 1);
                        match &c.node {
                            Constructor::Rel(i) if *i == expected_idx => {}
                            _ => return true, // irregular
                        }
                    }
                    // Also irregular if applied to more args than nargs
                    if n_applied > nargs {
                        return true;
                    }
                    // Not irregular at this call site
                    // But we still need to recurse into sub-expressions
                }
            }
            // Recurse into children
            recurse_irregular_exp(e, member_ids, nargs, cn)
        }
        Expression::CAbs(_, _, body) => {
            // Entering an extra type-level binder increases cn
            is_irregular_at(body, member_ids, nargs, cn + 1)
        }
        _ => recurse_irregular_exp(e, member_ids, nargs, cn),
    }
}

fn recurse_irregular_exp(
    e: &LocatedExpression,
    member_ids: &std::collections::HashSet<usize>,
    nargs: usize,
    cn: usize,
) -> bool {
    match &e.node {
        Expression::Prim(_) | Expression::Rel(_) | Expression::Named(_) | Expression::Ffi(_, _) => {
            false
        }

        Expression::Constructor(_, _, _, arg) => arg
            .as_ref()
            .map_or(false, |a| is_irregular_at(a, member_ids, nargs, cn)),

        Expression::FfiApp(_, _, args) => args
            .iter()
            .any(|(a, _)| is_irregular_at(a, member_ids, nargs, cn)),

        Expression::App(f, a) => {
            is_irregular_at(f, member_ids, nargs, cn) || is_irregular_at(a, member_ids, nargs, cn)
        }
        Expression::Abs(_, _, _, body) => is_irregular_at(body, member_ids, nargs, cn),
        Expression::CApp(f, _) => is_irregular_at(f, member_ids, nargs, cn),
        Expression::CAbs(_, _, body) => is_irregular_at(body, member_ids, nargs, cn + 1),
        Expression::KAbs(_, body) => is_irregular_at(body, member_ids, nargs, cn),
        Expression::KApp(f, _) => is_irregular_at(f, member_ids, nargs, cn),
        Expression::Record(fields) => fields
            .iter()
            .any(|(_, v, _)| is_irregular_at(v, member_ids, nargs, cn)),
        Expression::Field(r, _, _) => is_irregular_at(r, member_ids, nargs, cn),
        Expression::Concat(le, _, re, _) => {
            is_irregular_at(le, member_ids, nargs, cn) || is_irregular_at(re, member_ids, nargs, cn)
        }
        Expression::Cut(r, _, _) => is_irregular_at(r, member_ids, nargs, cn),
        Expression::CutMulti(r, _, _) => is_irregular_at(r, member_ids, nargs, cn),
        Expression::Case(disc, arms, _) => {
            if is_irregular_at(disc, member_ids, nargs, cn) {
                return true;
            }
            arms.iter()
                .any(|(_, arm_e)| is_irregular_at(arm_e, member_ids, nargs, cn))
        }
        Expression::Write(inner) => is_irregular_at(inner, member_ids, nargs, cn),
        Expression::Closure(_, env) => env
            .iter()
            .any(|env_e| is_irregular_at(env_e, member_ids, nargs, cn)),
        Expression::Let(_, _, e1, e2) => {
            is_irregular_at(e1, member_ids, nargs, cn) || is_irregular_at(e2, member_ids, nargs, cn)
        }
        Expression::ServerCall(_, args, _, _) => args
            .iter()
            .any(|a| is_irregular_at(a, member_ids, nargs, cn)),
    }
}

// ---------------------------------------------------------------------------
// de_abs — strip nargs outer CAbs binders from an expression
// ---------------------------------------------------------------------------

fn de_abs(e: LocatedExpression, cargs: &[LocatedKind]) -> LocatedExpression {
    if cargs.is_empty() {
        return e;
    }
    match e.node {
        Expression::CAbs(_, _, body) => de_abs(*body, &cargs[1..]),
        _ => panic!("Unpoly: de_abs — expected CAbs"),
    }
}

fn de_abs_ref<'a>(e: &'a LocatedExpression, cargs: &[LocatedKind]) -> &'a LocatedExpression {
    if cargs.is_empty() {
        return e;
    }
    match &e.node {
        Expression::CAbs(_, _, body) => de_abs_ref(body, &cargs[1..]),
        _ => panic!("Unpoly: de_abs_ref — expected CAbs"),
    }
}

// ---------------------------------------------------------------------------
// check_kinds_match: verify that a ValRec body has the expected CAbs structure
// ---------------------------------------------------------------------------

fn has_matching_cabs(e: &LocatedExpression, cargs: &[LocatedKind]) -> bool {
    if cargs.is_empty() {
        return true;
    }
    match &e.node {
        Expression::CAbs(_, k, body) => {
            kind_util::compare(k, &cargs[0]) == Ordering::Equal
                && has_matching_cabs(body, &cargs[1..])
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// walk_exp — main expression rewriter
// ---------------------------------------------------------------------------

/// Recursively walks an expression, specializing polymorphic calls.
fn walk_exp(e: LocatedExpression, state: &mut State) -> LocatedExpression {
    let span = e.span.clone();
    match e.node {
        // The interesting case: a (possibly curried) type application
        Expression::CApp(_, _) => {
            // First, unravel the nested CApps to get (function, [cargs])
            let original = Located::new(e.node.clone(), span.clone());
            // We need to reconstruct e from parts — but we moved e.node above.
            // Let's work with the original expression.
            let e_orig = Located {
                node: original.node,
                span: span.clone(),
            };
            specialize_capp(e_orig, state)
        }

        // All other forms: recurse into children
        Expression::Prim(_) | Expression::Rel(_) | Expression::Named(_) | Expression::Ffi(_, _) => {
            Located::new(e.node, span)
        }

        Expression::Constructor(dk, pc, cs, arg) => {
            let arg_new = arg.map(|a| Box::new(walk_exp(*a, state)));
            Located::new(Expression::Constructor(dk, pc, cs, arg_new), span)
        }
        Expression::FfiApp(m, f, args) => {
            let args_new = args
                .into_iter()
                .map(|(a, c)| (walk_exp(a, state), c))
                .collect();
            Located::new(Expression::FfiApp(m, f, args_new), span)
        }
        Expression::App(func, arg) => Located::new(
            Expression::App(
                Box::new(walk_exp(*func, state)),
                Box::new(walk_exp(*arg, state)),
            ),
            span,
        ),
        Expression::Abs(x, dom, ran, body) => Located::new(
            Expression::Abs(x, dom, ran, Box::new(walk_exp(*body, state))),
            span,
        ),
        Expression::CAbs(x, k, body) => Located::new(
            Expression::CAbs(x, k, Box::new(walk_exp(*body, state))),
            span,
        ),
        Expression::KAbs(x, body) => {
            Located::new(Expression::KAbs(x, Box::new(walk_exp(*body, state))), span)
        }
        Expression::KApp(func, k) => {
            Located::new(Expression::KApp(Box::new(walk_exp(*func, state)), k), span)
        }
        Expression::Record(fields) => {
            let fields_new = fields
                .into_iter()
                .map(|(name_c, val_e, ty_c)| (name_c, walk_exp(val_e, state), ty_c))
                .collect();
            Located::new(Expression::Record(fields_new), span)
        }
        Expression::Field(record, field_c, meta) => Located::new(
            Expression::Field(Box::new(walk_exp(*record, state)), field_c, meta),
            span,
        ),
        Expression::Concat(le, lc, re, rc) => Located::new(
            Expression::Concat(
                Box::new(walk_exp(*le, state)),
                lc,
                Box::new(walk_exp(*re, state)),
                rc,
            ),
            span,
        ),
        Expression::Cut(record, field_c, meta) => Located::new(
            Expression::Cut(Box::new(walk_exp(*record, state)), field_c, meta),
            span,
        ),
        Expression::CutMulti(record, field_c, rest_meta) => Located::new(
            Expression::CutMulti(Box::new(walk_exp(*record, state)), field_c, rest_meta),
            span,
        ),
        Expression::Case(disc, arms, meta) => {
            let disc_new = Box::new(walk_exp(*disc, state));
            let arms_new = arms
                .into_iter()
                .map(|(pat, arm_e)| (pat, walk_exp(arm_e, state)))
                .collect();
            Located::new(Expression::Case(disc_new, arms_new, meta), span)
        }
        Expression::Write(inner) => {
            Located::new(Expression::Write(Box::new(walk_exp(*inner, state))), span)
        }
        Expression::Closure(id, env) => {
            let env_new = env.into_iter().map(|e| walk_exp(e, state)).collect();
            Located::new(Expression::Closure(id, env_new), span)
        }
        Expression::Let(x, ty, e1, e2) => Located::new(
            Expression::Let(
                x,
                ty,
                Box::new(walk_exp(*e1, state)),
                Box::new(walk_exp(*e2, state)),
            ),
            span,
        ),
        Expression::ServerCall(id, args, result_ty, mode) => {
            let args_new = args.into_iter().map(|a| walk_exp(a, state)).collect();
            Located::new(Expression::ServerCall(id, args_new, result_ty, mode), span)
        }
    }
}

/// Handle the `ECApp` case: try to specialize a polymorphic call.
fn specialize_capp(e: LocatedExpression, state: &mut State) -> LocatedExpression {
    let span = e.span.clone();

    // Unravel the nested CApp spine
    let (func_id, cargs) = match unravel_capp(&e) {
        None => {
            // Not a plain Named application — still need to walk children
            return walk_capp_children(e, state);
        }
        Some(x) => x,
    };

    // If any constructor arg is open (has free CRel vars), skip specialization
    if cargs.iter().any(is_open) {
        return walk_capp_children(e, state);
    }

    // Look up the function in our registry
    let func_info = match state.funcs.get(&func_id) {
        None => return walk_capp_children(e, state),
        Some(fi) => fi.clone(),
    };

    // Reduce each constructor argument
    let cargs: Vec<LocatedConstructor> = cargs.into_iter().map(reduce_con).collect();
    let key = ConList(cargs.clone());

    // Check if we already have a specialization for this constructor list
    if let Some(&existing_id) = func_info.replacements.get(&key) {
        return Located::new(Expression::Named(existing_id), span);
    }

    // Allocate fresh ids for each member of the definition group
    let old_defs = func_info.defs.clone();
    let kinds = func_info.kinds.clone();

    // We need to find which new id corresponds to func_id
    let mut this_new_id: usize = 0;
    let mut next = state.next_name;

    // Map old_id → new_id for this specialization
    let id_map: Vec<(usize, usize)> = old_defs
        .iter()
        .map(|(_, old_id, _, _, _)| {
            let new_id = next;
            next += 1;
            (*old_id, new_id)
        })
        .collect();

    for &(old_id, new_id) in &id_map {
        if old_id == func_id {
            this_new_id = new_id;
        }
    }

    state.next_name = next;

    // Check: we need at least some cargs to specialize, and can't apply more
    // than we have kinds for
    if cargs.len() > kinds.len() {
        return walk_capp_children(
            Located::new(Expression::Named(func_id), span.clone()),
            state,
        );
    }

    // Also check that there are some cargs to specialize (otherwise nothing to do)
    if cargs.is_empty() {
        return walk_capp_children(
            Located::new(Expression::Named(func_id), span.clone()),
            state,
        );
    }

    // Update the replacements map for each old definition member
    for &(old_id, new_id) in &id_map {
        let replacements = state
            .funcs
            .get(&old_id)
            .map(|fi| fi.replacements.clone())
            .unwrap_or_default();
        // Insert the new specialization mapping
        let mut new_replacements = replacements;
        new_replacements.insert(key.clone(), new_id);

        // Update the funcs map with the new replacement
        if let Some(fi) = state.funcs.get_mut(&old_id) {
            fi.replacements = new_replacements;
        }
    }

    // Specialize each definition: trim the type and body
    let mut specialized: Vec<(
        String,
        usize,
        Option<(LocatedConstructor, LocatedExpression)>,
        String,
    )> = Vec::new();

    for ((_, old_id, ty, expr, tag), (_, new_id)) in old_defs.iter().zip(id_map.iter()) {
        let spec = trim_iter(ty.clone(), expr.clone(), &cargs);
        specialized.push((
            format!(
                "{}_unpoly",
                old_defs
                    .iter()
                    .find(|(_, id, _, _, _)| id == old_id)
                    .map(|(nm, _, _, _, _)| nm.as_str())
                    .unwrap_or("")
            ),
            *new_id,
            spec,
            tag.clone(),
        ));
    }

    // If any specialization failed, bail out
    if specialized.iter().any(|(_, _, s, _)| s.is_none()) {
        return walk_capp_children(
            Located::new(Expression::Named(func_id), span.clone()),
            state,
        );
    }

    // Build the specialized ValRec group
    let remaining_kinds: Vec<LocatedKind> = kinds.into_iter().skip(cargs.len()).collect();

    // Register each specialized function so it can itself be further specialized
    let vis_prime: Vec<(String, usize, LocatedConstructor, LocatedExpression, String)> =
        specialized
            .iter()
            .filter_map(|(nm, new_id, spec, tag)| {
                spec.as_ref()
                    .map(|(t, ex)| (nm.clone(), *new_id, t.clone(), ex.clone(), tag.clone()))
            })
            .collect();

    // Register each specialized function in the funcs map
    for (_, new_id, _, _) in &specialized {
        state.funcs.insert(
            *new_id,
            FuncInfo {
                kinds: remaining_kinds.clone(),
                defs: vis_prime.clone(),
                replacements: BTreeMap::new(),
            },
        );
    }

    // Walk the bodies of the specialized functions (recursively applying unpoly)
    let walked_vis: Vec<(String, usize, LocatedConstructor, LocatedExpression, String)> = vis_prime
        .into_iter()
        .map(|(nm, id, ty, expr, tag)| {
            let expr_walked = walk_exp(expr, state);
            (nm, id, ty, expr_walked, tag)
        })
        .collect();

    // Emit a new ValRec declaration
    let new_decl = Located::new(Declaration::ValRec(walked_vis), Span::dummy());
    state.new_decls.push(new_decl);

    Located::new(Expression::Named(this_new_id), span)
}

/// Walk the children of a CApp expression without specializing.
fn walk_capp_children(e: LocatedExpression, state: &mut State) -> LocatedExpression {
    let span = e.span.clone();
    match e.node {
        Expression::CApp(func, c) => {
            Located::new(Expression::CApp(Box::new(walk_exp(*func, state)), c), span)
        }
        other => Located::new(other, span),
    }
}

// ---------------------------------------------------------------------------
// walk_decl — register polymorphic functions into the state
// ---------------------------------------------------------------------------

/// Process a top-level declaration: registers `Val` and `ValRec` definitions
/// as polymorphic function candidates, then walks expressions.
fn walk_decl(d: LocatedDeclaration, state: &mut State) -> LocatedDeclaration {
    let span = d.span.clone();
    match d.node {
        Declaration::Val(name, id, ty, expr, tag) => {
            // Unravel leading CAbs binders to find the kind list
            let kinds = collect_cabs_kinds(&expr);

            state.funcs.insert(
                id,
                FuncInfo {
                    kinds,
                    defs: vec![(name.clone(), id, ty.clone(), expr.clone(), tag.clone())],
                    replacements: BTreeMap::new(),
                },
            );

            // Walk the expression
            let expr_walked = walk_exp(expr, state);
            Located::new(Declaration::Val(name, id, ty, expr_walked, tag), span)
        }

        Declaration::ValRec(vis) => {
            if vis.is_empty() {
                return Located::new(Declaration::ValRec(vis), span);
            }

            // Unravel the kind list from the first member
            let kinds = collect_cabs_kinds(&vis[0].3);

            // Check that all members have the same kind structure
            let all_match = vis
                .iter()
                .all(|(_, _, _, expr, _)| has_matching_cabs(expr, &kinds));

            if !all_match {
                // Walk expressions without registering
                let vis_walked = vis
                    .into_iter()
                    .map(|(nm, id, ty, expr, tag)| (nm, id, ty, walk_exp(expr, state), tag))
                    .collect();
                return Located::new(Declaration::ValRec(vis_walked), span);
            }

            // Collect member ids for irregularity check
            let member_ids: std::collections::HashSet<usize> =
                vis.iter().map(|(_, id, _, _, _)| *id).collect();
            let nargs = kinds.len();

            // Check for irregular polymorphic recursion
            let any_irregular = vis.iter().any(|(_, _, _, expr, _)| {
                let body = de_abs_ref(expr, &kinds);
                is_irregular(body, &member_ids, nargs)
            });

            if any_irregular {
                // Walk without registering
                let vis_walked = vis
                    .into_iter()
                    .map(|(nm, id, ty, expr, tag)| (nm, id, ty, walk_exp(expr, state), tag))
                    .collect();
                return Located::new(Declaration::ValRec(vis_walked), span);
            }

            // Register each member
            for (_, id, _, _, _) in &vis {
                state.funcs.insert(
                    *id,
                    FuncInfo {
                        kinds: kinds.clone(),
                        defs: vis.clone(),
                        replacements: BTreeMap::new(),
                    },
                );
            }

            // Walk expressions
            let vis_walked = vis
                .into_iter()
                .map(|(nm, id, ty, expr, tag)| (nm, id, ty, walk_exp(expr, state), tag))
                .collect();
            Located::new(Declaration::ValRec(vis_walked), span)
        }

        // All other declarations: no polymorphic registration needed,
        // just return as-is (expressions inside are not walked here — the
        // SML polyDecl only touches kinds, cons, exps and decls but the decl
        // callback only fires on Val/ValRec).
        other => Located::new(other, span),
    }
}

/// Collect the sequence of outer `CAbs` binder kinds from an expression.
fn collect_cabs_kinds(e: &LocatedExpression) -> Vec<LocatedKind> {
    let mut kinds = Vec::new();
    let mut cur = e;
    loop {
        match &cur.node {
            Expression::CAbs(_, k, body) => {
                kinds.push(*k.clone());
                cur = body;
            }
            _ => break,
        }
    }
    kinds
}

// ---------------------------------------------------------------------------
// unpoly — top-level entry point
// ---------------------------------------------------------------------------

/// Specialise polymorphic Core functions by substituting closed constructor
/// arguments at each call site.
///
/// Mirrors `Unpoly.unpoly`.
pub fn unpoly(file: File) -> File {
    let next_name = file_util::max_name(&file) + 1;
    let mut state = State {
        funcs: HashMap::new(),
        new_decls: Vec::new(),
        next_name,
    };

    let mut result: Vec<LocatedDeclaration> = Vec::new();

    for decl in file {
        // Reset new_decls before each top-level declaration
        state.new_decls.clear();

        let processed = walk_decl(decl, &mut state);

        // Prepend any specializations emitted during this declaration
        // (SML: `rev (d :: #decls st)` where new decls are pushed front-to-back)
        let mut new_decls = std::mem::take(&mut state.new_decls);
        result.append(&mut new_decls);
        result.push(processed);
    }

    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::{Located, Span};

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn mk_con(c: Constructor) -> LocatedConstructor {
        Located::dummy(c)
    }

    fn mk_exp(e: Expression) -> LocatedExpression {
        Located::dummy(e)
    }

    fn mk_kind(k: Kind) -> LocatedKind {
        Located::dummy(k)
    }

    // -----------------------------------------------------------------------
    // is_open tests
    // -----------------------------------------------------------------------

    #[test]
    fn is_open_rel_at_depth_0() {
        // CRel(0) with no enclosing binders => open
        let c = mk_con(Constructor::Rel(0));
        assert!(is_open(&c));
    }

    #[test]
    fn is_open_rel_inside_tcfun() {
        // TCFun("a", k, CRel(0)) => CRel(0) is bound by the TCFun => closed
        let k = mk_kind(Kind::Type);
        let body = mk_con(Constructor::Rel(0));
        let c = mk_con(Constructor::TCFun("a".into(), Box::new(k), Box::new(body)));
        assert!(!is_open(&c));
    }

    #[test]
    fn is_open_named_is_closed() {
        let c = mk_con(Constructor::Named(42));
        assert!(!is_open(&c));
    }

    #[test]
    fn is_open_rel_escapes_tcfun() {
        // TCFun("a", k, CRel(1)) => CRel(1) is free (only CRel(0) is bound)
        let k = mk_kind(Kind::Type);
        let body = mk_con(Constructor::Rel(1));
        let c = mk_con(Constructor::TCFun("a".into(), Box::new(k), Box::new(body)));
        assert!(is_open(&c));
    }

    #[test]
    fn is_open_tfun_both_closed() {
        let a = mk_con(Constructor::Named(1));
        let b = mk_con(Constructor::Named(2));
        let c = mk_con(Constructor::TFun(Box::new(a), Box::new(b)));
        assert!(!is_open(&c));
    }

    // -----------------------------------------------------------------------
    // sub_con_in_con tests
    // -----------------------------------------------------------------------

    #[test]
    fn sub_con_replaces_matching_rel() {
        let sub = mk_con(Constructor::Named(99));
        let body = mk_con(Constructor::Rel(0));
        let result = sub_con_in_con(0, &sub, body);
        assert!(matches!(result.node, Constructor::Named(99)));
    }

    #[test]
    fn sub_con_leaves_nonmatching_rel() {
        let sub = mk_con(Constructor::Named(99));
        let body = mk_con(Constructor::Rel(1));
        let result = sub_con_in_con(0, &sub, body);
        assert!(matches!(result.node, Constructor::Rel(1)));
    }

    #[test]
    fn sub_con_in_tfun() {
        let sub = mk_con(Constructor::Named(99));
        let a = mk_con(Constructor::Rel(0));
        let b = mk_con(Constructor::Named(5));
        let body = mk_con(Constructor::TFun(Box::new(a), Box::new(b)));
        let result = sub_con_in_con(0, &sub, body);
        match result.node {
            Constructor::TFun(left, right) => {
                assert!(matches!(left.node, Constructor::Named(99)));
                assert!(matches!(right.node, Constructor::Named(5)));
            }
            _ => panic!("Expected TFun"),
        }
    }

    // -----------------------------------------------------------------------
    // unravel_capp tests
    // -----------------------------------------------------------------------

    #[test]
    fn unravel_simple_named() {
        let e = mk_exp(Expression::Named(10));
        let result = unravel_capp(&e);
        assert!(result.is_some());
        let (id, cargs) = result.unwrap();
        assert_eq!(id, 10);
        assert!(cargs.is_empty());
    }

    #[test]
    fn unravel_capp_fails_on_abs() {
        let body = mk_exp(Expression::Named(1));
        let k = mk_kind(Kind::Type);
        let e = mk_exp(Expression::CAbs("a".into(), Box::new(k), Box::new(body)));
        // CAbs is not Named, so unravel returns None for its head
        // Actually CApp wrapping it would fail
        let result = unravel_capp(&e);
        assert!(result.is_none());
    }

    #[test]
    fn unravel_capp_single_arg() {
        let named = mk_exp(Expression::Named(7));
        let c = mk_con(Constructor::Named(42));
        let e = mk_exp(Expression::CApp(Box::new(named), c.clone()));
        let result = unravel_capp(&e);
        assert!(result.is_some());
        let (id, cargs) = result.unwrap();
        assert_eq!(id, 7);
        assert_eq!(cargs.len(), 1);
        assert!(matches!(cargs[0].node, Constructor::Named(42)));
    }

    #[test]
    fn unravel_capp_two_args() {
        let named = mk_exp(Expression::Named(3));
        let c1 = mk_con(Constructor::Named(10));
        let c2 = mk_con(Constructor::Named(20));
        let e1 = mk_exp(Expression::CApp(Box::new(named), c1));
        let e = mk_exp(Expression::CApp(Box::new(e1), c2));
        let (id, cargs) = unravel_capp(&e).unwrap();
        assert_eq!(id, 3);
        assert_eq!(cargs.len(), 2);
        assert!(matches!(cargs[0].node, Constructor::Named(10)));
        assert!(matches!(cargs[1].node, Constructor::Named(20)));
    }

    // -----------------------------------------------------------------------
    // trim_iter tests
    // -----------------------------------------------------------------------

    #[test]
    fn trim_empty_cargs_returns_original() {
        let _k = mk_kind(Kind::Type);
        let t = mk_con(Constructor::Named(1));
        let e = mk_exp(Expression::Named(1));
        let result = trim_iter(t.clone(), e.clone(), &[]);
        assert!(result.is_some());
        let (rt, re) = result.unwrap();
        assert!(matches!(rt.node, Constructor::Named(1)));
        assert!(matches!(re.node, Expression::Named(1)));
    }

    #[test]
    fn trim_peels_one_binder() {
        // t = TCFun("a", Type, Named(1))  — the body after stripping is Named(1)
        // e = CAbs("a", Type, Named(2))
        let k = mk_kind(Kind::Type);
        let t_body = mk_con(Constructor::Named(1));
        let e_body = mk_exp(Expression::Named(2));
        let t = mk_con(Constructor::TCFun(
            "a".into(),
            Box::new(k.clone()),
            Box::new(t_body),
        ));
        let e = mk_exp(Expression::CAbs(
            "a".into(),
            Box::new(k.clone()),
            Box::new(e_body),
        ));

        let carg = mk_con(Constructor::Named(99));
        let result = trim_iter(t, e, &[carg]);
        assert!(result.is_some());
        let (rt, re) = result.unwrap();
        // Body was Named(1)/Named(2) with no Rel references, so substitution is no-op
        assert!(matches!(rt.node, Constructor::Named(1)));
        assert!(matches!(re.node, Expression::Named(2)));
    }

    #[test]
    fn trim_substitutes_rel() {
        // t = TCFun("a", Type, Rel(0))   — body references the binder
        // e = CAbs("a", Type, Named(5))
        // cargs = [Named(42)]
        // After trim: t = Named(42), e = Named(5)
        let k = mk_kind(Kind::Type);
        let t_body = mk_con(Constructor::Rel(0));
        let e_body = mk_exp(Expression::Named(5));
        let t = mk_con(Constructor::TCFun(
            "a".into(),
            Box::new(k.clone()),
            Box::new(t_body),
        ));
        let e = mk_exp(Expression::CAbs("a".into(), Box::new(k), Box::new(e_body)));

        let carg = mk_con(Constructor::Named(42));
        let result = trim_iter(t, e, &[carg]);
        assert!(result.is_some());
        let (rt, _re) = result.unwrap();
        assert!(matches!(rt.node, Constructor::Named(42)));
    }

    #[test]
    fn trim_fails_on_mismatch() {
        // t = Named(1) — not a TCFun, can't peel
        // e = CAbs("a", Type, Named(2))
        // cargs = [Named(99)]
        let k = mk_kind(Kind::Type);
        let t = mk_con(Constructor::Named(1));
        let e_body = mk_exp(Expression::Named(2));
        let e = mk_exp(Expression::CAbs("a".into(), Box::new(k), Box::new(e_body)));

        let carg = mk_con(Constructor::Named(99));
        let result = trim_iter(t, e, &[carg]);
        assert!(result.is_none());
    }

    // -----------------------------------------------------------------------
    // con_list ordering
    // -----------------------------------------------------------------------

    #[test]
    fn con_list_ordering_by_length() {
        let a = ConList(vec![mk_con(Constructor::Named(1))]);
        let b = ConList(vec![
            mk_con(Constructor::Named(1)),
            mk_con(Constructor::Named(2)),
        ]);
        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn con_list_ordering_same_length_by_content() {
        let a = ConList(vec![mk_con(Constructor::Named(1))]);
        let b = ConList(vec![mk_con(Constructor::Named(2))]);
        assert_eq!(a.cmp(&b), Ordering::Less);
    }

    #[test]
    fn con_list_equal() {
        let a = ConList(vec![mk_con(Constructor::Named(5))]);
        let b = ConList(vec![mk_con(Constructor::Named(5))]);
        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    // -----------------------------------------------------------------------
    // collect_cabs_kinds
    // -----------------------------------------------------------------------

    #[test]
    fn collect_cabs_kinds_none() {
        let e = mk_exp(Expression::Named(1));
        let kinds = collect_cabs_kinds(&e);
        assert!(kinds.is_empty());
    }

    #[test]
    fn collect_cabs_kinds_two() {
        let k1 = mk_kind(Kind::Type);
        let k2 = mk_kind(Kind::Name);
        let inner = mk_exp(Expression::Named(1));
        let e2 = mk_exp(Expression::CAbs(
            "b".into(),
            Box::new(k2.clone()),
            Box::new(inner),
        ));
        let e = mk_exp(Expression::CAbs(
            "a".into(),
            Box::new(k1.clone()),
            Box::new(e2),
        ));
        let kinds = collect_cabs_kinds(&e);
        assert_eq!(kinds.len(), 2);
        assert!(matches!(kinds[0].node, Kind::Type));
        assert!(matches!(kinds[1].node, Kind::Name));
    }

    // -----------------------------------------------------------------------
    // unpoly end-to-end: non-polymorphic file is unchanged
    // -----------------------------------------------------------------------

    #[test]
    fn unpoly_passthrough_non_poly() {
        // A file with a single non-polymorphic Val: val f : int = 42
        let _k = mk_kind(Kind::Type);
        let ty = mk_con(Constructor::Named(0));
        let expr = mk_exp(Expression::Named(1));
        let decl = Located::dummy(Declaration::Val("f".into(), 1, ty, expr, "".into()));
        let file = vec![decl];
        let result = unpoly(file);
        assert_eq!(result.len(), 1);
        assert!(matches!(result[0].node, Declaration::Val(_, 1, _, _, _)));
    }

    // -----------------------------------------------------------------------
    // unpoly: polymorphic function that is never called is unchanged
    // -----------------------------------------------------------------------

    #[test]
    fn unpoly_poly_uncalled() {
        // val id : ∀a. a → a = Λa. λx:a. x
        // (simplified as: CAbs("a", Type, Named(99)))
        // No calls to it — should produce same output
        let k = mk_kind(Kind::Type);
        let ty_body = mk_con(Constructor::TFun(
            Box::new(mk_con(Constructor::Rel(0))),
            Box::new(mk_con(Constructor::Rel(0))),
        ));
        let ty = mk_con(Constructor::TCFun(
            "a".into(),
            Box::new(k.clone()),
            Box::new(ty_body),
        ));
        let expr_body = mk_exp(Expression::Named(99));
        let expr = mk_exp(Expression::CAbs(
            "a".into(),
            Box::new(k),
            Box::new(expr_body),
        ));
        let decl = Located::dummy(Declaration::Val("id".into(), 5, ty, expr, "".into()));
        let file = vec![decl];
        let result = unpoly(file);
        // No specializations should be emitted
        assert_eq!(result.len(), 1);
    }
}
