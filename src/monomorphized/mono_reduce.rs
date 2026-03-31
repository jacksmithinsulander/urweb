//! Algebraic reduction and inlining for the Mono IR.
//!
//! Ports `mono_reduce.sml`. Performs:
//! - Beta reduction (App(Abs, arg) → substitution)
//! - Let inlining (when safe: pure, used once, or record projection)
//! - Pattern matching case reduction
//! - Let commutation / floating
//! - String constant folding (Strcat of literals)
//! - SignalBind(SignalReturn(e1), e2) → App(e2, e1)
//! - Record field projection through Lets (yankLets)
//!
//! The pass runs in a fixpoint loop: if a "yanked case" optimisation fires
//! (converting a case-returning-function into a function-returning-case),
//! the whole file is reduced again.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};

use crate::error_types::{Located, Span};
use crate::monomorphized::{
    environment::{lift_exp_in_exp, multi_lift, pat_binds_n, sub_exp_in_exp, Env},
    CaseMeta, Decl, Exp, File, JavaScriptMode, LocDecl, LocExp, LocPat, LocTyp, Pat, PatCon,
    QueryMeta, Typ,
};
use crate::primitives::{Prim, StringMode};
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// Global full-mode flag (mirrors SML `val fullMode = ref false`)
// ---------------------------------------------------------------------------

/// When true, inline more aggressively (set by mono_inline before calling reduce).
pub static FULL_MODE: AtomicBool = AtomicBool::new(false);

// ---------------------------------------------------------------------------
// Events (for summarize / effect ordering analysis)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Event {
    WritePage,
    ReadDb,
    WriteDb,
    ReadCookie,
    UseRel,
    Unsure,
    Abort,
}

// ---------------------------------------------------------------------------
// MatchResult
// ---------------------------------------------------------------------------

#[derive(Debug)]
enum MatchResult {
    Yes(Vec<(String, LocTyp, LocExp)>),
    No,
    Maybe,
}

// ---------------------------------------------------------------------------
// ReduceCtx — shared context for a single reduce pass
// ---------------------------------------------------------------------------

struct ReduceCtx {
    /// Datatype IDs whose constructors carry types that are "simply impure"
    /// (i.e., they contain Typ::Fun or reference another impure datatype).
    timpures: HashSet<usize>,
    /// Named val IDs that are simply-impure.
    impures: HashSet<usize>,
    /// Use count for each named val.
    uses: HashMap<usize, usize>,
    /// Set to true when the "yanked case" optimisation fires.
    yanked_case: Cell<bool>,
    /// Full-mode flag (copied from FULL_MODE at pass start).
    full_mode: bool,
}

// ---------------------------------------------------------------------------
// simple_type_impure
// ---------------------------------------------------------------------------

/// Returns true if `t` contains a Fun type or a Datatype whose ID is in `timpures`.
fn simple_type_impure(t: &LocTyp, timpures: &HashSet<usize>) -> bool {
    use crate::monomorphized::utilities::typ;
    typ::exists(t, &|node| match node {
        Typ::Fun(..) => true,
        Typ::Datatype(n, _) => timpures.contains(n),
        _ => false,
    })
}

// ---------------------------------------------------------------------------
// simple_impure — conservative check (mirrors SML simpleImpure)
// ---------------------------------------------------------------------------

/// Conservative impurity check used in the analysis pass.
///
/// `is_global=true` means we treat EApp as pure (we're analysing top-level
/// definitions where unapplied calls are not yet impure).
fn simple_impure(
    is_global: bool,
    timpures: &HashSet<usize>,
    impures: &HashSet<usize>,
    env: &Env,
    e: &LocExp,
    settings: &Settings,
) -> bool {
    simple_impure_inner(is_global, timpures, impures, env, e, settings)
}

fn simple_impure_inner(
    is_global: bool,
    timpures: &HashSet<usize>,
    impures: &HashSet<usize>,
    env: &Env,
    e: &LocExp,
    settings: &Settings,
) -> bool {
    // Helper to recurse with current env
    let recurse =
        |inner: &LocExp| simple_impure_inner(is_global, timpures, impures, env, inner, settings);
    let recurse2 = |a: &LocExp, b: &LocExp| recurse(a) || recurse(b);

    match &e.node {
        // Immediately impure effects
        Exp::Write(_)
        | Exp::Query(_)
        | Exp::Dml(_, _)
        | Exp::Nextval(_)
        | Exp::Setval(_, _)
        | Exp::ServerCall(_, _, _, _)
        | Exp::Recv(_, _)
        | Exp::Sleep(_)
        | Exp::Spawn(_) => true,

        Exp::FfiApp(m, x, _) => {
            let ffi = (m.clone(), x.clone());
            settings.is_effectful(&ffi) || settings.is_benign_effectful(&ffi)
        }

        Exp::Named(n) => impures.contains(n),

        Exp::Rel(n) => {
            if let Ok((_, t, _)) = env.lookup_rel(*n) {
                simple_type_impure(t, timpures)
            } else {
                false
            }
        }

        Exp::App(_, _) => !is_global,

        // Binder-extending cases
        Exp::Abs(x, dom, _, body) => {
            let env2 = env.push_rel(x, dom.clone());
            simple_impure_inner(is_global, timpures, impures, &env2, body, settings)
        }
        Exp::Let(x, t, e1, e2) => {
            recurse(e1)
                || simple_impure_inner(
                    is_global,
                    timpures,
                    impures,
                    &env.push_rel(x, t.clone()),
                    e2,
                    settings,
                )
        }
        Exp::Case(disc, arms, _) => {
            recurse(disc)
                || arms.iter().any(|(p, arm_e)| {
                    simple_impure_inner(
                        is_global,
                        timpures,
                        impures,
                        &env.pat_binds(p),
                        arm_e,
                        settings,
                    )
                })
        }
        // Two-subexpression cases
        Exp::Seq(e1, e2) | Exp::Strcat(e1, e2) | Exp::SignalBind(e1, e2) => recurse2(e1, e2),
        Exp::Binop(_, _, e1, e2) => recurse2(e1, e2),

        // Single-subexpression cases
        Exp::Unop(_, inner)
        | Exp::Field(inner, _)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::JavaScript(_, inner)
        | Exp::Uurlify(inner, _, _)
        | Exp::Error(inner, _)
        | Exp::Redirect(inner, _) => recurse(inner),

        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => recurse(inner),

        Exp::Record(xets) => xets.iter().any(|(_, re, _)| recurse(re)),
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => blob.as_ref().is_some_and(|b| recurse(b)) || recurse(mime_type),
        Exp::Closure(_, envs) => envs.iter().any(recurse),

        // Leaves always pure
        Exp::Prim(_) | Exp::Ffi(_, _) | Exp::Con(_, _, None) | Exp::None(_) => false,
    }
}

// ---------------------------------------------------------------------------
// impure_rough — structural impurity check (mirrors SML `impure`)
// ---------------------------------------------------------------------------

/// Structural impurity check that requires only the expression itself
/// (no environment needed).
fn impure_rough(e: &LocExp) -> bool {
    match &e.node {
        // Immediately impure
        Exp::Write(_)
        | Exp::Query(_)
        | Exp::Dml(_, _)
        | Exp::Nextval(_)
        | Exp::Setval(_, _)
        | Exp::Error(_, _)
        | Exp::ServerCall(_, _, _, _)
        | Exp::Recv(_, _)
        | Exp::Sleep(_)
        | Exp::Spawn(_) => true,

        // FfiApp is conservatively impure (we don't have settings here)
        Exp::FfiApp(_, _, _) => true,

        // App(Ffi, _) is pure (FFI function applied); App(anything else, _) is impure
        Exp::App(f, _) => !matches!(&f.node, Exp::Ffi(_, _)),

        // Definitionally pure
        Exp::Abs(_, _, _, _)
        | Exp::Prim(_)
        | Exp::Rel(_)
        | Exp::Named(_)
        | Exp::Ffi(_, _)
        | Exp::None(_) => false,

        // Propagate through single subexpressions
        Exp::Uurlify(inner, _, _)
        | Exp::Unop(_, inner)
        | Exp::Field(inner, _)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Redirect(inner, _)
        | Exp::JavaScript(_, inner) => impure_rough(inner),

        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => impure_rough(inner),
        Exp::Con(_, _, None) => false,

        // Propagate through two subexpressions
        Exp::Strcat(e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::Let(_, _, e1, e2)
        | Exp::SignalBind(e1, e2)
        | Exp::Binop(_, _, e1, e2) => impure_rough(e1) || impure_rough(e2),

        Exp::Record(xets) => xets.iter().any(|(_, re, _)| impure_rough(re)),
        Exp::Case(disc, arms, _) => {
            impure_rough(disc) || arms.iter().any(|(_, ae)| impure_rough(ae))
        }
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => blob.as_ref().is_some_and(|b| impure_rough(b)) || impure_rough(mime_type),
        Exp::Closure(_, envs) => envs.iter().any(impure_rough),
    }
}

// ---------------------------------------------------------------------------
// impure_ctx — env-aware impurity check (refined, mirrors simpleImpure false)
// ---------------------------------------------------------------------------

/// Env-aware impurity: uses the rel environment to check types of Rel vars,
/// and the impures set for Named vals.
fn impure_ctx(env: &Env, e: &LocExp, ctx: &ReduceCtx, settings: &Settings) -> bool {
    simple_impure(false, &ctx.timpures, &ctx.impures, env, e, settings)
        && impure_rough(e)
        && !summarize(-1, e).is_empty()
}

// ---------------------------------------------------------------------------
// summarize — build the event list for an expression
// ---------------------------------------------------------------------------

/// Build the ordered list of effects of `e`.
///
/// `d` is the depth at which we consider UseRel events (Rel(d)).
/// Pass `d = 0` to track Rel(0) as UseRel.
/// Pass `d = -1` to never emit UseRel (i.e., summarize the whole expression
/// ignoring any particular variable).
fn summarize(d: i64, e: &LocExp) -> Vec<Event> {
    let mut events = Vec::new();
    summarize_inner(d, e, &mut events);
    events
}

fn summarize_inner(d: i64, e: &LocExp, out: &mut Vec<Event>) {
    match &e.node {
        Exp::Write(inner) => {
            summarize_inner(d, inner, out);
            out.push(Event::WritePage);
        }
        Exp::Prim(_) | Exp::Ffi(_, _) | Exp::Named(_) | Exp::None(_) | Exp::Abs(_, _, _, _) => {}
        Exp::Rel(n) => {
            if d >= 0 && *n == d as usize {
                out.push(Event::UseRel);
            }
        }
        Exp::FfiApp(_, _, args) => {
            // Args first (left-to-right evaluation)
            for (ae, _) in args {
                summarize_inner(d, ae, out);
            }
            // Then the call itself
            out.push(Event::Unsure);
        }
        Exp::App(f, arg) => {
            summarize_inner(d, f, out);
            summarize_inner(d, arg, out);
            out.push(Event::Unsure);
        }
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => {
            summarize_inner(d, inner, out);
        }
        Exp::Con(_, _, None) => {}
        Exp::Unop(_, inner) => summarize_inner(d, inner, out),
        Exp::Binop(_, _, e1, e2) => {
            summarize_inner(d, e1, out);
            summarize_inner(d, e2, out);
        }
        Exp::Record(xets) => {
            for (_, re, _) in xets {
                summarize_inner(d, re, out);
            }
        }
        Exp::Field(inner, _) => summarize_inner(d, inner, out),
        Exp::Case(disc, arms, _) => {
            summarize_inner(d, disc, out);
            // Cases are alternatives; collect the union (conservative approximation)
            for (_, ae) in arms {
                summarize_inner(d, ae, out);
            }
        }
        Exp::Strcat(e1, e2) => {
            summarize_inner(d, e1, out);
            summarize_inner(d, e2, out);
        }
        Exp::Error(_, _) => out.push(Event::Abort),
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            if let Some(b) = blob {
                summarize_inner(d, b, out);
            }
            summarize_inner(d, mime_type, out);
        }
        Exp::Redirect(inner, _) => summarize_inner(d, inner, out),
        Exp::Seq(e1, e2) => {
            summarize_inner(d, e1, out);
            summarize_inner(d, e2, out);
        }
        Exp::Let(_, _, e1, e2) => {
            summarize_inner(d, e1, out);
            let d2 = if d >= 0 { d + 1 } else { -1 };
            summarize_inner(d2, e2, out);
        }
        Exp::Closure(_, envs) => {
            for ce in envs {
                summarize_inner(d, ce, out);
            }
        }
        Exp::Query(qm) => {
            summarize_inner(d, &qm.query, out);
            out.push(Event::ReadDb);
            let d2 = if d >= 0 { d + 2 } else { -1 };
            summarize_inner(d2, &qm.body, out);
            summarize_inner(d, &qm.initial, out);
        }
        Exp::Dml(inner, _) => {
            summarize_inner(d, inner, out);
            out.push(Event::WriteDb);
        }
        Exp::Nextval(inner) => {
            summarize_inner(d, inner, out);
            out.push(Event::WriteDb);
        }
        Exp::Setval(e1, e2) => {
            summarize_inner(d, e1, out);
            summarize_inner(d, e2, out);
            out.push(Event::WriteDb);
        }
        Exp::Uurlify(inner, _, _) => summarize_inner(d, inner, out),
        Exp::JavaScript(_, inner) => summarize_inner(d, inner, out),
        Exp::SignalReturn(inner) => summarize_inner(d, inner, out),
        Exp::SignalBind(e1, e2) => {
            summarize_inner(d, e1, out);
            summarize_inner(d, e2, out);
        }
        Exp::SignalSource(inner) => summarize_inner(d, inner, out),
        Exp::ServerCall(inner, _, _, _) => {
            summarize_inner(d, inner, out);
            out.push(Event::Unsure);
        }
        Exp::Recv(inner, _) => {
            summarize_inner(d, inner, out);
            out.push(Event::Unsure);
        }
        Exp::Sleep(inner) | Exp::Spawn(inner) => {
            summarize_inner(d, inner, out);
            out.push(Event::Unsure);
        }
    }
}

// ---------------------------------------------------------------------------
// count_free — count free occurrences of Rel(target) in e
// ---------------------------------------------------------------------------

/// Count the number of free occurrences of Rel(`target`) in `e`.
///
/// When descending under binders, `target` is incremented (since the variable
/// we're tracking is now one deeper).
fn count_free(target: usize, e: &LocExp) -> usize {
    count_free_inner(target, e)
}

fn count_free_inner(target: usize, e: &LocExp) -> usize {
    match &e.node {
        Exp::Rel(n) => {
            if *n == target {
                1
            } else {
                0
            }
        }
        Exp::Abs(_, _, _, body) => count_free_inner(target + 1, body),
        Exp::Let(_, _, e1, e2) => count_free_inner(target, e1) + count_free_inner(target + 1, e2),
        Exp::Case(disc, arms, _) => {
            count_free_inner(target, disc)
                + arms
                    .iter()
                    .map(|(p, ae)| count_free_inner(target + pat_binds_n(p), ae))
                    .sum::<usize>()
        }
        Exp::Query(qm) => {
            count_free_inner(target, &qm.query)
                + count_free_inner(target + 2, &qm.body)
                + count_free_inner(target, &qm.initial)
        }
        Exp::App(f, arg) => count_free_inner(target, f) + count_free_inner(target, arg),
        Exp::Strcat(e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::Binop(_, _, e1, e2)
        | Exp::SignalBind(e1, e2)
        | Exp::Setval(e1, e2) => count_free_inner(target, e1) + count_free_inner(target, e2),
        Exp::Write(inner)
        | Exp::Unop(_, inner)
        | Exp::Field(inner, _)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Nextval(inner)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner)
        | Exp::JavaScript(_, inner)
        | Exp::Uurlify(inner, _, _)
        | Exp::Dml(inner, _)
        | Exp::Redirect(inner, _)
        | Exp::Error(inner, _)
        | Exp::ServerCall(inner, _, _, _)
        | Exp::Recv(inner, _) => count_free_inner(target, inner),
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => count_free_inner(target, inner),
        Exp::Con(_, _, None) => 0,
        Exp::FfiApp(_, _, args) => args
            .iter()
            .map(|(ae, _)| count_free_inner(target, ae))
            .sum(),
        Exp::Record(xets) => xets
            .iter()
            .map(|(_, re, _)| count_free_inner(target, re))
            .sum(),
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            blob.as_ref().map_or(0, |b| count_free_inner(target, b))
                + count_free_inner(target, mime_type)
        }
        Exp::Closure(_, envs) => envs.iter().map(|ce| count_free_inner(target, ce)).sum(),
        Exp::Prim(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::None(_) => 0,
    }
}

// ---------------------------------------------------------------------------
// free_in_abs — check if Rel(0) appears free inside any Abs or JavaScript
// ---------------------------------------------------------------------------

/// Returns true if the outermost free variable (Rel(0) from the outer scope,
/// tracked by `depth`) appears free inside any EAbs or EJavaScript node in `e`.
///
/// Used to prevent inlining a variable that would be captured inside a lambda
/// (which could duplicate work).
fn free_in_abs(e: &LocExp) -> bool {
    free_in_abs_aux(0, e)
}

fn free_in_abs_aux(depth: usize, e: &LocExp) -> bool {
    match &e.node {
        Exp::Abs(_, _, _, body) => {
            // Check if Rel(depth) is free in this body
            count_free_inner(depth, body) > 0
            // Also recurse into body with depth+1 (we've crossed an EAbs binder)
            || free_in_abs_aux(depth + 1, body)
        }
        Exp::JavaScript(_, body) => {
            // JavaScript doesn't introduce a new RelE binder
            count_free_inner(depth, body) > 0 || free_in_abs_aux(depth, body)
        }
        Exp::Let(_, _, e1, e2) => free_in_abs_aux(depth, e1) || free_in_abs_aux(depth + 1, e2),
        Exp::Case(disc, arms, _) => {
            free_in_abs_aux(depth, disc)
                || arms
                    .iter()
                    .any(|(p, ae)| free_in_abs_aux(depth + pat_binds_n(p), ae))
        }
        Exp::App(f, arg) => free_in_abs_aux(depth, f) || free_in_abs_aux(depth, arg),
        Exp::Strcat(e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::Binop(_, _, e1, e2)
        | Exp::SignalBind(e1, e2)
        | Exp::Setval(e1, e2) => free_in_abs_aux(depth, e1) || free_in_abs_aux(depth, e2),
        Exp::Write(inner)
        | Exp::Unop(_, inner)
        | Exp::Field(inner, _)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Nextval(inner)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner)
        | Exp::Uurlify(inner, _, _)
        | Exp::Dml(inner, _)
        | Exp::Redirect(inner, _)
        | Exp::Error(inner, _)
        | Exp::ServerCall(inner, _, _, _)
        | Exp::Recv(inner, _) => free_in_abs_aux(depth, inner),
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => free_in_abs_aux(depth, inner),
        Exp::FfiApp(_, _, args) => args.iter().any(|(ae, _)| free_in_abs_aux(depth, ae)),
        Exp::Record(xets) => xets.iter().any(|(_, re, _)| free_in_abs_aux(depth, re)),
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            blob.as_ref().is_some_and(|b| free_in_abs_aux(depth, b))
                || free_in_abs_aux(depth, mime_type)
        }
        Exp::Closure(_, envs) => envs.iter().any(|ce| free_in_abs_aux(depth, ce)),
        Exp::Query(qm) => {
            free_in_abs_aux(depth, &qm.query)
                || free_in_abs_aux(depth + 2, &qm.body)
                || free_in_abs_aux(depth, &qm.initial)
        }
        Exp::Con(_, _, None)
        | Exp::Prim(_)
        | Exp::Rel(_)
        | Exp::Named(_)
        | Exp::Ffi(_, _)
        | Exp::None(_) => false,
    }
}

// ---------------------------------------------------------------------------
// swap_exp_vars — swap Rel(lower) and Rel(lower+1)
// ---------------------------------------------------------------------------

fn swap_exp_vars(lower: usize, e: &LocExp) -> LocExp {
    let span = e.span.clone();
    let node = swap_exp_vars_node(lower, &e.node);
    Located::new(node, span)
}

fn swap_exp_vars_node(lower: usize, e: &Exp) -> Exp {
    match e {
        Exp::Rel(n) => {
            if *n == lower {
                Exp::Rel(lower + 1)
            } else if *n == lower + 1 {
                Exp::Rel(lower)
            } else {
                e.clone()
            }
        }
        Exp::Abs(x, dom, ran, body) => Exp::Abs(
            x.clone(),
            dom.clone(),
            ran.clone(),
            Box::new(swap_exp_vars(lower + 1, body)),
        ),
        Exp::Let(x, t, e1, e2) => Exp::Let(
            x.clone(),
            t.clone(),
            Box::new(swap_exp_vars(lower, e1)),
            Box::new(swap_exp_vars(lower + 1, e2)),
        ),
        Exp::Case(disc, arms, meta) => Exp::Case(
            Box::new(swap_exp_vars(lower, disc)),
            arms.iter()
                .map(|(p, ae)| (p.clone(), swap_exp_vars(lower + pat_binds_n(p), ae)))
                .collect(),
            meta.clone(),
        ),
        Exp::Query(qm) => Exp::Query(QueryMeta {
            exps: qm.exps.clone(),
            tables: qm.tables.clone(),
            state: qm.state.clone(),
            query: Box::new(swap_exp_vars(lower, &qm.query)),
            body: Box::new(swap_exp_vars(lower + 2, &qm.body)),
            initial: Box::new(swap_exp_vars(lower, &qm.initial)),
        }),
        Exp::App(f, arg) => Exp::App(
            Box::new(swap_exp_vars(lower, f)),
            Box::new(swap_exp_vars(lower, arg)),
        ),
        Exp::Strcat(e1, e2) => Exp::Strcat(
            Box::new(swap_exp_vars(lower, e1)),
            Box::new(swap_exp_vars(lower, e2)),
        ),
        Exp::Seq(e1, e2) => Exp::Seq(
            Box::new(swap_exp_vars(lower, e1)),
            Box::new(swap_exp_vars(lower, e2)),
        ),
        Exp::Binop(bi, op, e1, e2) => Exp::Binop(
            *bi,
            op.clone(),
            Box::new(swap_exp_vars(lower, e1)),
            Box::new(swap_exp_vars(lower, e2)),
        ),
        Exp::SignalBind(e1, e2) => Exp::SignalBind(
            Box::new(swap_exp_vars(lower, e1)),
            Box::new(swap_exp_vars(lower, e2)),
        ),
        Exp::Setval(e1, e2) => Exp::Setval(
            Box::new(swap_exp_vars(lower, e1)),
            Box::new(swap_exp_vars(lower, e2)),
        ),
        Exp::Write(inner) => Exp::Write(Box::new(swap_exp_vars(lower, inner))),
        Exp::Unop(op, inner) => Exp::Unop(op.clone(), Box::new(swap_exp_vars(lower, inner))),
        Exp::Field(inner, x) => Exp::Field(Box::new(swap_exp_vars(lower, inner)), x.clone()),
        Exp::SignalReturn(inner) => Exp::SignalReturn(Box::new(swap_exp_vars(lower, inner))),
        Exp::SignalSource(inner) => Exp::SignalSource(Box::new(swap_exp_vars(lower, inner))),
        Exp::Nextval(inner) => Exp::Nextval(Box::new(swap_exp_vars(lower, inner))),
        Exp::Sleep(inner) => Exp::Sleep(Box::new(swap_exp_vars(lower, inner))),
        Exp::Spawn(inner) => Exp::Spawn(Box::new(swap_exp_vars(lower, inner))),
        Exp::Uurlify(inner, t, b) => {
            Exp::Uurlify(Box::new(swap_exp_vars(lower, inner)), t.clone(), *b)
        }
        Exp::Dml(inner, fm) => Exp::Dml(Box::new(swap_exp_vars(lower, inner)), *fm),
        Exp::Redirect(inner, t) => Exp::Redirect(Box::new(swap_exp_vars(lower, inner)), t.clone()),
        Exp::Error(inner, t) => Exp::Error(Box::new(swap_exp_vars(lower, inner)), t.clone()),
        Exp::ServerCall(inner, t, eff, fm) => {
            Exp::ServerCall(Box::new(swap_exp_vars(lower, inner)), t.clone(), *eff, *fm)
        }
        Exp::Recv(inner, t) => Exp::Recv(Box::new(swap_exp_vars(lower, inner)), t.clone()),
        Exp::JavaScript(mode, inner) => {
            let mode2 = match mode {
                JavaScriptMode::Source(t) => JavaScriptMode::Source(t.clone()),
                other => other.clone(),
            };
            Exp::JavaScript(mode2, Box::new(swap_exp_vars(lower, inner)))
        }
        Exp::Con(dk, pc, arg) => Exp::Con(
            *dk,
            pc.clone(),
            arg.as_ref().map(|a| Box::new(swap_exp_vars(lower, a))),
        ),
        Exp::Some(t, inner) => Exp::Some(t.clone(), Box::new(swap_exp_vars(lower, inner))),
        Exp::FfiApp(m, f, args) => Exp::FfiApp(
            m.clone(),
            f.clone(),
            args.iter()
                .map(|(ae, t)| (swap_exp_vars(lower, ae), t.clone()))
                .collect(),
        ),
        Exp::Record(xets) => Exp::Record(
            xets.iter()
                .map(|(x, re, t)| (x.clone(), swap_exp_vars(lower, re), t.clone()))
                .collect(),
        ),
        Exp::ReturnBlob { blob, mime_type, t } => Exp::ReturnBlob {
            blob: blob.as_ref().map(|b| Box::new(swap_exp_vars(lower, b))),
            mime_type: Box::new(swap_exp_vars(lower, mime_type)),
            t: t.clone(),
        },
        Exp::Closure(n, envs) => {
            Exp::Closure(*n, envs.iter().map(|ce| swap_exp_vars(lower, ce)).collect())
        }
        // Leaves (Rel is already handled above)
        Exp::Prim(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::None(_) => e.clone(),
    }
}

// ---------------------------------------------------------------------------
// swap_exp_vars_pat — pattern-aware variable swap
// ---------------------------------------------------------------------------

/// Swap variables for pushing a case arm's application:
/// - Rel(lower) → Rel(lower + len)  (the scrutinee moves past the pat bindings)
/// - Rel(lower+1 .. lower+len) → each decremented by 1 (pat bindings shift down)
/// - Others → unchanged
///
/// When descending under binders, `lower` increments.
fn swap_exp_vars_pat(lower: usize, len: usize, e: &LocExp) -> LocExp {
    let span = e.span.clone();
    let node = swap_exp_vars_pat_node(lower, len, &e.node);
    Located::new(node, span)
}

fn swap_exp_vars_pat_node(lower: usize, len: usize, e: &Exp) -> Exp {
    match e {
        Exp::Rel(n) => {
            let n = *n;
            if n == lower {
                Exp::Rel(lower + len)
            } else if n > lower && n < lower + 1 + len {
                Exp::Rel(n - 1)
            } else {
                e.clone()
            }
        }
        Exp::Abs(x, dom, ran, body) => Exp::Abs(
            x.clone(),
            dom.clone(),
            ran.clone(),
            Box::new(swap_exp_vars_pat(lower + 1, len, body)),
        ),
        Exp::Let(x, t, e1, e2) => Exp::Let(
            x.clone(),
            t.clone(),
            Box::new(swap_exp_vars_pat(lower, len, e1)),
            Box::new(swap_exp_vars_pat(lower + 1, len, e2)),
        ),
        Exp::Case(disc, arms, meta) => Exp::Case(
            Box::new(swap_exp_vars_pat(lower, len, disc)),
            arms.iter()
                .map(|(p, ae)| {
                    (
                        p.clone(),
                        swap_exp_vars_pat(lower + pat_binds_n(p), len, ae),
                    )
                })
                .collect(),
            meta.clone(),
        ),
        Exp::Query(qm) => Exp::Query(QueryMeta {
            exps: qm.exps.clone(),
            tables: qm.tables.clone(),
            state: qm.state.clone(),
            query: Box::new(swap_exp_vars_pat(lower, len, &qm.query)),
            body: Box::new(swap_exp_vars_pat(lower + 2, len, &qm.body)),
            initial: Box::new(swap_exp_vars_pat(lower, len, &qm.initial)),
        }),
        Exp::App(f, arg) => Exp::App(
            Box::new(swap_exp_vars_pat(lower, len, f)),
            Box::new(swap_exp_vars_pat(lower, len, arg)),
        ),
        Exp::Strcat(e1, e2) => Exp::Strcat(
            Box::new(swap_exp_vars_pat(lower, len, e1)),
            Box::new(swap_exp_vars_pat(lower, len, e2)),
        ),
        Exp::Seq(e1, e2) => Exp::Seq(
            Box::new(swap_exp_vars_pat(lower, len, e1)),
            Box::new(swap_exp_vars_pat(lower, len, e2)),
        ),
        Exp::Binop(bi, op, e1, e2) => Exp::Binop(
            *bi,
            op.clone(),
            Box::new(swap_exp_vars_pat(lower, len, e1)),
            Box::new(swap_exp_vars_pat(lower, len, e2)),
        ),
        Exp::SignalBind(e1, e2) => Exp::SignalBind(
            Box::new(swap_exp_vars_pat(lower, len, e1)),
            Box::new(swap_exp_vars_pat(lower, len, e2)),
        ),
        Exp::Setval(e1, e2) => Exp::Setval(
            Box::new(swap_exp_vars_pat(lower, len, e1)),
            Box::new(swap_exp_vars_pat(lower, len, e2)),
        ),
        Exp::Write(inner) => Exp::Write(Box::new(swap_exp_vars_pat(lower, len, inner))),
        Exp::Unop(op, inner) => {
            Exp::Unop(op.clone(), Box::new(swap_exp_vars_pat(lower, len, inner)))
        }
        Exp::Field(inner, x) => {
            Exp::Field(Box::new(swap_exp_vars_pat(lower, len, inner)), x.clone())
        }
        Exp::SignalReturn(inner) => {
            Exp::SignalReturn(Box::new(swap_exp_vars_pat(lower, len, inner)))
        }
        Exp::SignalSource(inner) => {
            Exp::SignalSource(Box::new(swap_exp_vars_pat(lower, len, inner)))
        }
        Exp::Nextval(inner) => Exp::Nextval(Box::new(swap_exp_vars_pat(lower, len, inner))),
        Exp::Sleep(inner) => Exp::Sleep(Box::new(swap_exp_vars_pat(lower, len, inner))),
        Exp::Spawn(inner) => Exp::Spawn(Box::new(swap_exp_vars_pat(lower, len, inner))),
        Exp::Uurlify(inner, t, b) => Exp::Uurlify(
            Box::new(swap_exp_vars_pat(lower, len, inner)),
            t.clone(),
            *b,
        ),
        Exp::Dml(inner, fm) => Exp::Dml(Box::new(swap_exp_vars_pat(lower, len, inner)), *fm),
        Exp::Redirect(inner, t) => {
            Exp::Redirect(Box::new(swap_exp_vars_pat(lower, len, inner)), t.clone())
        }
        Exp::Error(inner, t) => {
            Exp::Error(Box::new(swap_exp_vars_pat(lower, len, inner)), t.clone())
        }
        Exp::ServerCall(inner, t, eff, fm) => Exp::ServerCall(
            Box::new(swap_exp_vars_pat(lower, len, inner)),
            t.clone(),
            *eff,
            *fm,
        ),
        Exp::Recv(inner, t) => Exp::Recv(Box::new(swap_exp_vars_pat(lower, len, inner)), t.clone()),
        Exp::JavaScript(mode, inner) => {
            let mode2 = match mode {
                JavaScriptMode::Source(t) => JavaScriptMode::Source(t.clone()),
                other => other.clone(),
            };
            Exp::JavaScript(mode2, Box::new(swap_exp_vars_pat(lower, len, inner)))
        }
        Exp::Con(dk, pc, arg) => Exp::Con(
            *dk,
            pc.clone(),
            arg.as_ref()
                .map(|a| Box::new(swap_exp_vars_pat(lower, len, a))),
        ),
        Exp::Some(t, inner) => Exp::Some(t.clone(), Box::new(swap_exp_vars_pat(lower, len, inner))),
        Exp::FfiApp(m, f, args) => Exp::FfiApp(
            m.clone(),
            f.clone(),
            args.iter()
                .map(|(ae, t)| (swap_exp_vars_pat(lower, len, ae), t.clone()))
                .collect(),
        ),
        Exp::Record(xets) => Exp::Record(
            xets.iter()
                .map(|(x, re, t)| (x.clone(), swap_exp_vars_pat(lower, len, re), t.clone()))
                .collect(),
        ),
        Exp::ReturnBlob { blob, mime_type, t } => Exp::ReturnBlob {
            blob: blob
                .as_ref()
                .map(|b| Box::new(swap_exp_vars_pat(lower, len, b))),
            mime_type: Box::new(swap_exp_vars_pat(lower, len, mime_type)),
            t: t.clone(),
        },
        Exp::Closure(n, envs) => Exp::Closure(
            *n,
            envs.iter()
                .map(|ce| swap_exp_vars_pat(lower, len, ce))
                .collect(),
        ),
        // Leaves (Rel is already handled above)
        Exp::Prim(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::None(_) => e.clone(),
    }
}

// ---------------------------------------------------------------------------
// match_pat — try to match a pattern against an expression
// ---------------------------------------------------------------------------

/// Try to match pattern `p` against expression `e`.
///
/// Returns:
/// - `Yes(subs)` — definitely matches; `subs` is a list of (name, typ, exp)
///   bindings in the order they should be substituted (outermost first).
/// - `No` — definitely doesn't match.
/// - `Maybe` — can't tell statically.
fn match_pat(subs: Vec<(String, LocTyp, LocExp)>, p: &LocPat, e: &LocExp) -> MatchResult {
    match (&p.node, &e.node) {
        (Pat::Var(x, t), _) => {
            let mut v = subs;
            v.push((x.clone(), t.clone(), e.clone()));
            MatchResult::Yes(v)
        }

        // String prefix/suffix checks for Strcat
        (Pat::Prim(Prim::String(_, s)), Exp::Strcat(box_e1, box_e2)) => {
            // Check if prefix of strcat definitely can't match
            if let Exp::Prim(Prim::String(_, s2)) = &box_e1.node {
                if !s2.starts_with(s.as_str()) && s.len() <= s2.len() {
                    return MatchResult::No;
                }
            }
            // Check if suffix of strcat definitely can't match
            if let Exp::Prim(Prim::String(_, s2)) = &box_e2.node {
                if !s2.ends_with(s.as_str()) && s.len() <= s2.len() {
                    return MatchResult::No;
                }
            }
            MatchResult::Maybe
        }

        // String length bound check
        (Pat::Prim(Prim::String(_, s)), _) => {
            let lb = string_length_lb(e);
            if lb > s.len() {
                MatchResult::No
            } else {
                MatchResult::Maybe
            }
        }

        // Primitive equality
        (Pat::Prim(p_prim), Exp::Prim(e_prim)) => {
            if p_prim == e_prim {
                MatchResult::Yes(subs)
            } else {
                MatchResult::No
            }
        }

        // Constructor matching (by ID)
        (Pat::Con(_, PatCon::Var(n1), po), Exp::Con(_, PatCon::Var(n2), eo)) => {
            if n1 != n2 {
                return MatchResult::No;
            }
            match (po, eo) {
                (None, None) => MatchResult::Yes(subs),
                (Some(pp), Some(ee)) => match_pat(subs, pp, ee),
                _ => MatchResult::Maybe,
            }
        }

        // FFI constructor matching (no arg)
        (
            Pat::Con(
                _,
                PatCon::Ffi {
                    module: m1,
                    con: c1,
                    ..
                },
                None,
            ),
            Exp::Con(
                _,
                PatCon::Ffi {
                    module: m2,
                    con: c2,
                    ..
                },
                None,
            ),
        ) => {
            if m1 == m2 && c1 == c2 {
                MatchResult::Yes(subs)
            } else {
                MatchResult::No
            }
        }

        // FFI constructor matching (with arg)
        (
            Pat::Con(
                _,
                PatCon::Ffi {
                    module: m1,
                    con: c1,
                    ..
                },
                Some(pp),
            ),
            Exp::Con(
                _,
                PatCon::Ffi {
                    module: m2,
                    con: c2,
                    ..
                },
                Some(ee),
            ),
        ) => {
            if m1 == m2 && c1 == c2 {
                match_pat(subs, pp, ee)
            } else {
                MatchResult::No
            }
        }

        // Record matching
        (Pat::Record(xps), Exp::Record(xes)) => {
            let mut current_subs = subs;
            for (px, pp, _) in xps {
                match xes.iter().find(|(ex, _, _)| ex == px) {
                    None => return MatchResult::No,
                    Some((_, ee, _)) => match match_pat(current_subs, pp, ee) {
                        MatchResult::No => return MatchResult::No,
                        MatchResult::Maybe => return MatchResult::Maybe,
                        MatchResult::Yes(new_subs) => current_subs = new_subs,
                    },
                }
            }
            MatchResult::Yes(current_subs)
        }

        // Option matching
        (Pat::None(_), Exp::None(_)) => MatchResult::Yes(subs),
        (Pat::None(_), Exp::Some(_, _)) => MatchResult::No,
        (Pat::Some(_, pp), Exp::Some(_, ee)) => match_pat(subs, pp, ee),
        (Pat::Some(_, _), Exp::None(_)) => MatchResult::No,

        _ => MatchResult::Maybe,
    }
}

/// Lower bound on the string length of expression `e` (for pattern matching).
fn string_length_lb(e: &LocExp) -> usize {
    match &e.node {
        Exp::Strcat(e1, e2) => string_length_lb(e1) + string_length_lb(e2),
        Exp::Prim(Prim::String(_, s)) => s.len(),
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// passive — check if expression needs no evaluation
// ---------------------------------------------------------------------------

/// Returns true if the expression is "passive" — it evaluates instantly and
/// has no effects (a value or simple variable reference).
fn passive(e: &LocExp) -> bool {
    match &e.node {
        Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::Abs(_, _, _, _) => true,
        Exp::Con(_, _, None) | Exp::None(_) => true,
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => passive(inner),
        Exp::Record(xets) => xets.iter().all(|(_, re, _)| passive(re)),
        Exp::Field(inner, _) => passive(inner),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// which_proj — check if a variable is used only in field projections
// ---------------------------------------------------------------------------

/// Returns Some(paths) if Rel(i) in `e` is only accessed via field projections,
/// None if it's used in any other context.
///
/// `i` is the de Bruijn index of the variable to check.
///
/// This is a conservative implementation: returns None always (disables the
/// optimisation safely). A full implementation would track field-path usage.
fn which_proj(_i: usize, _e: &LocExp) -> Option<Vec<Vec<String>>> {
    // Conservative: return None to disable the record-projection inlining
    // optimisation. This is safe (prevents some inlining, but never wrong).
    None
}

// ---------------------------------------------------------------------------
// may_inline — decide if a named val can be inlined
// ---------------------------------------------------------------------------

fn may_inline(
    n: usize,
    e: &LocExp,
    t: &LocTyp,
    s: &str,
    ctx: &ReduceCtx,
    settings: &Settings,
) -> bool {
    let count = match ctx.uses.get(&n) {
        None => return false,
        Some(&c) => c,
    };
    if settings.never_inline.contains(s) {
        return false;
    }
    count <= 1
        || exp_size(e) <= settings.mono_inline as usize
        || function_inside(t)
        || settings.always_inline.contains(s)
}

/// Count nodes in an expression (rough size estimate).
fn exp_size(e: &LocExp) -> usize {
    use crate::monomorphized::utilities::exp;
    exp::fold(e, 0, &|_, n| n, &|_, n| n + 1)
}

/// Returns true if `t` (interpreted as a function type) has a function type
/// anywhere in its domain.
fn function_inside(t: &LocTyp) -> bool {
    match &t.node {
        Typ::Fun(dom, ran) => function_inside_prime(dom) || function_inside(ran),
        _ => function_inside_prime(t),
    }
}

fn function_inside_prime(t: &LocTyp) -> bool {
    use crate::monomorphized::utilities::typ;
    typ::exists(t, &|node| matches!(node, Typ::Fun(..)))
}

// ---------------------------------------------------------------------------
// count_abs — count leading EAbs wrappers
// ---------------------------------------------------------------------------

fn count_abs(
    env: &Env,
    e: &LocExp,
    is_global: bool,
    timpures: &HashSet<usize>,
    impures: &HashSet<usize>,
    abs_counts: &HashMap<usize, usize>,
    settings: &Settings,
) -> usize {
    match &e.node {
        Exp::Abs(x, dom, _, body) => {
            let env2 = env.push_rel(x, dom.clone());
            1 + count_abs(
                &env2, body, is_global, timpures, impures, abs_counts, settings,
            )
        }
        _ => {
            // Try to determine remaining abstractions from named references
            remaining_abs(env, e, is_global, timpures, impures, abs_counts, settings).unwrap_or(0)
        }
    }
}

fn remaining_abs(
    env: &Env,
    e: &LocExp,
    is_global: bool,
    timpures: &HashSet<usize>,
    impures: &HashSet<usize>,
    abs_counts: &HashMap<usize, usize>,
    settings: &Settings,
) -> Option<usize> {
    match &e.node {
        Exp::Named(n) => abs_counts.get(n).copied(),
        Exp::App(f, arg) => {
            if simple_impure(is_global, timpures, impures, env, arg, settings) {
                None
            } else {
                remaining_abs(env, f, is_global, timpures, impures, abs_counts, settings)
                    .and_then(|n| if n > 0 { Some(n - 1) } else { None })
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// reduce_exp — main reduction function (bottom-up)
// ---------------------------------------------------------------------------

/// Reduce an expression in the given environment.
///
/// This function:
/// 1. Recursively reduces all sub-expressions (with appropriate env extensions).
/// 2. Applies node-level rewrites.
/// 3. When a rewrite generates a new term, recursively reduces that too.
fn reduce_exp(env: &Env, e: LocExp, ctx: &ReduceCtx, settings: &Settings) -> LocExp {
    let span = e.span.clone();
    // First reduce children
    let reduced = reduce_children(env, e, ctx, settings);
    // Then apply top-level rewrites
    let new_node = reduce_node(env, reduced.node, &span, ctx, settings);
    Located::new(new_node, span)
}

/// Recursively reduce all sub-expressions, then return the expression with
/// reduced children (no node-level rewrites applied yet).
fn reduce_children(env: &Env, e: LocExp, ctx: &ReduceCtx, settings: &Settings) -> LocExp {
    let span = e.span.clone();
    let node = match e.node {
        Exp::Abs(x, dom, ran, body) => {
            let env2 = env.push_rel(&x, dom.clone());
            let body2 = reduce_exp(&env2, *body, ctx, settings);
            Exp::Abs(x, dom, ran, Box::new(body2))
        }
        Exp::Let(x, t, e1, e2) => {
            let e1r = reduce_exp(env, *e1, ctx, settings);
            let env2 = env.push_rel(&x, t.clone());
            let e2r = reduce_exp(&env2, *e2, ctx, settings);
            Exp::Let(x, t, Box::new(e1r), Box::new(e2r))
        }
        Exp::Case(disc, arms, meta) => {
            let disc_r = reduce_exp(env, *disc, ctx, settings);
            let arms_r = arms
                .into_iter()
                .map(|(p, ae)| {
                    let env2 = env.pat_binds(&p);
                    let ae_r = reduce_exp(&env2, ae, ctx, settings);
                    (p, ae_r)
                })
                .collect();
            Exp::Case(Box::new(disc_r), arms_r, meta)
        }
        Exp::Query(qm) => {
            let query_r = reduce_exp(env, *qm.query, ctx, settings);
            // Query body has two extra bindings (row, accumulator)
            let body_env = env
                .push_rel("r", qm.state.clone())
                .push_rel("acc", qm.state.clone());
            let body_r = reduce_exp(&body_env, *qm.body, ctx, settings);
            let initial_r = reduce_exp(env, *qm.initial, ctx, settings);
            Exp::Query(QueryMeta {
                exps: qm.exps,
                tables: qm.tables,
                state: qm.state,
                query: Box::new(query_r),
                body: Box::new(body_r),
                initial: Box::new(initial_r),
            })
        }
        Exp::App(f, arg) => {
            let f_r = reduce_exp(env, *f, ctx, settings);
            let arg_r = reduce_exp(env, *arg, ctx, settings);
            Exp::App(Box::new(f_r), Box::new(arg_r))
        }
        Exp::Strcat(e1, e2) => {
            let e1r = reduce_exp(env, *e1, ctx, settings);
            let e2r = reduce_exp(env, *e2, ctx, settings);
            Exp::Strcat(Box::new(e1r), Box::new(e2r))
        }
        Exp::Seq(e1, e2) => {
            let e1r = reduce_exp(env, *e1, ctx, settings);
            let e2r = reduce_exp(env, *e2, ctx, settings);
            Exp::Seq(Box::new(e1r), Box::new(e2r))
        }
        Exp::Binop(bi, op, e1, e2) => {
            let e1r = reduce_exp(env, *e1, ctx, settings);
            let e2r = reduce_exp(env, *e2, ctx, settings);
            Exp::Binop(bi, op, Box::new(e1r), Box::new(e2r))
        }
        Exp::SignalBind(e1, e2) => {
            let e1r = reduce_exp(env, *e1, ctx, settings);
            let e2r = reduce_exp(env, *e2, ctx, settings);
            Exp::SignalBind(Box::new(e1r), Box::new(e2r))
        }
        Exp::Setval(e1, e2) => {
            let e1r = reduce_exp(env, *e1, ctx, settings);
            let e2r = reduce_exp(env, *e2, ctx, settings);
            Exp::Setval(Box::new(e1r), Box::new(e2r))
        }
        Exp::Write(inner) => Exp::Write(Box::new(reduce_exp(env, *inner, ctx, settings))),
        Exp::Unop(op, inner) => Exp::Unop(op, Box::new(reduce_exp(env, *inner, ctx, settings))),
        Exp::Field(inner, x) => Exp::Field(Box::new(reduce_exp(env, *inner, ctx, settings)), x),
        Exp::SignalReturn(inner) => {
            Exp::SignalReturn(Box::new(reduce_exp(env, *inner, ctx, settings)))
        }
        Exp::SignalSource(inner) => {
            Exp::SignalSource(Box::new(reduce_exp(env, *inner, ctx, settings)))
        }
        Exp::Nextval(inner) => Exp::Nextval(Box::new(reduce_exp(env, *inner, ctx, settings))),
        Exp::Sleep(inner) => Exp::Sleep(Box::new(reduce_exp(env, *inner, ctx, settings))),
        Exp::Spawn(inner) => Exp::Spawn(Box::new(reduce_exp(env, *inner, ctx, settings))),
        Exp::Uurlify(inner, t, b) => {
            Exp::Uurlify(Box::new(reduce_exp(env, *inner, ctx, settings)), t, b)
        }
        Exp::Dml(inner, fm) => Exp::Dml(Box::new(reduce_exp(env, *inner, ctx, settings)), fm),
        Exp::Redirect(inner, t) => {
            Exp::Redirect(Box::new(reduce_exp(env, *inner, ctx, settings)), t)
        }
        Exp::Error(inner, t) => Exp::Error(Box::new(reduce_exp(env, *inner, ctx, settings)), t),
        Exp::ServerCall(inner, t, eff, fm) => {
            Exp::ServerCall(Box::new(reduce_exp(env, *inner, ctx, settings)), t, eff, fm)
        }
        Exp::Recv(inner, t) => Exp::Recv(Box::new(reduce_exp(env, *inner, ctx, settings)), t),
        Exp::JavaScript(mode, inner) => {
            Exp::JavaScript(mode, Box::new(reduce_exp(env, *inner, ctx, settings)))
        }
        Exp::Con(dk, pc, arg) => Exp::Con(
            dk,
            pc,
            arg.map(|a| Box::new(reduce_exp(env, *a, ctx, settings))),
        ),
        Exp::Some(t, inner) => Exp::Some(t, Box::new(reduce_exp(env, *inner, ctx, settings))),
        Exp::FfiApp(m, f, args) => Exp::FfiApp(
            m,
            f,
            args.into_iter()
                .map(|(ae, t)| (reduce_exp(env, ae, ctx, settings), t))
                .collect(),
        ),
        Exp::Record(xets) => Exp::Record(
            xets.into_iter()
                .map(|(x, re, t)| (x, reduce_exp(env, re, ctx, settings), t))
                .collect(),
        ),
        Exp::ReturnBlob { blob, mime_type, t } => Exp::ReturnBlob {
            blob: blob.map(|b| Box::new(reduce_exp(env, *b, ctx, settings))),
            mime_type: Box::new(reduce_exp(env, *mime_type, ctx, settings)),
            t,
        },
        Exp::Closure(n, envs) => Exp::Closure(
            n,
            envs.into_iter()
                .map(|ce| reduce_exp(env, ce, ctx, settings))
                .collect(),
        ),
        // Leaves — no sub-expressions to reduce
        other => other,
    };
    Located::new(node, span)
}

/// Apply top-level (node-level) rewrites after children are reduced.
fn reduce_node(env: &Env, e: Exp, span: &Span, ctx: &ReduceCtx, settings: &Settings) -> Exp {
    match e {
        // ----------------------------------------------------------------
        // Rel(n) → inline cached expression if available
        // ----------------------------------------------------------------
        Exp::Rel(n) => {
            if let Ok((_, _, Some(cached))) = env.lookup_rel(n) {
                cached.node.clone()
            } else {
                Exp::Rel(n)
            }
        }

        // ----------------------------------------------------------------
        // Named(n) → inline body if available (and inlining is allowed)
        // ----------------------------------------------------------------
        Exp::Named(n) => {
            if let Ok((_, _, Some(cached), _)) = env.lookup_named(n) {
                cached.node.clone()
            } else {
                Exp::Named(n)
            }
        }

        // ----------------------------------------------------------------
        // App(Abs(x, t, _, e1), e2) → beta reduction
        // ----------------------------------------------------------------
        Exp::App(f, arg) => {
            if let Exp::Abs(x, t, _, body) = f.node.clone() {
                // Beta reduction
                let impure_arg = impure_ctx(env, &arg, ctx, settings);
                let cf = count_free(0, &body);
                let multi_use = !ctx.full_mode && cf > 1;
                tracing::debug!(
                    variable = %x,
                    impure_arg,
                    free_under_lambda = cf,
                    multi_use,
                    full_mode = ctx.full_mode,
                    "mono_reduce beta-reduction decision"
                );
                if impure_arg || multi_use {
                    // Too many uses or arg is impure: use ELet instead of substitution
                    let let_e = Located::new(
                        Exp::Let(x.clone(), t.clone(), arg.clone(), body.clone()),
                        span.clone(),
                    );
                    reduce_exp(env, let_e, ctx, settings).node
                } else {
                    // Safe to substitute directly
                    let subst = sub_exp_in_exp(0, &arg, &body);
                    reduce_exp(env, subst, ctx, settings).node
                }
            } else if let Exp::Let(x, t, e, b) = f.node.clone() {
                // Commutation: App(Let(x, t, e, b), arg) → Let(x, t, e, App(b, lift(arg)))
                // Mirrors SML: `EApp((ELet(x,t,e,b),loc), e') → ELet(x,t,e, EApp(b, liftExpInExp 0 e'))`
                let lifted_arg = lift_exp_in_exp(0, &arg);
                let new_app = Located::new(Exp::App(b, Box::new(lifted_arg)), span.clone());
                let new_let = Located::new(Exp::Let(x, t, e, Box::new(new_app)), span.clone());
                reduce_exp(env, new_let, ctx, settings).node
            } else {
                Exp::App(f, arg)
            }
        }

        // ----------------------------------------------------------------
        // Case reduction
        // ----------------------------------------------------------------
        Exp::Case(disc, arms, meta) => {
            // Don't reduce if discriminant is impure
            if impure_ctx(env, &disc, ctx, settings) {
                // Try "pushing" the case: if result type is a function,
                // we can abstract over the argument and push the case inside
                return push_case(env, disc, arms, meta, span, ctx, settings);
            }
            // Try to match patterns statically
            search_arms(env, *disc, arms, meta, span, ctx, settings)
        }

        // ----------------------------------------------------------------
        // Field(e1, x) → yankLets optimization
        // ----------------------------------------------------------------
        Exp::Field(e1, x) => yank_lets(*e1, &x),

        // ----------------------------------------------------------------
        // Let(x1, t1, Let(x2, t2, e1, b1), b2) → commute lets
        //   → Let(x2, t2, e1, Let(x1, t1, b1, lift(b2)))
        // ----------------------------------------------------------------
        Exp::Let(x1, t1, e1_box, b2_box) => {
            if let Exp::Let(x2, t2, inner_e1, b1) = e1_box.node.clone() {
                let loc = e1_box.span.clone();
                let b2_lifted = lift_exp_in_exp(1, &b2_box);
                let inner_let = Located::new(
                    Exp::Let(x1.clone(), t1.clone(), b1, Box::new(b2_lifted)),
                    loc.clone(),
                );
                let outer = Located::new(Exp::Let(x2, t2, inner_e1, Box::new(inner_let)), loc);
                return reduce_exp(env, outer, ctx, settings).node;
            }

            // ----------------------------------------------------------------
            // Let(x, t, e', Abs(x', unit_record_t, ran, e'')) when e' is pure
            //   → Abs(x', unit_record_t, ran, Let(x, t, lift(e'), swap(e'')))
            // ----------------------------------------------------------------
            if let Exp::Abs(x2, t2, ran2, body2) = b2_box.node.clone() {
                if is_unit_record_type(&t2) && !impure_ctx(env, &e1_box, ctx, settings) {
                    let env2 = env.push_rel(&x2, t2.clone());
                    let lifted_e1 = lift_exp_in_exp(0, &e1_box);
                    let swapped_body = swap_exp_vars(0, &body2);
                    let inner_let = Located::new(
                        Exp::Let(
                            x1.clone(),
                            t1.clone(),
                            Box::new(lifted_e1),
                            Box::new(swapped_body),
                        ),
                        span.clone(),
                    );
                    let abs_body = reduce_exp(&env2, inner_let, ctx, settings);
                    return Exp::Abs(x2, t2, ran2, Box::new(abs_body));
                }
            }

            // ----------------------------------------------------------------
            // General ELet: doLet
            // ----------------------------------------------------------------
            do_let(env, x1, t1, *e1_box, *b2_box, span, ctx, settings)
        }

        // ----------------------------------------------------------------
        // App(Let(x, t, e, b), e') → Let(x, t, e, App(b, lift(e')))
        // ----------------------------------------------------------------
        // Note: This is handled at the App level, but after App(Abs) is handled.
        // Actually this pattern matches when f is a Let, not Abs — we handle it here
        // by re-checking the App pattern.
        // The Abs case is already handled in Exp::App above.
        // We need to also handle App(Let) at the Let level, which is done via
        // the commutation rule above when the outer expression is App(Let(...)).
        // This particular rewrite pushes App inside Let:
        //   App(Let(x,t,e,b), e') → Let(x,t,e, App(b, lift(e')))
        // But since we process App first, and App's f may be a Let, we handle
        // this in a special pass. Since reduce_children already ran, the App's
        // f may still be a Let (if it couldn't be reduced further).
        // We handle this in reduce_node for App when f is Let:
        // (handled in the combined App match below - see "App with Let f" comment)

        // ----------------------------------------------------------------
        // Strcat constant folding
        // ----------------------------------------------------------------
        Exp::Strcat(e1, e2) => {
            if let (Exp::Prim(Prim::String(k1, s1)), Exp::Prim(Prim::String(k2, s2))) =
                (&e1.node, &e2.node)
            {
                let mode = match (k1, k2) {
                    (StringMode::Html, StringMode::Html) => StringMode::Html,
                    _ => StringMode::Normal,
                };
                Exp::Prim(Prim::String(mode, format!("{}{}", s1, s2)))
            } else {
                Exp::Strcat(e1, e2)
            }
        }

        // ----------------------------------------------------------------
        // SignalBind(SignalReturn(e1), e2) → App(e2, e1)
        // ----------------------------------------------------------------
        Exp::SignalBind(e1, e2) => {
            if let Exp::SignalReturn(inner) = e1.node.clone() {
                let app = Located::new(Exp::App(e2.clone(), inner), span.clone());
                reduce_exp(env, app, ctx, settings).node
            } else {
                Exp::SignalBind(e1, e2)
            }
        }

        // Unchanged
        other => other,
    }
}

/// Check if a type is the unit record type `{}` (TRecord []).
fn is_unit_record_type(t: &LocTyp) -> bool {
    matches!(&t.node, Typ::Record(fields) if fields.is_empty())
}

/// The "yank lets" optimization for field projection:
/// pull a record out from under lets.
fn yank_lets(e1: LocExp, x: &str) -> Exp {
    let span = e1.span.clone();
    match e1.node {
        Exp::Let(lx, lt, le1, le2) => {
            // Recurse: Let(lx, lt, le1, yank_lets(le2, x))
            let inner_span = le2.span.clone();
            let yanked = yank_lets(*le2, x);
            Exp::Let(lx, lt, le1, Box::new(Located::new(yanked, inner_span)))
        }
        Exp::Record(xets) => {
            // Found the record: look for field x
            match xets.iter().find(|(fx, _, _)| fx == x) {
                Some((_, fe, _)) => fe.node.clone(),
                None => Exp::Field(
                    Box::new(Located::new(Exp::Record(xets), span)),
                    x.to_string(),
                ),
            }
        }
        other => Exp::Field(Box::new(Located::new(other, span)), x.to_string()),
    }
}

/// Try to "push" a case expression: if the result type is a function, convert
///   case e of p1 => f1 | p2 => f2 | ...
/// into
///   fn y => case e of p1 => f1 y | p2 => f2 y | ...
/// (the "yanked case" optimisation, enabling more beta reductions later).
fn push_case(
    _env: &Env,
    disc: Box<LocExp>,
    arms: Vec<(LocPat, LocExp)>,
    meta: CaseMeta,
    span: &Span,
    ctx: &ReduceCtx,
    _settings: &Settings,
) -> Exp {
    // Check if result type is a function type
    if let Typ::Fun(dom, result_t) = &meta.result.node {
        let dom = dom.clone();
        let result_t = result_t.clone();

        // Check if each arm is "safe" (pure use of its bound variable, no side effects,
        // or an explicit abort)
        fn arm_safe(arm_e: &LocExp) -> bool {
            let effs = summarize(0, arm_e);
            effs.iter()
                .all(|eff| matches!(eff, Event::UseRel | Event::Abort))
        }

        if arms.iter().all(|(_, ae)| arm_safe(ae)) {
            ctx.yanked_case.set(true);
            let lifted_disc = lift_exp_in_exp(0, &disc);
            let new_arms: Vec<(LocPat, LocExp)> = arms
                .into_iter()
                .map(|(p, ae)| {
                    let n_binds = pat_binds_n(&p);
                    let ae_span = ae.span.clone();
                    let new_ae = match ae.node {
                        Exp::Abs(_, _, _, body) => {
                            // swap Rel(0) [the case scrutinee] with Rel(n_binds) [the new arg]
                            swap_exp_vars_pat(0, n_binds, &body)
                        }
                        Exp::Error(msg, err_t) => {
                            if let Typ::Fun(_, inner_t) = &err_t.node {
                                Located::new(Exp::Error(msg, *inner_t.clone()), ae_span.clone())
                            } else {
                                // fallback: apply to Rel(n_binds)
                                let rel = Located::new(Exp::Rel(n_binds), ae_span.clone());
                                let ae_rebuilt =
                                    Located::new(Exp::Error(msg, err_t), ae_span.clone());
                                Located::new(Exp::App(Box::new(ae_rebuilt), Box::new(rel)), ae_span)
                            }
                        }
                        _ => {
                            // Apply to Rel(n_binds)
                            let rel = Located::new(Exp::Rel(n_binds), ae_span.clone());
                            Located::new(
                                Exp::App(
                                    Box::new(lift_exp_in_exp(
                                        n_binds,
                                        &Located::new(ae.node, ae_span.clone()),
                                    )),
                                    Box::new(rel),
                                ),
                                ae_span,
                            )
                        }
                    };
                    (p, new_ae)
                })
                .collect();

            let inner_case = Located::new(
                Exp::Case(
                    Box::new(lifted_disc),
                    new_arms,
                    CaseMeta {
                        disc: meta.disc.clone(),
                        result: *result_t.clone(),
                    },
                ),
                span.clone(),
            );

            return Exp::Abs("y".to_string(), *dom, *result_t, Box::new(inner_case));
        }
    }

    Exp::Case(disc, arms, meta)
}

/// Try to match arms of a case expression statically.
fn search_arms(
    env: &Env,
    disc: LocExp,
    arms: Vec<(LocPat, LocExp)>,
    meta: CaseMeta,
    span: &Span,
    ctx: &ReduceCtx,
    settings: &Settings,
) -> Exp {
    for (p, body) in &arms {
        match match_pat(vec![], p, &disc) {
            MatchResult::No => continue,
            MatchResult::Maybe => {
                // Can't reduce; try push_case instead
                return push_case(env, Box::new(disc), arms, meta, span, ctx, settings);
            }
            MatchResult::Yes(subs) => {
                // Apply substitutions (innermost first)
                let n_subs = subs.len();
                let env2 = env.pat_binds(p);

                // Build up the substituted body by wrapping in ELets or substituting directly
                let mut current_body = body.clone();
                let mut remaining = n_subs as isize - 1;

                for (sx, st, se) in subs.into_iter() {
                    if count_free(0, &current_body) > 1 {
                        // Use ELet to avoid duplication
                        let lifted = multi_lift(remaining.max(0) as usize, &se);
                        current_body = Located::new(
                            Exp::Let(sx, st, Box::new(lifted), Box::new(current_body)),
                            disc.span.clone(),
                        );
                    } else {
                        // Safe to substitute directly
                        let lifted = multi_lift(remaining.max(0) as usize, &se);
                        current_body = sub_exp_in_exp(0, &lifted, &current_body);
                    }
                    remaining -= 1;
                }

                return reduce_exp(&env2, current_body, ctx, settings).node;
            }
        }
    }

    // No arm matched: try push_case
    push_case(env, Box::new(disc), arms, meta, span, ctx, settings)
}

/// The "doLet" function: decide whether to inline a let binding.
fn do_let(
    env: &Env,
    x: String,
    t: LocTyp,
    e_prime: LocExp,
    b: LocExp,
    _span: &Span,
    ctx: &ReduceCtx,
    settings: &Settings,
) -> Exp {
    let do_sub = |e_prime: &LocExp, b: &LocExp| -> Exp {
        let r = sub_exp_in_exp(0, e_prime, b);
        reduce_exp(env, r, ctx, settings).node
    };

    let try_sub = |e_prime: &LocExp, b: &LocExp| -> Exp {
        // Don't inline into a Signal type (they're lazy)
        if matches!(&t.node, Typ::Signal(_)) {
            return Exp::Let(
                x.clone(),
                t.clone(),
                Box::new(e_prime.clone()),
                Box::new(b.clone()),
            );
        }
        // Don't inline if the RHS is a case expression (complex)
        if matches!(&e_prime.node, Exp::Case(_, _, _)) {
            return Exp::Let(
                x.clone(),
                t.clone(),
                Box::new(e_prime.clone()),
                Box::new(b.clone()),
            );
        }
        do_sub(e_prime, b)
    };

    if impure_ctx(env, &e_prime, ctx, settings) {
        // The binding is impure — check if we can still safely reorder/inline
        let effs_eprime: Vec<Event> = summarize(0, &e_prime)
            .into_iter()
            .filter(|e| *e != Event::UseRel)
            .collect();
        let effs_b = summarize(0, &b);

        let writes_page = effs_eprime.contains(&Event::WritePage);
        let reads_db = effs_eprime.contains(&Event::ReadDb);
        let writes_db = effs_eprime.contains(&Event::WriteDb);
        // Single flag: summarize does not distinguish read vs write cookie (mirrors upstream).
        let cookie_effect = effs_eprime.contains(&Event::ReadCookie);

        let verify_unused = |eff: &Event| -> bool { *eff != Event::UseRel };

        let verify_compatible = |effs: &[Event]| -> bool {
            verify_compatible_impl(effs, writes_page, reads_db, writes_db, cookie_effect)
        };

        // Check if we can_sub:
        let can_sub = (effs_eprime.is_empty()
            || (effs_eprime.iter().all(|e| *e != Event::Unsure) && verify_compatible(&effs_b))
            || matches!(effs_b.as_slice(), [Event::UseRel, rest @ ..] if rest.iter().all(verify_unused)))
            && count_free(0, &b) == 1
            && !free_in_abs(&b);

        if can_sub {
            try_sub(&e_prime, &b)
        } else {
            Exp::Let(x, t, Box::new(e_prime), Box::new(b))
        }
    } else {
        // Pure binding
        let uses = count_free(0, &b);
        let is_record = matches!(&e_prime.node, Exp::Record(_));
        let proj_only = is_record && which_proj(0, &b).is_some();

        if uses > 1 && !ctx.full_mode && !passive(&e_prime) && !proj_only {
            // Would duplicate work — keep the let
            Exp::Let(x, t, Box::new(e_prime), Box::new(b))
        } else {
            try_sub(&e_prime, &b)
        }
    }
}

/// Check if the remaining effects in `effs` are compatible with already-seen effects.
fn verify_compatible_impl(
    effs: &[Event],
    writes_page: bool,
    reads_db: bool,
    writes_db: bool,
    cookie_effect: bool,
) -> bool {
    match effs.split_first() {
        None => false,
        Some((first, rest)) => match first {
            Event::Unsure => false,
            Event::UseRel => rest.iter().all(|e| *e != Event::UseRel),
            Event::WritePage => {
                !writes_page
                    && verify_compatible_impl(rest, writes_page, reads_db, writes_db, cookie_effect)
            }
            Event::ReadDb => {
                !writes_db
                    && verify_compatible_impl(rest, writes_page, reads_db, writes_db, cookie_effect)
            }
            Event::WriteDb => {
                !writes_db
                    && !reads_db
                    && verify_compatible_impl(rest, writes_page, reads_db, writes_db, cookie_effect)
            }
            Event::ReadCookie => {
                !cookie_effect
                    && verify_compatible_impl(rest, writes_page, reads_db, writes_db, cookie_effect)
            }
            Event::Abort => true,
        },
    }
}

// ---------------------------------------------------------------------------
// reduce_once — single pass over the file
// ---------------------------------------------------------------------------

/// Perform one reduction pass over the file.
///
/// Builds the analysis sets (timpures, impures, abs_counts, uses) by scanning
/// the declarations first, then processes each declaration.
fn reduce_once(file: File, settings: &Settings, full_mode: bool) -> (File, bool) {
    let (decls, exports) = file;

    // -----------------------------------------------------------------------
    // Analysis pass: compute timpures, impures, abs_counts
    // -----------------------------------------------------------------------
    let mut timpures: HashSet<usize> = HashSet::new();
    let mut impures: HashSet<usize> = HashSet::new();
    let mut abs_counts: HashMap<usize, usize> = HashMap::new();

    for loc_decl in &decls {
        match &loc_decl.node {
            Decl::Datatype(dts) => {
                // A datatype is "type-impure" if any constructor has a type
                // that is simply-impure (contains a function or impure datatype).
                let any_impure = dts.iter().any(|dt| {
                    dt.constrs.iter().any(|(_, _, ct)| {
                        ct.as_ref()
                            .is_some_and(|t| simple_type_impure(t, &timpures))
                    })
                });
                if any_impure {
                    for dt in dts {
                        timpures.insert(dt.id);
                    }
                }
            }
            Decl::Val(_, n, _, e, _) => {
                if simple_impure(true, &timpures, &impures, &Env::empty(), e, settings) {
                    impures.insert(*n);
                }
                abs_counts.insert(
                    *n,
                    count_abs(
                        &Env::empty(),
                        e,
                        true,
                        &timpures,
                        &impures,
                        &abs_counts,
                        settings,
                    ),
                );
            }
            Decl::ValRec(vis) => {
                let any_impure = vis.iter().any(|(_, _, _, e, _)| {
                    simple_impure(true, &timpures, &impures, &Env::empty(), e, settings)
                });
                if any_impure {
                    for (_, n, _, _, _) in vis {
                        impures.insert(*n);
                    }
                }
                for (_, n, _, e, _) in vis {
                    abs_counts.insert(
                        *n,
                        count_abs(
                            &Env::empty(),
                            e,
                            true,
                            &timpures,
                            &impures,
                            &abs_counts,
                            settings,
                        ),
                    );
                }
            }
            _ => {}
        }
    }

    // -----------------------------------------------------------------------
    // Use-count pass
    // -----------------------------------------------------------------------
    let mut uses: HashMap<usize, usize> = HashMap::new();
    for loc_decl in &decls {
        count_uses_in_decl(loc_decl, &mut uses);
    }

    // -----------------------------------------------------------------------
    // Build context
    // -----------------------------------------------------------------------
    let yanked_case = Cell::new(false);
    let ctx = ReduceCtx {
        timpures,
        impures,
        uses,
        yanked_case,
        full_mode,
    };

    // -----------------------------------------------------------------------
    // Reduction pass: process declarations sequentially
    // -----------------------------------------------------------------------
    let mut env = Env::empty();
    let new_decls: Vec<LocDecl> = decls
        .into_iter()
        .map(|loc_decl| {
            let span = loc_decl.span.clone();
            let new_node = reduce_decl(&mut env, loc_decl.node, &ctx, settings);
            Located::new(new_node, span)
        })
        .collect();

    let did_yank = ctx.yanked_case.get();
    ((new_decls, exports), did_yank)
}

/// Count uses of Named(n) in a declaration, accumulating into `uses`.
fn count_uses_in_decl(d: &LocDecl, uses: &mut HashMap<usize, usize>) {
    use crate::monomorphized::utilities::decl;
    let result = decl::fold(
        d,
        HashMap::<usize, usize>::new(),
        &|_, acc| acc,
        &|e, mut acc| {
            if let Exp::Named(n) = e {
                *acc.entry(*n).or_insert(0) += 1;
            }
            acc
        },
        &|_, acc| acc,
    );
    for (n, count) in result {
        *uses.entry(n).or_insert(0) += count;
    }
}

/// Reduce a single declaration, updating the environment.
fn reduce_decl(env: &mut Env, d: Decl, ctx: &ReduceCtx, settings: &Settings) -> Decl {
    match d {
        Decl::Datatype(dts) => {
            // Register datatypes in the environment
            for dt in &dts {
                *env = env.push_datatype(&dt.name, dt.id, dt.constrs.clone());
            }
            Decl::Datatype(dts)
        }

        Decl::Val(x, n, t, e, s) => {
            // Reduce the body
            let e_reduced = reduce_exp(env, e, ctx, settings);
            // Determine if we can inline this definition
            let cached = if may_inline(n, &e_reduced, &t, &s, ctx, settings) {
                Some(e_reduced.clone())
            } else {
                None
            };
            *env = env.push_named_opt(&x, n, t.clone(), cached, &s);
            Decl::Val(x, n, t, e_reduced, s)
        }

        Decl::ValRec(vis) => {
            // For recursive bindings: reduce each body, then register all
            // with no cached expression (recursive defs can't be naively inlined).
            let reduced_vis: Vec<(String, usize, LocTyp, LocExp, String)> = vis
                .into_iter()
                .map(|(x, n, t, e, s)| {
                    let e_reduced = reduce_exp(env, e, ctx, settings);
                    (x, n, t, e_reduced, s)
                })
                .collect();
            // Register all with no inlining
            for (x, n, t, _, s) in &reduced_vis {
                *env = env.push_named_opt(x, *n, t.clone(), None, s);
            }
            Decl::ValRec(reduced_vis)
        }

        // Other declarations: reduce expressions inside them
        Decl::Table(name, cols, pe, ce) => {
            let pe_r = reduce_exp(env, pe, ctx, settings);
            let ce_r = reduce_exp(env, ce, ctx, settings);
            Decl::Table(name, cols, pe_r, ce_r)
        }

        Decl::View(name, cols, e) => {
            let e_r = reduce_exp(env, e, ctx, settings);
            Decl::View(name, cols, e_r)
        }

        Decl::Task(e1, e2) => {
            let e1_r = reduce_exp(env, e1, ctx, settings);
            let e2_r = reduce_exp(env, e2, ctx, settings);
            Decl::Task(e1_r, e2_r)
        }

        Decl::Policy(pol) => {
            use crate::monomorphized::Policy;
            let pol_r = match pol {
                Policy::Client(e) => Policy::Client(reduce_exp(env, e, ctx, settings)),
                Policy::Insert(e) => Policy::Insert(reduce_exp(env, e, ctx, settings)),
                Policy::Delete(e) => Policy::Delete(reduce_exp(env, e, ctx, settings)),
                Policy::Update(e) => Policy::Update(reduce_exp(env, e, ctx, settings)),
                Policy::Sequence(e) => Policy::Sequence(reduce_exp(env, e, ctx, settings)),
            };
            Decl::Policy(pol_r)
        }

        // Leaf declarations (no sub-expressions)
        other => other,
    }
}

// ---------------------------------------------------------------------------
// reduce — public entry point (fixpoint loop)
// ---------------------------------------------------------------------------

/// Run the reduction pass to fixpoint.
///
/// If the "yanked case" optimisation fires, the entire pass is repeated
/// (since new beta-reduction opportunities may appear).
/// Bounded to prevent runaway mutants from looping forever.
const MAX_REDUCE_ITERATIONS: usize = 1000;

pub fn reduce(mut file: File, settings: &Settings) -> File {
    let full_mode = FULL_MODE.load(AtomicOrdering::Relaxed);
    let mut iterations = 0;
    loop {
        let (new_file, did_yank) = reduce_once(file, settings, full_mode);
        file = new_file;
        iterations += 1;
        if !did_yank || iterations >= MAX_REDUCE_ITERATIONS {
            return file;
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datatype_kind::DatatypeKind;
    use crate::error_types::Located;
    use crate::monomorphized::{DatatypeDef, DatatypeRef, Exp, Pat, Typ};
    use crate::primitives::Prim;
    use crate::settings::Settings;
    use std::sync::{Arc, Mutex};

    fn dummy_typ() -> LocTyp {
        Located::dummy(Typ::Ffi("Basis".into(), "int".into()))
    }

    fn prim_int(n: i64) -> LocExp {
        Located::dummy(Exp::Prim(Prim::Int(n)))
    }

    fn rel(n: usize) -> LocExp {
        Located::dummy(Exp::Rel(n))
    }

    fn mk_abs(x: &str, body: LocExp) -> LocExp {
        Located::dummy(Exp::Abs(
            x.to_string(),
            dummy_typ(),
            dummy_typ(),
            Box::new(body),
        ))
    }

    fn mk_let(x: &str, e1: LocExp, e2: LocExp) -> LocExp {
        Located::dummy(Exp::Let(
            x.to_string(),
            dummy_typ(),
            Box::new(e1),
            Box::new(e2),
        ))
    }

    fn mk_app(f: LocExp, arg: LocExp) -> LocExp {
        Located::dummy(Exp::App(Box::new(f), Box::new(arg)))
    }

    fn empty_file() -> File {
        (vec![], vec![])
    }

    #[test]
    fn test_empty_file() {
        let settings = Settings::new();
        let result = reduce(empty_file(), &settings);
        assert!(result.0.is_empty());
    }

    #[test]
    fn test_beta_reduction_simple() {
        // (fn x => x) 42  →  42
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let f = mk_abs("x", rel(0));
        let arg = prim_int(42);
        let app = mk_app(f, arg);
        let result = reduce_exp(&env, app, &ctx, &settings);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::Int(42))),
            "Expected Prim(42), got {:?}",
            result.node
        );
    }

    #[test]
    fn test_let_inlining_single_use() {
        // let x = 42 in x  →  42
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let e = mk_let("x", prim_int(42), rel(0));
        let result = reduce_exp(&env, e, &ctx, &settings);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::Int(42))),
            "Expected Prim(42), got {:?}",
            result.node
        );
    }

    #[test]
    fn test_strcat_constant_folding() {
        // "foo" ^ "bar"  →  "foobar"
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let e = Located::dummy(Exp::Strcat(
            Box::new(Located::dummy(Exp::Prim(Prim::String(
                StringMode::Normal,
                "foo".into(),
            )))),
            Box::new(Located::dummy(Exp::Prim(Prim::String(
                StringMode::Normal,
                "bar".into(),
            )))),
        ));
        let result = reduce_exp(&env, e, &ctx, &settings);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::String(StringMode::Normal, s)) if s == "foobar"),
            "Expected Prim(String(\"foobar\")), got {:?}",
            result.node
        );
    }

    #[test]
    fn test_strcat_html_both_stays_html() {
        // (Html "foo") ^ (Html "bar")  →  Html "foobar"
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let e = Located::dummy(Exp::Strcat(
            Box::new(Located::dummy(Exp::Prim(Prim::String(
                StringMode::Html,
                "foo".into(),
            )))),
            Box::new(Located::dummy(Exp::Prim(Prim::String(
                StringMode::Html,
                "bar".into(),
            )))),
        ));
        let result = reduce_exp(&env, e, &ctx, &settings);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::String(StringMode::Html, s)) if s == "foobar"),
            "Expected Html(\"foobar\"), got {:?}",
            result.node
        );
    }

    #[test]
    fn test_count_free_basic() {
        // Rel(0) in Rel(0) → 1
        let e = rel(0);
        assert_eq!(count_free(0, &e), 1);
        // Rel(1) in Rel(0) → 0
        assert_eq!(count_free(1, &e), 0);
    }

    #[test]
    fn test_count_free_under_binder() {
        // fn x => x  — count_free(0, e) should see Rel(0) shifts to Rel(1) under binder
        let e = mk_abs("x", rel(0));
        // The Abs introduces a binder, so Rel(0) inside = the Abs-bound var, not Rel(0) from outer
        assert_eq!(count_free(0, &e), 0); // Rel(0) from outer doesn't appear
                                          // Rel(1) from outer becomes the abs body's Rel(0)?
                                          // Actually: count_free(0, Abs(..., Rel(0))) = count_free(1, Rel(0)) = 0 (since 1 ≠ 0)
                                          // So free var tracking is correct.
    }

    #[test]
    fn test_passive_simple() {
        assert!(passive(&prim_int(42)));
        assert!(passive(&rel(0)));
        assert!(passive(&mk_abs("x", rel(0))));
        assert!(!passive(&mk_app(mk_abs("x", rel(0)), prim_int(1))));
    }

    #[test]
    fn test_signal_bind_signal_return() {
        // SignalBind(SignalReturn(e1), e2)  →  App(e2, e1)
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let e1 = prim_int(1);
        let e2 = mk_abs("y", rel(0)); // identity function
        let signal_bind = Located::dummy(Exp::SignalBind(
            Box::new(Located::dummy(Exp::SignalReturn(Box::new(e1.clone())))),
            Box::new(e2),
        ));
        let result = reduce_exp(&env, signal_bind, &ctx, &settings);
        // Should reduce to App(identity, 1) → 1
        assert!(
            matches!(&result.node, Exp::Prim(Prim::Int(1))),
            "Expected Prim(1) after SignalBind/SignalReturn reduction, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_field_record_projection() {
        // Field(Record([("x", 1), ("y", 2)]), "x")  →  1
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let record = Located::dummy(Exp::Record(vec![
            ("x".into(), prim_int(1), dummy_typ()),
            ("y".into(), prim_int(2), dummy_typ()),
        ]));
        let field = Located::dummy(Exp::Field(Box::new(record), "x".into()));
        let result = reduce_exp(&env, field, &ctx, &settings);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::Int(1))),
            "Expected Prim(1) from record projection, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_reduce_empty_decl_list() {
        let settings = Settings::new();
        let file: File = (vec![], vec![]);
        let result = reduce(file, &settings);
        assert!(result.0.is_empty());
        assert!(result.1.is_empty());
    }

    #[test]
    fn test_match_pat_var() {
        let p = Located::dummy(Pat::Var("x".into(), dummy_typ()));
        let e = prim_int(42);
        match match_pat(vec![], &p, &e) {
            MatchResult::Yes(subs) => {
                assert_eq!(subs.len(), 1);
                assert_eq!(subs[0].0, "x");
            }
            other => panic!("Expected Yes, got {:?}", other),
        }
    }

    #[test]
    fn test_match_pat_prim_equal() {
        let p = Located::dummy(Pat::Prim(Prim::Int(42)));
        let e = prim_int(42);
        match match_pat(vec![], &p, &e) {
            MatchResult::Yes(subs) => assert!(subs.is_empty()),
            other => panic!("Expected Yes, got {:?}", other),
        }
    }

    #[test]
    fn test_match_pat_prim_not_equal() {
        let p = Located::dummy(Pat::Prim(Prim::Int(1)));
        let e = prim_int(42);
        assert!(matches!(match_pat(vec![], &p, &e), MatchResult::No));
    }

    #[test]
    fn test_simple_type_impure_fun_true() {
        let t = Located::dummy(Typ::Fun(Box::new(dummy_typ()), Box::new(dummy_typ())));
        let timpures = HashSet::new();
        assert!(simple_type_impure(&t, &timpures));
    }

    #[test]
    fn test_simple_type_impure_ffi_false() {
        let t = dummy_typ();
        let timpures = HashSet::new();
        assert!(!simple_type_impure(&t, &timpures));
    }

    #[test]
    fn test_simple_type_impure_datatype_in_set() {
        let mut timpures = HashSet::new();
        timpures.insert(1);
        let dt_ref: DatatypeRef = Arc::new(Mutex::new(DatatypeDef {
            kind: DatatypeKind::Default,
            constrs: vec![],
        }));
        let t = Located::dummy(Typ::Datatype(1, dt_ref));
        assert!(simple_type_impure(&t, &timpures));
    }

    #[test]
    fn test_impure_rough_write_true() {
        let e = Located::dummy(Exp::Write(Box::new(prim_int(0))));
        assert!(impure_rough(&e));
    }

    #[test]
    fn test_impure_rough_prim_false() {
        assert!(!impure_rough(&prim_int(0)));
    }

    #[test]
    fn test_impure_rough_app_ffi_false() {
        let f = Located::dummy(Exp::Ffi("Basis".into(), "id".into()));
        let app = Located::dummy(Exp::App(Box::new(f), Box::new(prim_int(1))));
        assert!(!impure_rough(&app));
    }

    #[test]
    fn test_summarize_write_emits_write_page() {
        let e = Located::dummy(Exp::Write(Box::new(prim_int(0))));
        let evs = summarize(-1, &e);
        assert_eq!(evs.len(), 1);
        assert_eq!(evs[0], Event::WritePage);
    }

    #[test]
    fn test_summarize_prim_empty() {
        let evs = summarize(-1, &prim_int(0));
        assert!(evs.is_empty());
    }

    #[test]
    fn test_impure_rough_app_non_ffi_true() {
        let f = Located::dummy(Exp::Named(1));
        let app = Located::dummy(Exp::App(Box::new(f), Box::new(prim_int(0))));
        assert!(impure_rough(&app));
    }

    #[test]
    fn test_summarize_rel_emits_use_rel() {
        let e = rel(0);
        let evs = summarize(0, &e);
        assert_eq!(evs.len(), 1);
        assert_eq!(evs[0], Event::UseRel);
    }

    #[test]
    fn test_summarize_rel_d_mismatch_empty() {
        let e = rel(1);
        let evs = summarize(0, &e);
        assert!(evs.is_empty());
    }
}
