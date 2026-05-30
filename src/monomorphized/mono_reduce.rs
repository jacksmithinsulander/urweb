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

use crate::compiler_tracing::TRACING_TARGET_COMPILER_INTERNALS;
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
        Typ::Fun(..) | Typ::Transaction(..) => true,
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
///   bindings in pattern/source order. Case reduction applies them from
///   innermost binder outward to respect de Bruijn indexing.
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

/// Returns Some(disjoint_projection_paths) if Rel(i) in `e` is only accessed
/// via field projections, or None if it's used in any other context.
fn which_proj(i: usize, e: &LocExp) -> Option<HashSet<Vec<String>>> {
    match &e.node {
        Exp::Prim(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::Con(_, _, None) | Exp::None(_) => {
            Some(HashSet::new())
        }
        Exp::Rel(i_prime) => {
            if *i_prime == i {
                None
            } else {
                Some(HashSet::new())
            }
        }
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => which_proj(i, inner),
        Exp::FfiApp(_, _, args) => which_projs(i, args.iter().map(|(arg, _)| arg)),
        Exp::App(e1, e2)
        | Exp::Binop(_, _, e1, e2)
        | Exp::Strcat(e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::Setval(e1, e2)
        | Exp::SignalBind(e1, e2) => which_projs(i, [e1.as_ref(), e2.as_ref()]),
        Exp::Abs(_, _, _, body) => which_proj(i + 1, body),
        Exp::Unop(_, inner)
        | Exp::Error(inner, _)
        | Exp::Redirect(inner, _)
        | Exp::Write(inner)
        | Exp::Dml(inner, _)
        | Exp::Nextval(inner)
        | Exp::Uurlify(inner, _, _)
        | Exp::JavaScript(_, inner)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::ServerCall(inner, _, _, _)
        | Exp::Recv(inner, _)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner) => which_proj(i, inner),
        Exp::Record(fields) => which_projs(i, fields.iter().map(|(_, field_exp, _)| field_exp)),
        Exp::Field(inner, field) => match prefix_from(i, inner) {
            None => Some(HashSet::new()),
            Some(mut path) => {
                path.push(field.clone());
                Some(HashSet::from([path]))
            }
        },
        Exp::Case(disc, arms, _) => {
            let mut offset_exprs = Vec::with_capacity(arms.len() + 1);
            offset_exprs.push((0usize, disc.as_ref()));
            offset_exprs.extend(arms.iter().map(|(pat, arm)| (pat_binds_n(pat), arm)));
            which_projs_with_offsets(i, offset_exprs)
        }
        Exp::ReturnBlob {
            blob: None,
            mime_type,
            ..
        } => which_proj(i, mime_type),
        Exp::ReturnBlob {
            blob: Some(blob),
            mime_type,
            ..
        } => which_projs(i, [blob.as_ref(), mime_type.as_ref()]),
        Exp::Let(_, _, e1, e2) => {
            which_projs_with_offsets(i, [(0usize, e1.as_ref()), (1usize, e2.as_ref())])
        }
        Exp::Closure(_, envs) => which_projs(i, envs.iter()),
        Exp::Query(qm) => which_projs_with_offsets(
            i,
            [
                (0usize, qm.query.as_ref()),
                (2usize, qm.body.as_ref()),
                (0usize, qm.initial.as_ref()),
            ],
        ),
    }
}

fn prefix_from(i: usize, e: &LocExp) -> Option<Vec<String>> {
    match &e.node {
        Exp::Rel(i_prime) => (*i_prime == i).then(Vec::new),
        Exp::Field(inner, field) => {
            let mut path = prefix_from(i, inner)?;
            path.push(field.clone());
            Some(path)
        }
        _ => None,
    }
}

fn which_projs<'a, I>(i: usize, exprs: I) -> Option<HashSet<Vec<String>>>
where
    I: IntoIterator<Item = &'a LocExp>,
{
    which_projs_with_offsets(i, exprs.into_iter().map(|expr| (0usize, expr)))
}

fn which_projs_with_offsets<'a, I>(i: usize, exprs: I) -> Option<HashSet<Vec<String>>>
where
    I: IntoIterator<Item = (usize, &'a LocExp)>,
{
    let mut seen = HashSet::new();
    for (offset, expr) in exprs {
        let paths = which_proj(i + offset, expr)?;
        if !seen.is_disjoint(&paths) {
            return None;
        }
        seen.extend(paths);
    }
    Some(seen)
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

fn references_any_named(e: &LocExp, ids: &HashSet<usize>) -> bool {
    crate::monomorphized::utilities::exp::exists(e, &|_| false, &|node| match node {
        Exp::Named(n) => ids.contains(n),
        _ => false,
    })
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
        Typ::Transaction(ran) => function_inside(ran),
        _ => function_inside_prime(t),
    }
}

fn function_inside_prime(t: &LocTyp) -> bool {
    use crate::monomorphized::utilities::typ;
    typ::exists(t, &|node| {
        matches!(node, Typ::Fun(..) | Typ::Transaction(..))
    })
}

fn query_row_type(qm: &QueryMeta, span: &Span) -> LocTyp {
    let mut fields = qm.exps.clone();
    fields.extend(qm.tables.iter().map(|(table, xts)| {
        (
            table.clone(),
            Located::new(Typ::Record(xts.clone()), span.clone()),
        )
    }));
    Located::new(Typ::Record(fields), span.clone())
}

fn function_like_parts(t: &LocTyp) -> Option<(LocTyp, LocTyp)> {
    match &t.node {
        Typ::Fun(dom, ran) => Some((*dom.clone(), *ran.clone())),
        _ => None,
    }
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
            let row_t = query_row_type(&qm, &span);
            let query_r = reduce_exp(env, *qm.query, ctx, settings);
            // Query body has two extra bindings (row, accumulator)
            let body_env = env.push_rel("r", row_t).push_rel("acc", qm.state.clone());
            let mut body_r = reduce_exp(&body_env, *qm.body, ctx, settings);
            if function_like_parts(&qm.state).is_none() {
                if let Exp::Abs(_, dom, ran, _) = &body_r.node {
                    if is_unit_record_type(dom)
                        && function_like_parts(ran).is_none()
                        && crate::monomorphized::utilities::typ::compare(ran, &qm.state)
                            == std::cmp::Ordering::Equal
                    {
                        let forced = Located::new(
                            Exp::App(
                                Box::new(body_r),
                                Box::new(Located::new(Exp::Record(Vec::new()), span.clone())),
                            ),
                            span.clone(),
                        );
                        body_r = reduce_exp(&body_env, forced, ctx, settings);
                    }
                }
            }
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
        Exp::Field(inner, x) => {
            let (original_head, original_args) = strip_app_spine((*inner).clone());
            let preserve_receiver_shape =
                matches!(inner.node, Exp::App(_, _)) && app_head_is_projected_abs(&original_head);
            debug_mono_reduce_field_child(
                env,
                &span,
                &x,
                inner.as_ref(),
                &original_head,
                &original_args,
                preserve_receiver_shape,
            );
            let inner_r = if preserve_receiver_shape {
                *inner
            } else {
                reduce_exp(env, *inner, ctx, settings)
            };
            Exp::Field(Box::new(inner_r), x)
        }
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
            if let Some(stripped) = strip_spurious_unit_app_in_env(env, (*f).clone(), arg.as_ref())
            {
                debug_mono_reduce_rule(span, "strip_spurious_unit_app");
                return reduce_exp(env, stripped, ctx, settings).node;
            }
            if let Exp::Field(inner, _) = f.node.clone() {
                if let Exp::Field(base, missing_field) = inner.node.clone() {
                    if let Exp::Abs(_, _, ran, _) = base.node.clone() {
                        if direct_field_result_typ(&ran, &missing_field).is_none() {
                            return Exp::App(f, arg);
                        }
                    }
                }
            }
            if let Exp::App(f2, arg1) = f.node.clone() {
                if let Exp::Field(base, missing_field) = f2.node.clone() {
                    if let Exp::Abs(_, _, ran, _) = base.node.clone() {
                        if direct_field_result_typ(&ran, &missing_field).is_none()
                            && mono_exp_has_direct_field_in_env(env, arg.as_ref(), &missing_field)
                        {
                            debug_mono_reduce_rule(
                                span,
                                "redirect_nested_missing_field_to_tail_arg",
                            );
                            let projected = Located::new(
                                Exp::Field(Box::new((*arg).clone()), missing_field.clone()),
                                f2.span.clone(),
                            );
                            let redirected =
                                reapply_single_arg_if_function_like_in_env(env, projected, *arg1);
                            return reduce_exp(env, redirected, ctx, settings).node;
                        }
                        if direct_field_result_typ(&ran, &missing_field).is_none()
                            && mono_exp_has_direct_field_in_env(env, arg1.as_ref(), &missing_field)
                        {
                            debug_mono_reduce_rule(
                                span,
                                "redirect_nested_missing_field_to_earlier_arg",
                            );
                            let projected = Located::new(
                                Exp::Field(Box::new((*arg1).clone()), missing_field.clone()),
                                f2.span.clone(),
                            );
                            let redirected = reapply_single_arg_if_function_like_in_env(
                                env,
                                projected,
                                (*arg).clone(),
                            );
                            return reduce_exp(env, redirected, ctx, settings).node;
                        }
                    }
                }
                if let Exp::Field(inner, subfield) = f2.node.clone() {
                    if let Exp::Field(base, missing_field) = inner.node.clone() {
                        if let Exp::Abs(_, _, ran, _) = base.node.clone() {
                            if direct_field_result_typ(&ran, &missing_field).is_none()
                                && mono_exp_has_direct_field_in_env(
                                    env,
                                    arg.as_ref(),
                                    &missing_field,
                                )
                            {
                                debug_mono_reduce_rule(
                                    span,
                                    "redirect_nested_subfield_to_tail_arg",
                                );
                                let projected = Located::new(
                                    Exp::Field(
                                        Box::new(Located::new(
                                            Exp::Field(
                                                Box::new((*arg).clone()),
                                                missing_field.clone(),
                                            ),
                                            inner.span.clone(),
                                        )),
                                        subfield.clone(),
                                    ),
                                    f2.span.clone(),
                                );
                                let redirected = reapply_single_arg_if_function_like_in_env(
                                    env, projected, *arg1,
                                );
                                return reduce_exp(env, redirected, ctx, settings).node;
                            }
                            if direct_field_result_typ(&ran, &missing_field).is_none()
                                && mono_exp_has_direct_field_in_env(
                                    env,
                                    arg1.as_ref(),
                                    &missing_field,
                                )
                            {
                                debug_mono_reduce_rule(
                                    span,
                                    "redirect_nested_subfield_to_earlier_arg",
                                );
                                let projected = Located::new(
                                    Exp::Field(
                                        Box::new(Located::new(
                                            Exp::Field(
                                                Box::new((*arg1).clone()),
                                                missing_field.clone(),
                                            ),
                                            inner.span.clone(),
                                        )),
                                        subfield.clone(),
                                    ),
                                    f2.span.clone(),
                                );
                                let redirected = reapply_single_arg_if_function_like_in_env(
                                    env,
                                    projected,
                                    (*arg).clone(),
                                );
                                return reduce_exp(env, redirected, ctx, settings).node;
                            }
                        }
                    }
                }
            }
            if let Exp::Abs(x, t, _, body) = f.node.clone() {
                debug_mono_reduce_beta(span, f.as_ref(), arg.as_ref(), body.as_ref());
                if is_erased_witness_app(&arg, &t) {
                    let subst = sub_exp_in_exp(0, &arg, &body);
                    return reduce_exp(env, subst, ctx, settings).node;
                }
                // Beta reduction
                let impure_arg = impure_ctx(env, &arg, ctx, settings);
                let cf = count_free(0, &body);
                let multi_use = !ctx.full_mode && cf > 1;
                tracing::debug!(
                    target: TRACING_TARGET_COMPILER_INTERNALS,
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
            } else if let Exp::Case(disc, arms, meta) = f.node.clone() {
                let is_unit_arg = matches!(&arg.node, Exp::Record(fields) if fields.is_empty());
                let disc_is_thunk = matches!(&disc.node, Exp::Abs(_, _, _, _));
                let case_result_is_not_function = function_like_parts(&meta.result).is_none();

                if is_unit_arg && disc_is_thunk && case_result_is_not_function {
                    let forced_disc =
                        Located::new(Exp::App(disc, Box::new((*arg).clone())), span.clone());
                    let repaired_case =
                        Located::new(Exp::Case(Box::new(forced_disc), arms, meta), span.clone());
                    reduce_exp(env, repaired_case, ctx, settings).node
                } else {
                    Exp::App(f, arg)
                }
            } else if let Exp::Field(inner, field) = f.node.clone() {
                if let Exp::Abs(_, _, ran, _) = inner.node.clone() {
                    if direct_field_result_typ(&ran, &field).is_none()
                        && mono_exp_has_direct_field_in_env(env, arg.as_ref(), &field)
                    {
                        debug_mono_reduce_rule(span, "redirect_simple_missing_field_to_arg");
                        let projected = Located::new(
                            Exp::Field(Box::new((*arg).clone()), field),
                            f.span.clone(),
                        );
                        return reduce_exp(env, projected, ctx, settings).node;
                    }
                }
                let applied_inner = Located::new(
                    Exp::App(inner.clone(), Box::new((*arg).clone())),
                    f.span.clone(),
                );
                if matches!(
                    &inner.node,
                    Exp::Abs(_, _, _, _)
                        | Exp::App(_, _)
                        | Exp::Field(_, _)
                        | Exp::Record(_)
                        | Exp::Let(_, _, _, _)
                ) && !mono_exp_has_direct_field_in_env(env, &inner, &field)
                    && mono_exp_has_direct_field_in_env(env, &applied_inner, &field)
                {
                    debug_mono_reduce_app_push(
                        env,
                        span,
                        &field,
                        &inner,
                        &applied_inner,
                        arg.as_ref(),
                    );
                    debug_mono_reduce_rule(span, "push_app_through_missing_field_projection");
                    let pushed =
                        Located::new(Exp::Field(Box::new(applied_inner), field), span.clone());
                    reduce_exp(env, pushed, ctx, settings).node
                } else {
                    Exp::App(f, arg)
                }
            } else if let Exp::Record(fields) = f.node.clone() {
                if impure_ctx(env, &arg, ctx, settings) {
                    Exp::App(f, arg)
                } else if fields
                    .iter()
                    .all(|(_, _, field_t)| function_like_parts(field_t).is_some())
                {
                    let applied_fields = fields
                        .into_iter()
                        .map(|(name, field_exp, field_t)| {
                            let (_, field_ran) = function_like_parts(&field_t)
                                .expect("function-like fields prechecked above");
                            let applied = Located::new(
                                Exp::App(Box::new(field_exp), Box::new((*arg).clone())),
                                span.clone(),
                            );
                            (name, reduce_exp(env, applied, ctx, settings), field_ran)
                        })
                        .collect();
                    Exp::Record(applied_fields)
                } else {
                    Exp::App(f, arg)
                }
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

        // Repair a malformed nested unit thunk:
        //   fn _ : {} => (fn _ : {} => e)
        // when both thunk layers claim the same result type.
        Exp::Abs(x, dom, ran, body_box) => {
            if is_unit_record_type(&dom) {
                if let Exp::Abs(_, inner_dom, inner_ran, inner_body) = body_box.node.clone() {
                    if is_unit_record_type(&inner_dom)
                        && crate::monomorphized::utilities::typ::compare(&ran, &inner_ran)
                            == std::cmp::Ordering::Equal
                        && count_free(0, &inner_body) == 0
                    {
                        debug_mono_reduce_rule(span, "collapse_nested_unit_thunk");
                        let unit = Located::new(Exp::Record(Vec::new()), span.clone());
                        let collapsed = sub_exp_in_exp(0, &unit, &inner_body);
                        let env2 = env.push_rel(&x, dom.clone());
                        let collapsed = reduce_exp(&env2, collapsed, ctx, settings);
                        return Exp::Abs(x, dom, ran, Box::new(collapsed));
                    }
                }
            }
            Exp::Abs(x, dom, ran, body_box)
        }

        // ----------------------------------------------------------------
        // Field(e1, x) → yankLets optimization
        // ----------------------------------------------------------------
        Exp::Field(e1, x) => {
            let (head, args) = strip_app_spine(*e1);
            debug_mono_reduce_field(env, &span, &x, &head, &args);
            if !args.is_empty() && mono_exp_has_direct_field_in_env(env, &head, &x) {
                debug_mono_reduce_rule(span, "project_head_before_reapply");
                let projected_head =
                    Located::new(Exp::Field(Box::new(head), x.clone()), span.clone());
                return reduce_exp(env, reapply_app_spine(projected_head, args), ctx, settings)
                    .node;
            }
            match head.node {
                Exp::Record(fields) => {
                    if let Some((_, projected, _)) = fields.iter().find(|(name, _, _)| name == &x) {
                        debug_mono_reduce_rule(span, "project_record_field");
                        return reduce_exp(
                            env,
                            reapply_app_spine(projected.clone(), args),
                            ctx,
                            settings,
                        )
                        .node;
                    }
                    if let Some(projected_tail) =
                        project_missing_field_from_args_in_env(env, &args, &x, span)
                    {
                        debug_mono_reduce_rule(span, "project_record_missing_field_from_args");
                        return reduce_exp(env, projected_tail, ctx, settings).node;
                    }
                    yank_lets(Located::new(Exp::Record(fields), head.span), &x)
                }
                Exp::Abs(ax, dom, ran, body) => {
                    if function_like_parts(&ran).is_some() {
                        if let Some(projected_tail) =
                            project_missing_field_from_args_in_env(env, &args, &x, span)
                        {
                            debug_mono_reduce_rule(span, "project_abs_missing_field_from_args");
                            return reduce_exp(env, projected_tail, ctx, settings).node;
                        }
                    }

                    if let Some(projected_ran) = direct_field_result_typ(&ran, &x) {
                        debug_mono_reduce_rule(span, "push_field_through_abs");
                        let projected_body =
                            Located::new(Exp::Field(body, x.clone()), span.clone());
                        let projected_abs = Located::new(
                            Exp::Abs(ax, dom, projected_ran, Box::new(projected_body)),
                            span.clone(),
                        );
                        return reduce_exp(
                            env,
                            reapply_app_spine(projected_abs, args),
                            ctx,
                            settings,
                        )
                        .node;
                    }

                    if let Some(projected_tail) =
                        project_missing_field_from_args_in_env(env, &args, &x, span)
                    {
                        debug_mono_reduce_rule(span, "project_abs_field_from_args_fallback");
                        return reduce_exp(env, projected_tail, ctx, settings).node;
                    }

                    yank_lets(
                        reapply_app_spine(
                            Located::new(Exp::Abs(ax, dom, ran, body), head.span.clone()),
                            args,
                        ),
                        &x,
                    )
                }
                other => yank_lets(reapply_app_spine(Located::new(other, head.span), args), &x),
            }
        }

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
            // Let(x, t, (fn _ : {} => e'), body) when t is a plain value
            //   → Let(x, t, (fn _ : {} => e') {}, body)
            // ----------------------------------------------------------------
            if let Exp::Abs(_, dom, ran, _) = e1_box.node.clone() {
                if is_unit_record_type(&dom)
                    && !matches!(&t1.node, Typ::Fun(_, _) | Typ::Transaction(_))
                    && crate::monomorphized::utilities::typ::compare(&ran, &t1)
                        == std::cmp::Ordering::Equal
                {
                    let forced = Located::new(
                        Exp::App(
                            Box::new((*e1_box).clone()),
                            Box::new(Located::new(Exp::Record(Vec::new()), span.clone())),
                        ),
                        span.clone(),
                    );
                    let repaired = Located::new(
                        Exp::Let(x1.clone(), t1.clone(), Box::new(forced), b2_box.clone()),
                        span.clone(),
                    );
                    return reduce_exp(env, repaired, ctx, settings).node;
                }
            }

            // ----------------------------------------------------------------
            // Let(x, t, e', Abs(x', unit_record_t, ran, e'')) when e' is pure
            //   → Abs(x', unit_record_t, ran, Let(x, t, lift(e'), swap(e'')))
            // ----------------------------------------------------------------
            if let Exp::Abs(x2, t2, ran2, body2) = b2_box.node.clone() {
                if is_unit_record_type(&t2)
                    && function_like_parts(&ran2).is_none()
                    && !impure_ctx(env, &e1_box, ctx, settings)
                {
                    debug_mono_reduce_rule(span, "commute_let_into_unit_abs");
                    debug_mono_reduce_unit_let(span, &t1, &e1_box, &ran2, &body2);
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

fn is_erased_witness_app(arg: &LocExp, dom: &LocTyp) -> bool {
    is_erased_proof_arg(arg)
        && match &dom.node {
            Typ::Record(fields) if fields.is_empty() => false,
            Typ::Ffi(module, name) if module == "Basis" && name == "int" => false,
            _ => true,
        }
}

fn direct_field_result_typ(result_typ: &LocTyp, field: &str) -> Option<LocTyp> {
    match &result_typ.node {
        Typ::Record(fields) => fields
            .iter()
            .find(|(name, _)| name == field)
            .map(|(_, typ)| typ.clone()),
        _ => None,
    }
}

fn drop_applied_fun_layers(t: &LocTyp, args_applied: usize) -> Option<LocTyp> {
    let mut current = t.clone();
    for _ in 0..args_applied {
        match current.node {
            Typ::Fun(_, ran) => current = *ran,
            _ => return None,
        }
    }
    Some(current)
}

fn mono_exp_result_typ_in_env(env: &Env, e: &LocExp) -> Option<LocTyp> {
    match &e.node {
        Exp::Prim(prim) => Some(Located::new(
            Typ::Ffi(
                "Basis".into(),
                match prim {
                    Prim::Int(_) => "int",
                    Prim::Float(_) => "float",
                    Prim::String(_, _) => "string",
                    Prim::Char(_) => "char",
                }
                .into(),
            ),
            e.span.clone(),
        )),
        Exp::Rel(n) => env.lookup_rel(*n).ok().map(|(_, typ, _)| typ.clone()),
        Exp::Named(n) => env.lookup_named(*n).ok().map(|(_, typ, _, _)| typ.clone()),
        Exp::Record(fields) => Some(Located::new(
            Typ::Record(
                fields
                    .iter()
                    .map(|(name, _, typ)| (name.clone(), typ.clone()))
                    .collect(),
            ),
            e.span.clone(),
        )),
        Exp::Abs(_, dom, ran, _) => Some(Located::new(
            Typ::Fun(Box::new(dom.clone()), Box::new(ran.clone())),
            e.span.clone(),
        )),
        Exp::Let(_, _, _, body) => mono_exp_result_typ_in_env(env, body),
        Exp::Field(inner, projected) => {
            mono_exp_result_typ_in_env(env, inner).and_then(|typ| match &typ.node {
                Typ::Record(fields) => fields
                    .iter()
                    .find(|(name, _)| name == projected)
                    .map(|(_, field_typ)| field_typ.clone()),
                _ => None,
            })
        }
        Exp::App(_, _) => {
            let (head, args) = strip_app_spine(e.clone());
            mono_exp_result_typ_in_env(env, &head)
                .and_then(|typ| drop_applied_fun_layers(&typ, args.len()))
        }
        _ => None,
    }
}

fn strip_app_spine(mut e: LocExp) -> (LocExp, Vec<LocExp>) {
    let mut rev_args = Vec::new();
    loop {
        let span = e.span.clone();
        match e.node {
            Exp::App(f, arg) => {
                rev_args.push(*arg);
                e = *f;
            }
            other => {
                rev_args.reverse();
                return (Located::new(other, span), rev_args);
            }
        }
    }
}

fn reapply_app_spine(mut head: LocExp, args: Vec<LocExp>) -> LocExp {
    for arg in args {
        let span = head.span.clone();
        head = Located::new(Exp::App(Box::new(head), Box::new(arg)), span);
    }
    head
}

fn reapply_single_arg_if_function_like_in_env(env: &Env, head: LocExp, arg: LocExp) -> LocExp {
    let Some(head_typ) = mono_exp_result_typ_in_env(env, &head) else {
        return head;
    };
    let Some((dom, _)) = function_like_parts(&head_typ) else {
        return head;
    };

    // When we redirected a missing-field projection onto a later row argument,
    // the earlier partially-applied argument may actually be a continuation
    // lambda (for the next row parameter), not an argument for the projected
    // field itself. Reapplying it blindly recreates malformed terms like
    // `cols.A.Show (fn r2 => ...)`.
    if mono_exp_result_typ_in_env(env, &arg)
        .is_some_and(|arg_typ| function_like_parts(&arg_typ).is_some())
        && function_like_parts(&dom).is_none()
    {
        return head;
    }

    let span = head.span.clone();
    Located::new(Exp::App(Box::new(head), Box::new(arg)), span)
}

fn is_unit_record_exp(e: &LocExp) -> bool {
    matches!(&e.node, Exp::Record(fields) if fields.is_empty())
}

fn strip_spurious_unit_app_in_env(env: &Env, function: LocExp, arg: &LocExp) -> Option<LocExp> {
    if !is_unit_record_exp(arg) {
        return None;
    }

    let result_typ = mono_exp_result_typ_in_env(env, &function)?;
    (function_like_parts(&result_typ).is_none()).then_some(function)
}

fn is_erased_proof_arg(e: &LocExp) -> bool {
    matches!(&e.node, Exp::Record(fields) if fields.is_empty())
        || matches!(&e.node, Exp::Prim(Prim::Int(0)))
}

fn mono_exp_has_direct_field_in_env(env: &Env, e: &LocExp, field: &str) -> bool {
    mono_exp_result_typ_in_env(env, e).is_some_and(|typ| match &typ.node {
        Typ::Record(fields) => fields.iter().any(|(name, _)| name == field),
        _ => false,
    })
}

fn debug_mono_reduce_field(env: &Env, span: &Span, field: &str, head: &LocExp, args: &[LocExp]) {
    if std::env::var("URWEB_DEBUG_MONO_REDUCE_FIELD")
        .ok()
        .as_deref()
        != Some("1")
    {
        return;
    }
    if !(span.file.ends_with("/lib/ur/top.ur") || span.file.ends_with("/demo/crud.ur")) {
        return;
    }
    let head_typ = mono_exp_result_typ_in_env(env, head)
        .map(|typ| format!("{:?}", typ.node))
        .unwrap_or_else(|| "<unknown>".to_string());
    let arg_summaries = args
        .iter()
        .map(|arg| {
            let typ = mono_exp_result_typ_in_env(env, arg)
                .map(|typ| format!("{:?}", typ.node))
                .unwrap_or_else(|| "<unknown>".to_string());
            format!("{:?}:{typ}", arg.node)
        })
        .collect::<Vec<_>>()
        .join(" | ");
    eprintln!(
        "URWEB_DEBUG_MONO_REDUCE_FIELD {}:{} field={} head={:?} head_typ={} args=[{}]",
        span.file, span.first.line, field, head.node, head_typ, arg_summaries
    );
}

fn debug_mono_reduce_field_child(
    env: &Env,
    span: &Span,
    field: &str,
    inner: &LocExp,
    head: &LocExp,
    args: &[LocExp],
    preserved: bool,
) {
    if std::env::var("URWEB_DEBUG_MONO_REDUCE_FIELD_CHILD")
        .ok()
        .as_deref()
        != Some("1")
    {
        return;
    }
    if !(span.file.ends_with("/lib/ur/top.ur") || span.file.ends_with("/demo/crud.ur")) {
        return;
    }
    let head_typ = mono_exp_result_typ_in_env(env, head)
        .map(|typ| format!("{:?}", typ.node))
        .unwrap_or_else(|| "<unknown>".to_string());
    eprintln!(
        "URWEB_DEBUG_MONO_REDUCE_FIELD_CHILD {}:{} field={} inner_kind={} head_kind={} args_len={} preserved={} head_typ={} inner={:?}",
        span.file,
        span.first.line,
        field,
        exp_kind(inner),
        exp_kind(head),
        args.len(),
        preserved,
        head_typ,
        inner.node,
    );
}

fn debug_mono_reduce_recover(
    span: &Span,
    field: &str,
    idx: usize,
    receiver: &LocExp,
    args: &[LocExp],
) {
    if std::env::var("URWEB_DEBUG_MONO_REDUCE_FIELD")
        .ok()
        .as_deref()
        != Some("1")
    {
        return;
    }
    if !(span.file.ends_with("/lib/ur/top.ur") || span.file.ends_with("/demo/crud.ur")) {
        return;
    }
    let arg_summaries = args
        .iter()
        .map(|arg| format!("{:?}", arg.node))
        .collect::<Vec<_>>()
        .join(" | ");
    eprintln!(
        "URWEB_DEBUG_MONO_REDUCE_RECOVER {}:{} field={} idx={} receiver={:?} args=[{}]",
        span.file, span.first.line, field, idx, receiver.node, arg_summaries
    );
}

fn exp_kind(e: &LocExp) -> &'static str {
    match &e.node {
        Exp::Rel(_) => "Rel",
        Exp::Named(_) => "Named",
        Exp::Abs(_, _, _, _) => "Abs",
        Exp::App(_, _) => "App",
        Exp::Field(_, _) => "Field",
        Exp::Record(_) => "Record",
        Exp::Let(_, _, _, _) => "Let",
        Exp::Case(_, _, _) => "Case",
        Exp::Prim(_) => "Prim",
        _ => "Other",
    }
}

fn debug_mono_reduce_app_push(
    env: &Env,
    span: &Span,
    field: &str,
    inner: &LocExp,
    applied_inner: &LocExp,
    arg: &LocExp,
) {
    if std::env::var("URWEB_DEBUG_MONO_REDUCE_APP").ok().as_deref() != Some("1") {
        return;
    }
    if !(span.file.ends_with("/lib/ur/top.ur") || span.file.ends_with("/demo/crud.ur")) {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_MONO_REDUCE_APP {}:{} rule=push field={} inner_kind={} inner_has={} applied_kind={} applied_has={} arg_kind={} arg_has={}",
        span.file,
        span.first.line,
        field,
        exp_kind(inner),
        mono_exp_has_direct_field_in_env(env, inner, field),
        exp_kind(applied_inner),
        mono_exp_has_direct_field_in_env(env, applied_inner, field),
        exp_kind(arg),
        mono_exp_has_direct_field_in_env(env, arg, field),
    );
}

fn debug_mono_reduce_rule(span: &Span, rule: &str) {
    if std::env::var("URWEB_DEBUG_MONO_REDUCE_RULES")
        .ok()
        .as_deref()
        != Some("1")
    {
        return;
    }
    if !(span.file.ends_with("/lib/ur/top.ur") || span.file.ends_with("/demo/crud.ur")) {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_MONO_REDUCE_RULE {}:{} rule={}",
        span.file, span.first.line, rule
    );
}

fn debug_mono_reduce_unit_let(
    span: &Span,
    t1: &LocTyp,
    e1: &LocExp,
    ran2: &LocTyp,
    body2: &LocExp,
) {
    if std::env::var("URWEB_DEBUG_MONO_REDUCE_UNIT_LET")
        .ok()
        .as_deref()
        != Some("1")
    {
        return;
    }
    if !span.file.ends_with("/lib/ur/top.ur") {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_MONO_REDUCE_UNIT_LET {}:{} bind_typ={:?} bind_exp={:?} abs_ran={:?} abs_body={:?}",
        span.file,
        span.first.line,
        t1.node,
        e1.node,
        ran2.node,
        body2.node
    );
}

fn debug_mono_reduce_beta(span: &Span, f: &LocExp, arg: &LocExp, body: &LocExp) {
    if std::env::var("URWEB_DEBUG_MONO_REDUCE_BETA")
        .ok()
        .as_deref()
        != Some("1")
    {
        return;
    }
    if !span.file.ends_with("/lib/ur/top.ur") || !(153..=157).contains(&span.first.line) {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_MONO_REDUCE_BETA {}:{} fun={:?} arg={:?} body={:?}",
        span.file, span.first.line, f.node, arg.node, body.node
    );
}

fn app_head_is_projected_abs(head: &LocExp) -> bool {
    match &head.node {
        Exp::Abs(_, _, _, _) => true,
        Exp::Field(inner, _) => {
            matches!(inner.node, Exp::Abs(_, _, _, _))
                || matches!(&inner.node, Exp::Field(inner2, _) if matches!(inner2.node, Exp::Abs(_, _, _, _)))
        }
        _ => false,
    }
}

fn project_missing_field_from_args_in_env(
    env: &Env,
    args: &[LocExp],
    field: &str,
    span: &Span,
) -> Option<LocExp> {
    let direct_match = (0..args.len()).rev().find_map(|idx| {
        let arg = &args[idx];
        if is_erased_proof_arg(arg) || !mono_exp_has_direct_field_in_env(env, arg, field) {
            return None;
        }
        Some((idx, arg.clone()))
    });
    let fallback_match = (0..args.len()).rev().find_map(|idx| {
        let arg = &args[idx];
        if is_erased_proof_arg(arg) || mono_exp_has_direct_field_in_env(env, arg, field) {
            return None;
        }
        let receiver = reapply_app_spine(arg.clone(), args[idx + 1..].to_vec());
        mono_exp_has_direct_field_in_env(env, &receiver, field).then_some((idx, receiver))
    });
    let (idx, receiver) = direct_match.or(fallback_match)?;
    debug_mono_reduce_recover(span, field, idx, &receiver, args);
    Some(Located::new(
        Exp::Field(Box::new(receiver), field.to_string()),
        span.clone(),
    ))
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
    if let Some((dom, result_t)) = function_like_parts(&meta.result) {
        let dom = Box::new(dom);
        let result_t = Box::new(result_t);

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
                            if let Some((_, inner_t)) = function_like_parts(&err_t) {
                                Located::new(Exp::Error(msg, inner_t), ae_span.clone())
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

                for (sx, st, se) in subs.into_iter().rev() {
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

    let rhs_is_abs = matches!(&e_prime.node, Exp::Abs(_, _, _, _));
    let uses = count_free(0, &b);
    let rhs_impure = impure_ctx(env, &e_prime, ctx, settings);

    if rhs_is_abs && uses == 1 {
        return do_sub(&e_prime, &b);
    }

    if rhs_impure {
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
            // with cached expressions only for members that don't actually
            // reference any definition from the recursive group.
            let reduced_vis: Vec<(String, usize, LocTyp, LocExp, String)> = vis
                .into_iter()
                .map(|(x, n, t, e, s)| {
                    let e_reduced = reduce_exp(env, e, ctx, settings);
                    (x, n, t, e_reduced, s)
                })
                .collect();
            let group_ids: HashSet<usize> = reduced_vis.iter().map(|(_, n, _, _, _)| *n).collect();
            for (x, n, t, e, s) in &reduced_vis {
                let cached = if !references_any_named(e, &group_ids)
                    && may_inline(*n, e, t, s, ctx, settings)
                {
                    Some(e.clone())
                } else {
                    None
                };
                *env = env.push_named_opt(x, *n, t.clone(), cached, s);
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
    for _ in 0..MAX_REDUCE_ITERATIONS {
        let (new_file, did_yank) = reduce_once(file, settings, full_mode);
        file = new_file;
        if !did_yank {
            return file;
        }
    }
    file
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
    fn test_beta_reduction_drops_erased_witness_binder_before_runtime_arg() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let span = Span::dummy();
        let meta_t = Located::new(
            Typ::Record(vec![("NewState".into(), dummy_typ())]),
            span.clone(),
        );
        let body = Located::new(
            Exp::Abs(
                "row".into(),
                meta_t.clone(),
                dummy_typ(),
                Box::new(Located::new(
                    Exp::Field(
                        Box::new(Located::new(Exp::Rel(0), span.clone())),
                        "NewState".into(),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let app = Located::new(
            Exp::App(
                Box::new(Located::new(
                    Exp::Abs("m".into(), meta_t, dummy_typ(), Box::new(body)),
                    span.clone(),
                )),
                Box::new(Located::new(Exp::Record(vec![]), span.clone())),
            ),
            span,
        );

        let result = reduce_exp(&env, app, &ctx, &settings);
        assert!(
            matches!(
                result.node,
                Exp::Abs(_, _, _, ref body)
                    if matches!(
                        body.node,
                        Exp::Field(ref inner, ref name)
                            if name == "NewState"
                                && matches!(inner.node, Exp::Rel(0))
                    )
            ),
            "Expected erased witness binder to be dropped before runtime arg, got {:?}",
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
    fn test_field_projection_through_curried_abs() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let unit_t = Located::dummy(Typ::Record(vec![]));
        let int_t = dummy_typ();
        let record_t = Located::dummy(Typ::Record(vec![("Inject".into(), int_t.clone())]));
        let unit_e = Located::dummy(Exp::Record(vec![]));
        let outer = Located::dummy(Exp::Abs(
            "_".into(),
            unit_t.clone(),
            Located::dummy(Typ::Fun(
                Box::new(unit_t.clone()),
                Box::new(record_t.clone()),
            )),
            Box::new(Located::dummy(Exp::Abs(
                "_".into(),
                unit_t.clone(),
                record_t,
                Box::new(Located::dummy(Exp::Record(vec![(
                    "Inject".into(),
                    prim_int(13),
                    int_t.clone(),
                )]))),
            ))),
        ));
        let field = Located::dummy(Exp::Field(Box::new(outer), "Inject".into()));
        let applied = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(field),
                Box::new(unit_e.clone()),
            ))),
            Box::new(unit_e),
        ));

        let result = reduce_exp(&env, applied, &ctx, &settings);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::Int(13))),
            "Expected Prim(13) after curried field projection, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_record_of_functions_distributes_application() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let int_t = dummy_typ();
        let fn_t = Located::dummy(Typ::Fun(Box::new(int_t.clone()), Box::new(int_t.clone())));
        let record = Located::dummy(Exp::Record(vec![(
            "Inject".into(),
            Located::dummy(Exp::Abs(
                "x".into(),
                int_t.clone(),
                int_t.clone(),
                Box::new(Located::dummy(Exp::Rel(0))),
            )),
            fn_t,
        )]));
        let applied = Located::dummy(Exp::App(Box::new(record), Box::new(prim_int(21))));

        let result = reduce_exp(&env, applied, &ctx, &settings);
        match result.node {
            Exp::Record(fields) => {
                assert!(matches!(fields[0].1.node, Exp::Prim(Prim::Int(21))));
            }
            other => panic!(
                "Expected record fields to receive distributed application, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_field_projection_falls_through_concat_like_record_tail_application() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let unit_t = Located::dummy(Typ::Record(vec![]));
        let int_t = dummy_typ();
        let tail_record_t = Located::dummy(Typ::Record(vec![("A".into(), int_t.clone())]));
        let unit_e = Located::dummy(Exp::Record(vec![]));
        let tail = Located::dummy(Exp::Abs(
            "_".into(),
            unit_t.clone(),
            tail_record_t,
            Box::new(Located::dummy(Exp::Record(vec![(
                "A".into(),
                prim_int(7),
                int_t.clone(),
            )]))),
        ));
        let combined = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Record(vec![(
                    "B".into(),
                    prim_int(9),
                    int_t.clone(),
                )]))),
                Box::new(tail),
            ))),
            Box::new(unit_e),
        ));
        let projected = Located::dummy(Exp::Field(Box::new(combined), "A".into()));

        let result = reduce_exp(&env, projected, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected projection to continue into concat-like tail, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_field_projection_falls_through_abs_tail_args() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let unit_t = Located::dummy(Typ::Record(vec![]));
        let int_t = dummy_typ();
        let b_record_t = Located::dummy(Typ::Record(vec![("B".into(), int_t.clone())]));
        let unit_e = Located::dummy(Exp::Record(vec![]));
        let combined = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Abs(
                    "_".into(),
                    unit_t.clone(),
                    b_record_t,
                    Box::new(Located::dummy(Exp::Record(vec![(
                        "B".into(),
                        prim_int(9),
                        int_t.clone(),
                    )]))),
                ))),
                Box::new(unit_e.clone()),
            ))),
            Box::new(Located::dummy(Exp::Record(vec![(
                "A".into(),
                prim_int(7),
                int_t.clone(),
            )]))),
        ));
        let projected = Located::dummy(Exp::Field(Box::new(combined), "A".into()));

        let result = reduce_exp(&env, projected, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected projection to continue into abs tail args, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_field_projection_skips_erased_proof_args() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let int_t = dummy_typ();
        let combined = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Record(vec![(
                    "B".into(),
                    prim_int(9),
                    int_t.clone(),
                )]))),
                Box::new(Located::dummy(Exp::Prim(Prim::Int(0)))),
            ))),
            Box::new(Located::dummy(Exp::Record(vec![(
                "A".into(),
                prim_int(7),
                int_t.clone(),
            )]))),
        ));
        let projected = Located::dummy(Exp::Field(Box::new(combined), "A".into()));

        let result = reduce_exp(&env, projected, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected projection to skip erased proof args, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_field_projection_prefers_arg_that_can_supply_field() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let int_t = dummy_typ();
        let combined = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Record(vec![(
                    "B".into(),
                    prim_int(9),
                    int_t.clone(),
                )]))),
                Box::new(Located::dummy(Exp::Record(vec![(
                    "A".into(),
                    prim_int(7),
                    int_t.clone(),
                )]))),
            ))),
            Box::new(Located::dummy(Exp::Record(vec![(
                "C".into(),
                prim_int(13),
                int_t.clone(),
            )]))),
        ));
        let projected = Located::dummy(Exp::Field(Box::new(combined), "A".into()));

        let result = reduce_exp(&env, projected, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected projection to prefer the arg supplying the field, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_field_projection_prefers_direct_arg_over_earlier_reapplied_receiver() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let int_t = dummy_typ();
        let a_record_t = Located::dummy(Typ::Record(vec![("A".into(), int_t.clone())]));
        let earlier_receiver = Located::dummy(Exp::Abs(
            "row".into(),
            a_record_t.clone(),
            a_record_t.clone(),
            Box::new(Located::dummy(Exp::Record(vec![(
                "A".into(),
                prim_int(1),
                int_t.clone(),
            )]))),
        ));
        let direct_row =
            Located::dummy(Exp::Record(vec![("A".into(), prim_int(7), int_t.clone())]));
        let combined = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Record(vec![(
                    "B".into(),
                    prim_int(9),
                    int_t.clone(),
                )]))),
                Box::new(earlier_receiver),
            ))),
            Box::new(direct_row),
        ));
        let projected = Located::dummy(Exp::Field(Box::new(combined), "A".into()));

        let result = reduce_exp(&env, projected, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected direct arg to beat earlier reapplied receiver, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_app_pushes_through_missing_field_projection() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let unit_t = Located::dummy(Typ::Record(vec![]));
        let int_t = dummy_typ();
        let b_record_t = Located::dummy(Typ::Record(vec![("B".into(), int_t.clone())]));
        let unit_e = Located::dummy(Exp::Record(vec![]));
        let projected_app = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Field(
                    Box::new(Located::dummy(Exp::Abs(
                        "_".into(),
                        unit_t.clone(),
                        b_record_t,
                        Box::new(Located::dummy(Exp::Record(vec![(
                            "B".into(),
                            prim_int(9),
                            int_t.clone(),
                        )]))),
                    ))),
                    "A".into(),
                ))),
                Box::new(unit_e.clone()),
            ))),
            Box::new(Located::dummy(Exp::Record(vec![(
                "A".into(),
                prim_int(7),
                int_t.clone(),
            )]))),
        ));

        let result = reduce_exp(&env, projected_app, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected app to push through missing field projection, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_app_redirects_simple_missing_field_to_row_arg() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let unit_t = Located::dummy(Typ::Record(vec![]));
        let int_t = dummy_typ();
        let row_t = Located::dummy(Typ::Record(vec![("A".into(), int_t.clone())]));
        let curried_acc = Located::dummy(Exp::Abs(
            "r".into(),
            row_t.clone(),
            Located::dummy(Typ::Fun(Box::new(unit_t.clone()), Box::new(int_t.clone()))),
            Box::new(Located::dummy(Exp::Abs(
                "_".into(),
                unit_t,
                int_t.clone(),
                Box::new(prim_int(0)),
            ))),
        ));
        let projected_app = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::Field(
                Box::new(curried_acc),
                "A".into(),
            ))),
            Box::new(Located::dummy(Exp::Record(vec![(
                "A".into(),
                prim_int(7),
                int_t,
            )]))),
        ));

        let result = reduce_exp(&env, projected_app, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected simple missing field projection to redirect to row arg, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_app_redirects_nested_missing_field_to_tail_arg() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let unit_t = Located::dummy(Typ::Record(vec![]));
        let int_t = dummy_typ();
        let inject_fun_t =
            Located::dummy(Typ::Fun(Box::new(unit_t.clone()), Box::new(int_t.clone())));
        let meta_t = Located::dummy(Typ::Record(vec![("Inject".into(), inject_fun_t.clone())]));
        let b_record_t = Located::dummy(Typ::Record(vec![("B".into(), meta_t.clone())]));
        let unit_e = Located::dummy(Exp::Record(vec![]));
        let projected_app = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Field(
                    Box::new(Located::dummy(Exp::Field(
                        Box::new(Located::dummy(Exp::Abs(
                            "_".into(),
                            unit_t.clone(),
                            b_record_t,
                            Box::new(Located::dummy(Exp::Record(vec![(
                                "B".into(),
                                Located::dummy(Exp::Record(vec![(
                                    "Inject".into(),
                                    Located::dummy(Exp::Abs(
                                        "_".into(),
                                        unit_t.clone(),
                                        int_t.clone(),
                                        Box::new(prim_int(9)),
                                    )),
                                    inject_fun_t.clone(),
                                )])),
                                meta_t.clone(),
                            )]))),
                        ))),
                        "A".into(),
                    ))),
                    "Inject".into(),
                ))),
                Box::new(unit_e.clone()),
            ))),
            Box::new(Located::dummy(Exp::Record(vec![(
                "A".into(),
                Located::dummy(Exp::Record(vec![(
                    "Inject".into(),
                    Located::dummy(Exp::Abs(
                        "_".into(),
                        unit_t.clone(),
                        int_t.clone(),
                        Box::new(prim_int(7)),
                    )),
                    inject_fun_t,
                )])),
                meta_t,
            )]))),
        ));

        let result = reduce_exp(&env, projected_app, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected nested missing field projection to redirect to tail arg, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_app_redirects_nested_missing_field_to_earlier_arg() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let unit_t = Located::dummy(Typ::Record(vec![]));
        let int_t = dummy_typ();
        let row_t = Located::dummy(Typ::Record(vec![("A".into(), int_t.clone())]));
        let unit_e = Located::dummy(Exp::Record(vec![]));
        let projected_app = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Field(
                    Box::new(Located::dummy(Exp::Abs(
                        "_".into(),
                        row_t.clone(),
                        Located::dummy(Typ::Fun(Box::new(unit_t.clone()), Box::new(int_t.clone()))),
                        Box::new(Located::dummy(Exp::Abs(
                            "_".into(),
                            unit_t.clone(),
                            int_t.clone(),
                            Box::new(prim_int(0)),
                        ))),
                    ))),
                    "A".into(),
                ))),
                Box::new(Located::dummy(Exp::Record(vec![(
                    "A".into(),
                    prim_int(7),
                    int_t.clone(),
                )]))),
            ))),
            Box::new(unit_e),
        ));

        let result = reduce_exp(&env, projected_app, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected nested missing field projection to redirect to earlier arg, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_project_missing_field_prefers_later_row_arg_when_both_match() {
        let env = Env::empty();
        let span = Span::dummy();
        let int_t = dummy_typ();
        let first = Located::dummy(Exp::Record(vec![("A".into(), prim_int(7), int_t.clone())]));
        let second = Located::dummy(Exp::Record(vec![("A".into(), prim_int(9), int_t.clone())]));

        let projected = project_missing_field_from_args_in_env(&env, &[first, second], "A", &span)
            .expect("field should be recoverable");
        let reduced = reduce_exp(
            &env,
            projected,
            &ReduceCtx {
                timpures: HashSet::new(),
                impures: HashSet::new(),
                uses: HashMap::new(),
                yanked_case: Cell::new(false),
                full_mode: false,
            },
            &Settings::new(),
        );
        assert!(
            matches!(reduced.node, Exp::Prim(Prim::Int(9))),
            "Expected later row argument to win when both supply the field, got {:?}",
            reduced.node
        );
    }

    #[test]
    fn test_reapply_single_arg_skips_function_like_continuation_for_scalar_field() {
        let env = Env::empty();
        let int_t = dummy_typ();
        let string_t = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));
        let show_fun_t = Located::dummy(Typ::Fun(
            Box::new(int_t.clone()),
            Box::new(string_t.clone()),
        ));
        let meta_t = Located::dummy(Typ::Record(vec![("Show".into(), show_fun_t.clone())]));
        let row_t = Located::dummy(Typ::Record(vec![("A".into(), meta_t.clone())]));
        let head = Located::dummy(Exp::Field(
            Box::new(Located::dummy(Exp::Field(
                Box::new(Located::dummy(Exp::Record(vec![(
                    "A".into(),
                    Located::dummy(Exp::Record(vec![(
                        "Show".into(),
                        Located::dummy(Exp::Abs(
                            "_".into(),
                            int_t.clone(),
                            string_t,
                            Box::new(Located::dummy(Exp::Prim(Prim::String(
                                StringMode::Normal,
                                "ok".into(),
                            )))),
                        )),
                        show_fun_t,
                    )])),
                    meta_t,
                )]))),
                "A".into(),
            ))),
            "Show".into(),
        ));
        let continuation =
            Located::dummy(Exp::Abs("r2".into(), row_t, int_t, Box::new(prim_int(7))));

        let result = reapply_single_arg_if_function_like_in_env(&env, head.clone(), continuation);
        assert_eq!(
            format!("{:?}", result.node),
            format!("{:?}", head.node),
            "Expected continuation lambda not to be reapplied to scalar field head"
        );
    }

    #[test]
    fn test_reapply_single_arg_keeps_non_function_like_arg() {
        let env = Env::empty();
        let int_t = dummy_typ();
        let string_t = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));
        let show_fun_t = Located::dummy(Typ::Fun(
            Box::new(int_t.clone()),
            Box::new(string_t.clone()),
        ));
        let head = Located::dummy(Exp::Field(
            Box::new(Located::dummy(Exp::Record(vec![(
                "Show".into(),
                Located::dummy(Exp::Abs(
                    "_".into(),
                    int_t.clone(),
                    string_t,
                    Box::new(Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "ok".into(),
                    )))),
                )),
                show_fun_t,
            )]))),
            "Show".into(),
        ));

        let result = reapply_single_arg_if_function_like_in_env(
            &env,
            head,
            Located::dummy(Exp::Record(vec![])),
        );
        assert!(
            matches!(result.node, Exp::App(_, _)),
            "Expected non-function-like arg to keep reapplication, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_app_redirects_nested_missing_field_before_applying_mixed_record() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let unit_t = Located::dummy(Typ::Record(vec![]));
        let int_t = dummy_typ();
        let string_t = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));
        let show_fun_t = Located::dummy(Typ::Fun(
            Box::new(int_t.clone()),
            Box::new(string_t.clone()),
        ));
        let meta_t = Located::dummy(Typ::Record(vec![
            ("Name".into(), string_t.clone()),
            ("Show".into(), show_fun_t.clone()),
        ]));
        let b_record_t = Located::dummy(Typ::Record(vec![("B".into(), meta_t.clone())]));
        let unit_e = Located::dummy(Exp::Record(vec![]));
        let projected_app = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Field(
                    Box::new(Located::dummy(Exp::Field(
                        Box::new(Located::dummy(Exp::Abs(
                            "_".into(),
                            unit_t.clone(),
                            b_record_t,
                            Box::new(Located::dummy(Exp::Record(vec![(
                                "B".into(),
                                Located::dummy(Exp::Record(vec![
                                    (
                                        "Name".into(),
                                        Located::dummy(Exp::Prim(Prim::String(
                                            StringMode::Normal,
                                            "ignored".into(),
                                        ))),
                                        string_t.clone(),
                                    ),
                                    (
                                        "Show".into(),
                                        Located::dummy(Exp::Abs(
                                            "_".into(),
                                            unit_t.clone(),
                                            int_t.clone(),
                                            Box::new(prim_int(9)),
                                        )),
                                        show_fun_t.clone(),
                                    ),
                                ])),
                                meta_t.clone(),
                            )]))),
                        ))),
                        "A".into(),
                    ))),
                    "Show".into(),
                ))),
                Box::new(unit_e.clone()),
            ))),
            Box::new(Located::dummy(Exp::Record(vec![(
                "A".into(),
                Located::dummy(Exp::Record(vec![
                    (
                        "Name".into(),
                        Located::dummy(Exp::Prim(Prim::String(StringMode::Normal, "n".into()))),
                        string_t,
                    ),
                    (
                        "Show".into(),
                        Located::dummy(Exp::Abs(
                            "_".into(),
                            unit_t,
                            int_t.clone(),
                            Box::new(prim_int(7)),
                        )),
                        show_fun_t,
                    ),
                ])),
                meta_t,
            )]))),
        ));

        let result = reduce_exp(&env, projected_app, &ctx, &settings);
        assert!(
            matches!(result.node, Exp::Prim(Prim::Int(7))),
            "Expected mixed-record missing field projection to project before applying, got {:?}",
            result.node
        );
    }

    #[test]
    fn test_app_preserves_direct_field_projection_on_projected_record() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let int_t = dummy_typ();
        let string_t = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));
        let show_fun_t = Located::dummy(Typ::Fun(
            Box::new(int_t.clone()),
            Box::new(string_t.clone()),
        ));
        let meta_t = Located::dummy(Typ::Record(vec![("Show".into(), show_fun_t.clone())]));
        let holder = Located::dummy(Exp::Record(vec![(
            "A".into(),
            Located::dummy(Exp::Record(vec![(
                "Show".into(),
                Located::dummy(Exp::Abs(
                    "x".into(),
                    int_t.clone(),
                    string_t.clone(),
                    Box::new(Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "ok".into(),
                    )))),
                )),
                show_fun_t,
            )])),
            meta_t,
        )]));
        let applied = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::Field(
                Box::new(Located::dummy(Exp::Field(Box::new(holder), "A".into()))),
                "Show".into(),
            ))),
            Box::new(prim_int(7)),
        ));

        let result = reduce_exp(&env, applied, &ctx, &settings);
        assert!(matches!(
            result.node,
            Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
    }

    #[test]
    fn test_field_projects_direct_field_from_head_before_applying_arg() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let int_t = dummy_typ();
        let string_t = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));
        let show_fun_t = Located::dummy(Typ::Fun(
            Box::new(int_t.clone()),
            Box::new(string_t.clone()),
        ));
        let meta_t = Located::dummy(Typ::Record(vec![("Show".into(), show_fun_t.clone())]));
        let holder = Located::dummy(Exp::Record(vec![(
            "A".into(),
            Located::dummy(Exp::Record(vec![(
                "Show".into(),
                Located::dummy(Exp::Abs(
                    "x".into(),
                    int_t.clone(),
                    string_t.clone(),
                    Box::new(Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "ok".into(),
                    )))),
                )),
                show_fun_t,
            )])),
            meta_t,
        )]));
        let malformed = Located::dummy(Exp::Field(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Field(Box::new(holder), "A".into()))),
                Box::new(prim_int(7)),
            ))),
            "Show".into(),
        ));

        let result = reduce_exp(&env, malformed, &ctx, &settings);
        assert!(matches!(
            result.node,
            Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
    }

    #[test]
    fn test_app_preserves_direct_field_projection_on_projected_rel_record() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let int_t = dummy_typ();
        let string_t = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));
        let show_fun_t = Located::dummy(Typ::Fun(
            Box::new(int_t.clone()),
            Box::new(string_t.clone()),
        ));
        let meta_t = Located::dummy(Typ::Record(vec![("Show".into(), show_fun_t.clone())]));
        let holder_t = Located::dummy(Typ::Record(vec![("A".into(), meta_t.clone())]));
        let holder = Located::dummy(Exp::Record(vec![(
            "A".into(),
            Located::dummy(Exp::Record(vec![(
                "Show".into(),
                Located::dummy(Exp::Abs(
                    "x".into(),
                    int_t.clone(),
                    string_t.clone(),
                    Box::new(Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "ok".into(),
                    )))),
                )),
                show_fun_t,
            )])),
            meta_t,
        )]));
        let env = Env::empty().push_rel_opt("cols", holder_t, Some(holder));
        let applied = Located::dummy(Exp::App(
            Box::new(Located::dummy(Exp::Field(
                Box::new(Located::dummy(Exp::Field(
                    Box::new(Located::dummy(Exp::Rel(0))),
                    "A".into(),
                ))),
                "Show".into(),
            ))),
            Box::new(prim_int(7)),
        ));

        let result = reduce_exp(&env, applied, &ctx, &settings);
        assert!(matches!(
            result.node,
            Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
    }

    #[test]
    fn test_field_projects_direct_field_from_rel_head_before_applying_arg() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let int_t = dummy_typ();
        let string_t = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));
        let show_fun_t = Located::dummy(Typ::Fun(
            Box::new(int_t.clone()),
            Box::new(string_t.clone()),
        ));
        let meta_t = Located::dummy(Typ::Record(vec![("Show".into(), show_fun_t.clone())]));
        let holder_t = Located::dummy(Typ::Record(vec![("A".into(), meta_t.clone())]));
        let holder = Located::dummy(Exp::Record(vec![(
            "A".into(),
            Located::dummy(Exp::Record(vec![(
                "Show".into(),
                Located::dummy(Exp::Abs(
                    "x".into(),
                    int_t.clone(),
                    string_t.clone(),
                    Box::new(Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "ok".into(),
                    )))),
                )),
                show_fun_t,
            )])),
            meta_t,
        )]));
        let env = Env::empty().push_rel_opt("cols", holder_t, Some(holder));
        let malformed = Located::dummy(Exp::Field(
            Box::new(Located::dummy(Exp::App(
                Box::new(Located::dummy(Exp::Field(
                    Box::new(Located::dummy(Exp::Rel(0))),
                    "A".into(),
                ))),
                Box::new(prim_int(7)),
            ))),
            "Show".into(),
        ));

        let result = reduce_exp(&env, malformed, &ctx, &settings);
        assert!(matches!(
            result.node,
            Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
    }

    #[test]
    fn test_let_inlines_pure_record_used_only_via_field_projections() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let string_t = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));
        let record_t = Located::dummy(Typ::Record(vec![
            ("Inject".into(), string_t.clone()),
            ("Widget".into(), string_t.clone()),
        ]));
        let binding = Located::dummy(Exp::Record(vec![
            (
                "Inject".into(),
                Located::dummy(Exp::Strcat(
                    Box::new(Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "a".into(),
                    )))),
                    Box::new(Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "b".into(),
                    )))),
                )),
                string_t.clone(),
            ),
            (
                "Widget".into(),
                Located::dummy(Exp::Strcat(
                    Box::new(Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "x".into(),
                    )))),
                    Box::new(Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "y".into(),
                    )))),
                )),
                string_t.clone(),
            ),
        ]));
        let body = Located::dummy(Exp::Record(vec![
            (
                "Inject".into(),
                Located::dummy(Exp::Field(
                    Box::new(Located::dummy(Exp::Rel(0))),
                    "Inject".into(),
                )),
                string_t.clone(),
            ),
            (
                "Widget".into(),
                Located::dummy(Exp::Field(
                    Box::new(Located::dummy(Exp::Rel(0))),
                    "Widget".into(),
                )),
                string_t.clone(),
            ),
        ]));
        let let_exp = Located::dummy(Exp::Let(
            "cols".into(),
            record_t,
            Box::new(binding),
            Box::new(body),
        ));

        let result = reduce_exp(&env, let_exp, &ctx, &settings);
        match result.node {
            Exp::Record(fields) => {
                assert!(matches!(
                    fields[0].1.node,
                    Exp::Prim(Prim::String(StringMode::Normal, ref s)) if s == "ab"
                ));
                assert!(matches!(
                    fields[1].1.node,
                    Exp::Prim(Prim::String(StringMode::Normal, ref s)) if s == "xy"
                ));
            }
            other => panic!(
                "Expected projected record after pure record inlining, got {:?}",
                other
            ),
        }
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
    fn test_case_reduction_substitutes_pattern_binders_innermost_first() {
        let settings = Settings::new();
        let ctx = ReduceCtx {
            timpures: HashSet::new(),
            impures: HashSet::new(),
            uses: HashMap::new(),
            yanked_case: Cell::new(false),
            full_mode: false,
        };
        let env = Env::empty();
        let int_t = dummy_typ();
        let pair_t = Located::dummy(Typ::Record(vec![
            ("head".into(), int_t.clone()),
            ("tail".into(), int_t.clone()),
        ]));
        let dt_ref: DatatypeRef = Arc::new(Mutex::new(DatatypeDef {
            kind: DatatypeKind::Default,
            constrs: vec![("Cons".into(), 7001, Some(pair_t.clone()))],
        }));
        let list_t = Located::dummy(Typ::Datatype(7000, dt_ref));
        let pattern = Located::dummy(Pat::Con(
            DatatypeKind::Default,
            crate::monomorphized::PatCon::Var(7001),
            Some(Box::new(Located::dummy(Pat::Record(vec![
                (
                    "1".into(),
                    Located::dummy(Pat::Var("head".into(), int_t.clone())),
                    int_t.clone(),
                ),
                (
                    "2".into(),
                    Located::dummy(Pat::Var("tail".into(), int_t.clone())),
                    int_t.clone(),
                ),
            ])))),
        ));
        let disc = Located::dummy(Exp::Con(
            DatatypeKind::Default,
            crate::monomorphized::PatCon::Var(7001),
            Some(Box::new(Located::dummy(Exp::Record(vec![
                ("1".into(), prim_int(1), int_t.clone()),
                ("2".into(), prim_int(2), int_t.clone()),
            ])))),
        ));
        let body = Located::dummy(Exp::Record(vec![
            ("head".into(), rel(1), int_t.clone()),
            ("tail".into(), rel(0), int_t.clone()),
        ]));
        let case = Located::dummy(Exp::Case(
            Box::new(disc),
            vec![(pattern, body)],
            CaseMeta {
                disc: list_t,
                result: pair_t,
            },
        ));

        let result = reduce_exp(&env, case, &ctx, &settings);
        match result.node {
            Exp::Record(fields) => {
                assert!(matches!(fields[0].1.node, Exp::Prim(Prim::Int(1))));
                assert!(matches!(fields[1].1.node, Exp::Prim(Prim::Int(2))));
            }
            other => panic!(
                "Expected reduced record with preserved binder order, got {:?}",
                other
            ),
        }
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
