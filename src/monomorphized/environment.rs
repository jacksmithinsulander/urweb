//! Mono environment: tracks bound variables and named definitions.
//!
//! Ports `mono_env.sml`. Extended to carry optional cached expressions for
//! inlining (needed by `mono_reduce`).

use std::collections::HashMap;

use crate::monomorphized::{Exp, LocDecl, LocExp, LocPat, LocTyp, Pat};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct UnboundError {
    pub kind: UnboundKind,
    pub index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnboundKind {
    Rel,
    Named,
}

impl std::fmt::Display for UnboundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            UnboundKind::Rel => write!(f, "unbound relative variable {}", self.index),
            UnboundKind::Named => write!(f, "unbound named variable {}", self.index),
        }
    }
}

impl std::error::Error for UnboundError {}

// ---------------------------------------------------------------------------
// lift_exp_in_exp / sub_exp_in_exp — shared utilities for Env and reduce
// ---------------------------------------------------------------------------

/// Increment all de Bruijn indices ≥ `bound` by 1.
///
/// Used when pushing a new lambda/let binder to shift free variables.
pub fn lift_exp_in_exp(bound: usize, e: &LocExp) -> LocExp {
    let span = e.span.clone();
    let new_node = lift_exp_node(bound, &e.node);
    crate::error_types::Located::new(new_node, span)
}

fn lift_exp_node(bound: usize, e: &Exp) -> Exp {
    use crate::monomorphized::{JavaScriptMode, QueryMeta};
    match e {
        Exp::Rel(n) => {
            if *n < bound {
                Exp::Rel(*n)
            } else {
                Exp::Rel(*n + 1)
            }
        }
        Exp::Abs(x, dom, ran, body) => {
            let body2 = lift_exp_in_exp(bound + 1, body);
            Exp::Abs(x.clone(), dom.clone(), ran.clone(), Box::new(body2))
        }
        Exp::App(f, arg) => Exp::App(
            Box::new(lift_exp_in_exp(bound, f)),
            Box::new(lift_exp_in_exp(bound, arg)),
        ),
        Exp::Let(x, t, e1, e2) => Exp::Let(
            x.clone(),
            t.clone(),
            Box::new(lift_exp_in_exp(bound, e1)),
            Box::new(lift_exp_in_exp(bound + 1, e2)),
        ),
        Exp::Strcat(e1, e2) => Exp::Strcat(
            Box::new(lift_exp_in_exp(bound, e1)),
            Box::new(lift_exp_in_exp(bound, e2)),
        ),
        Exp::Seq(e1, e2) => Exp::Seq(
            Box::new(lift_exp_in_exp(bound, e1)),
            Box::new(lift_exp_in_exp(bound, e2)),
        ),
        Exp::Write(inner) => Exp::Write(Box::new(lift_exp_in_exp(bound, inner))),
        Exp::Unop(op, inner) => Exp::Unop(op.clone(), Box::new(lift_exp_in_exp(bound, inner))),
        Exp::Binop(intness, op, e1, e2) => Exp::Binop(
            *intness,
            op.clone(),
            Box::new(lift_exp_in_exp(bound, e1)),
            Box::new(lift_exp_in_exp(bound, e2)),
        ),
        Exp::Record(xets) => Exp::Record(
            xets.iter()
                .map(|(x, e, t)| (x.clone(), lift_exp_in_exp(bound, e), t.clone()))
                .collect(),
        ),
        Exp::Field(inner, x) => Exp::Field(Box::new(lift_exp_in_exp(bound, inner)), x.clone()),
        Exp::Case(disc, arms, meta) => Exp::Case(
            Box::new(lift_exp_in_exp(bound, disc)),
            arms.iter()
                .map(|(p, arm_e)| {
                    let pat_binds = pat_binds_n(p);
                    (p.clone(), lift_exp_in_exp(bound + pat_binds, arm_e))
                })
                .collect(),
            meta.clone(),
        ),
        Exp::Con(dk, pc, arg) => Exp::Con(
            *dk,
            pc.clone(),
            arg.as_ref().map(|a| Box::new(lift_exp_in_exp(bound, a))),
        ),
        Exp::Some(t, inner) => Exp::Some(t.clone(), Box::new(lift_exp_in_exp(bound, inner))),
        Exp::FfiApp(m, f, args) => Exp::FfiApp(
            m.clone(),
            f.clone(),
            args.iter()
                .map(|(e, t)| (lift_exp_in_exp(bound, e), t.clone()))
                .collect(),
        ),
        Exp::Query(qm) => Exp::Query(QueryMeta {
            exps: qm.exps.clone(),
            tables: qm.tables.clone(),
            state: qm.state.clone(),
            query: Box::new(lift_exp_in_exp(bound, &qm.query)),
            body: Box::new(lift_exp_in_exp(bound + 2, &qm.body)),
            initial: Box::new(lift_exp_in_exp(bound, &qm.initial)),
        }),
        Exp::Dml(inner, fm) => Exp::Dml(Box::new(lift_exp_in_exp(bound, inner)), *fm),
        Exp::Nextval(inner) => Exp::Nextval(Box::new(lift_exp_in_exp(bound, inner))),
        Exp::Setval(e1, e2) => Exp::Setval(
            Box::new(lift_exp_in_exp(bound, e1)),
            Box::new(lift_exp_in_exp(bound, e2)),
        ),
        Exp::Uurlify(inner, t, b) => {
            Exp::Uurlify(Box::new(lift_exp_in_exp(bound, inner)), t.clone(), *b)
        }
        Exp::JavaScript(mode, inner) => {
            let mode2 = match mode {
                JavaScriptMode::Source(t) => JavaScriptMode::Source(t.clone()),
                other => other.clone(),
            };
            Exp::JavaScript(mode2, Box::new(lift_exp_in_exp(bound, inner)))
        }
        Exp::SignalReturn(inner) => Exp::SignalReturn(Box::new(lift_exp_in_exp(bound, inner))),
        Exp::SignalBind(e1, e2) => Exp::SignalBind(
            Box::new(lift_exp_in_exp(bound, e1)),
            Box::new(lift_exp_in_exp(bound, e2)),
        ),
        Exp::SignalSource(inner) => Exp::SignalSource(Box::new(lift_exp_in_exp(bound, inner))),
        Exp::ServerCall(inner, t, eff, fm) => Exp::ServerCall(
            Box::new(lift_exp_in_exp(bound, inner)),
            t.clone(),
            *eff,
            *fm,
        ),
        Exp::Recv(inner, t) => Exp::Recv(Box::new(lift_exp_in_exp(bound, inner)), t.clone()),
        Exp::Sleep(inner) => Exp::Sleep(Box::new(lift_exp_in_exp(bound, inner))),
        Exp::Spawn(inner) => Exp::Spawn(Box::new(lift_exp_in_exp(bound, inner))),
        Exp::Error(inner, t) => Exp::Error(Box::new(lift_exp_in_exp(bound, inner)), t.clone()),
        Exp::ReturnBlob { blob, mime_type, t } => Exp::ReturnBlob {
            blob: blob.as_ref().map(|b| Box::new(lift_exp_in_exp(bound, b))),
            mime_type: Box::new(lift_exp_in_exp(bound, mime_type)),
            t: t.clone(),
        },
        Exp::Redirect(inner, t) => {
            Exp::Redirect(Box::new(lift_exp_in_exp(bound, inner)), t.clone())
        }
        Exp::Closure(n, envs) => {
            Exp::Closure(*n, envs.iter().map(|e| lift_exp_in_exp(bound, e)).collect())
        }
        // Leaves
        Exp::Prim(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::None(_) => e.clone(),
    }
}

/// Substitute `rep` for `Rel(xn)` in `body`, decrementing indices above `xn`.
///
/// When descending under a binder, `xn` is incremented and `rep` is lifted.
pub fn sub_exp_in_exp(xn: usize, rep: &LocExp, body: &LocExp) -> LocExp {
    let span = body.span.clone();
    let new_node = sub_exp_node(xn, rep, &body.node);
    crate::error_types::Located::new(new_node, span)
}

fn sub_exp_node(xn: usize, rep: &LocExp, e: &Exp) -> Exp {
    use crate::monomorphized::{JavaScriptMode, QueryMeta};
    match e {
        Exp::Rel(n) => {
            use std::cmp::Ordering;
            match n.cmp(&xn) {
                Ordering::Equal => rep.node.clone(),
                Ordering::Greater => Exp::Rel(*n - 1),
                Ordering::Less => Exp::Rel(*n),
            }
        }
        Exp::Abs(x, dom, ran, body) => {
            let rep_lifted = lift_exp_in_exp(0, rep);
            let body2 = sub_exp_in_exp(xn + 1, &rep_lifted, body);
            Exp::Abs(x.clone(), dom.clone(), ran.clone(), Box::new(body2))
        }
        Exp::Let(x, t, e1, e2) => {
            let e1_sub = sub_exp_in_exp(xn, rep, e1);
            let rep_lifted = lift_exp_in_exp(0, rep);
            let e2_sub = sub_exp_in_exp(xn + 1, &rep_lifted, e2);
            Exp::Let(x.clone(), t.clone(), Box::new(e1_sub), Box::new(e2_sub))
        }
        Exp::App(f, arg) => Exp::App(
            Box::new(sub_exp_in_exp(xn, rep, f)),
            Box::new(sub_exp_in_exp(xn, rep, arg)),
        ),
        Exp::Strcat(e1, e2) => Exp::Strcat(
            Box::new(sub_exp_in_exp(xn, rep, e1)),
            Box::new(sub_exp_in_exp(xn, rep, e2)),
        ),
        Exp::Seq(e1, e2) => Exp::Seq(
            Box::new(sub_exp_in_exp(xn, rep, e1)),
            Box::new(sub_exp_in_exp(xn, rep, e2)),
        ),
        Exp::Write(inner) => Exp::Write(Box::new(sub_exp_in_exp(xn, rep, inner))),
        Exp::Unop(op, inner) => Exp::Unop(op.clone(), Box::new(sub_exp_in_exp(xn, rep, inner))),
        Exp::Binop(intness, op, e1, e2) => Exp::Binop(
            *intness,
            op.clone(),
            Box::new(sub_exp_in_exp(xn, rep, e1)),
            Box::new(sub_exp_in_exp(xn, rep, e2)),
        ),
        Exp::Record(xets) => Exp::Record(
            xets.iter()
                .map(|(x, e, t)| (x.clone(), sub_exp_in_exp(xn, rep, e), t.clone()))
                .collect(),
        ),
        Exp::Field(inner, x) => Exp::Field(Box::new(sub_exp_in_exp(xn, rep, inner)), x.clone()),
        Exp::Case(disc, arms, meta) => Exp::Case(
            Box::new(sub_exp_in_exp(xn, rep, disc)),
            arms.iter()
                .map(|(p, arm_e)| {
                    let n_binds = pat_binds_n(p);
                    let rep_lifted = multi_lift(n_binds, rep);
                    (p.clone(), sub_exp_in_exp(xn + n_binds, &rep_lifted, arm_e))
                })
                .collect(),
            meta.clone(),
        ),
        Exp::Con(dk, pc, arg) => Exp::Con(
            *dk,
            pc.clone(),
            arg.as_ref().map(|a| Box::new(sub_exp_in_exp(xn, rep, a))),
        ),
        Exp::Some(t, inner) => Exp::Some(t.clone(), Box::new(sub_exp_in_exp(xn, rep, inner))),
        Exp::FfiApp(m, f, args) => Exp::FfiApp(
            m.clone(),
            f.clone(),
            args.iter()
                .map(|(e, t)| (sub_exp_in_exp(xn, rep, e), t.clone()))
                .collect(),
        ),
        Exp::Query(qm) => {
            let rep_for_body = multi_lift(2, rep);
            Exp::Query(QueryMeta {
                exps: qm.exps.clone(),
                tables: qm.tables.clone(),
                state: qm.state.clone(),
                query: Box::new(sub_exp_in_exp(xn, rep, &qm.query)),
                body: Box::new(sub_exp_in_exp(xn + 2, &rep_for_body, &qm.body)),
                initial: Box::new(sub_exp_in_exp(xn, rep, &qm.initial)),
            })
        }
        Exp::Dml(inner, fm) => Exp::Dml(Box::new(sub_exp_in_exp(xn, rep, inner)), *fm),
        Exp::Nextval(inner) => Exp::Nextval(Box::new(sub_exp_in_exp(xn, rep, inner))),
        Exp::Setval(e1, e2) => Exp::Setval(
            Box::new(sub_exp_in_exp(xn, rep, e1)),
            Box::new(sub_exp_in_exp(xn, rep, e2)),
        ),
        Exp::Uurlify(inner, t, b) => {
            Exp::Uurlify(Box::new(sub_exp_in_exp(xn, rep, inner)), t.clone(), *b)
        }
        Exp::JavaScript(mode, inner) => {
            let mode2 = match mode {
                JavaScriptMode::Source(t) => JavaScriptMode::Source(t.clone()),
                other => other.clone(),
            };
            Exp::JavaScript(mode2, Box::new(sub_exp_in_exp(xn, rep, inner)))
        }
        Exp::SignalReturn(inner) => Exp::SignalReturn(Box::new(sub_exp_in_exp(xn, rep, inner))),
        Exp::SignalBind(e1, e2) => Exp::SignalBind(
            Box::new(sub_exp_in_exp(xn, rep, e1)),
            Box::new(sub_exp_in_exp(xn, rep, e2)),
        ),
        Exp::SignalSource(inner) => Exp::SignalSource(Box::new(sub_exp_in_exp(xn, rep, inner))),
        Exp::ServerCall(inner, t, eff, fm) => Exp::ServerCall(
            Box::new(sub_exp_in_exp(xn, rep, inner)),
            t.clone(),
            *eff,
            *fm,
        ),
        Exp::Recv(inner, t) => Exp::Recv(Box::new(sub_exp_in_exp(xn, rep, inner)), t.clone()),
        Exp::Sleep(inner) => Exp::Sleep(Box::new(sub_exp_in_exp(xn, rep, inner))),
        Exp::Spawn(inner) => Exp::Spawn(Box::new(sub_exp_in_exp(xn, rep, inner))),
        Exp::Error(inner, t) => Exp::Error(Box::new(sub_exp_in_exp(xn, rep, inner)), t.clone()),
        Exp::ReturnBlob { blob, mime_type, t } => Exp::ReturnBlob {
            blob: blob.as_ref().map(|b| Box::new(sub_exp_in_exp(xn, rep, b))),
            mime_type: Box::new(sub_exp_in_exp(xn, rep, mime_type)),
            t: t.clone(),
        },
        Exp::Redirect(inner, t) => {
            Exp::Redirect(Box::new(sub_exp_in_exp(xn, rep, inner)), t.clone())
        }
        Exp::Closure(n, envs) => Exp::Closure(
            *n,
            envs.iter().map(|e| sub_exp_in_exp(xn, rep, e)).collect(),
        ),
        // Leaves
        Exp::Prim(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::None(_) => e.clone(),
    }
}

/// Apply `lift_exp_in_exp(0, ...)` `n` times.
pub fn multi_lift(n: usize, e: &LocExp) -> LocExp {
    let mut result = e.clone();
    for _ in 0..n {
        result = lift_exp_in_exp(0, &result);
    }
    result
}

/// Count how many variables a pattern binds.
pub fn pat_binds_n(p: &LocPat) -> usize {
    match &p.node {
        Pat::Var(_, _) => 1,
        Pat::Prim(_) => 0,
        Pat::Con(_, _, None) => 0,
        Pat::Con(_, _, Some(inner)) => pat_binds_n(inner),
        Pat::Record(xpts) => xpts.iter().map(|(_, p, _)| pat_binds_n(p)).sum(),
        Pat::None(_) => 0,
        Pat::Some(_, inner) => pat_binds_n(inner),
    }
}

// ---------------------------------------------------------------------------
// Env
// ---------------------------------------------------------------------------

/// A Mono type-checking / reduction environment.
///
/// Mirrors `mono_env.sml`. Carries optional cached expressions for inlining.
#[derive(Debug, Clone)]
pub struct Env {
    /// Datatype definitions: id → (name, constructors)
    pub datatypes: HashMap<usize, (String, Vec<(String, usize, Option<LocTyp>)>)>,
    /// Constructor lookup: constructor-id → (name, opt_arg_type, datatype_id)
    pub constructors: HashMap<usize, (String, Option<LocTyp>, usize)>,
    /// Relative (de Bruijn) bindings: index 0 = most recent.
    /// Each entry: (name, type, optional_cached_expr)
    pub rel_e: Vec<(String, LocTyp, Option<LocExp>)>,
    /// Named (top-level) bindings: id → (name, type, opt_body, settings_str)
    pub named_e: HashMap<usize, (String, LocTyp, Option<LocExp>, String)>,
}

impl Env {
    pub fn empty() -> Self {
        Env {
            datatypes: HashMap::new(),
            constructors: HashMap::new(),
            rel_e: Vec::new(),
            named_e: HashMap::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Datatype bindings
    // -----------------------------------------------------------------------

    #[must_use]
    pub fn push_datatype(
        &self,
        x: &str,
        n: usize,
        xncs: Vec<(String, usize, Option<LocTyp>)>,
    ) -> Env {
        let mut env = self.clone();
        for (cx, cn, ct) in &xncs {
            env.constructors.insert(*cn, (cx.clone(), ct.clone(), n));
        }
        env.datatypes.insert(n, (x.to_string(), xncs));
        env
    }

    pub fn lookup_datatype(
        &self,
        n: usize,
    ) -> Result<&(String, Vec<(String, usize, Option<LocTyp>)>), UnboundError> {
        self.datatypes.get(&n).ok_or(UnboundError {
            kind: UnboundKind::Named,
            index: n,
        })
    }

    // -----------------------------------------------------------------------
    // Relative bindings
    // -----------------------------------------------------------------------

    /// Push a relative binding with no cached expression.
    #[must_use]
    pub fn push_rel(&self, x: &str, t: LocTyp) -> Env {
        self.push_rel_opt(x, t, None)
    }

    /// Push a relative binding with an optional cached expression.
    ///
    /// Existing cached rel expressions are lifted to account for the new binder
    /// (mirrors SML `pushERel`).
    #[must_use]
    pub fn push_rel_opt(&self, x: &str, t: LocTyp, opt_e: Option<LocExp>) -> Env {
        let mut env = self.clone();
        // Lift all existing cached expressions by 1 (new binder shifts indices)
        for (_, _, oe) in &mut env.rel_e {
            if let Some(e) = oe.take() {
                *oe = Some(lift_exp_in_exp(0, &e));
            }
        }
        env.rel_e.insert(0, (x.to_string(), t, opt_e));
        env
    }

    /// Look up the `n`th de Bruijn relative variable.
    /// Returns `(name, type, optional_cached_expr)`.
    pub fn lookup_rel(&self, n: usize) -> Result<&(String, LocTyp, Option<LocExp>), UnboundError> {
        self.rel_e.get(n).ok_or(UnboundError {
            kind: UnboundKind::Rel,
            index: n,
        })
    }

    pub fn rel_len(&self) -> usize {
        self.rel_e.len()
    }

    // -----------------------------------------------------------------------
    // Named bindings
    // -----------------------------------------------------------------------

    /// Register a named binding (no cached expression).
    #[must_use]
    pub fn push_named(&self, x: &str, n: usize, t: LocTyp) -> Env {
        self.push_named_opt(x, n, t, None, "")
    }

    /// Register a named binding with optional cached expression and settings string.
    #[must_use]
    pub fn push_named_opt(
        &self,
        x: &str,
        n: usize,
        t: LocTyp,
        opt_e: Option<LocExp>,
        s: &str,
    ) -> Env {
        let mut env = self.clone();
        env.named_e
            .insert(n, (x.to_string(), t, opt_e, s.to_string()));
        env
    }

    /// Look up a named binding.
    /// Returns `(name, type, optional_cached_expr, settings_str)`.
    pub fn lookup_named(
        &self,
        n: usize,
    ) -> Result<&(String, LocTyp, Option<LocExp>, String), UnboundError> {
        self.named_e.get(&n).ok_or(UnboundError {
            kind: UnboundKind::Named,
            index: n,
        })
    }

    // -----------------------------------------------------------------------
    // Pattern bindings (pushes all variables bound by a pattern)
    // -----------------------------------------------------------------------

    /// Extend environment with all variables bound by `p` (no cached exprs).
    #[must_use]
    pub fn pat_binds(&self, p: &LocPat) -> Env {
        match &p.node {
            Pat::Var(x, t) => self.push_rel(x, t.clone()),
            Pat::Prim(_) => self.clone(),
            Pat::Con(_, _, None) => self.clone(),
            Pat::Con(_, _, Some(inner)) => self.pat_binds(inner),
            Pat::Record(xpts) => xpts
                .iter()
                .fold(self.clone(), |env, (_, p, _)| env.pat_binds(p)),
            Pat::None(_) => self.clone(),
            Pat::Some(_, inner) => self.pat_binds(inner),
        }
    }

    // -----------------------------------------------------------------------
    // decl_binds — extend env with a declaration's definitions
    // -----------------------------------------------------------------------

    /// Process a declaration, adding its bindings to the environment.
    ///
    /// For `DVal`, adds the body as the cached expression (enables inlining).
    /// For `DValRec`, adds `None` as cached expression (no inlining for recursive).
    #[must_use]
    pub fn decl_binds(&self, d: &LocDecl) -> Env {
        use crate::monomorphized::{DatatypeDecl, Decl};
        match &d.node {
            Decl::Datatype(dts) => {
                let mut env = self.clone();
                for DatatypeDecl { name, id, constrs } in dts {
                    let loc = d.span.clone();
                    let constrs_for_env: Vec<_> = constrs
                        .iter()
                        .map(|(cx, cn, ct)| (cx.clone(), *cn, ct.clone()))
                        .collect();
                    env = env.push_datatype(name, *id, constrs_for_env.clone());
                    // Register each constructor as a named binding
                    let dt_typ = crate::error_types::Located::new(
                        crate::monomorphized::Typ::Datatype(
                            *id,
                            std::sync::Arc::new(std::sync::Mutex::new(
                                crate::monomorphized::DatatypeDef {
                                    kind: crate::datatype_kind::DatatypeKind::Option,
                                    constrs: constrs_for_env.clone(),
                                },
                            )),
                        ),
                        loc.clone(),
                    );
                    for (cx, cn, ct) in constrs {
                        let con_typ = match ct {
                            None => dt_typ.clone(),
                            Some(arg_t) => crate::error_types::Located::new(
                                crate::monomorphized::Typ::Fun(
                                    Box::new(arg_t.clone()),
                                    Box::new(dt_typ.clone()),
                                ),
                                loc.clone(),
                            ),
                        };
                        env = env.push_named_opt(cx, *cn, con_typ, None, "");
                    }
                }
                env
            }
            Decl::Val(x, n, t, e, s) => self.push_named_opt(x, *n, t.clone(), Some(e.clone()), s),
            Decl::ValRec(vis) => {
                vis.iter().fold(self.clone(), |env, (x, n, t, _e, s)| {
                    // ValRec: no cached expression (recursive, can't inline directly)
                    env.push_named_opt(x, *n, t.clone(), None, s)
                })
            }
            _ => self.clone(),
        }
    }
}

impl Default for Env {
    fn default() -> Self {
        Env::empty()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;
    use crate::monomorphized::{Exp, Typ};

    fn dummy_t() -> LocTyp {
        Located::dummy(Typ::Ffi("Basis".into(), "int".into()))
    }

    fn rel(n: usize) -> LocExp {
        Located::dummy(Exp::Rel(n))
    }

    #[test]
    fn lift_shifts_free_var() {
        let e = rel(0);
        let lifted = lift_exp_in_exp(0, &e);
        assert!(matches!(lifted.node, Exp::Rel(1)));
    }

    #[test]
    fn lift_does_not_shift_bound_var() {
        let e = rel(0);
        let lifted = lift_exp_in_exp(1, &e);
        assert!(matches!(lifted.node, Exp::Rel(0)));
    }

    #[test]
    fn sub_replaces_target() {
        let target = rel(0);
        let rep = Located::dummy(Exp::Prim(crate::primitives::Prim::Int(42)));
        let result = sub_exp_in_exp(0, &rep, &target);
        assert!(matches!(
            result.node,
            Exp::Prim(crate::primitives::Prim::Int(42))
        ));
    }

    #[test]
    fn sub_decrements_above() {
        let e = rel(2);
        let rep = Located::dummy(Exp::Prim(crate::primitives::Prim::Int(0)));
        let result = sub_exp_in_exp(0, &rep, &e);
        assert!(matches!(result.node, Exp::Rel(1)));
    }

    #[test]
    fn env_push_rel_opt_lifts_existing() {
        // Push x=42 as a cached expression, then push another binding.
        // The cached expression for x should be lifted (Rel(0) → Rel(1))
        let mut env = Env::empty();
        let rep = Located::dummy(Exp::Rel(0));
        env = env.push_rel_opt("x", dummy_t(), Some(rep));
        env = env.push_rel("y", dummy_t());
        // The cached expression for x (now at index 1) should have been lifted
        if let Some(cached) = &env.rel_e[1].2 {
            assert!(
                matches!(cached.node, Exp::Rel(1)),
                "Expected Rel(1), got {:?}",
                cached.node
            );
        } else {
            panic!("Expected cached expression");
        }
    }
}
