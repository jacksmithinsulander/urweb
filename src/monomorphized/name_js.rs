//! name_js — JavaScript fragment naming pass.
//!
//! Ports `name_js.sml`.  Hoists non-trivial `EJavaScript` (non-Source mode)
//! sub-expressions to fresh top-level `DVal` bindings so that the compiled
//! JavaScript can be placed in a single `app.js` file rather than being
//! duplicated inline in every generated page.

use std::collections::BTreeSet;

use crate::error_types::{Located, Span};
use crate::monomorphized::{
    Decl, Exp, File, JavaScriptMode, LocDecl, LocExp, LocPat, LocTyp, Pat, Typ,
};

// ---------------------------------------------------------------------------
// Free variable collection
// ---------------------------------------------------------------------------

/// Return the *depth* of binders introduced by pattern `p`.
fn pat_depth(p: &LocPat) -> usize {
    match &p.node {
        Pat::Var(_, _) => 1,
        Pat::Prim(_) | Pat::None(_) => 0,
        Pat::Con(_, _, inner) => inner.as_ref().map_or(0, |ip| pat_depth(ip)),
        Pat::Record(fields) => fields.iter().map(|(_, p, _)| pat_depth(p)).sum(),
        Pat::Some(_, inner) => pat_depth(inner),
    }
}

/// Collect the names and types introduced by a pattern, in bind order
/// (i.e. the order `pat_extend_ctx` would call `bind`).
fn collect_pat_bindings(p: &LocPat, out: &mut Vec<(String, LocTyp)>) {
    match &p.node {
        Pat::Var(x, t) => out.push((x.clone(), t.clone())),
        Pat::Prim(_) | Pat::None(_) => {}
        Pat::Con(_, _, inner) => {
            if let Some(ip) = inner {
                collect_pat_bindings(ip, out);
            }
        }
        Pat::Record(fields) => {
            for (_, fp, _) in fields {
                collect_pat_bindings(fp, out);
            }
        }
        Pat::Some(_, inner) => collect_pat_bindings(inner, out),
    }
}

/// Prepend the bindings introduced by pattern `p` to `env` so that de Bruijn
/// indices inside the arm body resolve correctly.
///
/// `pat_extend_ctx` calls `bind` in traversal order; each `bind` prepends to
/// `env`, so the last-processed binding ends up at index 0.  We replicate
/// that here by collecting bindings in traversal order and then prepending in
/// reverse (so the last one lands at index 0).
fn extend_env_with_pat(env: &[(String, LocTyp)], p: &LocPat) -> Vec<(String, LocTyp)> {
    let mut bindings = Vec::new();
    collect_pat_bindings(p, &mut bindings);
    // bindings = [first, second, ..., last]
    // after bind-order prepending: env = [last, ..., second, first, ...old]
    bindings
        .into_iter()
        .rev()
        .chain(env.iter().cloned())
        .collect()
}

/// Collect all free variable *levels* in `e`.
///
/// A "level" is `n - depth` for `Exp::Rel(n)` encountered at binder depth
/// `depth`.  Returned as a sorted `BTreeSet` so iteration is deterministic.
fn free_vars(e: &LocExp) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    collect_free(e, 0, &mut out);
    out
}

fn collect_free(e: &LocExp, depth: usize, out: &mut BTreeSet<usize>) {
    use Exp::*;
    match &e.node {
        Rel(n) => {
            if *n >= depth {
                out.insert(*n - depth);
            }
        }
        Prim(_) | Named(_) | Ffi(_, _) => {}
        Con(_, _, arg) => {
            if let std::option::Option::Some(a) = arg {
                collect_free(a, depth, out);
            }
        }
        None(_) => {}
        Some(_, inner) => collect_free(inner, depth, out),
        FfiApp(_, _, args) => {
            for (a, _) in args {
                collect_free(a, depth, out);
            }
        }
        App(e1, e2)
        | Strcat(e1, e2)
        | Seq(e1, e2)
        | Setval(e1, e2)
        | Binop(_, _, e1, e2)
        | SignalBind(e1, e2) => {
            collect_free(e1, depth, out);
            collect_free(e2, depth, out);
        }
        Abs(_, _, _, body) => collect_free(body, depth + 1, out),
        Unop(_, e1)
        | Field(e1, _)
        | Write(e1)
        | SignalReturn(e1)
        | SignalSource(e1)
        | Dml(e1, _)
        | Nextval(e1)
        | Uurlify(e1, _, _)
        | JavaScript(_, e1)
        | Recv(e1, _)
        | Sleep(e1)
        | Spawn(e1)
        | ServerCall(e1, _, _, _) => collect_free(e1, depth, out),
        Record(xets) => {
            for (_, e, _) in xets {
                collect_free(e, depth, out);
            }
        }
        Case(disc, arms, _) => {
            collect_free(disc, depth, out);
            for (p, arm_e) in arms {
                let extra = pat_depth(p);
                collect_free(arm_e, depth + extra, out);
            }
        }
        Error(e1, _) => collect_free(e1, depth, out),
        ReturnBlob {
            blob, mime_type, ..
        } => {
            if let std::option::Option::Some(b) = blob {
                collect_free(b, depth, out);
            }
            collect_free(mime_type, depth, out);
        }
        Redirect(e1, _) => collect_free(e1, depth, out),
        Let(_, _, e1, e2) => {
            collect_free(e1, depth, out);
            collect_free(e2, depth + 1, out);
        }
        Closure(_, envs) => {
            for a in envs {
                collect_free(a, depth, out);
            }
        }
        Query(qm) => {
            collect_free(&qm.query, depth, out);
            collect_free(&qm.body, depth, out);
            collect_free(&qm.initial, depth, out);
        }
    }
}

// ---------------------------------------------------------------------------
// squish — remap free variables to new parameter positions
// ---------------------------------------------------------------------------

/// Remap free variables in `e` so that each old free-variable level
/// `vs[i]` becomes `ERel(depth + i + 1)` (with `+1` reserving slot 0 for
/// the synthetic unit parameter `"_"`).
fn squish(vs: &[usize], e: LocExp) -> LocExp {
    squish_at(vs, 0, e)
}

fn squish_at(vs: &[usize], depth: usize, e: LocExp) -> LocExp {
    let span = e.span.clone();
    let new_node = squish_node(vs, depth, e.node);
    Located::new(new_node, span)
}

fn squish_node(vs: &[usize], depth: usize, e: Exp) -> Exp {
    use Exp::*;
    match e {
        Rel(n) if n >= depth => {
            let level = n - depth;
            let idx = vs.iter().position(|&v| v == level).unwrap_or(0);
            Rel(depth + idx + 1)
        }
        Rel(_) | Prim(_) | Named(_) | Ffi(_, _) | None(_) => e,
        Con(dk, pc, arg) => Con(dk, pc, arg.map(|a| Box::new(squish_at(vs, depth, *a)))),
        Some(t, inner) => Some(t, Box::new(squish_at(vs, depth, *inner))),
        FfiApp(m, x, args) => FfiApp(
            m,
            x,
            args.into_iter()
                .map(|(a, t)| (squish_at(vs, depth, a), t))
                .collect(),
        ),
        App(e1, e2) => App(
            Box::new(squish_at(vs, depth, *e1)),
            Box::new(squish_at(vs, depth, *e2)),
        ),
        Abs(x, dom, ran, body) => Abs(x, dom, ran, Box::new(squish_at(vs, depth + 1, *body))),
        Unop(s, e1) => Unop(s, Box::new(squish_at(vs, depth, *e1))),
        Binop(bi, s, e1, e2) => Binop(
            bi,
            s,
            Box::new(squish_at(vs, depth, *e1)),
            Box::new(squish_at(vs, depth, *e2)),
        ),
        Record(xets) => Record(
            xets.into_iter()
                .map(|(x, e, t)| (x, squish_at(vs, depth, e), t))
                .collect(),
        ),
        Field(e1, x) => Field(Box::new(squish_at(vs, depth, *e1)), x),
        Case(disc, arms, meta) => {
            let disc2 = squish_at(vs, depth, *disc);
            let arms2 = arms
                .into_iter()
                .map(|(p, arm_e)| {
                    let extra = pat_depth(&p);
                    (p, squish_at(vs, depth + extra, arm_e))
                })
                .collect();
            Case(Box::new(disc2), arms2, meta)
        }
        Strcat(e1, e2) => Strcat(
            Box::new(squish_at(vs, depth, *e1)),
            Box::new(squish_at(vs, depth, *e2)),
        ),
        Error(e1, t) => Error(Box::new(squish_at(vs, depth, *e1)), t),
        ReturnBlob { blob, mime_type, t } => ReturnBlob {
            blob: blob.map(|b| Box::new(squish_at(vs, depth, *b))),
            mime_type: Box::new(squish_at(vs, depth, *mime_type)),
            t,
        },
        Redirect(e1, t) => Redirect(Box::new(squish_at(vs, depth, *e1)), t),
        Write(e1) => Write(Box::new(squish_at(vs, depth, *e1))),
        Seq(e1, e2) => Seq(
            Box::new(squish_at(vs, depth, *e1)),
            Box::new(squish_at(vs, depth, *e2)),
        ),
        Let(x, t, e1, e2) => Let(
            x,
            t,
            Box::new(squish_at(vs, depth, *e1)),
            Box::new(squish_at(vs, depth + 1, *e2)),
        ),
        Closure(n, envs) => Closure(
            n,
            envs.into_iter().map(|a| squish_at(vs, depth, a)).collect(),
        ),
        Query(qm) => {
            use crate::monomorphized::QueryMeta;
            Query(QueryMeta {
                query: Box::new(squish_at(vs, depth, *qm.query)),
                body: Box::new(squish_at(vs, depth, *qm.body)),
                initial: Box::new(squish_at(vs, depth, *qm.initial)),
                ..qm
            })
        }
        Dml(e1, fm) => Dml(Box::new(squish_at(vs, depth, *e1)), fm),
        Nextval(e1) => Nextval(Box::new(squish_at(vs, depth, *e1))),
        Setval(e1, e2) => Setval(
            Box::new(squish_at(vs, depth, *e1)),
            Box::new(squish_at(vs, depth, *e2)),
        ),
        Uurlify(e1, t, b) => Uurlify(Box::new(squish_at(vs, depth, *e1)), t, b),
        JavaScript(mode, e1) => JavaScript(mode, Box::new(squish_at(vs, depth, *e1))),
        SignalReturn(e1) => SignalReturn(Box::new(squish_at(vs, depth, *e1))),
        SignalBind(e1, e2) => SignalBind(
            Box::new(squish_at(vs, depth, *e1)),
            Box::new(squish_at(vs, depth, *e2)),
        ),
        SignalSource(e1) => SignalSource(Box::new(squish_at(vs, depth, *e1))),
        ServerCall(e1, t, eff, fm) => ServerCall(Box::new(squish_at(vs, depth, *e1)), t, eff, fm),
        Recv(e1, t) => Recv(Box::new(squish_at(vs, depth, *e1)), t),
        Sleep(e1) => Sleep(Box::new(squish_at(vs, depth, *e1))),
        Spawn(e1) => Spawn(Box::new(squish_at(vs, depth, *e1))),
    }
}

// ---------------------------------------------------------------------------
// Trickiness predicate
// ---------------------------------------------------------------------------

/// `true` for expression nodes that make a JavaScript fragment un-nameable:
/// a reference to a "tricky" named function, or `Basis.sigString`.
fn is_tricky_node(dont_name: &BTreeSet<usize>, e: &Exp) -> bool {
    match e {
        Exp::Named(n) => dont_name.contains(n),
        Exp::FfiApp(m, x, _) => m == "Basis" && x == "sigString",
        _ => false,
    }
}

/// `true` if any sub-expression of `e` is tricky.
fn is_tricky(dont_name: &BTreeSet<usize>, e: &LocExp) -> bool {
    crate::monomorphized::utilities::exp::exists(e, &|_| false, &|node| {
        is_tricky_node(dont_name, node)
    })
}

/// `true` if any expression inside declaration `d` is tricky.
fn decl_is_tricky(dont_name: &BTreeSet<usize>, d: &LocDecl) -> bool {
    crate::monomorphized::utilities::decl::fold(
        d,
        false,
        &|_, s| s,
        &|node, s| s || is_tricky_node(dont_name, node),
        &|_, s| s,
    )
}

/// Build the set of named ids whose JavaScript fragments must not be hoisted
/// (because they reference `sigString` or another tricky function).
fn compute_dont_name(decls: &[LocDecl]) -> BTreeSet<usize> {
    let mut dont_name = BTreeSet::new();
    for d in decls {
        if decl_is_tricky(&dont_name, d) {
            match &d.node {
                Decl::Val(_, n, _, _, _) => {
                    dont_name.insert(*n);
                }
                Decl::ValRec(vis) => {
                    for (_, n, _, _, _) in vis {
                        dont_name.insert(*n);
                    }
                }
                _ => {}
            }
        }
    }
    dont_name
}

// ---------------------------------------------------------------------------
// "already simple" predicate
// ---------------------------------------------------------------------------

fn is_truly_simple(e: &LocExp) -> bool {
    match &e.node {
        Exp::Rel(_) | Exp::Named(_) => true,
        Exp::Record(fields) => fields.is_empty(),
        _ => false,
    }
}

/// `true` if `e` is a chain of applications to trivially-simple arguments
/// whose head is also trivially simple — such expressions need not be hoisted.
fn is_already_simple(e: &LocExp) -> bool {
    match &e.node {
        Exp::App(head, arg) => is_truly_simple(arg) && is_already_simple(head),
        _ => is_truly_simple(e),
    }
}

// ---------------------------------------------------------------------------
// max_named — find the maximum Named id in the file (to pick fresh ids)
// ---------------------------------------------------------------------------

fn max_named(decls: &[LocDecl]) -> usize {
    use crate::monomorphized::utilities::decl;
    decls.iter().fold(0usize, |acc, d| {
        decl::fold(
            d,
            acc,
            &|_, s| s,
            &|node, s| {
                if let Exp::Named(n) = node {
                    s.max(*n)
                } else {
                    s
                }
            },
            &|_, s| s,
        )
    })
}

// ---------------------------------------------------------------------------
// Main rewriter
// ---------------------------------------------------------------------------

/// Mutable state threaded through the rewrite traversal.
struct State<'a> {
    dont_name: &'a BTreeSet<usize>,
    next_name: usize,
    /// New `DVal` tuples accumulated while rewriting one top-level declaration.
    new_vals: Vec<(String, usize, LocTyp, LocExp, String)>,
}

impl<'a> State<'a> {
    /// Rewrite an expression, threading `env` (de Bruijn environment: index 0
    /// = innermost binding) to allow reconstruction of free-variable types.
    fn rw(&mut self, env: &[(String, LocTyp)], e: LocExp) -> LocExp {
        let span = e.span.clone();
        use Exp::*;
        match e.node {
            // ---- binders that extend the environment ---------------------
            Abs(x, dom, ran, body) => {
                let mut new_env = vec![(x.clone(), dom.clone())];
                new_env.extend_from_slice(env);
                let body2 = self.rw(&new_env, *body);
                Located::new(Abs(x, dom, ran, Box::new(body2)), span)
            }
            Let(x, t, e1, e2) => {
                let e1b = self.rw(env, *e1);
                let mut new_env = vec![(x.clone(), t.clone())];
                new_env.extend_from_slice(env);
                let e2b = self.rw(&new_env, *e2);
                Located::new(Let(x, t, Box::new(e1b), Box::new(e2b)), span)
            }
            Case(disc, arms, meta) => {
                let disc2 = self.rw(env, *disc);
                let arms2 = arms
                    .into_iter()
                    .map(|(p, arm_e)| {
                        let new_env = extend_env_with_pat(env, &p);
                        let arm_e2 = self.rw(&new_env, arm_e);
                        (p, arm_e2)
                    })
                    .collect();
                Located::new(Case(Box::new(disc2), arms2, meta), span)
            }

            // ---- the key case: JavaScript fragments ----------------------
            JavaScript(mode, inner) => {
                // Recurse into `inner` first (bottom-up, like SML foldMapB).
                let inner2 = self.rw(env, *inner);
                match &mode {
                    JavaScriptMode::Source(_) => {
                        // Source-mode fragments are not hoisted.
                        Located::new(JavaScript(mode, Box::new(inner2)), span)
                    }
                    _ => {
                        if is_already_simple(&inner2) || is_tricky(self.dont_name, &inner2) {
                            Located::new(JavaScript(mode, Box::new(inner2)), span)
                        } else {
                            self.hoist(env, mode, inner2, span)
                        }
                    }
                }
            }

            // ---- structural cases: recurse without env change -----------
            node => {
                let new_node = self.rw_node(env, node, &span);
                Located::new(new_node, span)
            }
        }
    }

    /// Recurse into the children of a non-binder expression node.
    fn rw_node(&mut self, env: &[(String, LocTyp)], e: Exp, _span: &Span) -> Exp {
        use Exp::*;
        macro_rules! rw {
            ($e:expr) => {
                self.rw(env, $e)
            };
        }
        match e {
            Prim(_) | Rel(_) | Named(_) | Ffi(_, _) | None(_) => e,
            Con(dk, pc, arg) => Con(dk, pc, arg.map(|a| Box::new(rw!(*a)))),
            Some(t, inner) => Some(t, Box::new(rw!(*inner))),
            FfiApp(m, x, args) => {
                FfiApp(m, x, args.into_iter().map(|(a, t)| (rw!(a), t)).collect())
            }
            App(e1, e2) => App(Box::new(rw!(*e1)), Box::new(rw!(*e2))),
            Unop(s, e1) => Unop(s, Box::new(rw!(*e1))),
            Binop(bi, s, e1, e2) => Binop(bi, s, Box::new(rw!(*e1)), Box::new(rw!(*e2))),
            Record(xets) => Record(xets.into_iter().map(|(x, e, t)| (x, rw!(e), t)).collect()),
            Field(e1, x) => Field(Box::new(rw!(*e1)), x),
            Strcat(e1, e2) => Strcat(Box::new(rw!(*e1)), Box::new(rw!(*e2))),
            Error(e1, t) => Error(Box::new(rw!(*e1)), t),
            ReturnBlob { blob, mime_type, t } => ReturnBlob {
                blob: blob.map(|b| Box::new(rw!(*b))),
                mime_type: Box::new(rw!(*mime_type)),
                t,
            },
            Redirect(e1, t) => Redirect(Box::new(rw!(*e1)), t),
            Write(e1) => Write(Box::new(rw!(*e1))),
            Seq(e1, e2) => Seq(Box::new(rw!(*e1)), Box::new(rw!(*e2))),
            Closure(n, envs) => Closure(n, envs.into_iter().map(|a| rw!(a)).collect()),
            Query(qm) => {
                use crate::monomorphized::QueryMeta;
                Query(QueryMeta {
                    query: Box::new(rw!(*qm.query)),
                    body: Box::new(rw!(*qm.body)),
                    initial: Box::new(rw!(*qm.initial)),
                    ..qm
                })
            }
            Dml(e1, fm) => Dml(Box::new(rw!(*e1)), fm),
            Nextval(e1) => Nextval(Box::new(rw!(*e1))),
            Setval(e1, e2) => Setval(Box::new(rw!(*e1)), Box::new(rw!(*e2))),
            Uurlify(e1, t, b) => Uurlify(Box::new(rw!(*e1)), t, b),
            SignalReturn(e1) => SignalReturn(Box::new(rw!(*e1))),
            SignalBind(e1, e2) => SignalBind(Box::new(rw!(*e1)), Box::new(rw!(*e2))),
            SignalSource(e1) => SignalSource(Box::new(rw!(*e1))),
            ServerCall(e1, t, eff, fm) => ServerCall(Box::new(rw!(*e1)), t, eff, fm),
            Recv(e1, t) => Recv(Box::new(rw!(*e1)), t),
            Sleep(e1) => Sleep(Box::new(rw!(*e1))),
            Spawn(e1) => Spawn(Box::new(rw!(*e1))),
            // Defensive: binders are normally handled in `rw` before `rw_node`.
            Abs(x, dom, ran, body) => {
                self.rw(env, Located::new(Abs(x, dom, ran, body), _span.clone()))
                    .node
            }
            Let(x, t, e1, e2) => {
                self.rw(env, Located::new(Let(x, t, e1, e2), _span.clone()))
                    .node
            }
            Case(d, arms, meta) => {
                self.rw(env, Located::new(Case(d, arms, meta), _span.clone()))
                    .node
            }
            JavaScript(m, inner) => {
                self.rw(env, Located::new(JavaScript(m, inner), _span.clone()))
                    .node
            }
        }
    }

    /// Hoist `inner` (a non-trivial non-tricky JavaScript sub-expression) to a
    /// fresh top-level `DVal`, replacing it with a call to that new binding.
    ///
    /// Mirrors the hoisting logic in `name_js.sml`:
    /// - Compute free variables `vs` of `inner`.
    /// - Build `λvs[0]. … λvs[n-1]. λ_:unit. squish(inner)`.
    /// - Record the new DVal and return `EJavaScript(Script, Named(id) vs… ())`.
    fn hoist(
        &mut self,
        env: &[(String, LocTyp)],
        _mode: JavaScriptMode,
        inner: LocExp,
        span: Span,
    ) -> LocExp {
        let loc = span.clone();
        let mkt = |node: Typ| Located::new(node, loc.clone());
        let mke = |node: Exp| Located::new(node, loc.clone());

        // Collect free variable levels (sorted).
        let free_set = free_vars(&inner);
        let vs: Vec<usize> = free_set.into_iter().collect();

        let n = self.next_name;
        self.next_name += 1;
        let x = format!("script{}", n);

        let unit_t = mkt(Typ::Record(vec![]));
        let string_t = mkt(Typ::Ffi("Basis".into(), "string".into()));
        let base_t = mkt(Typ::Fun(
            Box::new(unit_t.clone()),
            Box::new(string_t.clone()),
        ));

        // Build the full function type: type0 → type1 → … → unit → string
        // (foldl over vs in order, so vs[0] is the outermost param)
        let full_t = vs.iter().fold(base_t.clone(), |acc_t, &v| {
            let v_t = if v < env.len() {
                env[v].1.clone()
            } else {
                mkt(Typ::Record(vec![])) // fallback (shouldn't happen)
            };
            mkt(Typ::Fun(Box::new(v_t), Box::new(acc_t)))
        });

        // Squish free variables in `inner` to new de Bruijn indices.
        let squished = squish(&vs, inner);

        // Wrap in the unit lambda: λ_:unit. squished
        let unit_body = mke(Exp::Abs(
            "_".into(),
            unit_t.clone(),
            string_t.clone(),
            Box::new(squished),
        ));

        // foldl over vs: wrap with outer lambdas (vs[0] outermost)
        let (final_body, _) = vs.iter().fold((unit_body, base_t), |(body, t), &v| {
            let (vname, vt) = if v < env.len() {
                env[v].clone()
            } else {
                ("_".into(), mkt(Typ::Record(vec![])))
            };
            let new_e = mke(Exp::Abs(vname, vt.clone(), t.clone(), Box::new(body)));
            let new_t = mkt(Typ::Fun(Box::new(vt), Box::new(t)));
            (new_e, new_t)
        });

        self.new_vals
            .push((x.clone(), n, full_t, final_body, "<script>".into()));

        // Build the call expression:
        //   ENamed(n)  applied to vs in foldr order  applied to ()
        //
        // SML foldr: f(vs[0], f(vs[1], …, f(vs[k-1], ENamed n)…))
        //   where f(i, acc) = EApp(acc, ERel i)
        // ⟹ EApp(…EApp(EApp(ENamed n, ERel vs[k-1]), …, ERel vs[1])…, ERel vs[0])
        let base_call = mke(Exp::Named(n));
        let applied = vs.iter().rev().fold(base_call, |acc, &v| {
            mke(Exp::App(Box::new(acc), Box::new(mke(Exp::Rel(v)))))
        });
        let with_unit = mke(Exp::App(
            Box::new(applied),
            Box::new(mke(Exp::Record(vec![]))),
        ));

        mke(Exp::JavaScript(JavaScriptMode::Script, Box::new(with_unit)))
    }

    /// Rewrite a declaration.  Returns the (possibly transformed) declaration
    /// and populates `self.new_vals` with any hoisted DVal tuples.
    fn rw_decl(&mut self, d: LocDecl) -> LocDecl {
        let span = d.span.clone();
        match d.node {
            Decl::Val(x, n, t, e, s) => {
                let e2 = self.rw(&[], e);
                Located::new(Decl::Val(x, n, t, e2, s), span)
            }
            Decl::ValRec(vis) => {
                let vis2 = vis
                    .into_iter()
                    .map(|(x, n, t, e, s)| {
                        let e2 = self.rw(&[], e);
                        (x, n, t, e2, s)
                    })
                    .collect();
                Located::new(Decl::ValRec(vis2), span)
            }
            Decl::Export(ek, url, n, ts, rt, b) => {
                Located::new(Decl::Export(ek, url, n, ts, rt, b), span)
            }
            Decl::Table(nm, xts, pe, ce) => {
                let pe2 = self.rw(&[], pe);
                let ce2 = self.rw(&[], ce);
                Located::new(Decl::Table(nm, xts, pe2, ce2), span)
            }
            Decl::Task(e1, e2) => {
                let e1b = self.rw(&[], e1);
                let e2b = self.rw(&[], e2);
                Located::new(Decl::Task(e1b, e2b), span)
            }
            Decl::Policy(pol) => {
                use crate::monomorphized::Policy;
                let pol2 = match pol {
                    Policy::Client(e) => Policy::Client(self.rw(&[], e)),
                    Policy::Insert(e) => Policy::Insert(self.rw(&[], e)),
                    Policy::Delete(e) => Policy::Delete(self.rw(&[], e)),
                    Policy::Update(e) => Policy::Update(self.rw(&[], e)),
                    Policy::Sequence(e) => Policy::Sequence(self.rw(&[], e)),
                };
                Located::new(Decl::Policy(pol2), span)
            }
            // All other declarations have no expressions to rewrite.
            other => Located::new(other, span),
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Name JavaScript fragments in `file`.
///
/// Each non-trivial `EJavaScript` (non-Source-mode) sub-expression is hoisted
/// to a fresh top-level `DVal` so that the JavaScript can be placed in a
/// single `app.js` file.
pub fn rewrite(file: File) -> File {
    let (decls, exports) = file;

    let dont_name = compute_dont_name(&decls);
    let max_n = max_named(&decls);

    let mut state = State {
        dont_name: &dont_name,
        next_name: max_n + 1,
        new_vals: Vec::new(),
    };

    let mut result = Vec::with_capacity(decls.len());

    for d in decls {
        let span = d.span.clone();
        let new_d = state.rw_decl(d);
        let new_vals = std::mem::take(&mut state.new_vals);

        match &new_d.node {
            Decl::ValRec(vis) if !new_vals.is_empty() => {
                // Merge hoisted vals into the same recursive group so they can
                // be mutually recursive (matches SML `DValRec (vis @ newDs)`).
                let mut all = vis.clone();
                all.extend(new_vals);
                result.push(Located::new(Decl::ValRec(all), span));
            }
            _ => {
                // Prepend hoisted vals (in encounter order) before the decl.
                // SML: `List.revAppend (map DVal newDs, [d])` = rev(newDs) ++ [d].
                // `new_vals` is in encounter order; we emit them as-is.
                for (vx, vn, vt, ve, vs) in new_vals {
                    result.push(Located::new(Decl::Val(vx, vn, vt, ve, vs), span.clone()));
                }
                result.push(new_d);
            }
        }
    }

    (result, exports)
}
