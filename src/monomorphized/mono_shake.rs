//! Dead-code elimination for the Mono IR.
//!
//! Removes unreachable `DVal`, `DValRec`, and `DDatatype` declarations by
//! starting from "root" declarations (exports, tables, tasks, etc.) and
//! transitively marking everything they reference.
//!
//! Mirrors `mono_shake.sml`.

use std::collections::{HashMap, HashSet};

use crate::monomorphized::*;

// ---------------------------------------------------------------------------
// Reachability state
// ---------------------------------------------------------------------------

struct Free {
    con: HashSet<usize>,
    exp: HashSet<usize>,
}

// ---------------------------------------------------------------------------
// shake_typ — mark every datatype reachable through a type
// ---------------------------------------------------------------------------

fn shake_typ(
    mut s: Free,
    cdef: &HashMap<usize, Vec<(String, usize, Option<LocTyp>)>>,
    t: &LocTyp,
) -> Free {
    match &t.node {
        Typ::Datatype(n, _) => {
            let n = *n;
            if !s.con.contains(&n) {
                s.con.insert(n);
                // Eagerly walk constructor field types.
                if let Some(xncs) = cdef.get(&n).cloned() {
                    for (_, _, opt_t) in xncs {
                        if let Some(inner_t) = opt_t {
                            s = shake_typ(s, cdef, &inner_t);
                        }
                    }
                }
            }
            s
        }
        Typ::Fun(d, r) => {
            let s = shake_typ(s, cdef, d);
            shake_typ(s, cdef, r)
        }
        Typ::Record(xts) => xts.iter().fold(s, |s, (_, t)| shake_typ(s, cdef, t)),
        Typ::Option(inner) | Typ::List(inner) | Typ::Signal(inner) => shake_typ(s, cdef, inner),
        // Shake the result type of a transaction to keep reachable datatypes alive.
        Typ::Transaction(inner) => shake_typ(s, cdef, inner),
        Typ::Ffi(_, _) | Typ::Source => s,
    }
}

// ---------------------------------------------------------------------------
// shake_pat — mark types reachable through a pattern
// ---------------------------------------------------------------------------

fn shake_pat(
    s: Free,
    cdef: &HashMap<usize, Vec<(String, usize, Option<LocTyp>)>>,
    p: &LocPat,
) -> Free {
    match &p.node {
        Pat::Var(_, t) => shake_typ(s, cdef, t),
        Pat::Prim(_) => s,
        Pat::Con(_, pc, inner) => {
            let s = match pc {
                PatCon::Ffi { arg: Some(t), .. } => shake_typ(s, cdef, t),
                _ => s,
            };
            if let Some(inner_p) = inner.as_ref() {
                shake_pat(s, cdef, inner_p)
            } else {
                s
            }
        }
        Pat::Record(xpts) => xpts.iter().fold(s, |s, (_, p, t)| {
            let s = shake_pat(s, cdef, p);
            shake_typ(s, cdef, t)
        }),
        Pat::None(t) => shake_typ(s, cdef, t),
        Pat::Some(t, inner) => {
            let s = shake_typ(s, cdef, t);
            shake_pat(s, cdef, inner)
        }
    }
}

// ---------------------------------------------------------------------------
// shake_exp — mark every name / type reachable through an expression
// ---------------------------------------------------------------------------

fn shake_exp(
    mut s: Free,
    cdef: &HashMap<usize, Vec<(String, usize, Option<LocTyp>)>>,
    edef: &HashMap<usize, (LocTyp, LocExp)>,
    e: &LocExp,
) -> Free {
    match &e.node {
        Exp::Named(n) => {
            let n = *n;
            if s.exp.contains(&n) {
                return s;
            }
            s.exp.insert(n);
            if let Some((t, body)) = edef.get(&n).cloned() {
                s = shake_typ(s, cdef, &t);
                s = shake_exp(s, cdef, edef, &body);
            }
            s
        }

        Exp::Prim(_) | Exp::Rel(_) | Exp::Ffi(_, _) => s,

        Exp::Con(_, pc, arg) => {
            let s = match pc {
                PatCon::Ffi { arg: Some(t), .. } => shake_typ(s, cdef, t),
                _ => s,
            };
            if let Some(a) = arg.as_ref() {
                shake_exp(s, cdef, edef, a)
            } else {
                s
            }
        }

        Exp::None(t) => shake_typ(s, cdef, t),
        Exp::Some(t, inner) => {
            let s = shake_typ(s, cdef, t);
            shake_exp(s, cdef, edef, inner)
        }

        Exp::FfiApp(_, _, args) => args.iter().fold(s, |s, (e, t)| {
            let s = shake_exp(s, cdef, edef, e);
            shake_typ(s, cdef, t)
        }),

        Exp::App(e1, e2)
        | Exp::Binop(_, _, e1, e2)
        | Exp::Strcat(e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::SignalBind(e1, e2)
        | Exp::Setval(e1, e2) => {
            let s = shake_exp(s, cdef, edef, e1);
            shake_exp(s, cdef, edef, e2)
        }

        Exp::Abs(_, dom, ran, body) => {
            let s = shake_typ(s, cdef, dom);
            let s = shake_typ(s, cdef, ran);
            shake_exp(s, cdef, edef, body)
        }

        Exp::Unop(_, inner)
        | Exp::Field(inner, _)
        | Exp::Write(inner)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner)
        | Exp::Nextval(inner)
        | Exp::Dml(inner, _) => shake_exp(s, cdef, edef, inner),

        Exp::Record(xets) => xets.iter().fold(s, |s, (_, e, t)| {
            let s = shake_exp(s, cdef, edef, e);
            shake_typ(s, cdef, t)
        }),

        Exp::Case(disc, arms, meta) => {
            let s = shake_exp(s, cdef, edef, disc);
            let s = arms.iter().fold(s, |s, (p, arm_e)| {
                let s = shake_pat(s, cdef, p);
                shake_exp(s, cdef, edef, arm_e)
            });
            let s = shake_typ(s, cdef, &meta.disc);
            shake_typ(s, cdef, &meta.result)
        }

        Exp::Error(inner, t) | Exp::Redirect(inner, t) | Exp::Uurlify(inner, t, _) => {
            let s = shake_exp(s, cdef, edef, inner);
            shake_typ(s, cdef, t)
        }

        Exp::ReturnBlob { blob, mime_type, t } => {
            let s = if let Some(b) = blob.as_ref() {
                shake_exp(s, cdef, edef, b)
            } else {
                s
            };
            let s = shake_exp(s, cdef, edef, mime_type);
            shake_typ(s, cdef, t)
        }

        Exp::Let(_, t, e1, e2) => {
            let s = shake_typ(s, cdef, t);
            let s = shake_exp(s, cdef, edef, e1);
            shake_exp(s, cdef, edef, e2)
        }

        Exp::Closure(_, envs) => envs.iter().fold(s, |s, e| shake_exp(s, cdef, edef, e)),

        Exp::Query(qm) => {
            let s = qm.exps.iter().fold(s, |s, (_, t)| shake_typ(s, cdef, t));
            let s = qm.tables.iter().fold(s, |s, (_, xts)| {
                xts.iter().fold(s, |s, (_, t)| shake_typ(s, cdef, t))
            });
            let s = shake_typ(s, cdef, &qm.state);
            let s = shake_exp(s, cdef, edef, &qm.query);
            let s = shake_exp(s, cdef, edef, &qm.body);
            shake_exp(s, cdef, edef, &qm.initial)
        }

        Exp::JavaScript(mode, inner) => {
            let s = if let JavaScriptMode::Source(t) = mode {
                shake_typ(s, cdef, t)
            } else {
                s
            };
            shake_exp(s, cdef, edef, inner)
        }

        Exp::ServerCall(inner, t, _, _) | Exp::Recv(inner, t) => {
            let s = shake_exp(s, cdef, edef, inner);
            shake_typ(s, cdef, t)
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Remove unreachable declarations from a Mono file.
///
/// Mirrors `MonoShake.shake`.
pub fn shake(file: File) -> File {
    let (decls, exports) = file;

    // Build definition maps.
    let mut cdef: HashMap<usize, Vec<(String, usize, Option<LocTyp>)>> = HashMap::new();
    let mut edef: HashMap<usize, (LocTyp, LocExp)> = HashMap::new();
    for d in &decls {
        match &d.node {
            Decl::Datatype(dts) => {
                for dt in dts {
                    cdef.insert(dt.id, dt.constrs.clone());
                }
            }
            Decl::Val(_, n, t, e, _) => {
                edef.insert(*n, (t.clone(), e.clone()));
            }
            Decl::ValRec(vis) => {
                for (_, n, t, e, _) in vis {
                    edef.insert(*n, (t.clone(), e.clone()));
                }
            }
            _ => {}
        }
    }

    // Seed from root declarations.
    let mut s = Free {
        con: HashSet::new(),
        exp: HashSet::new(),
    };
    for d in &decls {
        match &d.node {
            Decl::Export(_, _, n, _, _, _) => {
                s.exp.insert(*n);
            }
            Decl::Database {
                expunge,
                initialize,
                ..
            } => {
                s.exp.insert(*expunge);
                s.exp.insert(*initialize);
            }
            Decl::Task(e1, e2) => {
                s = shake_exp(s, &cdef, &edef, e1);
                s = shake_exp(s, &cdef, &edef, e2);
            }
            Decl::Table(_, xts, e1, e2) => {
                for (_, t) in xts {
                    s = shake_typ(s, &cdef, t);
                }
                s = shake_exp(s, &cdef, &edef, e1);
                s = shake_exp(s, &cdef, &edef, e2);
            }
            Decl::View(_, xts, e) => {
                for (_, t) in xts {
                    s = shake_typ(s, &cdef, t);
                }
                s = shake_exp(s, &cdef, &edef, e);
            }
            Decl::Policy(pol) => {
                let pol_e = match pol {
                    Policy::Client(e)
                    | Policy::Insert(e)
                    | Policy::Delete(e)
                    | Policy::Update(e)
                    | Policy::Sequence(e) => e,
                };
                s = shake_exp(s, &cdef, &edef, pol_e);
            }
            Decl::OnError(n) => {
                s.exp.insert(*n);
            }
            _ => {}
        }
    }

    // Expand seeded cons (their field types may reference more cons).
    let seeded_cons: Vec<usize> = s.con.iter().copied().collect();
    for n in seeded_cons {
        if let Some(xncs) = cdef.get(&n).cloned() {
            for (_, _, opt_t) in xncs {
                if let Some(t) = opt_t {
                    s = shake_typ(s, &cdef, &t);
                }
            }
        }
    }

    // Expand seeded exps (traverse their bodies).
    let seeded_exps: Vec<usize> = s.exp.iter().copied().collect();
    for n in seeded_exps {
        if let Some((t, body)) = edef.get(&n).cloned() {
            s = shake_typ(s, &cdef, &t);
            s = shake_exp(s, &cdef, &edef, &body);
        }
    }

    // Fix ValRec groups: when any member is reachable, mark all members.
    // Bounded to prevent runaway mutants from looping forever.
    const MAX_SHAKE_VALREC_ITERATIONS: usize = 10_000;
    for _ in 0..MAX_SHAKE_VALREC_ITERATIONS {
        let mut changed = false;
        for d in &decls {
            if let Decl::ValRec(vis) = &d.node {
                if vis.iter().any(|(_, n, _, _, _)| s.exp.contains(n)) {
                    for (_, n, _, e, _) in vis {
                        if !s.exp.contains(n) {
                            changed = true;
                            s.exp.insert(*n);
                            let body = e.clone();
                            s = shake_exp(s, &cdef, &edef, &body);
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Filter declarations.
    let filtered = decls
        .into_iter()
        .filter(|d| match &d.node {
            Decl::Datatype(dts) => dts.iter().any(|dt| s.con.contains(&dt.id)),
            Decl::Val(_, n, _, _, _) => s.exp.contains(n),
            Decl::ValRec(vis) => vis.iter().any(|(_, n, _, _, _)| s.exp.contains(n)),
            _ => true,
        })
        .collect();

    (filtered, exports)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    #[test]
    fn shake_empty_file() {
        let result = shake((vec![], vec![]));
        assert!(result.0.is_empty());
        assert!(result.1.is_empty());
    }

    /// An unreferenced DVal is removed.
    #[test]
    fn shake_removes_unreferenced_val() {
        let e = dummy(Exp::Prim(crate::primitives::Prim::Int(42)));
        let t = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let decl = dummy(Decl::Val("foo".into(), 1, t, e, "foo".into()));
        let (out, _) = shake((vec![decl], vec![]));
        assert!(out.is_empty(), "unreferenced DVal should be removed");
    }
}
