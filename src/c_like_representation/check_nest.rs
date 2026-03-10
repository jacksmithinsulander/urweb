//! CheckNest pass: annotate EQuery.prepared.nested on CJR.
//!
//! For each `EQuery` that has a prepared statement, checks whether that
//! prepared statement's id appears inside the query body (i.e. the query is
//! "nested" — a prepared query references itself inside the row-processing
//! body). Sets `PreparedQuery.nested` accordingly.
//!
//! In `prepare.rs`, `nested` is conservatively set to `true`; this pass
//! refines it to the precise value.
//!
//! Mirrors `CheckNest.annotate` in `checknest.sml`.

use std::collections::{HashMap, HashSet};

use crate::c_like_representation::{Decl, Exp, File, LocDecl, LocExp};
use crate::error_types::Located;

// ---------------------------------------------------------------------------
// expUses — collect prepared-statement IDs used in an expression
// ---------------------------------------------------------------------------

/// Return the set of prepared-statement IDs used (directly or indirectly via
/// named globals) by expression `e`.
fn exp_uses(globals: &HashMap<usize, HashSet<usize>>, e: &LocExp) -> HashSet<usize> {
    let mut out = HashSet::new();
    exp_uses_into(globals, e, &mut out);
    out
}

fn exp_uses_into(globals: &HashMap<usize, HashSet<usize>>, e: &LocExp, out: &mut HashSet<usize>) {
    match &e.node {
        Exp::Prim(_) | Exp::Rel(_) | Exp::Ffi(_, _) => {}

        Exp::Named(n) => {
            if let Some(ids) = globals.get(n) {
                out.extend(ids.iter().copied());
            }
        }

        Exp::Con(_, _, Some(inner)) => exp_uses_into(globals, inner, out),
        Exp::Con(_, _, None) | Exp::None(_) => {}
        Exp::Some(_, inner) => exp_uses_into(globals, inner, out),

        Exp::FfiApp(_, _, args) => {
            for (ae, _) in args {
                exp_uses_into(globals, ae, out);
            }
        }
        Exp::App(f, args) => {
            exp_uses_into(globals, f, out);
            for ae in args {
                exp_uses_into(globals, ae, out);
            }
        }

        Exp::Unop(_, inner) => exp_uses_into(globals, inner, out),
        Exp::Binop(_, e1, e2) => {
            exp_uses_into(globals, e1, out);
            exp_uses_into(globals, e2, out);
        }

        Exp::Record(_, fields) => {
            for (_, fe) in fields {
                exp_uses_into(globals, fe, out);
            }
        }
        Exp::Field(inner, _) => exp_uses_into(globals, inner, out),

        Exp::Case(scrutinee, arms, _) => {
            exp_uses_into(globals, scrutinee, out);
            for (_, ae) in arms {
                exp_uses_into(globals, ae, out);
            }
        }

        Exp::Error(inner, _) => exp_uses_into(globals, inner, out),
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            if let Some(b) = blob {
                exp_uses_into(globals, b, out);
            }
            exp_uses_into(globals, mime_type, out);
        }
        Exp::Redirect(inner, _) => exp_uses_into(globals, inner, out),

        Exp::Write(inner) => exp_uses_into(globals, inner, out),
        Exp::Seq(e1, e2) => {
            exp_uses_into(globals, e1, out);
            exp_uses_into(globals, e2, out);
        }
        Exp::Let(_, _, e1, e2) => {
            exp_uses_into(globals, e1, out);
            exp_uses_into(globals, e2, out);
        }

        Exp::Query(qm) => {
            exp_uses_into(globals, &qm.query, out);
            exp_uses_into(globals, &qm.body, out);
            exp_uses_into(globals, &qm.initial, out);
            if let Some(pq) = &qm.prepared {
                out.insert(pq.id);
            }
        }
        Exp::Dml(dm) => {
            exp_uses_into(globals, &dm.dml, out);
        }
        Exp::Nextval { seq, .. } => {
            exp_uses_into(globals, seq, out);
        }
        Exp::Setval { seq, count } => {
            exp_uses_into(globals, seq, out);
            exp_uses_into(globals, count, out);
        }

        Exp::Uurlify(inner, _, _) => exp_uses_into(globals, inner, out),
    }
}

// ---------------------------------------------------------------------------
// annotateExp — rewrite EQuery.prepared.nested
// ---------------------------------------------------------------------------

fn annotate_exp(globals: &HashMap<usize, HashSet<usize>>, e: LocExp) -> LocExp {
    let loc = e.span.clone();
    let new_node = match e.node {
        Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) => return e,

        Exp::Con(dk, pc, opt_e) => Exp::Con(
            dk,
            pc,
            opt_e.map(|inner| Box::new(annotate_exp(globals, *inner))),
        ),
        Exp::None(_) => return e,
        Exp::Some(t, inner) => Exp::Some(t, Box::new(annotate_exp(globals, *inner))),

        Exp::FfiApp(m, f, args) => {
            let args = args
                .into_iter()
                .map(|(ae, at)| (annotate_exp(globals, ae), at))
                .collect();
            Exp::FfiApp(m, f, args)
        }
        Exp::App(f, args) => {
            let f = Box::new(annotate_exp(globals, *f));
            let args = args
                .into_iter()
                .map(|ae| annotate_exp(globals, ae))
                .collect();
            Exp::App(f, args)
        }

        Exp::Unop(op, inner) => Exp::Unop(op, Box::new(annotate_exp(globals, *inner))),
        Exp::Binop(op, e1, e2) => Exp::Binop(
            op,
            Box::new(annotate_exp(globals, *e1)),
            Box::new(annotate_exp(globals, *e2)),
        ),

        Exp::Record(id, fields) => {
            let fields = fields
                .into_iter()
                .map(|(name, fe)| (name, annotate_exp(globals, fe)))
                .collect();
            Exp::Record(id, fields)
        }
        Exp::Field(inner, f) => Exp::Field(Box::new(annotate_exp(globals, *inner)), f),

        Exp::Case(scrutinee, arms, meta) => {
            let scrutinee = Box::new(annotate_exp(globals, *scrutinee));
            let arms = arms
                .into_iter()
                .map(|(p, ae)| (p, annotate_exp(globals, ae)))
                .collect();
            Exp::Case(scrutinee, arms, meta)
        }

        Exp::Error(inner, t) => Exp::Error(Box::new(annotate_exp(globals, *inner)), t),
        Exp::ReturnBlob { blob, mime_type, t } => Exp::ReturnBlob {
            blob: blob.map(|b| Box::new(annotate_exp(globals, *b))),
            mime_type: Box::new(annotate_exp(globals, *mime_type)),
            t,
        },
        Exp::Redirect(inner, t) => Exp::Redirect(Box::new(annotate_exp(globals, *inner)), t),

        Exp::Write(inner) => Exp::Write(Box::new(annotate_exp(globals, *inner))),
        Exp::Seq(e1, e2) => Exp::Seq(
            Box::new(annotate_exp(globals, *e1)),
            Box::new(annotate_exp(globals, *e2)),
        ),
        Exp::Let(x, t, e1, e2) => Exp::Let(
            x,
            t,
            Box::new(annotate_exp(globals, *e1)),
            Box::new(annotate_exp(globals, *e2)),
        ),

        Exp::Query(mut qm) => {
            // Annotate sub-expressions first.
            qm.body = Box::new(annotate_exp(globals, *qm.body));

            // Compute what prepared-statement IDs the body uses.
            if let Some(pq) = &mut qm.prepared {
                let body_uses = exp_uses(globals, &qm.body);
                pq.nested = body_uses.contains(&pq.id);
            }

            Exp::Query(qm)
        }

        Exp::Dml(dm) => {
            let dml = Box::new(annotate_exp(globals, *dm.dml));
            Exp::Dml(crate::c_like_representation::DmlMeta { dml, ..dm })
        }
        Exp::Nextval { seq, prepared } => Exp::Nextval {
            seq: Box::new(annotate_exp(globals, *seq)),
            prepared,
        },
        Exp::Setval { seq, count } => Exp::Setval {
            seq: Box::new(annotate_exp(globals, *seq)),
            count: Box::new(annotate_exp(globals, *count)),
        },

        Exp::Uurlify(inner, t, b) => Exp::Uurlify(Box::new(annotate_exp(globals, *inner)), t, b),
    };
    Located::new(new_node, loc)
}

// ---------------------------------------------------------------------------
// Declaration processing
// ---------------------------------------------------------------------------

/// Compute the set of prepared-statement IDs used by a named value.
fn global_uses(globals: &HashMap<usize, HashSet<usize>>, e: &LocExp) -> HashSet<usize> {
    exp_uses(globals, e)
}

fn annotate_decl(globals: &HashMap<usize, HashSet<usize>>, d: LocDecl) -> LocDecl {
    let loc = d.span.clone();
    let new_node = match d.node {
        Decl::Val(x, n, t, e) => Decl::Val(x, n, t, annotate_exp(globals, e)),
        Decl::Fun(x, n, params, t, e) => Decl::Fun(x, n, params, t, annotate_exp(globals, e)),
        Decl::FunRec(fs) => {
            let fs = fs
                .into_iter()
                .map(|(x, n, params, t, e)| (x, n, params, t, annotate_exp(globals, e)))
                .collect();
            Decl::FunRec(fs)
        }
        Decl::Task(task, x1, x2, e) => Decl::Task(task, x1, x2, annotate_exp(globals, e)),
        other => other,
    };
    Located::new(new_node, loc)
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Annotate a CJR file: set `PreparedQuery.nested` correctly for each
/// `EQuery` that has a prepared statement.
///
/// A query is nested if the prepared-statement ID it uses appears inside
/// its own body (i.e., the body performs another query using the same
/// prepared statement — this requires special handling in the C runtime).
///
/// Mirrors `CheckNest.annotate` in `checknest.sml`.
pub fn annotate(file: File) -> File {
    let (decls, exports) = file;

    // First pass: build `globals` map (named id → set of prepared ids used).
    // Mirror the SML: DVal/DFun/DFunRec contribute entries.
    let mut globals: HashMap<usize, HashSet<usize>> = HashMap::new();

    for d in &decls {
        match &d.node {
            Decl::Val(_, n, _, e) => {
                let uses = global_uses(&globals, e);
                globals.insert(*n, uses);
            }
            Decl::Fun(_, n, _, _, e) => {
                let uses = global_uses(&globals, e);
                globals.insert(*n, uses);
            }
            Decl::FunRec(fs) => {
                // For mutual recursion, union all uses and assign to all.
                let mut all_uses: HashSet<usize> = HashSet::new();
                for (_, _, _, _, e) in fs {
                    all_uses.extend(global_uses(&globals, e));
                }
                for (_, n, _, _, _) in fs {
                    globals.insert(*n, all_uses.clone());
                }
            }
            _ => {}
        }
    }

    // Second pass: annotate EQuery.prepared.nested.
    let decls = decls
        .into_iter()
        .map(|d| annotate_decl(&globals, d))
        .collect();

    (decls, exports)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c_like_representation::{PreparedQuery, QueryMeta, Typ};
    use crate::error_types::Located;

    fn dummy_typ() -> crate::c_like_representation::LocTyp {
        Located::dummy(Typ::Record(0))
    }

    fn dummy_exp() -> LocExp {
        Located::dummy(Exp::Prim(crate::primitives::Prim::Int(0)))
    }

    #[test]
    fn annotate_empty_file_ok() {
        let (decls, exports) = annotate((vec![], vec![]));
        assert!(decls.is_empty());
        assert!(exports.is_empty());
    }

    #[test]
    fn non_nested_query_gets_false() {
        // Build an EQuery whose body doesn't use the prepared id.
        let prepared = Some(PreparedQuery {
            id: 42,
            query: "SELECT 1".into(),
            nested: true, // conservative initial value from prepare.rs
        });
        let qm = QueryMeta {
            exps: vec![],
            tables: vec![],
            rnum: 0,
            state: dummy_typ(),
            query: Box::new(dummy_exp()),
            body: Box::new(dummy_exp()), // body doesn't use id 42
            initial: Box::new(dummy_exp()),
            prepared,
        };
        let e = Located::dummy(Exp::Query(qm));
        let globals = HashMap::new();
        let result = annotate_exp(&globals, e);
        if let Exp::Query(qm) = result.node {
            assert_eq!(qm.prepared.unwrap().nested, false);
        } else {
            panic!("expected Query");
        }
    }

    #[test]
    fn nested_query_gets_true() {
        // Build an EQuery whose body uses a nested EQuery with the same id.
        let id = 7;
        let inner_prepared = Some(PreparedQuery {
            id,
            query: "SELECT 1".into(),
            nested: false,
        });
        let inner_qm = QueryMeta {
            exps: vec![],
            tables: vec![],
            rnum: 0,
            state: dummy_typ(),
            query: Box::new(dummy_exp()),
            body: Box::new(dummy_exp()),
            initial: Box::new(dummy_exp()),
            prepared: inner_prepared,
        };
        let body = Located::dummy(Exp::Query(inner_qm));

        let outer_prepared = Some(PreparedQuery {
            id,
            query: "SELECT 1".into(),
            nested: false,
        });
        let outer_qm = QueryMeta {
            exps: vec![],
            tables: vec![],
            rnum: 0,
            state: dummy_typ(),
            query: Box::new(dummy_exp()),
            body: Box::new(body),
            initial: Box::new(dummy_exp()),
            prepared: outer_prepared,
        };
        let e = Located::dummy(Exp::Query(outer_qm));
        let globals = HashMap::new();
        let result = annotate_exp(&globals, e);
        if let Exp::Query(qm) = result.node {
            assert_eq!(qm.prepared.unwrap().nested, true);
        } else {
            panic!("expected Query");
        }
    }
}
