//! Explify pass: translate elaborated AST to explicit AST.
//!
//! Drops constraint declarations (`DConstraint`, `SgiConstraint`), resolves
//! implicit arguments, and removes unification-variable wrappers.  Panics on
//! any residual error or unresolved unification variable — those indicate bugs
//! in the elaborator.
//!
//! Mirrors `explify.sml`.

use crate::elaborated as elab;
use crate::error_types::{ErrorReporter, Located};
use crate::explicit as expl;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Convert an elaborated file to the explicit representation.
///
/// Returns `Some(file)` on success.  Panics if the elaborated AST contains
/// unresolved unification variables or error nodes (which the elaborator
/// should have already caught).
pub fn explify(file: elab::File, _errors: &mut ErrorReporter) -> Option<expl::File> {
    Some(file.into_iter().filter_map(explify_decl).collect())
}

// ---------------------------------------------------------------------------
// Kinds
// ---------------------------------------------------------------------------

fn explify_kind(k: elab::LocatedKind) -> expl::LocatedKind {
    let span = k.span.clone();
    match k.node {
        elab::Kind::Type => Located::new(expl::Kind::Type, span),
        elab::Kind::Arrow(k1, k2) => Located::new(
            expl::Kind::Arrow(Box::new(explify_kind(*k1)), Box::new(explify_kind(*k2))),
            span,
        ),
        elab::Kind::Name => Located::new(expl::Kind::Name, span),
        elab::Kind::Record(k) => Located::new(expl::Kind::Record(Box::new(explify_kind(*k))), span),
        elab::Kind::Unit => Located::new(expl::Kind::Unit, span),
        elab::Kind::Tuple(ks) => Located::new(
            expl::Kind::Tuple(ks.into_iter().map(explify_kind).collect()),
            span,
        ),
        elab::Kind::Error => panic!("explifyKind: KError at {}", span),
        elab::Kind::Unif(unif_span, _, unif_ref) => {
            let guard = unif_ref.lock().unwrap();
            match &*guard {
                elab::KUnif::Known(known) => {
                    let k = *known.clone();
                    drop(guard);
                    explify_kind(k)
                }
                elab::KUnif::Unknown => panic!("explifyKind: KUnif at {}", unif_span),
            }
        }
        elab::Kind::TupleUnif(unif_span, _, unif_ref) => {
            let guard = unif_ref.lock().unwrap();
            match &*guard {
                elab::KUnif::Known(known) => {
                    let k = *known.clone();
                    drop(guard);
                    explify_kind(k)
                }
                elab::KUnif::Unknown => panic!("explifyKind: KTupleUnif at {}", unif_span),
            }
        }
        elab::Kind::Rel(n) => Located::new(expl::Kind::Rel(n), span),
        elab::Kind::Fun(x, k) => Located::new(expl::Kind::Fun(x, Box::new(explify_kind(*k))), span),
    }
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

fn explify_con(c: elab::LocatedConstructor) -> expl::LocatedConstructor {
    let span = c.span.clone();
    match c.node {
        elab::Constructor::TFun(t1, t2) => Located::new(
            expl::Constructor::TFun(Box::new(explify_con(*t1)), Box::new(explify_con(*t2))),
            span,
        ),
        // Drop explicitness annotation; TCFun becomes TCFun(x, k, t)
        elab::Constructor::TCFun(_, x, k, t) => Located::new(
            expl::Constructor::TCFun(x, Box::new(explify_kind(*k)), Box::new(explify_con(*t))),
            span,
        ),
        // TDisjoint is erased — keep only the inner type
        elab::Constructor::TDisjoint(_, _, t) => explify_con(*t),
        elab::Constructor::TRecord(c) => {
            Located::new(expl::Constructor::TRecord(Box::new(explify_con(*c))), span)
        }
        elab::Constructor::Rel(n) => Located::new(expl::Constructor::Rel(n), span),
        elab::Constructor::Named(n) => Located::new(expl::Constructor::Named(n), span),
        elab::Constructor::ModProj(m, ms, x) => {
            Located::new(expl::Constructor::ModProj(m, ms, x), span)
        }
        elab::Constructor::App(c1, c2) => Located::new(
            expl::Constructor::App(Box::new(explify_con(*c1)), Box::new(explify_con(*c2))),
            span,
        ),
        elab::Constructor::Abs(x, k, c) => Located::new(
            expl::Constructor::Abs(x, Box::new(explify_kind(*k)), Box::new(explify_con(*c))),
            span,
        ),
        elab::Constructor::KAbs(x, c) => {
            Located::new(expl::Constructor::KAbs(x, Box::new(explify_con(*c))), span)
        }
        elab::Constructor::KApp(c, k) => Located::new(
            expl::Constructor::KApp(Box::new(explify_con(*c)), Box::new(explify_kind(*k))),
            span,
        ),
        elab::Constructor::TKFun(x, c) => {
            Located::new(expl::Constructor::TKFun(x, Box::new(explify_con(*c))), span)
        }
        elab::Constructor::Name(s) => Located::new(expl::Constructor::Name(s), span),
        elab::Constructor::Record(k, xcs) => Located::new(
            expl::Constructor::Record(
                Box::new(explify_kind(*k)),
                xcs.into_iter()
                    .map(|(c1, c2)| (explify_con(c1), explify_con(c2)))
                    .collect(),
            ),
            span,
        ),
        elab::Constructor::Concat(c1, c2) => Located::new(
            expl::Constructor::Concat(Box::new(explify_con(*c1)), Box::new(explify_con(*c2))),
            span,
        ),
        elab::Constructor::Map(dom, ran) => Located::new(
            expl::Constructor::Map(Box::new(explify_kind(*dom)), Box::new(explify_kind(*ran))),
            span,
        ),
        elab::Constructor::Unit => Located::new(expl::Constructor::Unit, span),
        elab::Constructor::Tuple(cs) => Located::new(
            expl::Constructor::Tuple(cs.into_iter().map(explify_con).collect()),
            span,
        ),
        elab::Constructor::Proj(c, n) => {
            Located::new(expl::Constructor::Proj(Box::new(explify_con(*c)), n), span)
        }
        elab::Constructor::Error => panic!("explifyCon: CError at {}", span),
        elab::Constructor::Unif(nl, _, _, _, unif_ref) => {
            let guard = unif_ref.lock().unwrap();
            match &*guard {
                elab::CUnif::Known(known) => {
                    let c = *known.clone();
                    drop(guard);
                    // Adjust de Bruijn indices for the `nl` binders that were in scope
                    // when the unification variable was created.
                    let lifted = crate::elaborated::utilities::mlift_con_in_con(nl, c);
                    explify_con(lifted)
                }
                elab::CUnif::Unknown => panic!("explifyCon: CUnif at {}", span),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

fn explify_pat_con(pc: elab::PatternConstructor) -> expl::PatternConstructor {
    match pc {
        elab::PatternConstructor::Var(n) => expl::PatternConstructor::Var(n),
        elab::PatternConstructor::Proj(m, ms, x) => expl::PatternConstructor::Proj(m, ms, x),
    }
}

fn explify_pat(p: elab::LocatedPattern) -> expl::LocatedPattern {
    let span = p.span.clone();
    match p.node {
        elab::Pattern::Var(x, t) => Located::new(expl::Pattern::Var(x, explify_con(t)), span),
        elab::Pattern::Prim(p) => Located::new(expl::Pattern::Prim(p), span),
        elab::Pattern::Constructor(dk, pc, cs, po) => Located::new(
            expl::Pattern::Constructor(
                dk,
                explify_pat_con(pc),
                cs.into_iter().map(explify_con).collect(),
                po.map(|p| Box::new(explify_pat(*p))),
            ),
            span,
        ),
        elab::Pattern::Record(xps) => Located::new(
            expl::Pattern::Record(
                xps.into_iter()
                    .map(|(x, p, t)| (x, explify_pat(p), explify_con(t)))
                    .collect(),
            ),
            span,
        ),
    }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

fn explify_exp(e: elab::LocatedExpression) -> expl::LocatedExpression {
    let span = e.span.clone();
    match e.node {
        elab::Expression::Prim(p) => Located::new(expl::Expression::Prim(p), span),
        elab::Expression::Rel(n) => Located::new(expl::Expression::Rel(n), span),
        elab::Expression::Named(n) => Located::new(expl::Expression::Named(n), span),
        elab::Expression::ModProj(m, ms, x) => {
            Located::new(expl::Expression::ModProj(m, ms, x), span)
        }
        elab::Expression::App(e1, e2) => Located::new(
            expl::Expression::App(Box::new(explify_exp(*e1)), Box::new(explify_exp(*e2))),
            span,
        ),
        elab::Expression::Abs(x, dom, ran, e1) => Located::new(
            expl::Expression::Abs(
                x,
                explify_con(dom),
                explify_con(ran),
                Box::new(explify_exp(*e1)),
            ),
            span,
        ),
        elab::Expression::CApp(e1, c) => Located::new(
            expl::Expression::CApp(Box::new(explify_exp(*e1)), explify_con(c)),
            span,
        ),
        // Drop explicitness annotation
        elab::Expression::CAbs(_, x, k, e1) => Located::new(
            expl::Expression::CAbs(x, Box::new(explify_kind(*k)), Box::new(explify_exp(*e1))),
            span,
        ),
        elab::Expression::KAbs(x, e) => {
            Located::new(expl::Expression::KAbs(x, Box::new(explify_exp(*e))), span)
        }
        elab::Expression::KApp(e, k) => Located::new(
            expl::Expression::KApp(Box::new(explify_exp(*e)), Box::new(explify_kind(*k))),
            span,
        ),
        elab::Expression::Record(xes) => Located::new(
            expl::Expression::Record(
                xes.into_iter()
                    .map(|(c, e, t)| (explify_con(c), explify_exp(e), explify_con(t)))
                    .collect(),
            ),
            span,
        ),
        elab::Expression::Field(e1, c, meta) => Located::new(
            expl::Expression::Field(
                Box::new(explify_exp(*e1)),
                explify_con(c),
                expl::FieldMeta {
                    field: explify_con(meta.field),
                    rest: explify_con(meta.rest),
                },
            ),
            span,
        ),
        elab::Expression::Concat(e1, c1, e2, c2) => Located::new(
            expl::Expression::Concat(
                Box::new(explify_exp(*e1)),
                explify_con(c1),
                Box::new(explify_exp(*e2)),
                explify_con(c2),
            ),
            span,
        ),
        elab::Expression::Cut(e1, c, meta) => Located::new(
            expl::Expression::Cut(
                Box::new(explify_exp(*e1)),
                explify_con(c),
                expl::FieldMeta {
                    field: explify_con(meta.field),
                    rest: explify_con(meta.rest),
                },
            ),
            span,
        ),
        elab::Expression::CutMulti(e1, c, meta) => Located::new(
            expl::Expression::CutMulti(
                Box::new(explify_exp(*e1)),
                explify_con(c),
                expl::RestMeta {
                    rest: explify_con(meta.rest),
                },
            ),
            span,
        ),
        elab::Expression::Case(e, pes, meta) => Located::new(
            expl::Expression::Case(
                Box::new(explify_exp(*e)),
                pes.into_iter()
                    .map(|(p, e)| (explify_pat(p), explify_exp(e)))
                    .collect(),
                expl::CaseMeta {
                    disc: explify_con(meta.disc),
                    result: explify_con(meta.result),
                },
            ),
            span,
        ),
        elab::Expression::Error => panic!("explifyExp: EError at {}", span),
        elab::Expression::Unif(unif_ref) => {
            let guard = unif_ref.lock().unwrap();
            match &*guard {
                Some(e) => {
                    let e = e.clone();
                    drop(guard);
                    explify_exp(e)
                }
                None => panic!("explifyExp: Undetermined EUnif at {}", span),
            }
        }
        elab::Expression::Hole(_) => panic!("explifyExp: EHole present at {}", span),

        // ELet is translated into nested ELet / ECase by foldr over des.
        // The SML does: foldr f (explifyExp e) des
        // where f ((de,loc), body) rewrites each binding.
        elab::Expression::Let(des, e, t) => {
            let base = explify_exp(*e);
            // `t` is the result type of the whole let; needed for ECase branches.
            des.into_iter().rev().fold(base, move |acc, de| {
                let de_span = de.span.clone();
                match de.node {
                    elab::ElaboratedDeclaration::ValRec(_) => {
                        panic!("explifyExp: Local 'val rec' remains")
                    }
                    elab::ElaboratedDeclaration::Val(pat, t_prime, e_prime) => match pat.node {
                        elab::Pattern::Var(x, _) => Located::new(
                            expl::Expression::Let(
                                x,
                                explify_con(t_prime),
                                Box::new(explify_exp(e_prime)),
                                Box::new(acc),
                            ),
                            de_span,
                        ),
                        _ => Located::new(
                            expl::Expression::Case(
                                Box::new(explify_exp(e_prime)),
                                vec![(explify_pat(pat), acc)],
                                expl::CaseMeta {
                                    disc: explify_con(t_prime),
                                    result: explify_con(t.clone()),
                                },
                            ),
                            de_span,
                        ),
                    },
                }
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Signature items & signatures
// ---------------------------------------------------------------------------

fn explify_dt_decl(dt: elab::DatatypeDecl) -> expl::DatatypeDecl {
    expl::DatatypeDecl {
        name: dt.name,
        id: dt.id,
        params: dt.params,
        constrs: dt
            .constrs
            .into_iter()
            .map(|(x, n, co)| (x, n, co.map(explify_con)))
            .collect(),
    }
}

fn explify_sgi(sgi: elab::LocatedSignatureItem) -> Option<expl::LocatedSignatureItem> {
    let span = sgi.span.clone();
    match sgi.node {
        elab::SignatureItem::ConAbs(x, n, k) => Some(Located::new(
            expl::SignatureItem::ConAbs(x, n, explify_kind(k)),
            span,
        )),
        elab::SignatureItem::Constructor(x, n, k, c) => Some(Located::new(
            expl::SignatureItem::Constructor(x, n, explify_kind(k), explify_con(c)),
            span,
        )),
        elab::SignatureItem::Datatype(dts) => Some(Located::new(
            expl::SignatureItem::Datatype(dts.into_iter().map(explify_dt_decl).collect()),
            span,
        )),
        elab::SignatureItem::DatatypeImp {
            name,
            id,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path,
            constrs,
        } => Some(Located::new(
            expl::SignatureItem::DatatypeImp {
                name,
                id,
                orig_mod,
                orig_path,
                orig_name,
                orig_constrs_path,
                constrs: constrs
                    .into_iter()
                    .map(|(x, n, co)| (x, n, co.map(explify_con)))
                    .collect(),
            },
            span,
        )),
        elab::SignatureItem::Val(x, n, c) => Some(Located::new(
            expl::SignatureItem::Val(x, n, explify_con(c)),
            span,
        )),
        // Drop ImportMode
        elab::SignatureItem::Structure(_, x, n, sgn) => Some(Located::new(
            expl::SignatureItem::Structure(x, n, explify_sgn(sgn)),
            span,
        )),
        elab::SignatureItem::Signature(x, n, sgn) => Some(Located::new(
            expl::SignatureItem::Signature(x, n, explify_sgn(sgn)),
            span,
        )),
        // Constraints are erased
        elab::SignatureItem::Constraint(_, _) => None,
        // ClassAbs becomes ConAbs with kind (k → Type)
        elab::SignatureItem::ClassAbs(x, n, k) => {
            let k_span = k.span.clone();
            let k_expl = explify_kind(k);
            let arrow_k = Located::new(
                expl::Kind::Arrow(
                    Box::new(k_expl),
                    Box::new(Located::new(expl::Kind::Type, k_span.clone())),
                ),
                k_span,
            );
            Some(Located::new(
                expl::SignatureItem::ConAbs(x, n, arrow_k),
                span,
            ))
        }
        // Class becomes Constructor with kind (k → Type)
        elab::SignatureItem::Class(x, n, k, c) => {
            let k_span = k.span.clone();
            let k_expl = explify_kind(k);
            let arrow_k = Located::new(
                expl::Kind::Arrow(
                    Box::new(k_expl),
                    Box::new(Located::new(expl::Kind::Type, k_span.clone())),
                ),
                k_span,
            );
            Some(Located::new(
                expl::SignatureItem::Constructor(x, n, arrow_k, explify_con(c)),
                span,
            ))
        }
    }
}

fn explify_sgn(sgn: elab::LocatedSignature) -> expl::LocatedSignature {
    let span = sgn.span.clone();
    match sgn.node {
        elab::Signature::Const(sgis) => Located::new(
            expl::Signature::Const(sgis.into_iter().filter_map(explify_sgi).collect()),
            span,
        ),
        elab::Signature::Var(n) => Located::new(expl::Signature::Var(n), span),
        elab::Signature::Fun(m, n, dom, ran) => Located::new(
            expl::Signature::Fun(
                m,
                n,
                Box::new(explify_sgn(*dom)),
                Box::new(explify_sgn(*ran)),
            ),
            span,
        ),
        elab::Signature::Where(sgn, ms, x, c) => Located::new(
            expl::Signature::Where(Box::new(explify_sgn(*sgn)), ms, x, explify_con(c)),
            span,
        ),
        elab::Signature::Proj(m, ms, x) => Located::new(expl::Signature::Proj(m, ms, x), span),
        elab::Signature::Error => panic!("explifySgn: SgnError at {}", span),
    }
}

// ---------------------------------------------------------------------------
// Structures & declarations
// ---------------------------------------------------------------------------

fn explify_str(str_: elab::LocatedStructure) -> expl::LocatedStructure {
    let span = str_.span.clone();
    match str_.node {
        elab::Structure::Const(ds) => Located::new(
            expl::Structure::Const(ds.into_iter().filter_map(explify_decl).collect()),
            span,
        ),
        elab::Structure::Var(n) => Located::new(expl::Structure::Var(n), span),
        elab::Structure::Proj(str_, s) => {
            Located::new(expl::Structure::Proj(Box::new(explify_str(*str_)), s), span)
        }
        elab::Structure::Fun(m, n, dom, ran, str_) => Located::new(
            expl::Structure::Fun(
                m,
                n,
                explify_sgn(dom),
                explify_sgn(ran),
                Box::new(explify_str(*str_)),
            ),
            span,
        ),
        elab::Structure::App(str1, str2) => Located::new(
            expl::Structure::App(Box::new(explify_str(*str1)), Box::new(explify_str(*str2))),
            span,
        ),
        elab::Structure::Error => panic!("explifyStr: StrError at {}", span),
    }
}

fn explify_decl(d: elab::LocatedDeclaration) -> Option<expl::LocatedDeclaration> {
    let span = d.span.clone();
    match d.node {
        elab::Declaration::Constructor(x, n, k, c) => Some(Located::new(
            expl::Declaration::Constructor(x, n, explify_kind(k), explify_con(c)),
            span,
        )),
        elab::Declaration::Datatype(dts) => Some(Located::new(
            expl::Declaration::Datatype(dts.into_iter().map(explify_dt_decl).collect()),
            span,
        )),
        elab::Declaration::DatatypeImp {
            name,
            id,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path,
            constrs,
        } => Some(Located::new(
            expl::Declaration::DatatypeImp {
                name,
                id,
                orig_mod,
                orig_path,
                orig_name,
                orig_constrs_path,
                constrs: constrs
                    .into_iter()
                    .map(|(x, n, co)| (x, n, co.map(explify_con)))
                    .collect(),
            },
            span,
        )),
        elab::Declaration::Val(x, n, t, e) => Some(Located::new(
            expl::Declaration::Val(x, n, explify_con(t), explify_exp(e)),
            span,
        )),
        elab::Declaration::ValRec(vis) => Some(Located::new(
            expl::Declaration::ValRec(
                vis.into_iter()
                    .map(|(x, n, t, e)| (x, n, explify_con(t), explify_exp(e)))
                    .collect(),
            ),
            span,
        )),
        elab::Declaration::Signature(x, n, sgn) => Some(Located::new(
            expl::Declaration::Signature(x, n, explify_sgn(sgn)),
            span,
        )),
        elab::Declaration::Structure(x, n, sgn, str_) => Some(Located::new(
            expl::Declaration::Structure(x, n, explify_sgn(sgn), explify_str(str_)),
            span,
        )),
        elab::Declaration::FfiStr(x, n, sgn) => Some(Located::new(
            expl::Declaration::FfiStr(x, n, explify_sgn(sgn)),
            span,
        )),
        // Constraints are erased
        elab::Declaration::Constraint(_, _) => None,
        elab::Declaration::Export(en, sgn, str_) => Some(Located::new(
            expl::Declaration::Export(en, explify_sgn(sgn), explify_str(str_)),
            span,
        )),
        elab::Declaration::Table {
            mod_id,
            name,
            name_id,
            con,
            exp,
            pk_con,
            pk_exp,
            unique_con,
        } => Some(Located::new(
            expl::Declaration::Table {
                mod_id,
                name,
                name_id,
                con: explify_con(con),
                exp: explify_exp(exp),
                pk_con: explify_con(pk_con),
                pk_exp: explify_exp(pk_exp),
                unique_con: explify_con(unique_con),
            },
            span,
        )),
        elab::Declaration::Sequence(nt, x, n) => {
            Some(Located::new(expl::Declaration::Sequence(nt, x, n), span))
        }
        elab::Declaration::View(nt, x, n, e, c) => Some(Located::new(
            expl::Declaration::View(nt, x, n, explify_exp(e), explify_con(c)),
            span,
        )),
        elab::Declaration::Index(e1, e2) => Some(Located::new(
            expl::Declaration::Index(explify_exp(e1), explify_exp(e2)),
            span,
        )),
        elab::Declaration::Database(s) => Some(Located::new(expl::Declaration::Database(s), span)),
        elab::Declaration::Cookie(nt, x, n, c) => Some(Located::new(
            expl::Declaration::Cookie(nt, x, n, explify_con(c)),
            span,
        )),
        elab::Declaration::Style(nt, x, n) => {
            Some(Located::new(expl::Declaration::Style(nt, x, n), span))
        }
        elab::Declaration::Task(e1, e2) => Some(Located::new(
            expl::Declaration::Task(explify_exp(e1), explify_exp(e2)),
            span,
        )),
        elab::Declaration::Policy(e) => Some(Located::new(
            expl::Declaration::Policy(explify_exp(e)),
            span,
        )),
        elab::Declaration::OnError(n, ms, x) => {
            Some(Located::new(expl::Declaration::OnError(n, ms, x), span))
        }
        elab::Declaration::Ffi(x, n, modes, t) => Some(Located::new(
            expl::Declaration::Ffi(x, n, modes, explify_con(t)),
            span,
        )),
    }
}
