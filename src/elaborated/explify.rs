//! Explify pass: translate elaborated AST to explicit AST.
//!
//! Drops constraint declarations (`DConstraint`, `SgiConstraint`), resolves
//! implicit arguments, and removes unification-variable wrappers. Residual
//! elaboration errors and unresolved unifiers are reported via
//! [`ErrorReporter`] (with recovery nodes) instead of panicking.
//!
//! Mirrors `explify.sml`.

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::elaborated as elab;
use crate::error_types::{ErrorReporter, Located, Span};
use crate::explicit as expl;
use crate::primitives::Prim;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Convert an elaborated [`elab::File`] to the explicit intermediate representation.
///
/// Drops constraints, resolves implicits, and strips unification wrappers; recovery nodes may be emitted.
///
/// # Arguments
///
/// * `file` — Output of elaboration (after [`crate::elaborated::unnest`] in the full pipeline).
/// * `errors` — Receives diagnostics from the pass.
///
/// # Returns
///
/// `Some(explicit file)` when [`ErrorReporter::has_hard_errors`] is false after the pass; otherwise `None`.
pub fn explify(file: elab::File, errors: &mut ErrorReporter) -> Option<expl::File> {
    let out: expl::File = file
        .into_iter()
        .filter_map(|d| explify_decl(d, errors))
        .collect();
    if errors.has_hard_errors() {
        None
    } else {
        Some(out)
    }
}

fn recovery_kind(span: Span) -> expl::LocatedKind {
    Located::new(expl::Kind::Type, span)
}

fn recovery_con(span: Span) -> expl::LocatedConstructor {
    Located::new(expl::Constructor::Unit, span)
}

fn recovery_exp(span: Span) -> expl::LocatedExpression {
    Located::new(expl::Expression::Prim(Prim::Int(0)), span)
}

fn recovery_sgn(span: Span) -> expl::LocatedSignature {
    Located::new(expl::Signature::Const(vec![]), span)
}

fn recovery_str(span: Span) -> expl::LocatedStructure {
    Located::new(expl::Structure::Const(vec![]), span)
}

// ---------------------------------------------------------------------------
// Kinds
// ---------------------------------------------------------------------------

fn explify_kind(k: elab::LocatedKind, errors: &mut ErrorReporter) -> expl::LocatedKind {
    let span = k.span.clone();
    match k.node {
        elab::Kind::Typed(_) => Located::new(expl::Kind::Type, span),
        elab::Kind::Arrow(k1, k2) => Located::new(
            expl::Kind::Arrow(
                Box::new(explify_kind(*k1, errors)),
                Box::new(explify_kind(*k2, errors)),
            ),
            span,
        ),
        elab::Kind::Name => Located::new(expl::Kind::Name, span),
        elab::Kind::Record(k) => {
            Located::new(expl::Kind::Record(Box::new(explify_kind(*k, errors))), span)
        }
        elab::Kind::Unit => Located::new(expl::Kind::Unit, span),
        elab::Kind::Tuple(ks) => Located::new(
            expl::Kind::Tuple(ks.into_iter().map(|k| explify_kind(k, errors)).collect()),
            span,
        ),
        elab::Kind::Error => {
            errors.report_type_at_with_hint(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ExplifyKindErrorPlaceholder, vec![]),
                DiagnosticId::HintExplifyKindErrorPlaceholder,
                vec![],
            );
            recovery_kind(span)
        }
        elab::Kind::Unif(unif_span, _, unif_ref) => {
            let guard = crate::compiler_diagnostics::lock_for_compile(
                unif_ref.as_ref(),
                "explify unification cell",
            );
            match &*guard {
                elab::KUnif::Known(known) => {
                    let k = *known.clone();
                    drop(guard);
                    explify_kind(k, errors)
                }
                elab::KUnif::Unknown => {
                    errors.report_type_at_with_hint(
                        unif_span.clone(),
                        DiagnosticPayload::new(DiagnosticId::ExplifyKindMetavarUnknown, vec![]),
                        DiagnosticId::HintExplifyKindMetavarUnknown,
                        vec![],
                    );
                    recovery_kind(span)
                }
            }
        }
        elab::Kind::TupleUnif(unif_span, _, unif_ref) => {
            let guard = crate::compiler_diagnostics::lock_for_compile(
                unif_ref.as_ref(),
                "explify unification cell",
            );
            match &*guard {
                elab::KUnif::Known(known) => {
                    let k = *known.clone();
                    drop(guard);
                    explify_kind(k, errors)
                }
                elab::KUnif::Unknown => {
                    errors.report_type_at_with_hint(
                        unif_span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ExplifyTupleKindMetavarUnknown,
                            vec![],
                        ),
                        DiagnosticId::HintExplifyTupleKindMetavarUnknown,
                        vec![],
                    );
                    recovery_kind(span)
                }
            }
        }
        elab::Kind::Rel(n) => Located::new(expl::Kind::Rel(n), span),
        elab::Kind::Fun(x, k) => {
            Located::new(expl::Kind::Fun(x, Box::new(explify_kind(*k, errors))), span)
        }
    }
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

fn explify_con(
    c: elab::LocatedConstructor,
    errors: &mut ErrorReporter,
) -> expl::LocatedConstructor {
    let span = c.span.clone();
    match c.node {
        elab::Constructor::TFun(t1, t2) => Located::new(
            expl::Constructor::TFun(
                Box::new(explify_con(*t1, errors)),
                Box::new(explify_con(*t2, errors)),
            ),
            span,
        ),
        elab::Constructor::TCFun(_, x, k, t) => Located::new(
            expl::Constructor::TCFun(
                x,
                Box::new(explify_kind(*k, errors)),
                Box::new(explify_con(*t, errors)),
            ),
            span,
        ),
        elab::Constructor::TDisjoint(_, _, t) => explify_con(*t, errors),
        elab::Constructor::TRecord(c) => Located::new(
            expl::Constructor::TRecord(Box::new(explify_con(*c, errors))),
            span,
        ),
        elab::Constructor::Rel(n) => Located::new(expl::Constructor::Rel(n), span),
        elab::Constructor::Named(n) => Located::new(expl::Constructor::Named(n), span),
        elab::Constructor::ModProj(m, ms, x) => {
            Located::new(expl::Constructor::ModProj(m, ms, x), span)
        }
        elab::Constructor::App(c1, c2) => Located::new(
            expl::Constructor::App(
                Box::new(explify_con(*c1, errors)),
                Box::new(explify_con(*c2, errors)),
            ),
            span,
        ),
        elab::Constructor::Abs(x, k, c) => Located::new(
            expl::Constructor::Abs(
                x,
                Box::new(explify_kind(*k, errors)),
                Box::new(explify_con(*c, errors)),
            ),
            span,
        ),
        elab::Constructor::KAbs(x, c) => Located::new(
            expl::Constructor::KAbs(x, Box::new(explify_con(*c, errors))),
            span,
        ),
        elab::Constructor::KApp(c, k) => Located::new(
            expl::Constructor::KApp(
                Box::new(explify_con(*c, errors)),
                Box::new(explify_kind(*k, errors)),
            ),
            span,
        ),
        elab::Constructor::TKFun(x, c) => Located::new(
            expl::Constructor::TKFun(x, Box::new(explify_con(*c, errors))),
            span,
        ),
        elab::Constructor::Name(s) => Located::new(expl::Constructor::Name(s), span),
        elab::Constructor::Record(k, xcs) => Located::new(
            expl::Constructor::Record(
                Box::new(explify_kind(*k, errors)),
                xcs.into_iter()
                    .map(|(c1, c2)| (explify_con(c1, errors), explify_con(c2, errors)))
                    .collect(),
            ),
            span,
        ),
        elab::Constructor::Concat(c1, c2) => Located::new(
            expl::Constructor::Concat(
                Box::new(explify_con(*c1, errors)),
                Box::new(explify_con(*c2, errors)),
            ),
            span,
        ),
        elab::Constructor::Map(dom, ran) => Located::new(
            expl::Constructor::Map(
                Box::new(explify_kind(*dom, errors)),
                Box::new(explify_kind(*ran, errors)),
            ),
            span,
        ),
        elab::Constructor::Unit => Located::new(expl::Constructor::Unit, span),
        elab::Constructor::Tuple(cs) => Located::new(
            expl::Constructor::Tuple(cs.into_iter().map(|c| explify_con(c, errors)).collect()),
            span,
        ),
        elab::Constructor::Proj(c, n) => Located::new(
            expl::Constructor::Proj(Box::new(explify_con(*c, errors)), n),
            span,
        ),
        elab::Constructor::Error => {
            errors.report_type_at(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ExplifyUnexpectedConstructorError, vec![]),
            );
            recovery_con(span)
        }
        elab::Constructor::Unif(nl, _, _, _, unif_ref) => {
            let guard = crate::compiler_diagnostics::lock_for_compile(
                unif_ref.as_ref(),
                "explify unification cell",
            );
            match &*guard {
                elab::CUnif::Known(known) => {
                    let c = *known.clone();
                    drop(guard);
                    let lifted = crate::elaborated::utilities::mlift_con_in_con(nl, c);
                    explify_con(lifted, errors)
                }
                elab::CUnif::Unknown => {
                    errors.report_type_at_with_hint(
                        span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ExplifyConstructorMetavarUnknown,
                            vec![],
                        ),
                        DiagnosticId::HintExplifyConstructorMetavarUnknown,
                        vec![],
                    );
                    recovery_con(span)
                }
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

fn explify_pat(p: elab::LocatedPattern, errors: &mut ErrorReporter) -> expl::LocatedPattern {
    let span = p.span.clone();
    match p.node {
        elab::Pattern::Var(x, t) => {
            Located::new(expl::Pattern::Var(x, explify_con(t, errors)), span)
        }
        elab::Pattern::Prim(p) => Located::new(expl::Pattern::Prim(p), span),
        elab::Pattern::Constructor(dk, pc, cs, po) => Located::new(
            expl::Pattern::Constructor(
                dk,
                explify_pat_con(pc),
                cs.into_iter().map(|c| explify_con(c, errors)).collect(),
                po.map(|p| Box::new(explify_pat(*p, errors))),
            ),
            span,
        ),
        elab::Pattern::Record(xps) => Located::new(
            expl::Pattern::Record(
                xps.into_iter()
                    .map(|(x, p, t)| (x, explify_pat(p, errors), explify_con(t, errors)))
                    .collect(),
            ),
            span,
        ),
    }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

fn explify_exp(e: elab::LocatedExpression, errors: &mut ErrorReporter) -> expl::LocatedExpression {
    let span = e.span.clone();
    match e.node {
        elab::Expression::Prim(p) => Located::new(expl::Expression::Prim(p), span),
        elab::Expression::Rel(n) => Located::new(expl::Expression::Rel(n), span),
        elab::Expression::Named(n) => Located::new(expl::Expression::Named(n), span),
        elab::Expression::ModProj(m, ms, x) => {
            Located::new(expl::Expression::ModProj(m, ms, x), span)
        }
        elab::Expression::App(e1, e2) => Located::new(
            expl::Expression::App(
                Box::new(explify_exp(*e1, errors)),
                Box::new(explify_exp(*e2, errors)),
            ),
            span,
        ),
        elab::Expression::Abs(x, dom, ran, e1) => Located::new(
            expl::Expression::Abs(
                x,
                explify_con(dom, errors),
                explify_con(ran, errors),
                Box::new(explify_exp(*e1, errors)),
            ),
            span,
        ),
        elab::Expression::CApp(e1, c) => Located::new(
            expl::Expression::CApp(Box::new(explify_exp(*e1, errors)), explify_con(c, errors)),
            span,
        ),
        elab::Expression::CAbs(_, x, k, e1) => Located::new(
            expl::Expression::CAbs(
                x,
                Box::new(explify_kind(*k, errors)),
                Box::new(explify_exp(*e1, errors)),
            ),
            span,
        ),
        elab::Expression::KAbs(x, e) => Located::new(
            expl::Expression::KAbs(x, Box::new(explify_exp(*e, errors))),
            span,
        ),
        elab::Expression::KApp(e, k) => Located::new(
            expl::Expression::KApp(
                Box::new(explify_exp(*e, errors)),
                Box::new(explify_kind(*k, errors)),
            ),
            span,
        ),
        elab::Expression::Record(xes) => Located::new(
            expl::Expression::Record(
                xes.into_iter()
                    .map(|(c, e, t)| {
                        (
                            explify_con(c, errors),
                            explify_exp(e, errors),
                            explify_con(t, errors),
                        )
                    })
                    .collect(),
            ),
            span,
        ),
        elab::Expression::Field(e1, c, meta) => Located::new(
            expl::Expression::Field(
                Box::new(explify_exp(*e1, errors)),
                explify_con(c, errors),
                expl::FieldMeta {
                    field: explify_con(meta.field, errors),
                    rest: explify_con(meta.rest, errors),
                },
            ),
            span,
        ),
        elab::Expression::Concat(e1, c1, e2, c2) => Located::new(
            expl::Expression::Concat(
                Box::new(explify_exp(*e1, errors)),
                explify_con(c1, errors),
                Box::new(explify_exp(*e2, errors)),
                explify_con(c2, errors),
            ),
            span,
        ),
        elab::Expression::Cut(e1, c, meta) => Located::new(
            expl::Expression::Cut(
                Box::new(explify_exp(*e1, errors)),
                explify_con(c, errors),
                expl::FieldMeta {
                    field: explify_con(meta.field, errors),
                    rest: explify_con(meta.rest, errors),
                },
            ),
            span,
        ),
        elab::Expression::CutMulti(e1, c, meta) => Located::new(
            expl::Expression::CutMulti(
                Box::new(explify_exp(*e1, errors)),
                explify_con(c, errors),
                expl::RestMeta {
                    rest: explify_con(meta.rest, errors),
                },
            ),
            span,
        ),
        elab::Expression::Case(e, pes, meta) => Located::new(
            expl::Expression::Case(
                Box::new(explify_exp(*e, errors)),
                pes.into_iter()
                    .map(|(p, e)| (explify_pat(p, errors), explify_exp(e, errors)))
                    .collect(),
                expl::CaseMeta {
                    disc: explify_con(meta.disc, errors),
                    result: explify_con(meta.result, errors),
                },
            ),
            span,
        ),
        elab::Expression::Error => {
            errors.report_type_at(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ExplifyUnexpectedExpressionError, vec![]),
            );
            recovery_exp(span)
        }
        elab::Expression::Unif(unif_ref) => {
            let guard = crate::compiler_diagnostics::lock_for_compile(
                unif_ref.as_ref(),
                "explify unification cell",
            );
            match &*guard {
                Some(e) => {
                    let e = e.clone();
                    drop(guard);
                    explify_exp(e, errors)
                }
                None => {
                    errors.report_type_at(
                        span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ExplifyExpressionUnificationUnknown,
                            vec![],
                        ),
                    );
                    recovery_exp(span)
                }
            }
        }
        elab::Expression::Hole(_) => {
            errors.report_type_at(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ExplifyTypedHoleRemains, vec![]),
            );
            recovery_exp(span)
        }

        elab::Expression::Let(des, e, t) => {
            let mut acc = explify_exp(*e, errors);
            let t_ran = explify_con(t, errors);
            for de in des.into_iter().rev() {
                let de_span = de.span.clone();
                acc = match de.node {
                    elab::ElaboratedDeclaration::ValRec(_) => {
                        errors.report_type_at(
                            de_span.clone(),
                            DiagnosticPayload::new(
                                DiagnosticId::ExplifyLocalValRecShouldBeLifted,
                                vec![],
                            ),
                        );
                        acc
                    }
                    elab::ElaboratedDeclaration::Val(pat, t_prime, e_prime) => match pat.node {
                        elab::Pattern::Var(x, _) => Located::new(
                            expl::Expression::Let(
                                x,
                                explify_con(t_prime, errors),
                                Box::new(explify_exp(e_prime, errors)),
                                Box::new(acc),
                            ),
                            de_span,
                        ),
                        _ => Located::new(
                            expl::Expression::Case(
                                Box::new(explify_exp(e_prime, errors)),
                                vec![(explify_pat(pat, errors), acc)],
                                expl::CaseMeta {
                                    disc: explify_con(t_prime, errors),
                                    result: t_ran.clone(),
                                },
                            ),
                            de_span,
                        ),
                    },
                };
            }
            acc
        }
    }
}

// ---------------------------------------------------------------------------
// Signature items & signatures
// ---------------------------------------------------------------------------

fn explify_dt_decl(dt: elab::DatatypeDecl, errors: &mut ErrorReporter) -> expl::DatatypeDecl {
    expl::DatatypeDecl {
        name: dt.name,
        id: dt.id,
        params: dt.params,
        constrs: dt
            .constrs
            .into_iter()
            .map(|(x, n, co)| (x, n, co.map(|c| explify_con(c, errors))))
            .collect(),
    }
}

fn explify_sgi(
    sgi: elab::LocatedSignatureItem,
    errors: &mut ErrorReporter,
) -> Option<expl::LocatedSignatureItem> {
    let span = sgi.span.clone();
    match sgi.node {
        elab::SignatureItem::ConAbs(x, n, k) => Some(Located::new(
            expl::SignatureItem::ConAbs(x, n, explify_kind(k, errors)),
            span,
        )),
        elab::SignatureItem::Constructor(x, n, k, c) => Some(Located::new(
            expl::SignatureItem::Constructor(x, n, explify_kind(k, errors), explify_con(c, errors)),
            span,
        )),
        elab::SignatureItem::Datatype(dts) => Some(Located::new(
            expl::SignatureItem::Datatype(
                dts.into_iter()
                    .map(|d| explify_dt_decl(d, errors))
                    .collect(),
            ),
            span,
        )),
        elab::SignatureItem::DatatypeImp {
            name,
            id,
            params: _,
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
                    .map(|(x, n, co)| (x, n, co.map(|c| explify_con(c, errors))))
                    .collect(),
            },
            span,
        )),
        elab::SignatureItem::Val(x, n, c) => Some(Located::new(
            expl::SignatureItem::Val(x, n, explify_con(c, errors)),
            span,
        )),
        elab::SignatureItem::Structure(_, x, n, sgn) => Some(Located::new(
            expl::SignatureItem::Structure(x, n, explify_sgn(sgn, errors)),
            span,
        )),
        elab::SignatureItem::Signature(x, n, sgn) => Some(Located::new(
            expl::SignatureItem::Signature(x, n, explify_sgn(sgn, errors)),
            span,
        )),
        elab::SignatureItem::Constraint(_, _) => None,
        elab::SignatureItem::ClassAbs(x, n, k) => {
            let k_span = k.span.clone();
            let k_expl = explify_kind(k, errors);
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
        elab::SignatureItem::Class(x, n, k, c) => {
            let k_span = k.span.clone();
            let k_expl = explify_kind(k, errors);
            let arrow_k = Located::new(
                expl::Kind::Arrow(
                    Box::new(k_expl),
                    Box::new(Located::new(expl::Kind::Type, k_span.clone())),
                ),
                k_span,
            );
            Some(Located::new(
                expl::SignatureItem::Constructor(x, n, arrow_k, explify_con(c, errors)),
                span,
            ))
        }
    }
}

fn explify_sgn(sgn: elab::LocatedSignature, errors: &mut ErrorReporter) -> expl::LocatedSignature {
    let span = sgn.span.clone();
    match sgn.node {
        elab::Signature::Const(sgis) => Located::new(
            expl::Signature::Const(
                sgis.into_iter()
                    .filter_map(|s| explify_sgi(s, errors))
                    .collect(),
            ),
            span,
        ),
        elab::Signature::Var(n) => Located::new(expl::Signature::Var(n), span),
        elab::Signature::Fun(m, n, dom, ran) => Located::new(
            expl::Signature::Fun(
                m,
                n,
                Box::new(explify_sgn(*dom, errors)),
                Box::new(explify_sgn(*ran, errors)),
            ),
            span,
        ),
        elab::Signature::Where(sgn, ms, x, c) => Located::new(
            expl::Signature::Where(
                Box::new(explify_sgn(*sgn, errors)),
                ms,
                x,
                explify_con(c, errors),
            ),
            span,
        ),
        elab::Signature::Proj(m, ms, x) => Located::new(expl::Signature::Proj(m, ms, x), span),
        elab::Signature::Error => {
            errors.report_type_at_with_hint(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ExplifySignatureErrorPlaceholder, vec![]),
                DiagnosticId::HintExplifySignatureErrorPlaceholder,
                vec![],
            );
            recovery_sgn(span)
        }
    }
}

// ---------------------------------------------------------------------------
// Structures & declarations
// ---------------------------------------------------------------------------

fn explify_str(str_: elab::LocatedStructure, errors: &mut ErrorReporter) -> expl::LocatedStructure {
    let span = str_.span.clone();
    match str_.node {
        elab::Structure::Const(ds) => Located::new(
            expl::Structure::Const(
                ds.into_iter()
                    .filter_map(|d| explify_decl(d, errors))
                    .collect(),
            ),
            span,
        ),
        elab::Structure::Var(n) => Located::new(expl::Structure::Var(n), span),
        elab::Structure::Proj(str_, s) => Located::new(
            expl::Structure::Proj(Box::new(explify_str(*str_, errors)), s),
            span,
        ),
        elab::Structure::Fun(m, n, dom, ran, str_) => Located::new(
            expl::Structure::Fun(
                m,
                n,
                explify_sgn(dom, errors),
                explify_sgn(ran, errors),
                Box::new(explify_str(*str_, errors)),
            ),
            span,
        ),
        elab::Structure::App(str1, str2) => Located::new(
            expl::Structure::App(
                Box::new(explify_str(*str1, errors)),
                Box::new(explify_str(*str2, errors)),
            ),
            span,
        ),
        elab::Structure::Error => {
            errors.report_type_at_with_hint(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ExplifyStructureErrorPlaceholder, vec![]),
                DiagnosticId::HintExplifyStructureErrorPlaceholder,
                vec![],
            );
            recovery_str(span)
        }
    }
}

fn explify_decl(
    d: elab::LocatedDeclaration,
    errors: &mut ErrorReporter,
) -> Option<expl::LocatedDeclaration> {
    let span = d.span.clone();
    match d.node {
        elab::Declaration::Constructor(x, n, k, c) => Some(Located::new(
            expl::Declaration::Constructor(x, n, explify_kind(k, errors), explify_con(c, errors)),
            span,
        )),
        elab::Declaration::Datatype(dts) => Some(Located::new(
            expl::Declaration::Datatype(
                dts.into_iter()
                    .map(|d| explify_dt_decl(d, errors))
                    .collect(),
            ),
            span,
        )),
        elab::Declaration::DatatypeImp {
            name,
            id,
            params: _,
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
                    .map(|(x, n, co)| (x, n, co.map(|c| explify_con(c, errors))))
                    .collect(),
            },
            span,
        )),
        elab::Declaration::Val(x, n, t, e) => Some(Located::new(
            expl::Declaration::Val(x, n, explify_con(t, errors), explify_exp(e, errors)),
            span,
        )),
        elab::Declaration::ValRec(vis) => Some(Located::new(
            expl::Declaration::ValRec(
                vis.into_iter()
                    .map(|(x, n, t, e)| (x, n, explify_con(t, errors), explify_exp(e, errors)))
                    .collect(),
            ),
            span,
        )),
        elab::Declaration::Signature(x, n, sgn) => Some(Located::new(
            expl::Declaration::Signature(x, n, explify_sgn(sgn, errors)),
            span,
        )),
        elab::Declaration::Structure(x, n, sgn, str_) => Some(Located::new(
            expl::Declaration::Structure(x, n, explify_sgn(sgn, errors), explify_str(str_, errors)),
            span,
        )),
        elab::Declaration::FfiStr(x, n, sgn) => Some(Located::new(
            expl::Declaration::FfiStr(x, n, explify_sgn(sgn, errors)),
            span,
        )),
        elab::Declaration::Constraint(_, _) => None,
        elab::Declaration::Export(en, sgn, str_) => Some(Located::new(
            expl::Declaration::Export(en, explify_sgn(sgn, errors), explify_str(str_, errors)),
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
                con: explify_con(con, errors),
                exp: explify_exp(exp, errors),
                pk_con: explify_con(pk_con, errors),
                pk_exp: explify_exp(pk_exp, errors),
                unique_con: explify_con(unique_con, errors),
            },
            span,
        )),
        elab::Declaration::Sequence(nt, x, n) => {
            Some(Located::new(expl::Declaration::Sequence(nt, x, n), span))
        }
        elab::Declaration::View(nt, x, n, e, c) => Some(Located::new(
            expl::Declaration::View(nt, x, n, explify_exp(e, errors), explify_con(c, errors)),
            span,
        )),
        elab::Declaration::Index(e1, e2) => Some(Located::new(
            expl::Declaration::Index(explify_exp(e1, errors), explify_exp(e2, errors)),
            span,
        )),
        elab::Declaration::Database(s) => Some(Located::new(expl::Declaration::Database(s), span)),
        elab::Declaration::Cookie(nt, x, n, c) => Some(Located::new(
            expl::Declaration::Cookie(nt, x, n, explify_con(c, errors)),
            span,
        )),
        elab::Declaration::Style(nt, x, n) => {
            Some(Located::new(expl::Declaration::Style(nt, x, n), span))
        }
        elab::Declaration::Task(e1, e2) => Some(Located::new(
            expl::Declaration::Task(explify_exp(e1, errors), explify_exp(e2, errors)),
            span,
        )),
        elab::Declaration::Policy(e) => Some(Located::new(
            expl::Declaration::Policy(explify_exp(e, errors)),
            span,
        )),
        elab::Declaration::OnError(n, ms, x) => {
            Some(Located::new(expl::Declaration::OnError(n, ms, x), span))
        }
        elab::Declaration::Ffi(x, n, modes, t) => Some(Located::new(
            expl::Declaration::Ffi(x, n, modes, explify_con(t, errors)),
            span,
        )),
    }
}
