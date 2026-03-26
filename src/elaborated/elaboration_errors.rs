#![allow(dead_code, unused_variables, unused_imports)]

//! Elaboration error types and reporting.
//!
//! Translated from `elab_err.sml`.

use crate::elaborated::{
    Constructor, Declaration, Expression, Kind, LocatedConstructor, LocatedDeclaration,
    LocatedExpression, LocatedKind, LocatedPattern, LocatedSignature, LocatedSignatureItem,
    Pattern, Signature, SignatureItem,
};
use crate::error_types::{CompileError, Span};

// ---------------------------------------------------------------------------
// Kind errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum KindError {
    UnboundKind(Span, String),
    KDisallowedWildcard(Span),
}

pub fn kind_error(err: &KindError) -> CompileError {
    match err {
        KindError::UnboundKind(span, s) => {
            CompileError::at(span.clone(), format!("Unbound kind variable:  {}", s))
        }
        KindError::KDisallowedWildcard(span) => {
            CompileError::at(span.clone(), "Wildcard not allowed in signature")
        }
    }
}

// ---------------------------------------------------------------------------
// Kind unification errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum KunifyError {
    KOccursCheckFailed(LocatedKind, LocatedKind),
    KIncompatible(LocatedKind, LocatedKind),
    KScope(LocatedKind, LocatedKind),
}

pub fn kunify_error_message(err: &KunifyError) -> String {
    match err {
        KunifyError::KOccursCheckFailed(k1, k2) => {
            format!("Kind occurs check failed: {:?} vs {:?}", k1.node, k2.node)
        }
        KunifyError::KIncompatible(k1, k2) => {
            format!("Incompatible kinds: {:?} vs {:?}", k1.node, k2.node)
        }
        KunifyError::KScope(k1, k2) => {
            format!(
                "Scoping prevents kind unification: {:?} vs {:?}",
                k1.node, k2.node
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum ConError {
    UnboundCon(Span, String),
    UnboundDatatype(Span, String),
    UnboundStrInCon(Span, String),
    WrongKind(LocatedConstructor, LocatedKind, LocatedKind, KunifyError),
    DuplicateField(Span, String),
    ProjBounds(LocatedConstructor, usize),
    ProjMismatch(LocatedConstructor, LocatedKind),
    CDisallowedWildcard(Span),
}

pub fn con_error(err: &ConError) -> CompileError {
    match err {
        ConError::UnboundCon(span, s) => CompileError::at(
            span.clone(),
            format!("Unbound constructor variable:  {}", s),
        ),
        ConError::UnboundDatatype(span, s) => {
            CompileError::at(span.clone(), format!("Unbound datatype:  {}", s))
        }
        ConError::UnboundStrInCon(span, s) => {
            CompileError::at(span.clone(), format!("Unbound structure:  {}", s))
        }
        ConError::WrongKind(c, k1, k2, kerr) => {
            let msg = format!(
                "Wrong kind; have {:?}, need {:?}; {}",
                k1.node,
                k2.node,
                kunify_error_message(kerr)
            );
            CompileError::at(c.span.clone(), msg)
        }
        ConError::DuplicateField(span, s) => {
            CompileError::at(span.clone(), format!("Duplicate record field:  {}", s))
        }
        ConError::ProjBounds(c, n) => CompileError::at(
            c.span.clone(),
            format!("Out of bounds constructor projection (index {})", n),
        ),
        ConError::ProjMismatch(c, k) => CompileError::at(
            c.span.clone(),
            format!("Projection from non-tuple constructor (kind {:?})", k.node),
        ),
        ConError::CDisallowedWildcard(span) => {
            CompileError::at(span.clone(), "Wildcard not allowed in signature")
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor unification errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum CunifyError {
    CKind(LocatedKind, LocatedKind, KunifyError),
    COccursCheckFailed(LocatedConstructor, LocatedConstructor),
    CIncompatible(LocatedConstructor, LocatedConstructor),
    CExplicitness(LocatedConstructor, LocatedConstructor),
    CKindof(LocatedKind, LocatedConstructor, String),
    CRecordFailure(
        LocatedConstructor,
        LocatedConstructor,
        Option<(
            LocatedConstructor,
            LocatedConstructor,
            LocatedConstructor,
            Option<Box<CunifyError>>,
        )>,
    ),
    TooLifty(Span, Span),
    TooUnify(LocatedConstructor, LocatedConstructor),
    TooDeep,
    CScope(LocatedConstructor, LocatedConstructor),
}

pub fn cunify_error(err: &CunifyError) -> CompileError {
    match err {
        CunifyError::CKind(k1, k2, kerr) => {
            let msg = format!(
                "Kind unification failure: have {:?}, need {:?}; {}",
                k1.node,
                k2.node,
                kunify_error_message(kerr)
            );
            CompileError::Plain(msg)
        }
        CunifyError::COccursCheckFailed(c1, c2) => {
            CompileError::Plain(format!(
                "Constructor occurs check failed: {:?} vs {:?}",
                c1.node, c2.node
            ))
        }
        CunifyError::CIncompatible(c1, c2) => {
            CompileError::Plain(format!(
                "Incompatible constructors: {:?} vs {:?}",
                c1.node, c2.node
            ))
        }
        CunifyError::CExplicitness(c1, c2) => {
            CompileError::Plain(format!(
                "Differing constructor function explicitness: {:?} vs {:?}",
                c1.node, c2.node
            ))
        }
        CunifyError::CKindof(k, c, expected) => {
            CompileError::Plain(format!(
                "Unexpected kind for kindof calculation (expecting {}): kind {:?}, con {:?}",
                expected, k.node, c.node
            ))
        }
        CunifyError::CRecordFailure(c1, c2, fo) => {
            let base = format!(
                "Can't unify record constructors: {:?} vs {:?}",
                c1.node, c2.node
            );
            let detail = if let Some((nm, t1, t2, inner_err)) = fo {
                let field_msg = format!(
                    "; field {:?}: {:?} vs {:?}",
                    nm.node, t1.node, t2.node
                );
                let inner_msg = if let Some(inner) = inner_err {
                    format!("; {}", cunify_error(inner))
                } else {
                    String::new()
                };
                format!("{}{}", field_msg, inner_msg)
            } else {
                String::new()
            };
            CompileError::Plain(format!("{}{}", base, detail))
        }
        CunifyError::TooLifty(loc1, loc2) => {
            CompileError::at(
                loc1.clone(),
                format!(
                    "Can't unify two unification variables that both have suspended liftings; other location: {}",
                    loc2
                ),
            )
        }
        CunifyError::TooUnify(c1, c2) => {
            CompileError::at(
                c1.span.clone(),
                format!(
                    "Substitution in constructor is blocked by a too-deep unification variable; body: {:?}",
                    c2.node
                ),
            )
        }
        CunifyError::TooDeep => {
            CompileError::Plain("Can't reverse-engineer unification variable lifting".to_string())
        }
        CunifyError::CScope(c1, c2) => {
            CompileError::Plain(format!(
                "Scoping prevents constructor unification: {:?} vs {:?}",
                c1.node, c2.node
            ))
        }
    }
}

// ---------------------------------------------------------------------------
// Expression errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum ExpError {
    UnboundExp(Span, String),
    UnboundStrInExp(Span, String),
    Unify(
        LocatedExpression,
        LocatedConstructor,
        LocatedConstructor,
        CunifyError,
    ),
    Unif(String, Span, LocatedConstructor),
    WrongForm(String, LocatedExpression, LocatedConstructor),
    IncompatibleCons(LocatedConstructor, LocatedConstructor),
    DuplicatePatternVariable(Span, String),
    PatUnify(
        LocatedPattern,
        LocatedConstructor,
        LocatedConstructor,
        CunifyError,
    ),
    UnboundConstructor(Span, Vec<String>, String),
    PatHasArg(Span),
    PatHasNoArg(Span),
    Inexhaustive(Span, LocatedPattern),
    DuplicatePatField(Span, String),
    Unresolvable(Span, LocatedConstructor),
    OutOfContext(Span, Option<(LocatedExpression, LocatedConstructor)>),
    IllegalRec(String, LocatedExpression),
}

pub fn exp_error(err: &ExpError) -> CompileError {
    match err {
        ExpError::UnboundExp(span, s) => {
            CompileError::at(span.clone(), format!("Unbound expression variable:  {}", s))
        }
        ExpError::UnboundStrInExp(span, s) => {
            CompileError::at(span.clone(), format!("Unbound structure:  {}", s))
        }
        ExpError::Unify(e, c1, c2, uerr) => {
            let msg = format!(
                "Unification failure; have con {:?}, need con {:?}; {}",
                c1.node,
                c2.node,
                cunify_error(uerr)
            );
            CompileError::at(e.span.clone(), msg)
        }
        ExpError::Unif(action, span, c) => CompileError::at(
            span.clone(),
            format!("Unification variable blocks {}", action),
        ),
        ExpError::WrongForm(variety, e, t) => {
            CompileError::at(e.span.clone(), format!("Expression is not a {}", variety))
        }
        ExpError::IncompatibleCons(c1, c2) => CompileError::at(
            c1.span.clone(),
            format!("Incompatible constructors: {:?} vs {:?}", c1.node, c2.node),
        ),
        ExpError::DuplicatePatternVariable(span, s) => {
            CompileError::at(span.clone(), format!("Duplicate pattern variable:  {}", s))
        }
        ExpError::PatUnify(p, c1, c2, uerr) => {
            let msg = format!(
                "Unification failure for pattern; have con {:?}, need con {:?}; {}",
                c1.node,
                c2.node,
                cunify_error(uerr)
            );
            CompileError::at(p.span.clone(), msg)
        }
        ExpError::UnboundConstructor(span, ms, s) => {
            let full = {
                let mut parts = ms.clone();
                parts.push(s.clone());
                parts.join(".")
            };
            CompileError::at(
                span.clone(),
                format!("Unbound constructor {} in pattern", full),
            )
        }
        ExpError::PatHasArg(span) => CompileError::at(
            span.clone(),
            "Constructor expects no argument but is used with argument",
        ),
        ExpError::PatHasNoArg(span) => CompileError::at(
            span.clone(),
            "Constructor expects argument but is used with no argument",
        ),
        ExpError::Inexhaustive(span, p) => CompileError::at(
            span.clone(),
            format!("Inexhaustive 'case'; missed case: {:?}", p.node),
        ),
        ExpError::DuplicatePatField(span, s) => CompileError::at(
            span.clone(),
            format!("Duplicate record field {} in pattern", s),
        ),
        ExpError::Unresolvable(span, c) => CompileError::at(
            span.clone(),
            format!(
                "Can't resolve type class instance; class constraint: {:?}",
                c.node
            ),
        ),
        ExpError::OutOfContext(span, co) => {
            let detail = if let Some((e, c)) = co {
                format!("; function: {:?}, type: {:?}", e.node, c.node)
            } else {
                String::new()
            };
            CompileError::at(
                span.clone(),
                format!("Type class wildcard occurs out of context{}", detail),
            )
        }
        ExpError::IllegalRec(x, e) => CompileError::at(
            e.span.clone(),
            format!(
                "Illegal 'val rec' righthand side (must be a function abstraction); variable: {}",
                x
            ),
        ),
    }
}

// ---------------------------------------------------------------------------
// Declaration errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum DeclError {
    KunifsRemain(Box<Vec<LocatedDeclaration>>),
    CunifsRemain(Box<Vec<LocatedDeclaration>>),
    Nonpositive(LocatedDeclaration),
    Hole(LocatedConstructor),
}

fn lspan(ds: &[LocatedDeclaration]) -> Span {
    ds.first()
        .map(|d| d.span.clone())
        .unwrap_or_else(Span::dummy)
}

pub fn decl_error(err: &DeclError) -> CompileError {
    match err {
        DeclError::KunifsRemain(ds) => {
            CompileError::at(
                lspan(ds),
                "Some kind unification variables are undetermined in declaration\n(look for them as \"<UNIF:...>\")",
            )
        }
        DeclError::CunifsRemain(ds) => {
            CompileError::at(
                lspan(ds),
                "Some constructor unification variables are undetermined in declaration\n(look for them as \"<UNIF:...>\")",
            )
        }
        DeclError::Nonpositive(d) => {
            CompileError::at(
                d.span.clone(),
                "Non-strictly-positive datatype declaration (could allow non-termination)",
            )
        }
        DeclError::Hole(c) => {
            CompileError::Plain(format!("Hole found with type: {:?}", c.node))
        }
    }
}

// ---------------------------------------------------------------------------
// Signature errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum SgnError {
    UnboundSgn(Span, String),
    UnmatchedSgi(Span, LocatedSignatureItem),
    SgiWrongKind(
        Span,
        LocatedSignatureItem,
        LocatedKind,
        LocatedSignatureItem,
        LocatedKind,
        KunifyError,
    ),
    SgiWrongCon(
        Span,
        LocatedSignatureItem,
        LocatedConstructor,
        LocatedSignatureItem,
        LocatedConstructor,
        CunifyError,
    ),
    SgiMismatchedDatatypes(
        Span,
        LocatedSignatureItem,
        LocatedSignatureItem,
        Option<(LocatedConstructor, LocatedConstructor, CunifyError)>,
    ),
    SgnWrongForm(Span, LocatedSignature, LocatedSignature),
    UnWhereable(LocatedSignature, String),
    WhereWrongKind(LocatedKind, LocatedKind, KunifyError),
    NotIncludable(LocatedSignature),
    DuplicateCon(Span, String),
    DuplicateVal(Span, String),
    DuplicateSgn(Span, String),
    DuplicateStr(Span, String),
    NotConstraintsable(LocatedSignature),
}

pub fn sgn_error(err: &SgnError) -> CompileError {
    match err {
        SgnError::UnboundSgn(span, s) => {
            CompileError::at(span.clone(), format!("Unbound signature variable:  {}", s))
        }
        SgnError::UnmatchedSgi(span, sgi) => {
            CompileError::at(span.clone(), format!("Unmatched signature item: {:?}", sgi.node))
        }
        SgnError::SgiWrongKind(span, sgi1, k1, sgi2, k2, kerr) => {
            CompileError::at(
                span.clone(),
                format!(
                    "Kind unification failure in signature matching: have {:?} (kind {:?}), need {:?} (kind {:?}); {}",
                    sgi1.node, k1.node, sgi2.node, k2.node,
                    kunify_error_message(kerr)
                ),
            )
        }
        SgnError::SgiWrongCon(span, sgi1, c1, sgi2, c2, cerr) => {
            CompileError::at(
                span.clone(),
                format!(
                    "Constructor unification failure in signature matching: have {:?} (con {:?}), need {:?} (con {:?}); {}",
                    sgi1.node, c1.node, sgi2.node, c2.node,
                    cunify_error(cerr)
                ),
            )
        }
        SgnError::SgiMismatchedDatatypes(span, sgi1, sgi2, cerro) => {
            let detail = if let Some((c1, c2, ue)) = cerro {
                format!("; unification error: {:?} vs {:?}; {}", c1.node, c2.node, cunify_error(ue))
            } else {
                String::new()
            };
            CompileError::at(
                span.clone(),
                format!(
                    "Mismatched 'datatype' specifications: {:?} vs {:?}{}",
                    sgi1.node, sgi2.node, detail
                ),
            )
        }
        SgnError::SgnWrongForm(span, sgn1, sgn2) => {
            CompileError::at(
                span.clone(),
                format!("Incompatible signatures: {:?} vs {:?}", sgn1.node, sgn2.node),
            )
        }
        SgnError::UnWhereable(sgn, x) => {
            CompileError::at(
                sgn.span.clone(),
                format!("Unavailable field for 'where': {}", x),
            )
        }
        SgnError::WhereWrongKind(k1, k2, kerr) => {
            CompileError::at(
                k1.span.clone(),
                format!(
                    "Wrong kind for 'where': have {:?}, need {:?}; {}",
                    k1.node,
                    k2.node,
                    kunify_error_message(kerr)
                ),
            )
        }
        SgnError::NotIncludable(sgn) => {
            CompileError::at(sgn.span.clone(), "Invalid signature to 'include'")
        }
        SgnError::DuplicateCon(span, s) => {
            CompileError::at(span.clone(), format!("Duplicate constructor {} in signature", s))
        }
        SgnError::DuplicateVal(span, s) => {
            CompileError::at(span.clone(), format!("Duplicate value {} in signature", s))
        }
        SgnError::DuplicateSgn(span, s) => {
            CompileError::at(span.clone(), format!("Duplicate signature {} in signature", s))
        }
        SgnError::DuplicateStr(span, s) => {
            CompileError::at(span.clone(), format!("Duplicate structure {} in signature", s))
        }
        SgnError::NotConstraintsable(sgn) => {
            CompileError::at(sgn.span.clone(), "Invalid signature for 'open constraints'")
        }
    }
}

// ---------------------------------------------------------------------------
// Structure errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum StrError {
    UnboundStr(Span, String),
    NotFunctor(LocatedSignature),
    FunctorRebind(Span),
    UnOpenable(LocatedSignature),
    NotType(Span, LocatedKind, (LocatedKind, LocatedKind, KunifyError)),
    DuplicateConstructor(String, Span),
    NotDatatype(Span),
}

pub fn str_error(err: &StrError) -> CompileError {
    match err {
        StrError::UnboundStr(span, s) => {
            CompileError::at(span.clone(), format!("Unbound structure variable {}", s))
        }
        StrError::NotFunctor(sgn) => {
            CompileError::at(sgn.span.clone(), "Application of non-functor")
        }
        StrError::FunctorRebind(span) => {
            CompileError::at(span.clone(), "Attempt to rebind functor")
        }
        StrError::UnOpenable(sgn) => CompileError::at(sgn.span.clone(), "Un-openable structure"),
        StrError::NotType(span, k, (k1, k2, ue)) => CompileError::at(
            span.clone(),
            format!(
                "'val' type kind is not 'Type': kind {:?}, subkind 1 {:?}, subkind 2 {:?}; {}",
                k.node,
                k1.node,
                k2.node,
                kunify_error_message(ue)
            ),
        ),
        StrError::DuplicateConstructor(x, span) => CompileError::at(
            span.clone(),
            format!("Duplicate datatype constructor {}", x),
        ),
        StrError::NotDatatype(span) => {
            CompileError::at(span.clone(), "Trying to import non-datatype as a datatype")
        }
    }
}
