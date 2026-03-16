#![allow(dead_code, unused_variables, unused_imports)]

//! Disjointness constraint environment and proof search.
//!
//! Translated from `disjoint.sml`.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use crate::elaborated::type_operations::hnorm_con;
use crate::elaborated::{Constructor, LocatedConstructor};
use crate::error_types::{Located, Span};

// ---------------------------------------------------------------------------
// Piece representation
// ---------------------------------------------------------------------------

/// The "first component" of a disjointness piece: what kind of name/row is it?
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PieceFst {
    /// A literal name constructor: `#"Foo"`
    NameC(String),
    /// A name from a de Bruijn rel variable
    NameR(usize),
    /// A name from a globally-named constructor
    NameN(usize),
    /// A name from a module projection
    NameM(usize, Vec<String>, String),
    /// A row from a de Bruijn rel variable
    RowR(usize),
    /// A row from a globally-named constructor
    RowN(usize),
    /// A row from a module projection
    RowM(usize, Vec<String>, String),
}

/// A piece is a `PieceFst` paired with a list of projection indices (for nested tuples).
pub type Piece = (PieceFst, Vec<usize>);

pub fn piece_to_string(p: &PieceFst) -> String {
    match p {
        PieceFst::NameC(s) => format!("NameC({})", s),
        PieceFst::NameR(n) => format!("NameR({})", n),
        PieceFst::NameN(n) => format!("NameN({})", n),
        PieceFst::NameM(n, _, s) => format!("NameM({}, {})", n, s),
        PieceFst::RowR(n) => format!("RowR({})", n),
        PieceFst::RowN(n) => format!("RowN({})", n),
        PieceFst::RowM(n, _, s) => format!("RowM({}, {})", n, s),
    }
}

pub fn rp_to_string(p: &Piece) -> String {
    let ns: Vec<String> = p.1.iter().map(|n| n.to_string()).collect();
    let mut parts = vec![piece_to_string(&p.0)];
    parts.extend(ns);
    parts.join(" ")
}

// ---------------------------------------------------------------------------
// Disjointness environment
// ---------------------------------------------------------------------------

/// The disjointness environment: for each piece `p1`, the set of pieces known
/// to be disjoint from it.
pub type DisjointEnv = BTreeMap<Piece, BTreeSet<Piece>>;

pub fn empty_env() -> DisjointEnv {
    BTreeMap::new()
}

/// Print the disjointness environment for debugging.
pub fn print_env(env: &DisjointEnv) {
    eprintln!("\nDENV:");
    for (p1, pset) in env {
        for p2 in pset {
            eprintln!("{} ~ {}", rp_to_string(p1), rp_to_string(p2));
        }
    }
}

// ---------------------------------------------------------------------------
// Goal type
// ---------------------------------------------------------------------------

/// An unresolved disjointness goal.
#[derive(Debug, Clone)]
pub struct Goal {
    pub span: Span,
    pub c1: LocatedConstructor,
    pub c2: LocatedConstructor,
    pub denv: DisjointEnv,
}

// ---------------------------------------------------------------------------
// Row conversion helpers
// ---------------------------------------------------------------------------

fn name_to_row(c: LocatedConstructor) -> LocatedConstructor {
    let span = c.span.clone();
    let unit_kind = Located {
        node: crate::elaborated::Kind::Unit,
        span: span.clone(),
    };
    let unit_con = Located {
        node: Constructor::Unit,
        span: span.clone(),
    };
    Located {
        node: Constructor::Record(Box::new(unit_kind), vec![(c, unit_con)]),
        span,
    }
}

fn piece_fst_to_row(p: &PieceFst, span: &Span) -> LocatedConstructor {
    let make = |c: Constructor| Located {
        node: c,
        span: span.clone(),
    };
    match p {
        PieceFst::NameC(s) => name_to_row(make(Constructor::Name(s.clone()))),
        PieceFst::NameR(n) => name_to_row(make(Constructor::Rel(*n))),
        PieceFst::NameN(n) => name_to_row(make(Constructor::Named(*n))),
        PieceFst::NameM(n, ms, x) => {
            name_to_row(make(Constructor::ModProj(*n, ms.clone(), x.clone())))
        }
        PieceFst::RowR(n) => make(Constructor::Rel(*n)),
        PieceFst::RowN(n) => make(Constructor::Named(*n)),
        PieceFst::RowM(n, ms, x) => make(Constructor::ModProj(*n, ms.clone(), x.clone())),
    }
}

pub fn piece_to_row(piece: &Piece, span: &Span) -> LocatedConstructor {
    let base = piece_fst_to_row(&piece.0, span);
    piece.1.iter().fold(base, |acc, &n| Located {
        node: Constructor::Proj(Box::new(acc), n),
        span: span.clone(),
    })
}

// ---------------------------------------------------------------------------
// De Bruijn shifting for pieces when entering a binder
// ---------------------------------------------------------------------------

fn piece_fst_enter(p: &PieceFst) -> PieceFst {
    match p {
        PieceFst::NameR(n) => PieceFst::NameR(n + 1),
        PieceFst::RowR(n) => PieceFst::RowR(n + 1),
        other => other.clone(),
    }
}

fn piece_enter(p: &Piece) -> Piece {
    (piece_fst_enter(&p.0), p.1.clone())
}

/// Shift the disjointness environment when entering a constructor binder.
pub fn enter(denv: DisjointEnv) -> DisjointEnv {
    let mut new_env = BTreeMap::new();
    for (p, pset) in denv {
        let new_p = piece_enter(&p);
        let new_pset = pset.into_iter().map(|q| piece_enter(&q)).collect();
        new_env.insert(new_p, new_pset);
    }
    new_env
}

// ---------------------------------------------------------------------------
// Decompose a row constructor into pieces
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Piece_ {
    Piece(Piece),
    Unknown(LocatedConstructor),
}

/// Decompose nested `CProj` projections, returning the base and the list of indices.
fn decompose_proj(c: LocatedConstructor) -> (LocatedConstructor, Vec<usize>) {
    let normed = hnorm_con(c.clone());
    match normed.node.clone() {
        Constructor::Proj(inner, n) => {
            let (base, mut ns) = decompose_proj(*inner);
            ns.push(n);
            (base, ns)
        }
        _ => (normed, vec![]),
    }
}

fn decompose_name(c: LocatedConstructor, acc: Vec<Piece_>) -> Vec<Piece_> {
    let (base, ns) = decompose_proj(c);
    let piece = match &base.node {
        Constructor::Name(s) => Some(Piece_::Piece((PieceFst::NameC(s.clone()), ns))),
        Constructor::Rel(n) => Some(Piece_::Piece((PieceFst::NameR(*n), ns))),
        Constructor::Named(n) => Some(Piece_::Piece((PieceFst::NameN(*n), ns))),
        Constructor::ModProj(m, ms, x) => Some(Piece_::Piece((
            PieceFst::NameM(*m, ms.clone(), x.clone()),
            ns,
        ))),
        _ => None,
    };
    let mut result = acc;
    match piece {
        Some(p) => result.push(p),
        None => result.push(Piece_::Unknown(base)),
    }
    result
}

fn decompose_row_inner(c: LocatedConstructor, acc: Vec<Piece_>) -> Vec<Piece_> {
    // Check for Map application first (skip it)
    let normed = hnorm_con(c.clone());
    match normed.node.clone() {
        Constructor::App(app_f, r) => {
            if let Constructor::App(map_f, _) = &app_f.node {
                if matches!(&map_f.node, Constructor::Map(_, _)) {
                    return decompose_row_inner(*r, acc);
                }
            }
            // fall through to default
            decompose_row_default(c, acc)
        }
        _ => decompose_row_default(c, acc),
    }
}

fn decompose_row_default(c: LocatedConstructor, acc: Vec<Piece_>) -> Vec<Piece_> {
    let normed = hnorm_con(c.clone());
    let (base, ns) = decompose_proj(c.clone());
    match base.node.clone() {
        Constructor::Record(_, xcs) => {
            let mut result = acc;
            for (x, _) in xcs {
                result = decompose_name(x, result);
            }
            result
        }
        Constructor::Concat(c1, c2) => {
            let acc2 = decompose_row_inner(*c2, acc);
            decompose_row_inner(*c1, acc2)
        }
        Constructor::Rel(n) => {
            let mut result = acc;
            result.push(Piece_::Piece((PieceFst::RowR(n), ns)));
            result
        }
        Constructor::Named(n) => {
            let mut result = acc;
            result.push(Piece_::Piece((PieceFst::RowN(n), ns)));
            result
        }
        Constructor::ModProj(m, ms, x) => {
            let mut result = acc;
            result.push(Piece_::Piece((PieceFst::RowM(m, ms, x), ns)));
            result
        }
        _ => {
            let mut result = acc;
            result.push(Piece_::Unknown(base));
            result
        }
    }
}

pub fn decompose_row(c: LocatedConstructor) -> Vec<Piece_> {
    decompose_row_inner(c, vec![])
}

// ---------------------------------------------------------------------------
// prove1 : primitive disjointness check
// ---------------------------------------------------------------------------

/// Returns `true` if `p1` and `p2` are statically known to be disjoint.
pub fn prove1(denv: &DisjointEnv, p1: &Piece, p2: &Piece) -> bool {
    match (&p1.0, &p2.0) {
        (PieceFst::NameC(s1), PieceFst::NameC(s2)) => s1.to_lowercase() != s2.to_lowercase(),
        _ => denv.get(p1).map(|pset| pset.contains(p2)).unwrap_or(false),
    }
}

// ---------------------------------------------------------------------------
// assert : add a disjointness fact
// ---------------------------------------------------------------------------

/// Record that `c1` and `c2` are disjoint, updating the environment.
pub fn assert(
    c1: LocatedConstructor,
    c2: LocatedConstructor,
    mut denv: DisjointEnv,
) -> DisjointEnv {
    let ps1_raw = decompose_row(c1);
    let ps2_raw = decompose_row(c2);

    let ps1: Vec<Piece> = ps1_raw
        .into_iter()
        .filter_map(|p| match p {
            Piece_::Piece(p) => Some(p),
            Piece_::Unknown(_) => None,
        })
        .collect();
    let ps2: Vec<Piece> = ps2_raw
        .into_iter()
        .filter_map(|p| match p {
            Piece_::Piece(p) => Some(p),
            Piece_::Unknown(_) => None,
        })
        .collect();

    // For each p1 in ps1, add all of ps2 as known disjoint from p1
    for p1 in &ps1 {
        let entry = denv.entry(p1.clone()).or_insert_with(BTreeSet::new);
        for p2 in &ps2 {
            // NameC pieces know they're disjoint from other NameC pieces automatically;
            // don't record them to keep the env smaller
            if !matches!((&p1.0, &p2.0), (PieceFst::NameC(_), PieceFst::NameC(_))) {
                entry.insert(p2.clone());
            }
        }
    }
    // And vice versa
    for p2 in &ps2 {
        let entry = denv.entry(p2.clone()).or_insert_with(BTreeSet::new);
        for p1 in &ps1 {
            if !matches!((&p2.0, &p1.0), (PieceFst::NameC(_), PieceFst::NameC(_))) {
                entry.insert(p1.clone());
            }
        }
    }

    denv
}

// ---------------------------------------------------------------------------
// prove : attempt to discharge a disjointness goal
// ---------------------------------------------------------------------------

/// Proved goals counter (mirrors SML's `proved` ref).
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
static PROVED: AtomicUsize = AtomicUsize::new(0);

pub fn reset() {
    PROVED.store(0, AtomicOrdering::Relaxed);
    crate::elaborated::type_operations::reset_stats();
}

/// Try to prove that `c1` and `c2` are disjoint using `denv`.
///
/// Returns a (possibly empty) list of unresolved `Goal`s.  An empty list
/// means the proof succeeded.
pub fn prove(
    span: Span,
    denv: &DisjointEnv,
    c1: LocatedConstructor,
    c2: LocatedConstructor,
) -> Vec<Goal> {
    PROVED.fetch_add(1, AtomicOrdering::Relaxed);

    let ps1 = decompose_row(c1.clone());
    let ps2 = decompose_row(c2.clone());

    let has_unknown = |ps: &[Piece_]| ps.iter().any(|p| matches!(p, Piece_::Unknown(_)));
    let has_pieces = |ps: &[Piece_]| ps.iter().any(|p| matches!(p, Piece_::Piece(_)));

    // If either side has unknowns and the other is non-empty, we can't decide
    if (has_unknown(&ps1) && has_pieces(&ps2)) || (has_unknown(&ps2) && has_pieces(&ps1)) {
        return vec![Goal {
            span,
            c1,
            c2,
            denv: denv.clone(),
        }];
    }

    let clean_ps1: Vec<Piece> = ps1
        .into_iter()
        .filter_map(|p| match p {
            Piece_::Piece(p) => Some(p),
            _ => None,
        })
        .collect();
    let clean_ps2: Vec<Piece> = ps2
        .into_iter()
        .filter_map(|p| match p {
            Piece_::Piece(p) => Some(p),
            _ => None,
        })
        .collect();

    let mut remaining = vec![];
    for p1 in &clean_ps1 {
        for p2 in &clean_ps2 {
            if !prove1(denv, p1, p2) {
                remaining.push(Goal {
                    span: span.clone(),
                    c1: piece_to_row(p1, &span),
                    c2: piece_to_row(p2, &span),
                    denv: denv.clone(),
                });
            }
        }
    }
    remaining
}
