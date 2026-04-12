//! Disjointness constraint environment and proof search.
//!
//! Translated from `disjoint.sml`.
//!
//! Public [`prove`], [`assert`], [`decompose_row`], and helpers document `# Arguments` / `# Returns`.

use std::collections::{BTreeMap, BTreeSet};

use crate::compiler_tracing::TRACING_TARGET_COMPILER_INTERNALS;
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

/// Debug string for the “head” of a disjointness [`Piece`].
///
/// # Arguments
///
/// * `p` — First component only (no projection suffix).
///
/// # Returns
///
/// Human-readable label (not valid Ur/Web syntax).
pub fn piece_to_string(head_piece: &PieceFst) -> String {
    match head_piece {
        PieceFst::NameC(s) => format!("NameC({})", s),
        PieceFst::NameR(n) => format!("NameR({})", n),
        PieceFst::NameN(n) => format!("NameN({})", n),
        PieceFst::NameM(n, _, s) => format!("NameM({}, {})", n, s),
        PieceFst::RowR(n) => format!("RowR({})", n),
        PieceFst::RowN(n) => format!("RowN({})", n),
        PieceFst::RowM(n, _, s) => format!("RowM({}, {})", n, s),
    }
}

/// Debug string for a full [`Piece`] including projection indices.
///
/// # Returns
///
/// Space-separated [`piece_to_string`] head plus index numbers.
pub fn rp_to_string(piece_with_projections: &Piece) -> String {
    let projection_indices: Vec<String> = piece_with_projections
        .1
        .iter()
        .map(|index| index.to_string())
        .collect();
    let mut parts = vec![piece_to_string(&piece_with_projections.0)];
    parts.extend(projection_indices);
    parts.join(" ")
}

// ---------------------------------------------------------------------------
// Disjointness environment
// ---------------------------------------------------------------------------

/// The disjointness environment: for each piece `p1`, the set of pieces known
/// to be disjoint from it.
pub type DisjointEnv = BTreeMap<Piece, BTreeSet<Piece>>;

/// Empty disjointness map (no facts yet).
///
/// # Returns
///
/// New [`DisjointEnv`].
pub fn empty_env() -> DisjointEnv {
    BTreeMap::new()
}

/// Log `disjointness_map` at [`tracing::Level::DEBUG`] (`DENV` snapshot, one event per disjoint pair).
///
/// # Arguments
///
/// * `disjointness_map` — Environment to dump.
///
/// # Returns
///
/// Nothing.
pub fn print_env(disjointness_map: &DisjointEnv) {
    tracing::debug!(
        target: TRACING_TARGET_COMPILER_INTERNALS,
        "DENV: {} roots",
        disjointness_map.len()
    );
    for (left_piece, disjoint_right_set) in disjointness_map {
        for right_piece in disjoint_right_set {
            tracing::debug!(
                target: TRACING_TARGET_COMPILER_INTERNALS,
                left = %rp_to_string(left_piece),
                right = %rp_to_string(right_piece),
                "DENV pair"
            );
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
    pub left_constructor: LocatedConstructor,
    pub right_constructor: LocatedConstructor,
    pub disjointness_environment: DisjointEnv,
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

/// Turn abstract [`Piece`] plus `span` into a row-shaped [`LocatedConstructor`] (for reifying goals).
///
/// # Arguments
///
/// * `piece` — Name or row piece with optional projection-index suffix.
/// * `span` — Source span for synthetic nodes.
///
/// # Returns
///
/// Constructor representing that piece as a row (wrapped names become single-field records).
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

/// Shift de Bruijn-relative [`PieceFst::NameR`] / [`PieceFst::RowR`] entries when entering a binder.
///
/// # Arguments
///
/// * `denv` — Prior environment.
///
/// # Returns
///
/// New map with incremented rel levels on key and value pieces.
pub fn enter(disjointness_environment: DisjointEnv) -> DisjointEnv {
    let mut shifted = BTreeMap::new();
    for (piece, right_set) in disjointness_environment {
        let shifted_piece = piece_enter(&piece);
        let shifted_right_set = right_set
            .into_iter()
            .map(|other| piece_enter(&other))
            .collect();
        shifted.insert(shifted_piece, shifted_right_set);
    }
    shifted
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
    let _normed = hnorm_con(c.clone());
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

/// Primitive disjointness: distinct literal names, or `p2` recorded under `p1` in `denv`.
///
/// # Arguments
///
/// * `denv` — Known disjoint pairs.
/// * `p1`, `p2` — Pieces to test.
///
/// # Returns
///
/// `true` if disjoint under those rules.
pub fn prove1(
    disjointness_hypotheses: &DisjointEnv,
    left_piece: &Piece,
    right_piece: &Piece,
) -> bool {
    match (&left_piece.0, &right_piece.0) {
        (PieceFst::NameC(left_name), PieceFst::NameC(right_name)) => {
            left_name.to_lowercase() != right_name.to_lowercase()
        }
        _ => disjointness_hypotheses
            .get(left_piece)
            .map(|right_set| right_set.contains(right_piece))
            .unwrap_or(false),
    }
}

// ---------------------------------------------------------------------------
// assert : add a disjointness fact
// ---------------------------------------------------------------------------

/// Record that row shapes `c1` and `c2` are disjoint by decomposing and linking all piece pairs.
///
/// Ignores [`Piece_::Unknown`] halves. Symmetric edges are inserted (except redundant literal–literal pairs).
///
/// # Arguments
///
/// * `c1`, `c2` — Row (or name) constructors.
/// * `denv` — Environment to extend.
///
/// # Returns
///
/// Updated [`DisjointEnv`].
pub fn assert(
    left_row_constructor: LocatedConstructor,
    right_row_constructor: LocatedConstructor,
    mut disjointness_environment: DisjointEnv,
) -> DisjointEnv {
    let left_decomposition = decompose_row(left_row_constructor);
    let right_decomposition = decompose_row(right_row_constructor);

    let left_pieces: Vec<Piece> = left_decomposition
        .into_iter()
        .filter_map(|fragment| match fragment {
            Piece_::Piece(piece) => Some(piece),
            Piece_::Unknown(_) => None,
        })
        .collect();
    let right_pieces: Vec<Piece> = right_decomposition
        .into_iter()
        .filter_map(|fragment| match fragment {
            Piece_::Piece(piece) => Some(piece),
            Piece_::Unknown(_) => None,
        })
        .collect();

    for left_piece in &left_pieces {
        let entry = disjointness_environment
            .entry(left_piece.clone())
            .or_default();
        for right_piece in &right_pieces {
            if !matches!(
                (&left_piece.0, &right_piece.0),
                (PieceFst::NameC(_), PieceFst::NameC(_))
            ) {
                entry.insert(right_piece.clone());
            }
        }
    }
    for right_piece in &right_pieces {
        let entry = disjointness_environment
            .entry(right_piece.clone())
            .or_default();
        for left_piece in &left_pieces {
            if !matches!(
                (&right_piece.0, &left_piece.0),
                (PieceFst::NameC(_), PieceFst::NameC(_))
            ) {
                entry.insert(left_piece.clone());
            }
        }
    }

    disjointness_environment
}

// ---------------------------------------------------------------------------
// prove : attempt to discharge a disjointness goal
// ---------------------------------------------------------------------------

/// Proved goals counter (mirrors SML's `proved` ref).
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
static PROVED: AtomicUsize = AtomicUsize::new(0);

/// Reset the proved-goal counter and [`crate::elaborated::type_operations::reset_stats`].
///
/// # Returns
///
/// Nothing.
pub fn reset() {
    PROVED.store(0, AtomicOrdering::Relaxed);
    crate::elaborated::type_operations::reset_stats();
}

/// Try to show two row constructors disjoint using `disjointness_hypotheses`.
///
/// Pairs every piece from each side; any pair not justified by [`prove1`] becomes a [`Goal`].
/// Mixed unknown/known decompositions short-circuit to a single goal.
///
/// # Arguments
///
/// * `diagnostic_span` — Span for emitted goals.
/// * `disjointness_hypotheses` — Current disjointness map.
/// * `left_constructor`, `right_constructor` — Row (or name) types to relate.
///
/// # Returns
///
/// Empty `Vec` when fully discharged; otherwise one [`Goal`] per missing pairwise proof (may contain duplicates).
pub fn prove(
    diagnostic_span: Span,
    disjointness_hypotheses: &DisjointEnv,
    left_constructor: LocatedConstructor,
    right_constructor: LocatedConstructor,
) -> Vec<Goal> {
    PROVED.fetch_add(1, AtomicOrdering::Relaxed);

    let left_fragments = decompose_row(left_constructor.clone());
    let right_fragments = decompose_row(right_constructor.clone());

    let decomposition_has_unknown = |fragments: &[Piece_]| {
        fragments
            .iter()
            .any(|fragment| matches!(fragment, Piece_::Unknown(_)))
    };
    let decomposition_has_piece = |fragments: &[Piece_]| {
        fragments
            .iter()
            .any(|fragment| matches!(fragment, Piece_::Piece(_)))
    };

    if (decomposition_has_unknown(&left_fragments) && decomposition_has_piece(&right_fragments))
        || (decomposition_has_unknown(&right_fragments) && decomposition_has_piece(&left_fragments))
    {
        return vec![Goal {
            span: diagnostic_span,
            left_constructor,
            right_constructor,
            disjointness_environment: disjointness_hypotheses.clone(),
        }];
    }

    let left_pieces: Vec<Piece> = left_fragments
        .into_iter()
        .filter_map(|fragment| match fragment {
            Piece_::Piece(piece) => Some(piece),
            _ => None,
        })
        .collect();
    let right_pieces: Vec<Piece> = right_fragments
        .into_iter()
        .filter_map(|fragment| match fragment {
            Piece_::Piece(piece) => Some(piece),
            _ => None,
        })
        .collect();

    let mut unresolved_goals = vec![];
    for left_piece in &left_pieces {
        for right_piece in &right_pieces {
            if !prove1(disjointness_hypotheses, left_piece, right_piece) {
                unresolved_goals.push(Goal {
                    span: diagnostic_span.clone(),
                    left_constructor: piece_to_row(left_piece, &diagnostic_span),
                    right_constructor: piece_to_row(right_piece, &diagnostic_span),
                    disjointness_environment: disjointness_hypotheses.clone(),
                });
            }
        }
    }
    unresolved_goals
}
