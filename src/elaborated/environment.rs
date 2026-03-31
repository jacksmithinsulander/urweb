//! Environment for the Elaborated AST — tracks all bindings during type inference.
//!
//! The `Env` struct is the central context threaded through the elaboration pass.
//! It records every in-scope binding at every point in the source, grouped by
//! their syntactic category:
//!
//! | Category | Relative (de Bruijn) | Named (global id) |
//! |----------|---------------------|-------------------|
//! | Kinds | `rel_k` / `rename_k` | — |
//! | Constructors | `rel_c` / `rename_c` | `named_c` |
//! | Expressions | `rel_e` / `rename_e` | `named_e` |
//! | Signatures | — | `named_sgn` / `rename_sgn` |
//! | Structures | — | `named_str` / `rename_str` |
//!
//! The environment also stores datatype definitions (for constructor lookup) and
//! typeclass instances (for implicit argument synthesis).
//!
//! All `push_*` methods return a new `Env` value (functional-update style), faithfully
//! mirroring the SML original which builds new record values on each binding.
//!
//! Mirrors `elab_env.sml` (1721 lines).
//!
//! Public binders and [`hnorm_sgn`] document `# Arguments` / `# Returns`; [`new_named_id`] is thread-safe.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

use super::type_operations;
use crate::datatype_kind::DatatypeKind;
use crate::elaborated::{
    CaseMeta, Constructor, DatatypeDecl, Declaration, ElaboratedDeclaration, Explicitness,
    Expression, FieldMeta, Kind, LocatedConstructor, LocatedDeclaration,
    LocatedElaboratedDeclaration, LocatedExpression, LocatedKind, LocatedPattern, LocatedSignature,
    LocatedSignatureItem, Pattern, RestMeta, Signature, SignatureItem,
};
use crate::error_types::{Located, Span};

// ---------------------------------------------------------------------------
// Global fresh-id counter
// ---------------------------------------------------------------------------

/// Monotonically increasing counter used to assign globally-unique ids to
/// named constructors, expressions, signatures, and structures.
///
/// Mirrors `val namedCounter = ref 0` in `elab_env.sml`.
static NAMED_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Allocate a fresh globally unique id for [`Constructor::Named`], expressions, signatures, structures.
///
/// # Returns
///
/// Next counter value (monotonic, [`AtomicUsize::fetch_add`]).
pub fn new_named_id() -> usize {
    NAMED_COUNTER.fetch_add(1, AtomicOrdering::Relaxed)
}

/// Reset the global named-id counter to zero — only for isolated unit tests.
///
/// # Safety
///
/// Must not run while elaboration that allocates named ids is in progress.
///
/// # Returns
///
/// Nothing.
#[cfg(test)]
pub fn reset_named_counter() {
    NAMED_COUNTER.store(0, AtomicOrdering::Relaxed);
}

// ---------------------------------------------------------------------------
// Class name key
// ---------------------------------------------------------------------------

/// Identifies a typeclass in the class environment.
///
/// A class is either a global named constructor (`Named(id)`) or a constructor
/// projected from a module (`Proj(mod_id, path, name)`).
///
/// Mirrors `datatype class_name = ClNamed of int | ClProj of int * string list * string`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ClassName {
    /// A named class, identified by its globally-unique id.
    Named(usize),
    /// A class projected from a structure: `Proj(module_id, module_path, class_name)`.
    Proj(usize, Vec<String>, String),
}

impl ClassName {
    /// Convert to a constructor suitable for inserting into the elaborated AST.
    pub fn to_con(&self, span: Span) -> LocatedConstructor {
        let node = match self {
            ClassName::Named(id) => Constructor::Named(*id),
            ClassName::Proj(module_id, path, name) => {
                Constructor::ModProj(*module_id, path.clone(), name.clone())
            }
        };
        Located::new(node, span)
    }
}

// ---------------------------------------------------------------------------
// Typeclass rules
// ---------------------------------------------------------------------------

/// A single typeclass resolution rule:
/// `(num_quantifiers, hypotheses, conclusion_con, witness_exp)`.
///
/// - `num_quantifiers`: number of universally-quantified constructor variables.
/// - `hypotheses`: the list of class constraints that must be satisfied.
/// - `conclusion`: the constructor to which the rule's head matches.
/// - `witness`: the expression term to inject when the rule fires.
///
/// Mirrors `type rules = (int * con list * con * exp) list`.
pub type ClassRule = (
    usize,
    Vec<LocatedConstructor>,
    LocatedConstructor,
    LocatedExpression,
);

/// Closed and open resolution rules for a single typeclass.
///
/// - `closed_rules`: rules from named (globally imported) instances — fire first.
/// - `open_rules`: rules from locally-bound variables (e.g. function parameters) — fire
///   after closed rules and are lifted when the expression environment grows.
///
/// Mirrors `type class = {closedRules : rules, openRules : rules}`.
#[derive(Debug, Clone)]
pub struct ClassRules {
    /// Rules that do not depend on any local expression variable.
    pub closed_rules: Vec<ClassRule>,
    /// Rules derived from locally-bound expression variables; must be lifted
    /// when new expression bindings are introduced via [`Env::push_e_rel`].
    pub open_rules: Vec<ClassRule>,
}

impl ClassRules {
    pub fn empty() -> Self {
        ClassRules {
            closed_rules: vec![],
            open_rules: vec![],
        }
    }
}

// ---------------------------------------------------------------------------
// Internal variable-entry types
// ---------------------------------------------------------------------------

/// Internal record for a constructor variable — either a relative de Bruijn
/// binding or a named (globally-identified) binding.
///
/// Mirrors `'a var' = Rel' of int * 'a | Named' of int * 'a`.
#[derive(Debug, Clone)]
enum CVarEntry {
    /// A relative constructor binding: `(de_bruijn_index, kind)`.
    Rel(usize, LocatedKind),
    /// A named constructor binding: `(id, kind)`.
    Named(usize, LocatedKind),
}

/// Internal record for an expression variable — either a relative de Bruijn
/// binding or a named (globally-identified) binding.
#[derive(Debug, Clone)]
enum EVarEntry {
    /// A relative expression binding: `(de_bruijn_index, constructor_type)`.
    Rel(usize, LocatedConstructor),
    /// A named expression binding: `(id, constructor_type)`.
    Named(usize, LocatedConstructor),
}

// ---------------------------------------------------------------------------
// Public variable-lookup result
// ---------------------------------------------------------------------------

/// Result of looking up a variable by name in the environment.
///
/// Mirrors `datatype 'a var = NotBound | Rel of int * 'a | Named of int * 'a`.
#[derive(Debug, Clone)]
pub enum VarLookup<T> {
    /// The name is not bound in any enclosing scope.
    NotBound,
    /// The name was bound by a relative (de Bruijn) binder at depth `index`.
    Rel(usize, T),
    /// The name was bound as a globally-named declaration with id `id`.
    Named(usize, T),
}

impl<T> VarLookup<T> {
    /// Returns `true` when the name was not found in any scope.
    pub fn is_not_bound(&self) -> bool {
        matches!(self, VarLookup::NotBound)
    }

    /// Returns `true` when the name resolves to a relative de Bruijn binding.
    pub fn is_rel(&self) -> bool {
        matches!(self, VarLookup::Rel(_, _))
    }

    /// Returns `true` when the name resolves to a globally-named binding.
    pub fn is_named(&self) -> bool {
        matches!(self, VarLookup::Named(_, _))
    }

    /// De Bruijn index when this lookup is a `Rel` binding.
    pub fn rel_index(&self) -> Option<usize> {
        match self {
            VarLookup::Rel(index, _) => Some(*index),
            _ => None,
        }
    }

    /// Named id when this lookup is a `Named` binding.
    pub fn named_id(&self) -> Option<usize> {
        match self {
            VarLookup::Named(id, _) => Some(*id),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Datatype storage
// ---------------------------------------------------------------------------

/// Stored information about a declared datatype.
///
/// Mirrors `type datatyp = string list * (string * con option) IM.map`.
#[derive(Debug, Clone)]
pub struct DatatypeInfo {
    /// Names of type parameters (one per `KArrow` in the kind).
    pub type_params: Vec<String>,
    /// Map from constructor id to `(constructor_name, optional_argument_type)`.
    pub constructors_by_id: HashMap<usize, (String, Option<LocatedConstructor>)>,
}

/// Lookup information for a single datatype constructor, stored by name.
///
/// Mirrors the `constructors` field: `(dk * int * string list * con option * int) SM.map`.
#[derive(Debug, Clone)]
pub struct ConstructorInfo {
    /// Whether this datatype is represented as Enum, Option, or Default.
    pub datatype_kind: DatatypeKind,
    /// Globally-unique id of this constructor.
    pub constructor_id: usize,
    /// Type parameter names of the enclosing datatype.
    pub type_params: Vec<String>,
    /// Optional payload type for this constructor.
    pub arg_type: Option<LocatedConstructor>,
    /// Globally-unique id of the enclosing datatype.
    pub datatype_id: usize,
}

// ---------------------------------------------------------------------------
// Lookup errors
// ---------------------------------------------------------------------------

/// Errors that can arise when querying the environment.
#[derive(Debug, Clone)]
pub enum EnvError {
    /// No kind variable with this de Bruijn index exists.
    UnboundKRel(usize),
    /// No constructor variable with this de Bruijn index exists.
    UnboundCRel(usize),
    /// No named constructor with this id is registered.
    UnboundCNamed(usize),
    /// No expression variable with this de Bruijn index exists.
    UnboundERel(usize),
    /// No named expression with this id is registered.
    UnboundENamed(usize),
    /// No named signature with this id is registered.
    UnboundSgnNamed(usize),
    /// No named structure with this id is registered.
    UnboundStrNamed(usize),
}

impl std::fmt::Display for EnvError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvError::UnboundKRel(index) => write!(formatter, "unbound kind rel #{index}"),
            EnvError::UnboundCRel(index) => write!(formatter, "unbound con rel #{index}"),
            EnvError::UnboundCNamed(id) => write!(formatter, "unbound named con [{id}]"),
            EnvError::UnboundERel(index) => write!(formatter, "unbound exp rel #{index}"),
            EnvError::UnboundENamed(id) => write!(formatter, "unbound named exp [{id}]"),
            EnvError::UnboundSgnNamed(id) => write!(formatter, "unbound named sgn [{id}]"),
            EnvError::UnboundStrNamed(id) => write!(formatter, "unbound named str [{id}]"),
        }
    }
}

impl std::error::Error for EnvError {}

// ---------------------------------------------------------------------------
// Expression-level de Bruijn lifting helpers
// ---------------------------------------------------------------------------
//
// These functions walk Exp trees and lift the specified kind of free index by 1.
// They are called by push_k_rel, push_c_rel, and push_e_rel to update the types
// of already-stored class open rules.
//
// Each function tracks the relevant "depth" variable: the number of local
// binders of the appropriate category we have descended through, below which
// indices are local (bound) and must NOT be lifted.

/// Counts the number of expression variables bound by a pattern.
fn pattern_binds_count(pattern: &LocatedPattern) -> usize {
    match &pattern.node {
        Pattern::Var(_, _) => 1,
        Pattern::Prim(_) => 0,
        Pattern::Constructor(_, _, _, None) => 0,
        Pattern::Constructor(_, _, _, Some(inner_pattern)) => pattern_binds_count(inner_pattern),
        Pattern::Record(fields) => fields
            .iter()
            .map(|(_, sub_pattern, _)| pattern_binds_count(sub_pattern))
            .sum(),
    }
}

/// Lift all free `Kind::Rel(n)` for `n >= kind_bound` by 1 inside an expression.
///
/// Used by [`Env::push_k_rel`] to update stored class open-rule expressions.
/// The bound increments whenever we enter a `KAbs` body (which introduces one
/// new kind variable).  Other binders (constructor or expression) do not affect
/// the kind bound.
fn lift_kind_in_exp_bound(kind_bound: usize, expression: LocatedExpression) -> LocatedExpression {
    let span = expression.span.clone();
    let node = match expression.node {
        // Leaves with no sub-structure relevant to kinds:
        Expression::Prim(_)
        | Expression::Rel(_)
        | Expression::Named(_)
        | Expression::ModProj(_, _, _)
        | Expression::Error
        | Expression::Unif(_)
        | Expression::Hole(_) => expression.node,

        Expression::App(function_exp, argument_exp) => Expression::App(
            Box::new(lift_kind_in_exp_bound(kind_bound, *function_exp)),
            Box::new(lift_kind_in_exp_bound(kind_bound, *argument_exp)),
        ),

        // Abs introduces an expression binder — kind_bound does not change.
        Expression::Abs(param_name, param_type, result_type, body) => Expression::Abs(
            param_name,
            lift_kind_in_con_at(kind_bound, param_type),
            lift_kind_in_con_at(kind_bound, result_type),
            Box::new(lift_kind_in_exp_bound(kind_bound, *body)),
        ),

        Expression::CApp(function_exp, constructor_arg) => Expression::CApp(
            Box::new(lift_kind_in_exp_bound(kind_bound, *function_exp)),
            lift_kind_in_con_at(kind_bound, constructor_arg),
        ),

        // CAbs introduces a constructor binder — kind_bound does not change.
        Expression::CAbs(explicitness, name, kind_annotation, body) => Expression::CAbs(
            explicitness,
            name,
            Box::new(lift_kind_at(kind_bound, *kind_annotation)),
            Box::new(lift_kind_in_exp_bound(kind_bound, *body)),
        ),

        // KAbs introduces a KIND binder — kind_bound increments for the body.
        Expression::KAbs(name, body) => Expression::KAbs(
            name,
            Box::new(lift_kind_in_exp_bound(kind_bound + 1, *body)),
        ),

        Expression::KApp(function_exp, kind_arg) => Expression::KApp(
            Box::new(lift_kind_in_exp_bound(kind_bound, *function_exp)),
            Box::new(lift_kind_at(kind_bound, *kind_arg)),
        ),

        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(field_name_con, value_exp, field_type_con)| {
                    (
                        lift_kind_in_con_at(kind_bound, field_name_con),
                        lift_kind_in_exp_bound(kind_bound, value_exp),
                        lift_kind_in_con_at(kind_bound, field_type_con),
                    )
                })
                .collect(),
        ),

        Expression::Field(record_exp, field_con, meta) => Expression::Field(
            Box::new(lift_kind_in_exp_bound(kind_bound, *record_exp)),
            lift_kind_in_con_at(kind_bound, field_con),
            FieldMeta {
                field: lift_kind_in_con_at(kind_bound, meta.field),
                rest: lift_kind_in_con_at(kind_bound, meta.rest),
            },
        ),

        Expression::Concat(left_exp, left_con, right_exp, right_con) => Expression::Concat(
            Box::new(lift_kind_in_exp_bound(kind_bound, *left_exp)),
            lift_kind_in_con_at(kind_bound, left_con),
            Box::new(lift_kind_in_exp_bound(kind_bound, *right_exp)),
            lift_kind_in_con_at(kind_bound, right_con),
        ),

        Expression::Cut(record_exp, field_con, meta) => Expression::Cut(
            Box::new(lift_kind_in_exp_bound(kind_bound, *record_exp)),
            lift_kind_in_con_at(kind_bound, field_con),
            FieldMeta {
                field: lift_kind_in_con_at(kind_bound, meta.field),
                rest: lift_kind_in_con_at(kind_bound, meta.rest),
            },
        ),

        Expression::CutMulti(record_exp, fields_con, meta) => Expression::CutMulti(
            Box::new(lift_kind_in_exp_bound(kind_bound, *record_exp)),
            lift_kind_in_con_at(kind_bound, fields_con),
            RestMeta {
                rest: lift_kind_in_con_at(kind_bound, meta.rest),
            },
        ),

        Expression::Case(scrutinee, branches, case_meta) => Expression::Case(
            Box::new(lift_kind_in_exp_bound(kind_bound, *scrutinee)),
            branches
                .into_iter()
                .map(|(pattern, branch_exp)| {
                    (
                        lift_kind_in_pat_bound(kind_bound, pattern),
                        // Case branches do not introduce kind binders.
                        lift_kind_in_exp_bound(kind_bound, branch_exp),
                    )
                })
                .collect(),
            CaseMeta {
                disc: lift_kind_in_con_at(kind_bound, case_meta.disc),
                result: lift_kind_in_con_at(kind_bound, case_meta.result),
            },
        ),

        Expression::Let(e_decls, body, result_type) => Expression::Let(
            e_decls
                .into_iter()
                .map(|decl| lift_kind_in_edecl_bound(kind_bound, decl))
                .collect(),
            Box::new(lift_kind_in_exp_bound(kind_bound, *body)),
            lift_kind_in_con_at(kind_bound, result_type),
        ),
    };
    Located::new(node, span)
}

/// Lift `Kind::Rel` in a pattern's type annotations (kind_bound is preserved).
fn lift_kind_in_pat_bound(kind_bound: usize, pattern: LocatedPattern) -> LocatedPattern {
    let span = pattern.span.clone();
    let node = match pattern.node {
        Pattern::Var(name, type_con) => {
            Pattern::Var(name, lift_kind_in_con_at(kind_bound, type_con))
        }
        Pattern::Prim(prim) => Pattern::Prim(prim),
        Pattern::Constructor(dk, pat_con, type_args, inner_pattern) => Pattern::Constructor(
            dk,
            pat_con,
            type_args
                .into_iter()
                .map(|arg| lift_kind_in_con_at(kind_bound, arg))
                .collect(),
            inner_pattern.map(|inner| Box::new(lift_kind_in_pat_bound(kind_bound, *inner))),
        ),
        Pattern::Record(fields) => Pattern::Record(
            fields
                .into_iter()
                .map(|(name, sub_pat, type_con)| {
                    (
                        name,
                        lift_kind_in_pat_bound(kind_bound, sub_pat),
                        lift_kind_in_con_at(kind_bound, type_con),
                    )
                })
                .collect(),
        ),
    };
    Located::new(node, span)
}

/// Lift `Kind::Rel` in an expression-level declaration.
fn lift_kind_in_edecl_bound(
    kind_bound: usize,
    e_decl: LocatedElaboratedDeclaration,
) -> LocatedElaboratedDeclaration {
    let span = e_decl.span.clone();
    let node = match e_decl.node {
        ElaboratedDeclaration::Val(pattern, type_con, body_exp) => ElaboratedDeclaration::Val(
            lift_kind_in_pat_bound(kind_bound, pattern),
            lift_kind_in_con_at(kind_bound, type_con),
            lift_kind_in_exp_bound(kind_bound, body_exp),
        ),
        ElaboratedDeclaration::ValRec(bindings) => ElaboratedDeclaration::ValRec(
            bindings
                .into_iter()
                .map(|(name, type_con, body_exp)| {
                    (
                        name,
                        lift_kind_in_con_at(kind_bound, type_con),
                        lift_kind_in_exp_bound(kind_bound, body_exp),
                    )
                })
                .collect(),
        ),
    };
    Located::new(node, span)
}

/// Lift `Kind::Rel(n)` for `n >= kind_bound` by 1 within a kind.
fn lift_kind_at(kind_bound: usize, kind: LocatedKind) -> LocatedKind {
    lift_kind_in_kind_recursively(kind_bound, kind)
}

/// Recursive kind lifter with configurable bound.
fn lift_kind_in_kind_recursively(kind_bound: usize, kind: LocatedKind) -> LocatedKind {
    let span = kind.span.clone();
    let node = match kind.node {
        Kind::Rel(index) => {
            if index >= kind_bound {
                Kind::Rel(index + 1)
            } else {
                Kind::Rel(index)
            }
        }
        Kind::Arrow(domain, codomain) => Kind::Arrow(
            Box::new(lift_kind_in_kind_recursively(kind_bound, *domain)),
            Box::new(lift_kind_in_kind_recursively(kind_bound, *codomain)),
        ),
        Kind::Record(inner) => {
            Kind::Record(Box::new(lift_kind_in_kind_recursively(kind_bound, *inner)))
        }
        Kind::Tuple(kinds) => Kind::Tuple(
            kinds
                .into_iter()
                .map(|k| lift_kind_in_kind_recursively(kind_bound, k))
                .collect(),
        ),
        Kind::Fun(name, body) => Kind::Fun(
            name,
            Box::new(lift_kind_in_kind_recursively(kind_bound + 1, *body)),
        ),
        other => other,
    };
    Located::new(node, span)
}

/// Lift `Kind::Rel` references inside a constructor, with configurable starting bound.
fn lift_kind_in_con_at(kind_bound: usize, constructor: LocatedConstructor) -> LocatedConstructor {
    lift_kind_in_con_recursively(kind_bound, constructor)
}

/// Recursive con lifter for kind indices.
fn lift_kind_in_con_recursively(
    kind_bound: usize,
    constructor: LocatedConstructor,
) -> LocatedConstructor {
    let span = constructor.span.clone();
    let node = match constructor.node {
        // Leaves that contain no kind references:
        Constructor::Rel(_)
        | Constructor::Named(_)
        | Constructor::Name(_)
        | Constructor::Unit
        | Constructor::Error => constructor.node,
        Constructor::ModProj(module_id, path, name) => Constructor::ModProj(module_id, path, name),

        Constructor::TFun(domain, codomain) => Constructor::TFun(
            Box::new(lift_kind_in_con_recursively(kind_bound, *domain)),
            Box::new(lift_kind_in_con_recursively(kind_bound, *codomain)),
        ),

        // TCFun binds a CONSTRUCTOR variable (not a kind) — kind_bound unchanged.
        Constructor::TCFun(explicitness, name, kind_annotation, body) => Constructor::TCFun(
            explicitness,
            name,
            Box::new(lift_kind_in_kind_recursively(kind_bound, *kind_annotation)),
            Box::new(lift_kind_in_con_recursively(kind_bound, *body)),
        ),

        Constructor::TRecord(record_con) => Constructor::TRecord(Box::new(
            lift_kind_in_con_recursively(kind_bound, *record_con),
        )),

        Constructor::TDisjoint(left, right, body) => Constructor::TDisjoint(
            Box::new(lift_kind_in_con_recursively(kind_bound, *left)),
            Box::new(lift_kind_in_con_recursively(kind_bound, *right)),
            Box::new(lift_kind_in_con_recursively(kind_bound, *body)),
        ),

        Constructor::App(function_con, argument_con) => Constructor::App(
            Box::new(lift_kind_in_con_recursively(kind_bound, *function_con)),
            Box::new(lift_kind_in_con_recursively(kind_bound, *argument_con)),
        ),

        // Abs binds a CONSTRUCTOR variable — kind_bound unchanged.
        Constructor::Abs(name, kind_annotation, body) => Constructor::Abs(
            name,
            Box::new(lift_kind_in_kind_recursively(kind_bound, *kind_annotation)),
            Box::new(lift_kind_in_con_recursively(kind_bound, *body)),
        ),

        // KAbs binds a KIND variable — kind_bound increments.
        Constructor::KAbs(name, body) => Constructor::KAbs(
            name,
            Box::new(lift_kind_in_con_recursively(kind_bound + 1, *body)),
        ),

        Constructor::KApp(function_con, kind_arg) => Constructor::KApp(
            Box::new(lift_kind_in_con_recursively(kind_bound, *function_con)),
            Box::new(lift_kind_in_kind_recursively(kind_bound, *kind_arg)),
        ),

        // TKFun binds a KIND variable — kind_bound increments.
        Constructor::TKFun(name, body) => Constructor::TKFun(
            name,
            Box::new(lift_kind_in_con_recursively(kind_bound + 1, *body)),
        ),

        Constructor::Record(kind_annotation, fields) => Constructor::Record(
            Box::new(lift_kind_in_kind_recursively(kind_bound, *kind_annotation)),
            fields
                .into_iter()
                .map(|(name_con, value_con)| {
                    (
                        lift_kind_in_con_recursively(kind_bound, name_con),
                        lift_kind_in_con_recursively(kind_bound, value_con),
                    )
                })
                .collect(),
        ),

        Constructor::Concat(left, right) => Constructor::Concat(
            Box::new(lift_kind_in_con_recursively(kind_bound, *left)),
            Box::new(lift_kind_in_con_recursively(kind_bound, *right)),
        ),

        Constructor::Map(domain_kind, codomain_kind) => Constructor::Map(
            Box::new(lift_kind_in_kind_recursively(kind_bound, *domain_kind)),
            Box::new(lift_kind_in_kind_recursively(kind_bound, *codomain_kind)),
        ),

        Constructor::Tuple(elements) => Constructor::Tuple(
            elements
                .into_iter()
                .map(|element| lift_kind_in_con_recursively(kind_bound, element))
                .collect(),
        ),

        Constructor::Proj(tuple_con, index) => Constructor::Proj(
            Box::new(lift_kind_in_con_recursively(kind_bound, *tuple_con)),
            index,
        ),

        Constructor::Unif(nesting_level, span_ref, kind_annotation, name, unif_ref) => {
            Constructor::Unif(nesting_level, span_ref, kind_annotation, name, unif_ref)
        }
    };
    Located::new(node, span)
}

/// Lift all free `Constructor::Rel(n)` for `n >= con_bound` by 1 inside an expression.
///
/// Used by [`Env::push_c_rel`] to update stored class open-rule expressions.
/// The bound increments whenever we enter a `CAbs` body.
fn lift_con_in_exp_bound(con_bound: usize, expression: LocatedExpression) -> LocatedExpression {
    let span = expression.span.clone();
    let node = match expression.node {
        Expression::Prim(_)
        | Expression::Rel(_)
        | Expression::Named(_)
        | Expression::ModProj(_, _, _)
        | Expression::Error
        | Expression::Unif(_)
        | Expression::Hole(_) => expression.node,

        Expression::App(function_exp, argument_exp) => Expression::App(
            Box::new(lift_con_in_exp_bound(con_bound, *function_exp)),
            Box::new(lift_con_in_exp_bound(con_bound, *argument_exp)),
        ),

        // Abs binds an EXPRESSION variable — con_bound unchanged.
        Expression::Abs(param_name, param_type, result_type, body) => Expression::Abs(
            param_name,
            lift_con_in_con_at(con_bound, param_type),
            lift_con_in_con_at(con_bound, result_type),
            Box::new(lift_con_in_exp_bound(con_bound, *body)),
        ),

        Expression::CApp(function_exp, constructor_arg) => Expression::CApp(
            Box::new(lift_con_in_exp_bound(con_bound, *function_exp)),
            lift_con_in_con_at(con_bound, constructor_arg),
        ),

        // CAbs binds a CONSTRUCTOR variable — con_bound increments for body.
        Expression::CAbs(explicitness, name, kind_annotation, body) => Expression::CAbs(
            explicitness,
            name,
            kind_annotation,
            Box::new(lift_con_in_exp_bound(con_bound + 1, *body)),
        ),

        Expression::KAbs(name, body) => {
            Expression::KAbs(name, Box::new(lift_con_in_exp_bound(con_bound, *body)))
        }

        Expression::KApp(function_exp, kind_arg) => Expression::KApp(
            Box::new(lift_con_in_exp_bound(con_bound, *function_exp)),
            kind_arg,
        ),

        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(field_name_con, value_exp, field_type_con)| {
                    (
                        lift_con_in_con_at(con_bound, field_name_con),
                        lift_con_in_exp_bound(con_bound, value_exp),
                        lift_con_in_con_at(con_bound, field_type_con),
                    )
                })
                .collect(),
        ),

        Expression::Field(record_exp, field_con, meta) => Expression::Field(
            Box::new(lift_con_in_exp_bound(con_bound, *record_exp)),
            lift_con_in_con_at(con_bound, field_con),
            FieldMeta {
                field: lift_con_in_con_at(con_bound, meta.field),
                rest: lift_con_in_con_at(con_bound, meta.rest),
            },
        ),

        Expression::Concat(left_exp, left_con, right_exp, right_con) => Expression::Concat(
            Box::new(lift_con_in_exp_bound(con_bound, *left_exp)),
            lift_con_in_con_at(con_bound, left_con),
            Box::new(lift_con_in_exp_bound(con_bound, *right_exp)),
            lift_con_in_con_at(con_bound, right_con),
        ),

        Expression::Cut(record_exp, field_con, meta) => Expression::Cut(
            Box::new(lift_con_in_exp_bound(con_bound, *record_exp)),
            lift_con_in_con_at(con_bound, field_con),
            FieldMeta {
                field: lift_con_in_con_at(con_bound, meta.field),
                rest: lift_con_in_con_at(con_bound, meta.rest),
            },
        ),

        Expression::CutMulti(record_exp, fields_con, meta) => Expression::CutMulti(
            Box::new(lift_con_in_exp_bound(con_bound, *record_exp)),
            lift_con_in_con_at(con_bound, fields_con),
            RestMeta {
                rest: lift_con_in_con_at(con_bound, meta.rest),
            },
        ),

        Expression::Case(scrutinee, branches, case_meta) => Expression::Case(
            Box::new(lift_con_in_exp_bound(con_bound, *scrutinee)),
            branches
                .into_iter()
                .map(|(pattern, branch_exp)| {
                    (
                        lift_con_in_pat_bound(con_bound, pattern),
                        lift_con_in_exp_bound(con_bound, branch_exp),
                    )
                })
                .collect(),
            CaseMeta {
                disc: lift_con_in_con_at(con_bound, case_meta.disc),
                result: lift_con_in_con_at(con_bound, case_meta.result),
            },
        ),

        Expression::Let(e_decls, body, result_type) => Expression::Let(
            e_decls
                .into_iter()
                .map(|decl| lift_con_in_edecl_bound(con_bound, decl))
                .collect(),
            Box::new(lift_con_in_exp_bound(con_bound, *body)),
            lift_con_in_con_at(con_bound, result_type),
        ),
    };
    Located::new(node, span)
}

fn lift_con_in_con_at(con_bound: usize, constructor: LocatedConstructor) -> LocatedConstructor {
    lift_con_in_con_recursively(con_bound, constructor)
}

fn lift_con_in_con_recursively(
    con_bound: usize,
    constructor: LocatedConstructor,
) -> LocatedConstructor {
    let span = constructor.span.clone();
    let node = match constructor.node {
        Constructor::Rel(index) => {
            if index >= con_bound {
                Constructor::Rel(index + 1)
            } else {
                Constructor::Rel(index)
            }
        }
        Constructor::Unif(nesting_level, span_ref, kind_annotation, name, unif_ref) => {
            Constructor::Unif(nesting_level + 1, span_ref, kind_annotation, name, unif_ref)
        }
        Constructor::TFun(domain, codomain) => Constructor::TFun(
            Box::new(lift_con_in_con_recursively(con_bound, *domain)),
            Box::new(lift_con_in_con_recursively(con_bound, *codomain)),
        ),
        // TCFun introduces a CON binder — con_bound increments for body.
        Constructor::TCFun(explicitness, name, kind_annotation, body) => Constructor::TCFun(
            explicitness,
            name,
            kind_annotation,
            Box::new(lift_con_in_con_recursively(con_bound + 1, *body)),
        ),
        Constructor::TRecord(record_con) => Constructor::TRecord(Box::new(
            lift_con_in_con_recursively(con_bound, *record_con),
        )),
        Constructor::TDisjoint(left, right, body) => Constructor::TDisjoint(
            Box::new(lift_con_in_con_recursively(con_bound, *left)),
            Box::new(lift_con_in_con_recursively(con_bound, *right)),
            Box::new(lift_con_in_con_recursively(con_bound, *body)),
        ),
        Constructor::App(function_con, argument_con) => Constructor::App(
            Box::new(lift_con_in_con_recursively(con_bound, *function_con)),
            Box::new(lift_con_in_con_recursively(con_bound, *argument_con)),
        ),
        // Abs introduces a CON binder — con_bound increments for body.
        Constructor::Abs(name, kind_annotation, body) => Constructor::Abs(
            name,
            kind_annotation,
            Box::new(lift_con_in_con_recursively(con_bound + 1, *body)),
        ),
        Constructor::KAbs(name, body) => Constructor::KAbs(
            name,
            Box::new(lift_con_in_con_recursively(con_bound, *body)),
        ),
        Constructor::KApp(function_con, kind_arg) => Constructor::KApp(
            Box::new(lift_con_in_con_recursively(con_bound, *function_con)),
            kind_arg,
        ),
        Constructor::TKFun(name, body) => Constructor::TKFun(
            name,
            Box::new(lift_con_in_con_recursively(con_bound, *body)),
        ),
        Constructor::Record(kind_annotation, fields) => Constructor::Record(
            kind_annotation,
            fields
                .into_iter()
                .map(|(name_con, value_con)| {
                    (
                        lift_con_in_con_recursively(con_bound, name_con),
                        lift_con_in_con_recursively(con_bound, value_con),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(left, right) => Constructor::Concat(
            Box::new(lift_con_in_con_recursively(con_bound, *left)),
            Box::new(lift_con_in_con_recursively(con_bound, *right)),
        ),
        Constructor::Tuple(elements) => Constructor::Tuple(
            elements
                .into_iter()
                .map(|element| lift_con_in_con_recursively(con_bound, element))
                .collect(),
        ),
        Constructor::Proj(tuple_con, index) => Constructor::Proj(
            Box::new(lift_con_in_con_recursively(con_bound, *tuple_con)),
            index,
        ),
        other => other,
    };
    Located::new(node, span)
}

fn lift_con_in_pat_bound(con_bound: usize, pattern: LocatedPattern) -> LocatedPattern {
    let span = pattern.span.clone();
    let node = match pattern.node {
        Pattern::Var(name, type_con) => Pattern::Var(name, lift_con_in_con_at(con_bound, type_con)),
        Pattern::Prim(prim) => Pattern::Prim(prim),
        Pattern::Constructor(dk, pat_con, type_args, inner_pattern) => Pattern::Constructor(
            dk,
            pat_con,
            type_args
                .into_iter()
                .map(|arg| lift_con_in_con_at(con_bound, arg))
                .collect(),
            inner_pattern.map(|inner| Box::new(lift_con_in_pat_bound(con_bound, *inner))),
        ),
        Pattern::Record(fields) => Pattern::Record(
            fields
                .into_iter()
                .map(|(name, sub_pat, type_con)| {
                    (
                        name,
                        lift_con_in_pat_bound(con_bound, sub_pat),
                        lift_con_in_con_at(con_bound, type_con),
                    )
                })
                .collect(),
        ),
    };
    Located::new(node, span)
}

fn lift_con_in_edecl_bound(
    con_bound: usize,
    e_decl: LocatedElaboratedDeclaration,
) -> LocatedElaboratedDeclaration {
    let span = e_decl.span.clone();
    let node = match e_decl.node {
        ElaboratedDeclaration::Val(pattern, type_con, body_exp) => ElaboratedDeclaration::Val(
            lift_con_in_pat_bound(con_bound, pattern),
            lift_con_in_con_at(con_bound, type_con),
            lift_con_in_exp_bound(con_bound, body_exp),
        ),
        ElaboratedDeclaration::ValRec(bindings) => ElaboratedDeclaration::ValRec(
            bindings
                .into_iter()
                .map(|(name, type_con, body_exp)| {
                    (
                        name,
                        lift_con_in_con_at(con_bound, type_con),
                        lift_con_in_exp_bound(con_bound, body_exp),
                    )
                })
                .collect(),
        ),
    };
    Located::new(node, span)
}

/// Lift all free `Expression::Rel(n)` for `n >= exp_bound` by 1 inside an expression.
///
/// Used by [`Env::push_e_rel`] to keep class open-rule expressions valid when
/// a new expression variable is pushed onto the stack.
/// The bound increments whenever we enter a binding form (`Abs`, `Case`
/// branches, or `Let`).
fn lift_exp_in_exp_bound(exp_bound: usize, expression: LocatedExpression) -> LocatedExpression {
    let span = expression.span.clone();
    let node = match expression.node {
        Expression::Rel(index) => {
            if index >= exp_bound {
                Expression::Rel(index + 1)
            } else {
                Expression::Rel(index)
            }
        }

        Expression::Prim(_)
        | Expression::Named(_)
        | Expression::ModProj(_, _, _)
        | Expression::Error
        | Expression::Unif(_)
        | Expression::Hole(_) => expression.node,

        Expression::App(function_exp, argument_exp) => Expression::App(
            Box::new(lift_exp_in_exp_bound(exp_bound, *function_exp)),
            Box::new(lift_exp_in_exp_bound(exp_bound, *argument_exp)),
        ),

        // Abs introduces an EXPRESSION binder — exp_bound increments for body.
        Expression::Abs(param_name, param_type, result_type, body) => Expression::Abs(
            param_name,
            param_type,
            result_type,
            Box::new(lift_exp_in_exp_bound(exp_bound + 1, *body)),
        ),

        Expression::CApp(function_exp, constructor_arg) => Expression::CApp(
            Box::new(lift_exp_in_exp_bound(exp_bound, *function_exp)),
            constructor_arg,
        ),

        Expression::CAbs(explicitness, name, kind_annotation, body) => Expression::CAbs(
            explicitness,
            name,
            kind_annotation,
            // CAbs binds a constructor — exp_bound unchanged.
            Box::new(lift_exp_in_exp_bound(exp_bound, *body)),
        ),

        Expression::KAbs(name, body) => Expression::KAbs(
            name,
            // KAbs binds a kind — exp_bound unchanged.
            Box::new(lift_exp_in_exp_bound(exp_bound, *body)),
        ),

        Expression::KApp(function_exp, kind_arg) => Expression::KApp(
            Box::new(lift_exp_in_exp_bound(exp_bound, *function_exp)),
            kind_arg,
        ),

        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(field_name_con, value_exp, field_type_con)| {
                    (
                        field_name_con,
                        lift_exp_in_exp_bound(exp_bound, value_exp),
                        field_type_con,
                    )
                })
                .collect(),
        ),

        Expression::Field(record_exp, field_con, meta) => Expression::Field(
            Box::new(lift_exp_in_exp_bound(exp_bound, *record_exp)),
            field_con,
            meta,
        ),

        Expression::Concat(left_exp, left_con, right_exp, right_con) => Expression::Concat(
            Box::new(lift_exp_in_exp_bound(exp_bound, *left_exp)),
            left_con,
            Box::new(lift_exp_in_exp_bound(exp_bound, *right_exp)),
            right_con,
        ),

        Expression::Cut(record_exp, field_con, meta) => Expression::Cut(
            Box::new(lift_exp_in_exp_bound(exp_bound, *record_exp)),
            field_con,
            meta,
        ),

        Expression::CutMulti(record_exp, fields_con, meta) => Expression::CutMulti(
            Box::new(lift_exp_in_exp_bound(exp_bound, *record_exp)),
            fields_con,
            meta,
        ),

        // Each Case branch binds variables from the pattern.
        Expression::Case(scrutinee, branches, case_meta) => Expression::Case(
            Box::new(lift_exp_in_exp_bound(exp_bound, *scrutinee)),
            branches
                .into_iter()
                .map(|(pattern, branch_exp)| {
                    let bindings_count = pattern_binds_count(&pattern);
                    (
                        pattern,
                        lift_exp_in_exp_bound(exp_bound + bindings_count, branch_exp),
                    )
                })
                .collect(),
            case_meta,
        ),

        Expression::Let(e_decls, body, result_type) => {
            let bindings_count: usize = e_decls
                .iter()
                .map(|decl| match &decl.node {
                    ElaboratedDeclaration::Val(pattern, _, _) => pattern_binds_count(pattern),
                    ElaboratedDeclaration::ValRec(bindings) => bindings.len(),
                })
                .sum();
            Expression::Let(
                e_decls,
                Box::new(lift_exp_in_exp_bound(exp_bound + bindings_count, *body)),
                result_type,
            )
        }
    };
    Located::new(node, span)
}

// ---------------------------------------------------------------------------
// Env
// ---------------------------------------------------------------------------

/// The elaboration environment: tracks every in-scope binding during type inference.
///
/// Each `push_*` method returns a **new** `Env` with the added binding, leaving
/// the original unchanged (functional-update semantics matching the SML original).
///
/// Mirrors the `env` record type in `elab_env.sml`.
#[derive(Debug, Clone)]
pub struct Env {
    // -- Kind variables -------------------------------------------------------
    /// Maps kind variable names to their current de Bruijn index.
    /// Updated on every `push_k_rel` (all existing indices are bumped by 1).
    rename_k: HashMap<String, usize>,
    /// The stack of relative kind-variable names, innermost first.
    /// `rel_k[0]` corresponds to de Bruijn index 0.
    rel_k: Vec<String>,

    // -- Constructor variables ------------------------------------------------
    /// Maps constructor names to either a relative or named entry.
    rename_c: HashMap<String, CVarEntry>,
    /// Relative constructor bindings: `(name, kind)`, innermost first.
    rel_c: Vec<(String, LocatedKind)>,
    /// Named constructor definitions: `id → (name, kind, optional_definition)`.
    named_c: HashMap<usize, (String, LocatedKind, Option<LocatedConstructor>)>,

    // -- Datatypes & constructors ---------------------------------------------
    /// Declared datatypes: `datatype_id → DatatypeInfo`.
    datatypes: HashMap<usize, DatatypeInfo>,
    /// Constructor-name lookup table: `constructor_name → ConstructorInfo`.
    constructors_by_name: HashMap<String, ConstructorInfo>,

    // -- Typeclass instances --------------------------------------------------
    /// Open and closed resolution rules per class.
    classes: HashMap<ClassName, ClassRules>,

    // -- Expression variables -------------------------------------------------
    /// Maps expression names to either a relative or named entry.
    rename_e: HashMap<String, EVarEntry>,
    /// Relative expression bindings: `(name, type_constructor)`, innermost first.
    rel_e: Vec<(String, LocatedConstructor)>,
    /// Named expression definitions: `id → (name, type_constructor)`.
    named_e: HashMap<usize, (String, LocatedConstructor)>,

    // -- Signatures -----------------------------------------------------------
    /// Named signature lookup by name: `name → (id, signature)`.
    rename_sgn: HashMap<String, (usize, LocatedSignature)>,
    /// Named signatures: `id → (name, signature)`.
    named_sgn: HashMap<usize, (String, LocatedSignature)>,

    // -- Structures -----------------------------------------------------------
    /// Named structure lookup by name: `name → (id, signature)`.
    rename_str: HashMap<String, (usize, LocatedSignature)>,
    /// Named structures: `id → (name, signature)`.
    named_str: HashMap<usize, (String, LocatedSignature)>,
}

impl Env {
    // -----------------------------------------------------------------------
    // Construction
    // -----------------------------------------------------------------------

    /// Create an empty elaboration environment with no bindings.
    ///
    /// Mirrors `val empty = { renameK = SM.empty, ... }` in `elab_env.sml`.
    pub fn empty() -> Self {
        Env {
            rename_k: HashMap::new(),
            rel_k: vec![],
            rename_c: HashMap::new(),
            rel_c: vec![],
            named_c: HashMap::new(),
            datatypes: HashMap::new(),
            constructors_by_name: HashMap::new(),
            classes: HashMap::new(),
            rename_e: HashMap::new(),
            rel_e: vec![],
            named_e: HashMap::new(),
            rename_sgn: HashMap::new(),
            named_sgn: HashMap::new(),
            rename_str: HashMap::new(),
            named_str: HashMap::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Kind variable operations
    // -----------------------------------------------------------------------

    /// Push a relative kind variable onto the kind stack.
    ///
    /// All existing de Bruijn indices in `rename_k` are incremented by 1, and
    /// all stored constructor kinds / expression types have their free kind
    /// indices lifted accordingly.
    ///
    /// Mirrors `fun pushKRel (env : env) x = ...` in `elab_env.sml`.
    pub fn push_k_rel(self, name: String) -> Self {
        // Bump all existing kind rename indices by 1.
        let mut new_rename_k: HashMap<String, usize> = self
            .rename_k
            .into_iter()
            .map(|(existing_name, index)| (existing_name, index + 1))
            .collect();
        new_rename_k.insert(name.clone(), 0);

        let mut new_rel_k = vec![name];
        new_rel_k.extend(self.rel_k);

        // Lift kind indices in all stored constructor kinds (rename_c, rel_c).
        let new_rename_c: HashMap<String, CVarEntry> = self
            .rename_c
            .into_iter()
            .map(|(con_name, entry)| {
                let updated_entry = match entry {
                    CVarEntry::Rel(index, kind) => {
                        CVarEntry::Rel(index, type_operations::lift_kind_in_kind(kind))
                    }
                    CVarEntry::Named(id, kind) => CVarEntry::Named(id, kind),
                };
                (con_name, updated_entry)
            })
            .collect();

        let new_rel_c: Vec<(String, LocatedKind)> = self
            .rel_c
            .into_iter()
            .map(|(con_name, kind)| (con_name, type_operations::lift_kind_in_kind(kind)))
            .collect();

        // Lift kind indices in all stored expression types (rename_e, rel_e).
        let new_rename_e: HashMap<String, EVarEntry> = self
            .rename_e
            .into_iter()
            .map(|(exp_name, entry)| {
                let updated_entry = match entry {
                    EVarEntry::Rel(index, type_con) => {
                        EVarEntry::Rel(index, type_operations::lift_kind_in_con(type_con))
                    }
                    EVarEntry::Named(id, type_con) => EVarEntry::Named(id, type_con),
                };
                (exp_name, updated_entry)
            })
            .collect();

        let new_rel_e: Vec<(String, LocatedConstructor)> = self
            .rel_e
            .into_iter()
            .map(|(exp_name, type_con)| (exp_name, type_operations::lift_kind_in_con(type_con)))
            .collect();

        // Lift kind indices in class open rules.
        let new_classes: HashMap<ClassName, ClassRules> = self
            .classes
            .into_iter()
            .map(|(class_name, rules)| {
                let updated_open_rules = rules
                    .open_rules
                    .into_iter()
                    .map(|(num_quantifiers, hypotheses, conclusion, witness)| {
                        (
                            num_quantifiers,
                            hypotheses
                                .into_iter()
                                .map(type_operations::lift_kind_in_con)
                                .collect(),
                            type_operations::lift_kind_in_con(conclusion),
                            lift_kind_in_exp_bound(0, witness),
                        )
                    })
                    .collect();
                (
                    class_name,
                    ClassRules {
                        open_rules: updated_open_rules,
                        closed_rules: rules.closed_rules,
                    },
                )
            })
            .collect();

        Env {
            rename_k: new_rename_k,
            rel_k: new_rel_k,
            rename_c: new_rename_c,
            rel_c: new_rel_c,
            rename_e: new_rename_e,
            rel_e: new_rel_e,
            classes: new_classes,
            ..self
        }
    }

    /// Look up the name of kind relative variable at de Bruijn index `index`.
    ///
    /// Returns `Err(EnvError::UnboundKRel)` if `index` is out of range.
    ///
    /// Mirrors `fun lookupKRel (env : env) n = ...` in `elab_env.sml`.
    pub fn lookup_k_rel(&self, index: usize) -> Result<&str, EnvError> {
        self.rel_k
            .get(index)
            .map(|name| name.as_str())
            .ok_or(EnvError::UnboundKRel(index))
    }

    /// Look up a kind variable by name, returning its de Bruijn index if found.
    ///
    /// Mirrors `fun lookupK (env : env) x = SM.find (#renameK env, x)`.
    pub fn lookup_k(&self, name: &str) -> Option<usize> {
        self.rename_k.get(name).copied()
    }

    // -----------------------------------------------------------------------
    // Constructor variable operations
    // -----------------------------------------------------------------------

    /// Push a relative constructor variable onto the constructor stack.
    ///
    /// All existing relative constructor indices in `rename_c` are bumped by 1.
    /// All stored expression types have their free constructor indices lifted.
    ///
    /// Mirrors `fun pushCRel (env : env) x k = ...` in `elab_env.sml`.
    pub fn push_c_rel(self, name: String, kind: LocatedKind) -> Self {
        // Bump all existing relative constructor rename indices by 1.
        let mut new_rename_c: HashMap<String, CVarEntry> = self
            .rename_c
            .into_iter()
            .map(|(con_name, entry)| {
                let updated_entry = match entry {
                    CVarEntry::Rel(index, stored_kind) => CVarEntry::Rel(index + 1, stored_kind),
                    named_entry => named_entry,
                };
                (con_name, updated_entry)
            })
            .collect();
        new_rename_c.insert(name.clone(), CVarEntry::Rel(0, kind.clone()));

        let mut new_rel_c = vec![(name, kind)];
        new_rel_c.extend(self.rel_c);

        // Lift con indices in all stored expression types (using lift = liftConInCon 0).
        let new_rename_e: HashMap<String, EVarEntry> = self
            .rename_e
            .into_iter()
            .map(|(exp_name, entry)| {
                let updated_entry = match entry {
                    EVarEntry::Rel(index, type_con) => {
                        EVarEntry::Rel(index, type_operations::lift_con_in_con(type_con))
                    }
                    named_entry => named_entry,
                };
                (exp_name, updated_entry)
            })
            .collect();

        let new_rel_e: Vec<(String, LocatedConstructor)> = self
            .rel_e
            .into_iter()
            .map(|(exp_name, type_con)| (exp_name, type_operations::lift_con_in_con(type_con)))
            .collect();

        // Lift con indices in class open rules.
        let new_classes: HashMap<ClassName, ClassRules> = self
            .classes
            .into_iter()
            .map(|(class_name, rules)| {
                let updated_open_rules = rules
                    .open_rules
                    .into_iter()
                    .map(|(num_quantifiers, hypotheses, conclusion, witness)| {
                        (
                            num_quantifiers,
                            hypotheses
                                .into_iter()
                                .map(type_operations::lift_con_in_con)
                                .collect(),
                            type_operations::lift_con_in_con(conclusion),
                            lift_con_in_exp_bound(0, witness),
                        )
                    })
                    .collect();
                (
                    class_name,
                    ClassRules {
                        open_rules: updated_open_rules,
                        closed_rules: rules.closed_rules,
                    },
                )
            })
            .collect();

        Env {
            rename_c: new_rename_c,
            rel_c: new_rel_c,
            rename_e: new_rename_e,
            rel_e: new_rel_e,
            classes: new_classes,
            ..self
        }
    }

    /// Look up the `(name, kind)` of the relative constructor at de Bruijn index `index`.
    ///
    /// Mirrors `fun lookupCRel (env : env) n = ...` in `elab_env.sml`.
    pub fn lookup_c_rel(&self, index: usize) -> Result<&(String, LocatedKind), EnvError> {
        self.rel_c.get(index).ok_or(EnvError::UnboundCRel(index))
    }

    /// Push a named constructor with a pre-allocated id.
    ///
    /// Mirrors `fun pushCNamedAs (env : env) x n k co = ...` in `elab_env.sml`.
    pub fn push_c_named_as(
        self,
        name: String,
        id: usize,
        kind: LocatedKind,
        definition: Option<LocatedConstructor>,
    ) -> Self {
        let mut new_rename_c = self.rename_c;
        new_rename_c.insert(name.clone(), CVarEntry::Named(id, kind.clone()));

        let mut new_named_c = self.named_c;
        new_named_c.insert(id, (name, kind, definition));

        Env {
            rename_c: new_rename_c,
            named_c: new_named_c,
            ..self
        }
    }

    /// Push a named constructor, allocating a fresh id automatically.
    ///
    /// Returns `(new_env, fresh_id)`.
    ///
    /// Mirrors `fun pushCNamed env x k co = ...` in `elab_env.sml`.
    pub fn push_c_named(
        self,
        name: String,
        kind: LocatedKind,
        definition: Option<LocatedConstructor>,
    ) -> (Self, usize) {
        let fresh_id = new_named_id();
        let new_env = self.push_c_named_as(name, fresh_id, kind, definition);
        (new_env, fresh_id)
    }

    /// Look up a named constructor by its globally-unique id.
    ///
    /// Returns `Err(EnvError::UnboundCNamed)` if not found.
    ///
    /// Mirrors `fun lookupCNamed (env : env) n = ...` in `elab_env.sml`.
    pub fn lookup_c_named(
        &self,
        id: usize,
    ) -> Result<&(String, LocatedKind, Option<LocatedConstructor>), EnvError> {
        self.named_c.get(&id).ok_or(EnvError::UnboundCNamed(id))
    }

    /// Look up a constructor variable by name.
    ///
    /// Returns the most recent binding (relative beats named).
    ///
    /// Mirrors `fun lookupC (env : env) x = ...` in `elab_env.sml`.
    pub fn lookup_c(&self, name: &str) -> VarLookup<LocatedKind> {
        match self.rename_c.get(name) {
            None => VarLookup::NotBound,
            Some(CVarEntry::Rel(index, kind)) => VarLookup::Rel(*index, kind.clone()),
            Some(CVarEntry::Named(id, kind)) => VarLookup::Named(*id, kind.clone()),
        }
    }

    // -----------------------------------------------------------------------
    // Datatype operations
    // -----------------------------------------------------------------------

    /// Register a datatype declaration with its constructors.
    ///
    /// Mirrors `fun pushDatatype (env : env) n xs xncs = ...` in `elab_env.sml`.
    pub fn push_datatype(
        self,
        datatype_id: usize,
        type_params: Vec<String>,
        constructors: Vec<(String, usize, Option<LocatedConstructor>)>,
    ) -> Self {
        let datatype_kind = super::utilities::classify_datatype(&constructors);

        let constructors_by_id: HashMap<usize, (String, Option<LocatedConstructor>)> = constructors
            .iter()
            .map(|(con_name, con_id, arg_type)| (*con_id, (con_name.clone(), arg_type.clone())))
            .collect();

        let mut new_datatypes = self.datatypes;
        new_datatypes.insert(
            datatype_id,
            DatatypeInfo {
                type_params: type_params.clone(),
                constructors_by_id,
            },
        );

        let mut new_constructors_by_name = self.constructors_by_name;
        for (con_name, con_id, arg_type) in constructors {
            new_constructors_by_name.insert(
                con_name,
                ConstructorInfo {
                    datatype_kind,
                    constructor_id: con_id,
                    type_params: type_params.clone(),
                    arg_type,
                    datatype_id,
                },
            );
        }

        Env {
            datatypes: new_datatypes,
            constructors_by_name: new_constructors_by_name,
            ..self
        }
    }

    /// Look up a datatype by its id.
    ///
    /// Mirrors `fun lookupDatatype (env : env) n = ...` in `elab_env.sml`.
    pub fn lookup_datatype(&self, datatype_id: usize) -> Result<&DatatypeInfo, EnvError> {
        self.datatypes
            .get(&datatype_id)
            .ok_or(EnvError::UnboundCNamed(datatype_id))
    }

    /// Look up a datatype constructor by name.
    ///
    /// Mirrors `fun lookupConstructor (env : env) s = SM.find (#constructors env, s)`.
    pub fn lookup_constructor(&self, constructor_name: &str) -> Option<&ConstructorInfo> {
        self.constructors_by_name.get(constructor_name)
    }

    // -----------------------------------------------------------------------
    // Class operations
    // -----------------------------------------------------------------------

    /// Register a new empty typeclass.
    ///
    /// Mirrors `fun pushClass (env : env) n = ...` in `elab_env.sml`.
    pub fn push_class(self, class_id: usize) -> Self {
        let mut new_classes = self.classes;
        new_classes.insert(ClassName::Named(class_id), ClassRules::empty());
        Env {
            classes: new_classes,
            ..self
        }
    }

    /// Test whether a constructor head resolves to a known class.
    ///
    /// Mirrors `fun isClass (env : env) c = ...` in `elab_env.sml`.
    /// Currently only handles `Named` and `ModProj` heads.
    pub fn is_class(&self, constructor: &LocatedConstructor) -> bool {
        if let Some(class_name) = class_head_of(constructor) {
            self.classes.contains_key(&class_name)
        } else {
            false
        }
    }

    // -----------------------------------------------------------------------
    // Expression variable operations
    // -----------------------------------------------------------------------

    /// Push a relative expression variable onto the expression stack.
    ///
    /// Bumps existing relative rename indices by 1, lifts class open-rule
    /// expressions by 1, and adds the new type as a class rule if applicable.
    ///
    /// Mirrors `fun pushERel (env : env) x t = ...` in `elab_env.sml`.
    pub fn push_e_rel(self, name: String, expression_type: LocatedConstructor) -> Self {
        // Bump all existing relative expression rename indices by 1.
        let mut new_rename_e: HashMap<String, EVarEntry> = self
            .rename_e
            .into_iter()
            .map(|(exp_name, entry)| {
                let updated_entry = match entry {
                    EVarEntry::Rel(index, type_con) => EVarEntry::Rel(index + 1, type_con),
                    named_entry => named_entry,
                };
                (exp_name, updated_entry)
            })
            .collect();
        new_rename_e.insert(name.clone(), EVarEntry::Rel(0, expression_type.clone()));

        let mut new_rel_e = vec![(name, expression_type.clone())];
        new_rel_e.extend(self.rel_e);

        // Lift all class open-rule witness expressions by 1 (they are now
        // one expression binder deeper).
        let new_classes: HashMap<ClassName, ClassRules> = self
            .classes
            .into_iter()
            .map(|(class_name, rules)| {
                let updated_open_rules = rules
                    .open_rules
                    .into_iter()
                    .map(|(num_quantifiers, hypotheses, conclusion, witness)| {
                        (
                            num_quantifiers,
                            hypotheses,
                            conclusion,
                            lift_exp_in_exp_bound(0, witness),
                        )
                    })
                    .collect();
                (
                    class_name,
                    ClassRules {
                        open_rules: updated_open_rules,
                        closed_rules: rules.closed_rules,
                    },
                )
            })
            .collect();

        // If `expression_type` is a class instance type, add it as an open rule
        // (witness = ERel 0) for the relevant class.
        let loc = expression_type.span.clone();
        let mut new_classes = new_classes;
        if let Some((cn, nvs, hyps, conclusion)) = rule_in(&expression_type) {
            if let Some(class) = new_classes.get_mut(&cn) {
                let witness = Located::new(Expression::Rel(0), loc);
                class.open_rules.insert(0, (nvs, hyps, conclusion, witness));
            }
        }

        Env {
            rename_e: new_rename_e,
            rel_e: new_rel_e,
            classes: new_classes,
            ..self
        }
    }

    /// Look up the `(name, type)` of the relative expression at de Bruijn index `index`.
    ///
    /// Mirrors `fun lookupERel (env : env) n = ...` in `elab_env.sml`.
    pub fn lookup_e_rel(&self, index: usize) -> Result<&(String, LocatedConstructor), EnvError> {
        self.rel_e.get(index).ok_or(EnvError::UnboundERel(index))
    }

    /// Push a named expression with a pre-allocated id.
    ///
    /// Also adds a closed class rule if `expression_type` is a class instance type.
    ///
    /// Mirrors `fun pushENamedAs (env : env) x n t = ...` in `elab_env.sml`.
    pub fn push_e_named_as(
        self,
        name: String,
        id: usize,
        expression_type: LocatedConstructor,
    ) -> Self {
        let mut new_rename_e = self.rename_e;
        new_rename_e.insert(name.clone(), EVarEntry::Named(id, expression_type.clone()));

        let mut new_named_e = self.named_e;
        new_named_e.insert(id, (name, expression_type.clone()));

        // If `expression_type` is a class instance type, add it as a closed rule
        // (witness = ENamed id) for the relevant class.
        let loc = expression_type.span.clone();
        let mut new_classes = self.classes;
        if let Some((cn, nvs, hyps, conclusion)) = rule_in(&expression_type) {
            if let Some(class) = new_classes.get_mut(&cn) {
                let witness = Located::new(Expression::Named(id), loc);
                class.closed_rules.push((nvs, hyps, conclusion, witness));
            }
        }

        Env {
            rename_e: new_rename_e,
            named_e: new_named_e,
            classes: new_classes,
            ..self
        }
    }

    /// Push a named expression, allocating a fresh id automatically.
    ///
    /// Returns `(new_env, fresh_id)`.
    ///
    /// Mirrors `fun pushENamed env x t = ...` in `elab_env.sml`.
    pub fn push_e_named(self, name: String, expression_type: LocatedConstructor) -> (Self, usize) {
        let fresh_id = new_named_id();
        let new_env = self.push_e_named_as(name, fresh_id, expression_type);
        (new_env, fresh_id)
    }

    /// Look up a named expression by its globally-unique id.
    ///
    /// Mirrors `fun lookupENamed (env : env) n = ...` in `elab_env.sml`.
    pub fn lookup_e_named(&self, id: usize) -> Result<&(String, LocatedConstructor), EnvError> {
        self.named_e.get(&id).ok_or(EnvError::UnboundENamed(id))
    }

    /// Check whether a named expression id is registered (without returning its type).
    ///
    /// Mirrors `fun checkENamed (env : env) n = Option.isSome (IM.find (#namedE env, n))`.
    pub fn check_e_named(&self, id: usize) -> bool {
        self.named_e.contains_key(&id)
    }

    /// Look up an expression variable by name.
    ///
    /// Mirrors `fun lookupE (env : env) x = ...` in `elab_env.sml`.
    pub fn lookup_e(&self, name: &str) -> VarLookup<LocatedConstructor> {
        match self.rename_e.get(name) {
            None => VarLookup::NotBound,
            Some(EVarEntry::Rel(index, type_con)) => VarLookup::Rel(*index, type_con.clone()),
            Some(EVarEntry::Named(id, type_con)) => VarLookup::Named(*id, type_con.clone()),
        }
    }

    // -----------------------------------------------------------------------
    // Signature operations
    // -----------------------------------------------------------------------

    /// Push a named signature with a pre-allocated id.
    ///
    /// Mirrors `fun pushSgnNamedAs (env : env) x n sgis = ...` in `elab_env.sml`.
    pub fn push_sgn_named_as(self, name: String, id: usize, signature: LocatedSignature) -> Self {
        let mut new_rename_sgn = self.rename_sgn;
        new_rename_sgn.insert(name.clone(), (id, signature.clone()));

        let mut new_named_sgn = self.named_sgn;
        new_named_sgn.insert(id, (name, signature));

        Env {
            rename_sgn: new_rename_sgn,
            named_sgn: new_named_sgn,
            ..self
        }
    }

    /// Push a named signature, allocating a fresh id automatically.
    ///
    /// Returns `(new_env, fresh_id)`.
    ///
    /// Mirrors `fun pushSgnNamed env x sgis = ...` in `elab_env.sml`.
    pub fn push_sgn_named(self, name: String, signature: LocatedSignature) -> (Self, usize) {
        let fresh_id = new_named_id();
        let new_env = self.push_sgn_named_as(name, fresh_id, signature);
        (new_env, fresh_id)
    }

    /// Look up a named signature by its id.
    ///
    /// Mirrors `fun lookupSgnNamed (env : env) n = ...` in `elab_env.sml`.
    pub fn lookup_sgn_named(&self, id: usize) -> Result<&(String, LocatedSignature), EnvError> {
        self.named_sgn.get(&id).ok_or(EnvError::UnboundSgnNamed(id))
    }

    /// Look up a named signature by its source name.
    ///
    /// Mirrors `fun lookupSgn (env : env) x = SM.find (#renameSgn env, x)`.
    pub fn lookup_sgn(&self, name: &str) -> Option<&(usize, LocatedSignature)> {
        self.rename_sgn.get(name)
    }

    // -----------------------------------------------------------------------
    // Structure operations
    // -----------------------------------------------------------------------

    /// Push a named structure with a pre-allocated id (without class enrichment).
    ///
    /// Mirrors `pushStrNamedAs' false env x n sgn` in `elab_env.sml`.
    /// Class enrichment (scanning the signature for class instances) is
    /// deferred until `push_str_named_as` is called; this variant skips it.
    pub fn push_str_named_as_no_enrich(
        self,
        name: String,
        id: usize,
        signature: LocatedSignature,
    ) -> Self {
        let mut new_rename_str = self.rename_str;
        new_rename_str.insert(name.clone(), (id, signature.clone()));

        let mut new_named_str = self.named_str;
        new_named_str.insert(id, (name, signature));

        Env {
            rename_str: new_rename_str,
            named_str: new_named_str,
            ..self
        }
    }

    /// Push a named structure with class enrichment.
    ///
    /// Scans the structure's signature for class instance declarations and
    /// adds their closed rules to the class environment.
    ///
    /// Mirrors `fun pushStrNamedAs env x n sgn = pushStrNamedAs' true env x n sgn`.
    pub fn push_str_named_as(self, name: String, id: usize, signature: LocatedSignature) -> Self {
        let mut env_with_str = self.push_str_named_as_no_enrich(name, id, signature.clone());
        // Enrich classes: scan the signature for Val declarations that are
        // class instances, and add them as closed rules (witness = ModProj).
        enrich_classes(&mut env_with_str, id, &[], &signature);
        env_with_str
    }

    /// Push a named structure, allocating a fresh id automatically.
    ///
    /// Returns `(new_env, fresh_id)`.
    ///
    /// Mirrors `fun pushStrNamed env x sgn = ...` in `elab_env.sml`.
    pub fn push_str_named(self, name: String, signature: LocatedSignature) -> (Self, usize) {
        let fresh_id = new_named_id();
        let new_env = self.push_str_named_as(name, fresh_id, signature);
        (new_env, fresh_id)
    }

    /// Look up a named structure by its id.
    ///
    /// Mirrors `fun lookupStrNamed (env : env) n = ...` in `elab_env.sml`.
    pub fn lookup_str_named(&self, id: usize) -> Result<&(String, LocatedSignature), EnvError> {
        self.named_str.get(&id).ok_or(EnvError::UnboundStrNamed(id))
    }

    /// Look up a named structure by its source name.
    ///
    /// Mirrors `fun lookupStr (env : env) x = SM.find (#renameStr env, x)`.
    pub fn lookup_str(&self, name: &str) -> Option<&(usize, LocatedSignature)> {
        self.rename_str.get(name)
    }

    // -----------------------------------------------------------------------
    // Debug helpers
    // -----------------------------------------------------------------------

    /// Return a snapshot of all in-scope constructor names and their kinds.
    pub fn dump_constructors(&self) -> Vec<(String, LocatedKind)> {
        self.rename_c
            .iter()
            .map(|(name, entry)| {
                let kind = match entry {
                    CVarEntry::Rel(_, kind) | CVarEntry::Named(_, kind) => kind.clone(),
                };
                (name.clone(), kind)
            })
            .collect()
    }

    /// Return the number of relative constructor bindings currently in scope.
    pub fn rel_c_len(&self) -> usize {
        self.rel_c.len()
    }

    /// Return the number of relative expression bindings currently in scope.
    pub fn rel_e_len(&self) -> usize {
        self.rel_e.len()
    }

    /// Return the classes map (read-only) for typeclass resolution.
    pub fn classes(&self) -> &HashMap<ClassName, ClassRules> {
        &self.classes
    }

    /// Add a closed rule to the given class.
    pub fn add_class_rule(mut self, cn: ClassName, rule: ClassRule) -> Self {
        let entry = self.classes.entry(cn).or_insert_with(ClassRules::empty);
        entry.closed_rules.push(rule);
        self
    }

    /// Return a snapshot of all in-scope expression names and their types.
    pub fn dump_expressions(&self) -> Vec<(String, LocatedConstructor)> {
        self.rename_e
            .iter()
            .map(|(name, entry)| {
                let type_con = match entry {
                    EVarEntry::Rel(_, type_con) | EVarEntry::Named(_, type_con) => type_con.clone(),
                };
                (name.clone(), type_con)
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Class head extraction
// ---------------------------------------------------------------------------

/// Extract the class-name key from the head of a constructor, if any.
///
/// Strips `CApp` spines: `f a b` returns the head `f`.  If the head is
/// `Named(id)` or `ModProj(m, ms, x)`, returns the corresponding `ClassName`.
///
/// Mirrors `class_name_in` and `class_head_in` in `elab_env.sml`.
fn class_head_of(constructor: &LocatedConstructor) -> Option<ClassName> {
    match &constructor.node {
        Constructor::Named(id) => Some(ClassName::Named(*id)),
        Constructor::ModProj(module_id, path, name) => {
            Some(ClassName::Proj(*module_id, path.clone(), name.clone()))
        }
        Constructor::App(function_con, _) => class_head_of(function_con),
        Constructor::Abs(_, _, body) => class_head_of(body),
        Constructor::Unif(_, _, _, _, cell) => {
            let guard = crate::compiler_diagnostics::lock_for_compile(
                cell.as_ref(),
                "elaboration environment cell",
            );
            match &*guard {
                super::CUnif::Known(inner) => class_head_of(inner),
                super::CUnif::Unknown => None,
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Class instance rule extraction
// ---------------------------------------------------------------------------

/// Try to interpret a constructor `c` as a typeclass instance type, returning
/// `(class_head, num_quantifiers, hypotheses, conclusion)` if successful.
///
/// Mirrors `fun rule_in c = ...` in `elab_env.sml`.
fn rule_in(
    c: &LocatedConstructor,
) -> Option<(
    ClassName,
    usize,
    Vec<LocatedConstructor>,
    LocatedConstructor,
)> {
    // Peel TCFun quantifiers (counting them), chasing through solved CUnif.
    fn quantifiers(
        c: &LocatedConstructor,
        nvars: usize,
    ) -> Option<(
        ClassName,
        usize,
        Vec<LocatedConstructor>,
        LocatedConstructor,
    )> {
        match &c.node {
            Constructor::Unif(_, _, _, _, cell) => {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    cell.as_ref(),
                    "elaboration environment cell",
                );
                match &*guard {
                    super::CUnif::Known(inner) => {
                        let inner = inner.clone();
                        drop(guard);
                        quantifiers(&inner, nvars)
                    }
                    super::CUnif::Unknown => None,
                }
            }
            Constructor::TCFun(_, _, _, body) => quantifiers(body, nvars + 1),
            _ => clauses(c, nvars, vec![]),
        }
    }

    // Peel TFun hypotheses that themselves have class heads; then check the
    // remaining conclusion has a class head.
    fn clauses(
        c: &LocatedConstructor,
        nvars: usize,
        hyps: Vec<LocatedConstructor>,
    ) -> Option<(
        ClassName,
        usize,
        Vec<LocatedConstructor>,
        LocatedConstructor,
    )> {
        match &c.node {
            Constructor::TFun(hyp, body) => {
                if class_head_of(hyp).is_some() {
                    let mut new_hyps = hyps;
                    new_hyps.push(*hyp.clone());
                    clauses(body, nvars, new_hyps)
                } else {
                    None
                }
            }
            _ => class_head_of(c).map(|cn| (cn, nvars, hyps, c.clone())),
        }
    }

    quantifiers(c, 0)
}

// ---------------------------------------------------------------------------
// Signature head-normalisation (hnormSgn)
// ---------------------------------------------------------------------------

/// Head-normalize a signature: chase [`Signature::Var`], [`Signature::Proj`], and [`Signature::Where`].
///
/// Mirrors `hnormSgn` in `elab_env.sml`. Lookup failures leave the original spine (stuck projection).
///
/// # Arguments
///
/// * `elaboration_environment` — Elaboration environment for named signature/structure lookup.
/// * `signature` — Signature to normalize.
///
/// # Returns
///
/// Head-normal form or unchanged leaf when lookup cannot progress.
pub fn hnorm_sgn(elaboration_environment: &Env, signature: &LocatedSignature) -> LocatedSignature {
    match &signature.node {
        // Already in head-normal form.
        Signature::Const(_) | Signature::Fun(_, _, _, _) | Signature::Error => signature.clone(),

        // Chase a named signature variable (iteratively: long alias chains must not overflow the stack).
        Signature::Var(start_signature_id) => {
            let mut current_signature_id = *start_signature_id;
            let mut visited_signature_ids: HashSet<usize> = HashSet::new();
            loop {
                if !visited_signature_ids.insert(current_signature_id) {
                    // Cycle in signature aliases: treat as stuck, matching a failed lookup.
                    return signature.clone();
                }
                match elaboration_environment.lookup_sgn_named(current_signature_id) {
                    Ok((_, next_signature)) => match &next_signature.node {
                        Signature::Var(next_id) => {
                            current_signature_id = *next_id;
                        }
                        _ => return hnorm_sgn(elaboration_environment, next_signature),
                    },
                    Err(_) => return signature.clone(),
                }
            }
        }

        // SgnProj(m, ms, x) — walk structure `m` through path `ms`, then project out `x`.
        Signature::Proj(m, ms, x) => {
            // Get the signature of structure `m`.
            let root_sgn = match elaboration_environment.lookup_str_named(*m) {
                Ok((_, sgn)) => sgn.clone(),
                Err(_) => return signature.clone(),
            };
            // Walk through intermediate path components `ms`.
            let mut cur_sgn = hnorm_sgn(elaboration_environment, &root_sgn);
            for field in ms {
                cur_sgn = match project_str_field(elaboration_environment, &cur_sgn, field) {
                    Some(s) => hnorm_sgn(elaboration_environment, &s),
                    None => return signature.clone(),
                };
            }
            // Project out the target signature name `x`.
            match project_sgn_field(elaboration_environment, &cur_sgn, x) {
                Some(s) => hnorm_sgn(elaboration_environment, &s),
                None => signature.clone(),
            }
        }

        // SgnWhere(inner, ms, x, c) — rewrite SgiConAbs(x) to SgiCon(x, c) at path `ms`.
        Signature::Where(inner, ms, x, c) => {
            sgn_where_rewrite(elaboration_environment, inner, ms, x, c, &signature.span)
        }
    }
}

/// Walk a `SgnConst` to find sub-structure `field` and return its signature.
fn project_str_field(
    elaboration_environment: &Env,
    signature: &LocatedSignature,
    field: &str,
) -> Option<LocatedSignature> {
    match &hnorm_sgn(elaboration_environment, signature).node {
        Signature::Const(items) => {
            for item in items {
                if let SignatureItem::Structure(_, name, _, sub_sgn) = &item.node {
                    if name == field {
                        return Some(sub_sgn.clone());
                    }
                }
            }
            None
        }
        Signature::Error => Some(Located::new(Signature::Error, signature.span.clone())),
        _ => None,
    }
}

/// Walk a `SgnConst` to find sub-signature `field` and return it.
fn project_sgn_field(
    elaboration_environment: &Env,
    signature: &LocatedSignature,
    field: &str,
) -> Option<LocatedSignature> {
    match &hnorm_sgn(elaboration_environment, signature).node {
        Signature::Const(items) => {
            for item in items {
                if let SignatureItem::Signature(name, _, sub_sgn) = &item.node {
                    if name == field {
                        return Some(sub_sgn.clone());
                    }
                }
            }
            None
        }
        Signature::Error => Some(Located::new(Signature::Error, signature.span.clone())),
        _ => None,
    }
}

/// Implement the `SgnWhere` rewrite: replace `SgiConAbs(x, n, k)` at path `ms`
/// with `SgiCon(x, n, k, c)`.
///
/// Mirrors the `rewrite` helper inside `hnormSgn` for the `SgnWhere` case in `elab_env.sml`.
fn sgn_where_rewrite(
    elaboration_environment: &Env,
    inner: &LocatedSignature,
    ms: &[String],
    x: &str,
    replacement_constructor: &LocatedConstructor,
    _loc: &crate::error_types::Span,
) -> LocatedSignature {
    let hn = hnorm_sgn(elaboration_environment, inner);
    match hn.node {
        Signature::Error => Located::new(Signature::Error, hn.span),
        Signature::Const(items) => {
            let new_items =
                sgn_where_traverse(items, ms, x, replacement_constructor, hn.span.clone());
            Located::new(Signature::Const(new_items), hn.span)
        }
        _ => hn,
    }
}

fn sgn_where_traverse(
    items: Vec<LocatedSignatureItem>,
    ms: &[String],
    x: &str,
    c: &LocatedConstructor,
    _loc: crate::error_types::Span,
) -> Vec<LocatedSignatureItem> {
    let mut result = Vec::with_capacity(items.len());
    for item in items {
        let new_item = match &item.node {
            SignatureItem::ConAbs(name, id, kind) if ms.is_empty() && name == x => Located::new(
                SignatureItem::Constructor(name.clone(), *id, kind.clone(), c.clone()),
                item.span.clone(),
            ),
            SignatureItem::Structure(im, name, id, sub_sgn) if !ms.is_empty() && name == &ms[0] => {
                let new_sub = sgn_where_rewrite_const(sub_sgn, &ms[1..], x, c);
                Located::new(
                    SignatureItem::Structure(*im, name.clone(), *id, new_sub),
                    item.span.clone(),
                )
            }
            _ => item,
        };
        result.push(new_item);
    }
    result
}

fn sgn_where_rewrite_const(
    sgn: &LocatedSignature,
    ms: &[String],
    x: &str,
    replacement_constructor: &LocatedConstructor,
) -> LocatedSignature {
    match &sgn.node {
        Signature::Const(items) => {
            let new_items = sgn_where_traverse(
                items.clone(),
                ms,
                x,
                replacement_constructor,
                sgn.span.clone(),
            );
            Located::new(Signature::Const(new_items), sgn.span.clone())
        }
        _ => sgn.clone(),
    }
}

// ---------------------------------------------------------------------------
// enrich_classes — scan a signature for class instance Val declarations
// ---------------------------------------------------------------------------

/// Scan `signature` (bound to structure id `m1` at sub-path `ms`) and add any
/// `Val` declarations that are class instances as closed rules to `elaboration_environment.classes`.
///
/// Mirrors `fun enrichClasses env classes (m1, ms) sgn = ...` in `elab_env.sml`.
fn enrich_classes(
    elaboration_environment: &mut Env,
    structure_numeric_id: usize,
    structure_path: &[String],
    signature: &LocatedSignature,
) {
    let hn = {
        let elaboration_environment_ref = &*elaboration_environment;
        hnorm_sgn(elaboration_environment_ref, signature)
    };
    let items = match hn.node {
        Signature::Const(items) => items,
        _ => return,
    };
    for item in &items {
        match &item.node {
            SignatureItem::Val(val_name, _val_id, con) => {
                if let Some((cn, nvs, hyps, conclusion)) = rule_in(con) {
                    if elaboration_environment.classes.contains_key(&cn) {
                        let loc = item.span.clone();
                        let witness = Located::new(
                            Expression::ModProj(
                                structure_numeric_id,
                                structure_path.to_vec(),
                                val_name.clone(),
                            ),
                            loc,
                        );
                        if let Some(class) = elaboration_environment.classes.get_mut(&cn) {
                            class.closed_rules.push((nvs, hyps, conclusion, witness));
                        }
                    }
                }
            }
            SignatureItem::Structure(super::ImportMode::Import, sub_name, _sub_id, sub_sgn) => {
                let mut new_path = structure_path.to_vec();
                new_path.push(sub_name.clone());
                enrich_classes(
                    elaboration_environment,
                    structure_numeric_id,
                    &new_path,
                    sub_sgn,
                );
            }
            SignatureItem::ClassAbs(cls_name, _cls_id, _) => {
                let cn = ClassName::Proj(
                    structure_numeric_id,
                    structure_path.to_vec(),
                    cls_name.clone(),
                );
                elaboration_environment
                    .classes
                    .entry(cn)
                    .or_insert_with(ClassRules::empty);
            }
            SignatureItem::Class(cls_name, _cls_id, _, _) => {
                let cn = ClassName::Proj(
                    structure_numeric_id,
                    structure_path.to_vec(),
                    cls_name.clone(),
                );
                elaboration_environment
                    .classes
                    .entry(cn)
                    .or_insert_with(ClassRules::empty);
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// pat_binds and decl_binds
// ---------------------------------------------------------------------------

/// Count expression variables bound by `pattern` (for arity / stack depth).
///
/// Mirrors `patBindsN` in `elab_env.sml`.
///
/// # Arguments
///
/// * `pattern` — Elaborated pattern.
///
/// # Returns
///
/// Number of `Pattern::Var` leaves (record fields summed).
pub fn pat_binds_n(pattern: &LocatedPattern) -> usize {
    pattern_binds_count(pattern)
}

/// Extend `elaboration_environment` with relative expression bindings for every `Pattern::Var` in `pattern`.
///
/// Mirrors `patBinds` in `elab_env.sml`.
///
/// # Arguments
///
/// * `elaboration_environment` — Prior environment.
/// * `pattern` — Pattern introducing `rel_e` bindings.
///
/// # Returns
///
/// New [`Env`] (functional update).
pub fn pat_binds(elaboration_environment: Env, pattern: &LocatedPattern) -> Env {
    match &pattern.node {
        Pattern::Var(name, type_con) => {
            elaboration_environment.push_e_rel(name.clone(), type_con.clone())
        }
        Pattern::Prim(_) => elaboration_environment,
        Pattern::Constructor(_, _, _, None) => elaboration_environment,
        Pattern::Constructor(_, _, _, Some(inner_pattern)) => {
            pat_binds(elaboration_environment, inner_pattern)
        }
        Pattern::Record(fields) => fields.iter().fold(
            elaboration_environment,
            |accumulated_env, (_, sub_pattern, _)| pat_binds(accumulated_env, sub_pattern),
        ),
    }
}

/// Extend `elaboration_environment` for one `let`-level [`ElaboratedDeclaration`] (`val` / `val rec`).
///
/// Mirrors `edeclBinds` in `elab_env.sml`.
///
/// # Arguments
///
/// * `elaboration_environment` — Prior environment.
/// * `e_decl` — Inner declaration.
///
/// # Returns
///
/// [`Env`] with added `rel_e` bindings.
pub fn edecl_binds(elaboration_environment: Env, e_decl: &LocatedElaboratedDeclaration) -> Env {
    match &e_decl.node {
        ElaboratedDeclaration::Val(pattern, _, _) => pat_binds(elaboration_environment, pattern),
        ElaboratedDeclaration::ValRec(bindings) => bindings.iter().fold(
            elaboration_environment,
            |accumulated_env, (name, type_con, _)| {
                accumulated_env.push_e_rel(name.clone(), type_con.clone())
            },
        ),
    }
}

/// Extend `elaboration_environment` with bindings for one [`SignatureItem`] (datatype, `val`, substructure, etc.).
///
/// Mirrors `sgiBinds` in `elab_env.sml`.
///
/// # Arguments
///
/// * `elaboration_environment` — Prior environment.
/// * `sgn_item` — Single signature component.
///
/// # Returns
///
/// [`Env`] with `named_c` / `named_e` / `named_str` / `named_sgn` updates per item.
pub fn sgi_binds(elaboration_environment: Env, sgn_item: &LocatedSignatureItem) -> Env {
    let span = sgn_item.span.clone();
    match &sgn_item.node {
        SignatureItem::ConAbs(name, id, kind) => {
            elaboration_environment.push_c_named_as(name.clone(), *id, kind.clone(), None)
        }
        SignatureItem::Constructor(name, id, kind, definition) => elaboration_environment
            .push_c_named_as(name.clone(), *id, kind.clone(), Some(definition.clone())),
        SignatureItem::ClassAbs(name, id, kind) => {
            elaboration_environment.push_c_named_as(name.clone(), *id, kind.clone(), None)
        }
        SignatureItem::Class(name, id, kind, definition) => elaboration_environment
            .push_c_named_as(name.clone(), *id, kind.clone(), Some(definition.clone())),
        SignatureItem::Datatype(datatype_decls) => {
            datatype_decls
                .iter()
                .fold(elaboration_environment, |accumulated_env, datatype_decl| {
                    sgi_binds_datatype(accumulated_env, datatype_decl, &span)
                })
        }
        SignatureItem::DatatypeImp {
            name,
            id,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path: _,
            constrs,
        } => {
            let kind_type = Located::new(Kind::Type, span.clone());
            let definition = Located::new(
                Constructor::ModProj(*orig_mod, orig_path.clone(), orig_name.clone()),
                span.clone(),
            );
            let elaboration_environment = elaboration_environment.push_c_named_as(
                name.clone(),
                *id,
                kind_type.clone(),
                Some(definition),
            );

            constrs.iter().fold(
                elaboration_environment,
                |accumulated_env, (con_name, con_id, arg_type)| {
                    let expression_type =
                        build_constructor_type(*id, &[], arg_type.as_ref(), span.clone());
                    accumulated_env.push_e_named_as(con_name.clone(), *con_id, expression_type)
                },
            )
        }
        SignatureItem::Val(name, id, con_type) => {
            elaboration_environment.push_e_named_as(name.clone(), *id, con_type.clone())
        }
        SignatureItem::Structure(_, name, id, signature) => {
            // SignatureItem::Str with Import mode uses no-enrich.
            elaboration_environment.push_str_named_as_no_enrich(
                name.clone(),
                *id,
                signature.clone(),
            )
        }
        SignatureItem::Signature(name, id, signature) => {
            elaboration_environment.push_sgn_named_as(name.clone(), *id, signature.clone())
        }
        SignatureItem::Constraint(_, _) => elaboration_environment,
    }
}

/// Helper: extend `elaboration_environment` with the bindings from one datatype declaration inside a signature.
fn sgi_binds_datatype(
    elaboration_environment: Env,
    datatype_decl: &DatatypeDecl,
    span: &Span,
) -> Env {
    let kind_type = Located::new(Kind::Type, span.clone());
    // Build the kind for the datatype: (KType -> ... -> KType) with as many arrows
    // as there are type parameters.
    let datatype_kind: LocatedKind =
        datatype_decl
            .params
            .iter()
            .fold(kind_type.clone(), |acc_kind, _param| {
                Located::new(
                    Kind::Arrow(Box::new(kind_type.clone()), Box::new(acc_kind)),
                    span.clone(),
                )
            });

    let elaboration_environment = elaboration_environment.push_c_named_as(
        datatype_decl.name.clone(),
        datatype_decl.id,
        datatype_kind,
        None,
    );

    datatype_decl.constrs.iter().fold(
        elaboration_environment,
        |accumulated_env, (con_name, con_id, arg_type)| {
            let expression_type = build_constructor_type(
                datatype_decl.id,
                &datatype_decl.params,
                arg_type.as_ref(),
                span.clone(),
            );
            accumulated_env.push_e_named_as(con_name.clone(), *con_id, expression_type)
        },
    )
}

/// Build the expression type for a datatype constructor.
///
/// Given `datatype T 'a 'b = C of U`, the type of `C` is:
/// `∀ 'a :: * → ∀ 'b :: * → U -> T 'a 'b`
///
/// Mirrors the type-building logic in `sgiBinds` in `elab_env.sml`.
fn build_constructor_type(
    datatype_id: usize,
    type_params: &[String],
    arg_type: Option<&LocatedConstructor>,
    span: Span,
) -> LocatedConstructor {
    let kind_type = Located::new(Kind::Type, span.clone());
    let num_params = type_params.len();

    // Build `T rel(n-1) rel(n-2) ... rel(0)` (apply all type params to the type constructor).
    let base_type: LocatedConstructor = (0..num_params).fold(
        Located::new(Constructor::Named(datatype_id), span.clone()),
        |accumulated_type, param_index| {
            Located::new(
                Constructor::App(
                    Box::new(accumulated_type),
                    Box::new(Located::new(
                        Constructor::Rel(num_params - param_index - 1),
                        span.clone(),
                    )),
                ),
                span.clone(),
            )
        },
    );

    // If there is an argument type, wrap in TFun.
    let result_type: LocatedConstructor = match arg_type {
        None => base_type,
        Some(payload_type) => Located::new(
            Constructor::TFun(Box::new(payload_type.clone()), Box::new(base_type)),
            span.clone(),
        ),
    };

    // Universally quantify over all type parameters (outermost = first param).
    type_params
        .iter()
        .rev()
        .fold(result_type, |accumulated_type, _param_name| {
            Located::new(
                Constructor::TCFun(
                    Explicitness::Implicit,
                    "_".to_string(),
                    Box::new(kind_type.clone()),
                    Box::new(accumulated_type),
                ),
                span.clone(),
            )
        })
}

/// Extend `elaboration_environment` with bindings introduced by a top-level [`Declaration`] (datatype, FFI, SQL shapes, …).
///
/// Mirrors `declBinds` in `elab_env.sml`.
///
/// # Arguments
///
/// * `elaboration_environment` — Prior environment.
/// * `declaration` — Module-level declaration.
///
/// # Returns
///
/// [`Env`] after pushing all names introduced by `declaration`.
pub fn decl_binds(elaboration_environment: Env, declaration: &LocatedDeclaration) -> Env {
    let span = declaration.span.clone();
    match &declaration.node {
        Declaration::Constructor(name, id, kind, definition) => elaboration_environment
            .push_c_named_as(name.clone(), *id, kind.clone(), Some(definition.clone())),

        Declaration::Datatype(datatype_decls) => {
            datatype_decls
                .iter()
                .fold(elaboration_environment, |accumulated_env, datatype_decl| {
                    decl_binds_datatype(accumulated_env, datatype_decl, &span)
                })
        }

        Declaration::DatatypeImp {
            name,
            id,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path: _,
            constrs,
        } => {
            let kind_type = Located::new(Kind::Type, span.clone());
            let definition = Located::new(
                Constructor::ModProj(*orig_mod, orig_path.clone(), orig_name.clone()),
                span.clone(),
            );
            let elaboration_environment = elaboration_environment.push_c_named_as(
                name.clone(),
                *id,
                kind_type,
                Some(definition),
            );

            constrs.iter().fold(
                elaboration_environment,
                |accumulated_env, (con_name, con_id, arg_type)| {
                    let expression_type =
                        build_constructor_type(*id, &[], arg_type.as_ref(), span.clone());
                    accumulated_env.push_e_named_as(con_name.clone(), *con_id, expression_type)
                },
            )
        }

        Declaration::Val(name, id, expression_type, _body) => {
            elaboration_environment.push_e_named_as(name.clone(), *id, expression_type.clone())
        }

        Declaration::ValRec(bindings) => bindings.iter().fold(
            elaboration_environment,
            |accumulated_env, (name, id, expression_type, _body)| {
                accumulated_env.push_e_named_as(name.clone(), *id, expression_type.clone())
            },
        ),

        Declaration::Signature(name, id, signature) => {
            elaboration_environment.push_sgn_named_as(name.clone(), *id, signature.clone())
        }

        Declaration::Structure(name, id, signature, _body) => {
            elaboration_environment.push_str_named_as(name.clone(), *id, signature.clone())
        }

        Declaration::FfiStr(name, id, signature) => elaboration_environment
            .push_str_named_as_no_enrich(name.clone(), *id, signature.clone()),

        Declaration::Constraint(_, _) => elaboration_environment,
        Declaration::Export(_, _, _) => elaboration_environment,
        Declaration::Index(_, _) => elaboration_environment,
        Declaration::Database(_) => elaboration_environment,
        Declaration::Task(_, _) => elaboration_environment,
        Declaration::Policy(_) => elaboration_environment,
        Declaration::OnError(_, _, _) => elaboration_environment,

        Declaration::Table {
            mod_id,
            name,
            name_id,
            con,
            exp: _,
            pk_con,
            pk_exp: _,
            unique_con,
        } => {
            // `sql_table con (pk_con ++ unique_con)`
            let sql_table_con = Located::new(
                Constructor::ModProj(*mod_id, vec![], "sql_table".to_string()),
                span.clone(),
            );
            let combined_type = Located::new(
                Constructor::App(
                    Box::new(Located::new(
                        Constructor::App(Box::new(sql_table_con), Box::new(con.clone())),
                        span.clone(),
                    )),
                    Box::new(Located::new(
                        Constructor::Concat(Box::new(pk_con.clone()), Box::new(unique_con.clone())),
                        span.clone(),
                    )),
                ),
                span.clone(),
            );
            elaboration_environment.push_e_named_as(name.clone(), *name_id, combined_type)
        }

        Declaration::Sequence(mod_id, name, name_id) => {
            let seq_type = Located::new(
                Constructor::ModProj(*mod_id, vec![], "sql_sequence".to_string()),
                span.clone(),
            );
            elaboration_environment.push_e_named_as(name.clone(), *name_id, seq_type)
        }

        Declaration::View(mod_id, name, name_id, _query, view_con) => {
            let sql_view_con = Located::new(
                Constructor::ModProj(*mod_id, vec![], "sql_view".to_string()),
                span.clone(),
            );
            let combined_type = Located::new(
                Constructor::App(Box::new(sql_view_con), Box::new(view_con.clone())),
                span.clone(),
            );
            elaboration_environment.push_e_named_as(name.clone(), *name_id, combined_type)
        }

        Declaration::Cookie(mod_id, name, name_id, cookie_con) => {
            let cookie_type_con = Located::new(
                Constructor::ModProj(*mod_id, vec![], "cookie".to_string()),
                span.clone(),
            );
            let combined_type = Located::new(
                Constructor::App(Box::new(cookie_type_con), Box::new(cookie_con.clone())),
                span.clone(),
            );
            elaboration_environment.push_e_named_as(name.clone(), *name_id, combined_type)
        }

        Declaration::Style(mod_id, name, name_id) => {
            let css_class_type = Located::new(
                Constructor::ModProj(*mod_id, vec![], "css_class".to_string()),
                span.clone(),
            );
            elaboration_environment.push_e_named_as(name.clone(), *name_id, css_class_type)
        }

        Declaration::Ffi(name, id, _ffi_modes, ffi_type) => {
            elaboration_environment.push_e_named_as(name.clone(), *id, ffi_type.clone())
        }
    }
}

/// Helper: extend `elaboration_environment` with the bindings from one datatype declaration (top-level).
fn decl_binds_datatype(
    elaboration_environment: Env,
    datatype_decl: &DatatypeDecl,
    span: &Span,
) -> Env {
    let kind_type = Located::new(Kind::Type, span.clone());
    let _num_params = datatype_decl.params.len();

    // Build the full kind: `(KType -> ... -> KType)` with `num_params` arrows.
    // Also build the partially-applied type `(T rel(n-1) ... rel(0))` for use in
    // constructor types.
    let datatype_kind: LocatedKind =
        datatype_decl
            .params
            .iter()
            .fold(kind_type.clone(), |accumulated_kind, _| {
                Located::new(
                    Kind::Arrow(Box::new(kind_type.clone()), Box::new(accumulated_kind)),
                    span.clone(),
                )
            });

    let elaboration_environment = elaboration_environment.push_c_named_as(
        datatype_decl.name.clone(),
        datatype_decl.id,
        datatype_kind,
        None,
    );

    // Register the datatype for constructor lookup.
    let elaboration_environment = elaboration_environment.push_datatype(
        datatype_decl.id,
        datatype_decl.params.clone(),
        datatype_decl.constrs.clone(),
    );

    // Add each constructor as a named expression.
    datatype_decl.constrs.iter().fold(
        elaboration_environment,
        |accumulated_env, (con_name, con_id, arg_type)| {
            let expression_type = build_constructor_type(
                datatype_decl.id,
                &datatype_decl.params,
                arg_type.as_ref(),
                span.clone(),
            );
            accumulated_env.push_e_named_as(con_name.clone(), *con_id, expression_type)
        },
    )
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elaborated::PatternConstructor;
    use crate::error_types::Span;

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn kind_type() -> LocatedKind {
        Located::new(Kind::Type, dummy_span())
    }

    fn con_rel(index: usize) -> LocatedConstructor {
        Located::new(Constructor::Rel(index), dummy_span())
    }

    fn con_named(id: usize) -> LocatedConstructor {
        Located::new(Constructor::Named(id), dummy_span())
    }

    fn sgn_error() -> LocatedSignature {
        Located::new(Signature::Error, dummy_span())
    }

    // -----------------------------------------------------------------------
    // EnvError display
    // -----------------------------------------------------------------------

    /// Catches mutant: EnvError::fmt returns wrong message.
    #[test]
    fn env_error_unbound_k_rel_display() {
        let error = EnvError::UnboundKRel(3);
        assert_eq!(error.to_string(), "unbound kind rel #3");
    }

    /// Catches mutant: EnvError::UnboundCNamed uses wrong message.
    #[test]
    fn env_error_unbound_c_named_display() {
        let error = EnvError::UnboundCNamed(42);
        assert_eq!(error.to_string(), "unbound named con [42]");
    }

    /// Catches mutant: EnvError::UnboundStrNamed uses wrong message.
    #[test]
    fn env_error_unbound_str_named_display() {
        let error = EnvError::UnboundStrNamed(7);
        assert_eq!(error.to_string(), "unbound named str [7]");
    }

    // -----------------------------------------------------------------------
    // Kind variable operations
    // -----------------------------------------------------------------------

    /// Catches mutant: push_k_rel doesn't bump existing indices.
    #[test]
    fn push_k_rel_bumps_existing_indices() {
        let env = Env::empty().push_k_rel("alpha".to_string());
        // alpha is at index 0
        assert_eq!(env.lookup_k("alpha"), Some(0));

        let env2 = env.push_k_rel("beta".to_string());
        // beta is at 0, alpha is now at 1
        assert_eq!(env2.lookup_k("beta"), Some(0));
        assert_eq!(env2.lookup_k("alpha"), Some(1));
    }

    /// Catches mutant: lookup_k_rel uses wrong index direction.
    #[test]
    fn push_k_rel_lookup_by_index() {
        let env = Env::empty()
            .push_k_rel("outer".to_string())
            .push_k_rel("inner".to_string());

        // innermost is at index 0
        assert_eq!(env.lookup_k_rel(0).unwrap(), "inner");
        assert_eq!(env.lookup_k_rel(1).unwrap(), "outer");
        assert!(env.lookup_k_rel(2).is_err());
    }

    /// Catches mutant: push_k_rel shadows names incorrectly.
    #[test]
    fn push_k_rel_shadow_same_name() {
        let env = Env::empty()
            .push_k_rel("k".to_string())
            .push_k_rel("k".to_string());

        // The inner binding wins — lookup_k returns 0.
        assert_eq!(env.lookup_k("k"), Some(0));
        assert_eq!(env.lookup_k_rel(0).unwrap(), "k");
        assert_eq!(env.lookup_k_rel(1).unwrap(), "k");
    }

    // -----------------------------------------------------------------------
    // Constructor variable operations
    // -----------------------------------------------------------------------

    /// Catches mutant: push_c_rel doesn't bump existing relative indices.
    #[test]
    fn push_c_rel_bumps_existing_relative_indices() {
        let kind = kind_type();
        let env = Env::empty().push_c_rel("a".to_string(), kind.clone());
        // 'a' is at index 0
        let (_, a_kind) = env.lookup_c_rel(0).unwrap();
        assert!(matches!(a_kind.node, Kind::Type));

        let env2 = env.push_c_rel("b".to_string(), kind);
        // 'b' is now at 0, 'a' at 1
        match env2.lookup_c("b") {
            VarLookup::Rel(0, _) => {}
            other => panic!("expected Rel(0, ...), got {:?}", other),
        }
        match env2.lookup_c("a") {
            VarLookup::Rel(1, _) => {}
            other => panic!("expected Rel(1, ...), got {:?}", other),
        }
    }

    /// Catches mutant: push_c_named_as stores wrong id.
    #[test]
    fn push_c_named_as_stores_correct_id() {
        let env = Env::empty().push_c_named_as("Foo".to_string(), 99, kind_type(), None);

        let (name, _kind, def) = env.lookup_c_named(99).unwrap();
        assert_eq!(name, "Foo");
        assert!(def.is_none());

        match env.lookup_c("Foo") {
            VarLookup::Named(99, _) => {}
            other => panic!("expected Named(99, _), got {:?}", other),
        }
    }

    /// Catches mutant: lookup_c returns Named when should be NotBound.
    #[test]
    fn lookup_c_not_bound() {
        let env = Env::empty();
        assert!(env.lookup_c("missing").is_not_bound());
    }

    // -----------------------------------------------------------------------
    // Expression variable operations
    // -----------------------------------------------------------------------

    /// Catches mutant: push_e_rel doesn't bump existing indices.
    #[test]
    fn push_e_rel_bumps_existing_indices() {
        let env = Env::empty()
            .push_e_rel("x".to_string(), con_rel(0))
            .push_e_rel("y".to_string(), con_rel(1));

        match env.lookup_e("x") {
            VarLookup::Rel(1, _) => {}
            other => panic!("expected Rel(1, _), got {:?}", other),
        }
        match env.lookup_e("y") {
            VarLookup::Rel(0, _) => {}
            other => panic!("expected Rel(0, _), got {:?}", other),
        }
    }

    /// Catches mutant: push_e_named_as stores wrong id.
    #[test]
    fn push_e_named_as_stores_correct_id() {
        let env = Env::empty().push_e_named_as("foo".to_string(), 77, con_named(5));

        let (name, _type_con) = env.lookup_e_named(77).unwrap();
        assert_eq!(name, "foo");

        assert!(env.check_e_named(77));
        assert!(!env.check_e_named(78));
    }

    /// Catches mutant: lookup_e returns wrong variant.
    #[test]
    fn lookup_e_not_bound() {
        let env = Env::empty();
        assert!(env.lookup_e("nope").is_not_bound());
    }

    // -----------------------------------------------------------------------
    // Signature and structure operations
    // -----------------------------------------------------------------------

    /// Catches mutant: push_sgn_named_as uses wrong id.
    #[test]
    fn push_sgn_named_as_and_lookup() {
        let signature = sgn_error();
        let env = Env::empty().push_sgn_named_as("MySig".to_string(), 10, signature.clone());

        let (name, _sgn) = env.lookup_sgn_named(10).unwrap();
        assert_eq!(name, "MySig");

        let (id, _sgn) = env.lookup_sgn("MySig").unwrap();
        assert_eq!(*id, 10);
    }

    /// Catches mutant: push_str_named_as uses wrong id.
    #[test]
    fn push_str_named_as_and_lookup() {
        let signature = sgn_error();
        let env = Env::empty().push_str_named_as("MyMod".to_string(), 20, signature);

        let (name, _sgn) = env.lookup_str_named(20).unwrap();
        assert_eq!(name, "MyMod");

        let (id, _sgn) = env.lookup_str("MyMod").unwrap();
        assert_eq!(*id, 20);
    }

    // -----------------------------------------------------------------------
    // pat_binds_n
    // -----------------------------------------------------------------------

    /// Catches mutant: Pattern::Var doesn't count as 1 binding.
    #[test]
    fn pat_binds_n_var() {
        let pattern = Located::new(Pattern::Var("x".to_string(), con_rel(0)), dummy_span());
        assert_eq!(pat_binds_n(&pattern), 1);
    }

    /// Catches mutant: Pattern::Prim incorrectly counted as 1.
    #[test]
    fn pat_binds_n_prim() {
        let pattern = Located::new(
            Pattern::Prim(crate::primitives::Prim::Int(42)),
            dummy_span(),
        );
        assert_eq!(pat_binds_n(&pattern), 0);
    }

    /// Catches mutant: nested Con pattern doesn't sum correctly.
    #[test]
    fn pat_binds_n_con_with_inner() {
        let inner = Located::new(Pattern::Var("y".to_string(), con_rel(0)), dummy_span());
        let pattern = Located::new(
            Pattern::Constructor(
                crate::datatype_kind::DatatypeKind::Default,
                PatternConstructor::Var(0),
                vec![],
                Some(Box::new(inner)),
            ),
            dummy_span(),
        );
        assert_eq!(pat_binds_n(&pattern), 1);
    }

    /// Catches mutant: Record sum is wrong.
    #[test]
    fn pat_binds_n_record_two_vars() {
        let field_a = Located::new(Pattern::Var("a".to_string(), con_rel(0)), dummy_span());
        let field_b = Located::new(Pattern::Var("b".to_string(), con_rel(0)), dummy_span());
        let pattern = Located::new(
            Pattern::Record(vec![
                ("a".to_string(), field_a, con_rel(0)),
                ("b".to_string(), field_b, con_rel(0)),
            ]),
            dummy_span(),
        );
        assert_eq!(pat_binds_n(&pattern), 2);
    }

    // -----------------------------------------------------------------------
    // pat_binds
    // -----------------------------------------------------------------------

    /// Catches mutant: pat_binds doesn't actually push the binding.
    #[test]
    fn pat_binds_var_pushes_rel_binding() {
        let pattern = Located::new(
            Pattern::Var("value".to_string(), con_named(5)),
            dummy_span(),
        );
        let env = pat_binds(Env::empty(), &pattern);

        match env.lookup_e("value") {
            VarLookup::Rel(0, _) => {}
            other => panic!("expected Rel(0, _), got {:?}", other),
        }
    }

    /// Catches mutant: pat_binds on Prim changes the env.
    #[test]
    fn pat_binds_prim_is_identity() {
        let pattern = Located::new(Pattern::Prim(crate::primitives::Prim::Int(0)), dummy_span());
        let env_before = Env::empty();
        let env_after = pat_binds(env_before.clone(), &pattern);
        // No new expression bindings.
        assert_eq!(env_after.dump_expressions().len(), 0);
    }

    // -----------------------------------------------------------------------
    // Lift expression-in-expression
    // -----------------------------------------------------------------------

    /// Catches mutant: lift doesn't increment free Rel indices.
    #[test]
    fn lift_exp_in_exp_increments_free_rel() {
        let expression = Located::new(Expression::Rel(0), dummy_span());
        let lifted = lift_exp_in_exp_bound(0, expression);
        assert!(
            matches!(lifted.node, Expression::Rel(1)),
            "expected Rel(1), got {:?}",
            lifted.node
        );
    }

    /// Catches mutant: lift incorrectly lifts bound indices.
    #[test]
    fn lift_exp_in_exp_preserves_bound_rel() {
        // Rel(0) under one Abs binder is bound (exp_bound = 1 inside Abs body).
        let inner = Located::new(Expression::Rel(0), dummy_span());
        let abs_exp = Located::new(
            Expression::Abs("x".to_string(), con_rel(0), con_rel(0), Box::new(inner)),
            dummy_span(),
        );
        let lifted = lift_exp_in_exp_bound(0, abs_exp);
        if let Expression::Abs(_, _, _, body) = lifted.node {
            // Inside the Abs, exp_bound is 1, so Rel(0) is bound and unchanged.
            assert!(
                matches!(body.node, Expression::Rel(0)),
                "expected Rel(0), got {:?}",
                body.node
            );
        } else {
            panic!("expected Abs after lifting");
        }
    }

    /// Catches mutant: lift_exp increments a free index inside Abs (idx > 0).
    #[test]
    fn lift_exp_in_exp_lifts_free_above_binder() {
        // Rel(1) inside an Abs is free when exp_bound for lifting starts at 0:
        // inside the Abs, exp_bound becomes 1, so Rel(1) >= 1 → lifted to Rel(2).
        let inner = Located::new(Expression::Rel(1), dummy_span());
        let abs_exp = Located::new(
            Expression::Abs("x".to_string(), con_rel(0), con_rel(0), Box::new(inner)),
            dummy_span(),
        );
        let lifted = lift_exp_in_exp_bound(0, abs_exp);
        if let Expression::Abs(_, _, _, body) = lifted.node {
            assert!(
                matches!(body.node, Expression::Rel(2)),
                "expected Rel(2), got {:?}",
                body.node
            );
        } else {
            panic!("expected Abs");
        }
    }

    // -----------------------------------------------------------------------
    // Lift kind in expression
    // -----------------------------------------------------------------------

    /// Catches mutant: KAbs body doesn't increment kind_bound.
    #[test]
    fn lift_kind_in_exp_kabs_increments_kind_bound() {
        // Kind::Rel(0) inside a KAbs is bound (kind_bound = 1 inside body).
        let inner_kind = Located::new(Kind::Rel(0), dummy_span());
        let inner_exp = Located::new(
            Expression::KApp(
                Box::new(Located::new(Expression::Named(0), dummy_span())),
                Box::new(inner_kind),
            ),
            dummy_span(),
        );
        let kabs_exp = Located::new(
            Expression::KAbs("k".to_string(), Box::new(inner_exp)),
            dummy_span(),
        );

        let lifted = lift_kind_in_exp_bound(0, kabs_exp);
        if let Expression::KAbs(_, body) = lifted.node {
            if let Expression::KApp(_, kind_arg) = body.node {
                // Inside KAbs, kind_bound is 1, so Rel(0) is bound — should stay Rel(0).
                assert!(
                    matches!(kind_arg.node, Kind::Rel(0)),
                    "expected Rel(0) (bound), got {:?}",
                    kind_arg.node
                );
            } else {
                panic!("expected KApp");
            }
        } else {
            panic!("expected KAbs");
        }
    }

    // -----------------------------------------------------------------------
    // ClassName
    // -----------------------------------------------------------------------

    /// Catches mutant: ClassName::Named and Proj not distinguished in Hash.
    #[test]
    fn class_name_hash_distinguishes_variants() {
        use std::collections::HashMap;
        let mut map: HashMap<ClassName, i32> = HashMap::new();
        map.insert(ClassName::Named(1), 10);
        map.insert(ClassName::Proj(1, vec![], "x".to_string()), 20);

        assert_eq!(map[&ClassName::Named(1)], 10);
        assert_eq!(map[&ClassName::Proj(1, vec![], "x".to_string())], 20);
    }

    // -----------------------------------------------------------------------
    // Datatype operations
    // -----------------------------------------------------------------------

    /// Catches mutant: push_datatype doesn't register constructors by name.
    #[test]
    fn push_datatype_registers_constructor_by_name() {
        let env = Env::empty().push_datatype(
            100,
            vec!["a".to_string()],
            vec![
                ("None".to_string(), 200, None),
                ("Some".to_string(), 201, Some(con_rel(0))),
            ],
        );

        let none_info = env.lookup_constructor("None").unwrap();
        assert_eq!(none_info.datatype_id, 100);
        assert_eq!(none_info.constructor_id, 200);
        assert!(none_info.arg_type.is_none());

        let some_info = env.lookup_constructor("Some").unwrap();
        assert_eq!(some_info.constructor_id, 201);
        assert!(some_info.arg_type.is_some());
    }

    /// Catches mutant: lookup_constructor for missing name doesn't return None.
    #[test]
    fn lookup_constructor_missing_returns_none() {
        let env = Env::empty();
        assert!(env.lookup_constructor("NoSuchCon").is_none());
    }

    // -----------------------------------------------------------------------
    // Class operations
    // -----------------------------------------------------------------------

    /// Catches mutant: push_class doesn't add to the class map.
    #[test]
    fn push_class_makes_is_class_true() {
        let env = Env::empty().push_c_named_as("Eq".to_string(), 50, kind_type(), None);
        let env = env.push_class(50);

        let eq_con = Located::new(Constructor::Named(50), dummy_span());
        assert!(env.is_class(&eq_con));

        // A different id should not be a class.
        let other_con = Located::new(Constructor::Named(51), dummy_span());
        assert!(!env.is_class(&other_con));
    }

    // -----------------------------------------------------------------------
    // Env::empty
    // -----------------------------------------------------------------------

    /// Catches mutant: Env::empty has non-empty fields.
    #[test]
    fn env_empty_has_no_bindings() {
        let env = Env::empty();
        assert!(env.lookup_k("x").is_none());
        assert!(env.lookup_c("x").is_not_bound());
        assert!(env.lookup_e("x").is_not_bound());
        assert!(env.lookup_sgn("x").is_none());
        assert!(env.lookup_str("x").is_none());
        assert!(env.lookup_c_named(0).is_err());
        assert!(env.lookup_e_named(0).is_err());
    }
}
