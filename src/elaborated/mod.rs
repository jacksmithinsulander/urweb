//! Elaborated AST — the internal representation after type inference.
//!
//! Contains unification variables (`KUnif`, `CUnif`, `EUnif`) that get solved
//! during type inference. Variables use de Bruijn indices or globally-unique
//! names. `ModProj` for qualified module references.
//!
//! Mirrors `elab.sml`.
//!
//! **Style:** new/edited Rust here follows [README.md](../../README.md) Rust code style (exceptions documented there).
//!
//! Pipeline entry points [`elaborate::elab_file`], [`unnest::unnest`], and [`explify::explify`] document
//! `# Arguments`, `# Returns`, and error reporting (`ErrorReporter`) where relevant.
//! [`elaborate`], [`elaboration_errors`], [`type_operations`], [`environment`] binders,
//! [`disjointness_analysis`], and [`type_display`] use the same headings on their public helpers.

pub mod disjointness_analysis;
pub mod elaborate;
pub mod elaboration_errors;
pub mod environment;
pub mod explify;
pub mod module_database;
pub mod type_display;
pub mod type_operations;
pub mod unnest;
pub mod utilities;

use std::sync::{Arc, Mutex};

use crate::datatype_kind::DatatypeKind;
use crate::error_types::{Located, Span};
use crate::primitives::Prim;
use crate::source::FfiMode;

// ---------------------------------------------------------------------------
// Kinds
// ---------------------------------------------------------------------------

pub type KUnifRef = Arc<Mutex<KUnif>>;

#[derive(Debug, Clone)]
pub enum KUnif {
    /// Not yet solved; the closure checks validity.
    Unknown,
    Known(Box<LocatedKind>),
}

#[derive(Debug, Clone)]
pub enum Kind {
    Type,
    Arrow(Box<LocatedKind>, Box<LocatedKind>),
    Name,
    Record(Box<LocatedKind>),
    Unit,
    Tuple(Vec<LocatedKind>),

    Error,
    /// Unification variable for a kind.
    Unif(Span, String, KUnifRef),
    /// Tuple unification variable (partially known).
    TupleUnif(Span, Vec<(usize, LocatedKind)>, KUnifRef),

    /// De Bruijn index into the kind environment.
    Rel(usize),
    /// Kind-level abstraction (for kind-polymorphism).
    Fun(String, Box<LocatedKind>),
}

pub type LocatedKind = Located<Kind>;

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

pub type CUnifRef = Arc<Mutex<CUnif>>;

#[derive(Debug, Clone)]
pub enum CUnif {
    Unknown,
    Known(Box<LocatedConstructor>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Explicitness {
    Explicit,
    Implicit,
}

#[derive(Debug, Clone)]
pub enum Constructor {
    TFun(Box<LocatedConstructor>, Box<LocatedConstructor>),
    TCFun(
        Explicitness,
        String,
        Box<LocatedKind>,
        Box<LocatedConstructor>,
    ),
    TRecord(Box<LocatedConstructor>),
    TDisjoint(
        Box<LocatedConstructor>,
        Box<LocatedConstructor>,
        Box<LocatedConstructor>,
    ),

    /// De Bruijn index.
    Rel(usize),
    /// Globally unique name (from `CNamed`).
    Named(usize),
    /// Module projection: `module.path.name`.
    ModProj(usize, Vec<String>, String),
    App(Box<LocatedConstructor>, Box<LocatedConstructor>),
    Abs(String, Box<LocatedKind>, Box<LocatedConstructor>),

    KAbs(String, Box<LocatedConstructor>),
    KApp(Box<LocatedConstructor>, Box<LocatedKind>),
    TKFun(String, Box<LocatedConstructor>),

    Name(String),

    Record(
        Box<LocatedKind>,
        Vec<(LocatedConstructor, LocatedConstructor)>,
    ),
    Concat(Box<LocatedConstructor>, Box<LocatedConstructor>),
    Map(Box<LocatedKind>, Box<LocatedKind>),

    Unit,

    Tuple(Vec<LocatedConstructor>),
    Proj(Box<LocatedConstructor>, usize),

    Error,
    /// Elaboration-time unification variable.
    Unif(usize, Span, Box<LocatedKind>, String, CUnifRef),
}

pub type LocatedConstructor = Located<Constructor>;

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum PatternConstructor {
    Var(usize),
    Proj(usize, Vec<String>, String),
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Var(String, LocatedConstructor),
    Prim(Prim),
    Constructor(
        DatatypeKind,
        PatternConstructor,
        Vec<LocatedConstructor>,
        Option<Box<LocatedPattern>>,
    ),
    Record(Vec<(String, LocatedPattern, LocatedConstructor)>),
}

pub type LocatedPattern = Located<Pattern>;

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

/// Whether we're inside an elaboration-time `let` in `ELet`/`EDVal*`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportMode {
    Import,
    Skip,
}

#[derive(Debug, Clone)]
pub enum ElaboratedDeclaration {
    Val(LocatedPattern, LocatedConstructor, LocatedExpression),
    ValRec(Vec<(String, LocatedConstructor, LocatedExpression)>),
}

pub type LocatedElaboratedDeclaration = Located<ElaboratedDeclaration>;

#[derive(Debug, Clone)]
pub enum Expression {
    Prim(Prim),
    Rel(usize),
    Named(usize),
    ModProj(usize, Vec<String>, String),
    App(Box<LocatedExpression>, Box<LocatedExpression>),
    Abs(
        String,
        LocatedConstructor,
        LocatedConstructor,
        Box<LocatedExpression>,
    ),
    CApp(Box<LocatedExpression>, LocatedConstructor),
    CAbs(
        Explicitness,
        String,
        Box<LocatedKind>,
        Box<LocatedExpression>,
    ),

    KAbs(String, Box<LocatedExpression>),
    KApp(Box<LocatedExpression>, Box<LocatedKind>),

    Record(Vec<(LocatedConstructor, LocatedExpression, LocatedConstructor)>),
    Field(Box<LocatedExpression>, LocatedConstructor, FieldMeta),
    Concat(
        Box<LocatedExpression>,
        LocatedConstructor,
        Box<LocatedExpression>,
        LocatedConstructor,
    ),
    Cut(Box<LocatedExpression>, LocatedConstructor, FieldMeta),
    CutMulti(Box<LocatedExpression>, LocatedConstructor, RestMeta),

    Case(
        Box<LocatedExpression>,
        Vec<(LocatedPattern, LocatedExpression)>,
        CaseMeta,
    ),

    Error,
    Unif(Arc<Mutex<Option<LocatedExpression>>>),
    Hole(CUnifRef),

    Let(
        Vec<LocatedElaboratedDeclaration>,
        Box<LocatedExpression>,
        LocatedConstructor,
    ),
}

pub type LocatedExpression = Located<Expression>;

#[derive(Debug, Clone)]
pub struct FieldMeta {
    pub field: LocatedConstructor,
    pub rest: LocatedConstructor,
}

#[derive(Debug, Clone)]
pub struct RestMeta {
    pub rest: LocatedConstructor,
}

#[derive(Debug, Clone)]
pub struct CaseMeta {
    pub disc: LocatedConstructor,
    pub result: LocatedConstructor,
}

// ---------------------------------------------------------------------------
// Signature items
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct DatatypeDecl {
    pub name: String,
    pub id: usize,
    pub params: Vec<String>,
    pub constrs: Vec<(String, usize, Option<LocatedConstructor>)>,
}

#[derive(Debug, Clone)]
pub enum SignatureItem {
    ConAbs(String, usize, LocatedKind),
    Constructor(String, usize, LocatedKind, LocatedConstructor),
    Datatype(Vec<DatatypeDecl>),
    DatatypeImp {
        name: String,
        id: usize,
        orig_mod: usize,
        orig_path: Vec<String>,
        orig_name: String,
        orig_constrs_path: Vec<String>,
        constrs: Vec<(String, usize, Option<LocatedConstructor>)>,
    },
    Val(String, usize, LocatedConstructor),
    Structure(ImportMode, String, usize, LocatedSignature),
    Signature(String, usize, LocatedSignature),
    Constraint(LocatedConstructor, LocatedConstructor),
    ClassAbs(String, usize, LocatedKind),
    Class(String, usize, LocatedKind, LocatedConstructor),
}

pub type LocatedSignatureItem = Located<SignatureItem>;

#[derive(Debug, Clone)]
pub enum Signature {
    Const(Vec<LocatedSignatureItem>),
    Var(usize),
    Fun(String, usize, Box<LocatedSignature>, Box<LocatedSignature>),
    Where(
        Box<LocatedSignature>,
        Vec<String>,
        String,
        LocatedConstructor,
    ),
    Proj(usize, Vec<String>, String),
    Error,
}

pub type LocatedSignature = Located<Signature>;

// ---------------------------------------------------------------------------
// Top-level declarations
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Declaration {
    Constructor(String, usize, LocatedKind, LocatedConstructor),
    Datatype(Vec<DatatypeDecl>),
    DatatypeImp {
        name: String,
        id: usize,
        orig_mod: usize,
        orig_path: Vec<String>,
        orig_name: String,
        orig_constrs_path: Vec<String>,
        constrs: Vec<(String, usize, Option<LocatedConstructor>)>,
    },
    Val(String, usize, LocatedConstructor, LocatedExpression),
    ValRec(Vec<(String, usize, LocatedConstructor, LocatedExpression)>),
    Signature(String, usize, LocatedSignature),
    Structure(String, usize, LocatedSignature, LocatedStructure),
    FfiStr(String, usize, LocatedSignature),
    Constraint(LocatedConstructor, LocatedConstructor),
    Export(usize, LocatedSignature, LocatedStructure),
    Table {
        mod_id: usize,
        name: String,
        name_id: usize,
        con: LocatedConstructor,
        exp: LocatedExpression,
        pk_con: LocatedConstructor,
        pk_exp: LocatedExpression,
        unique_con: LocatedConstructor,
    },
    Sequence(usize, String, usize),
    View(usize, String, usize, LocatedExpression, LocatedConstructor),
    Index(LocatedExpression, LocatedExpression),
    Database(String),
    Cookie(usize, String, usize, LocatedConstructor),
    Style(usize, String, usize),
    Task(LocatedExpression, LocatedExpression),
    Policy(LocatedExpression),
    OnError(usize, Vec<String>, String),
    Ffi(String, usize, Vec<FfiMode>, LocatedConstructor),
}

pub type LocatedDeclaration = Located<Declaration>;

#[derive(Debug, Clone)]
pub enum Structure {
    Const(Vec<LocatedDeclaration>),
    Var(usize),
    Proj(Box<LocatedStructure>, String),
    Fun(
        String,
        usize,
        LocatedSignature,
        LocatedSignature,
        Box<LocatedStructure>,
    ),
    App(Box<LocatedStructure>, Box<LocatedStructure>),
    Error,
}

pub type LocatedStructure = Located<Structure>;

pub type File = Vec<LocatedDeclaration>;
