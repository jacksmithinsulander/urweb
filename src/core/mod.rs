//! Core AST — after elaboration and before monomorphization.
//!
//! This module defines the simplified intermediate representation used after
//! type inference and explification. All bindings use globally-unique integer
//! names (no module paths or de Bruijn at top level). FFI references are
//! `(module, name)` pairs.
//!
//! **Kinds** classify types: `Type`, `Arrow`, `Record`, `Tuple`, `Rel` (de Bruijn), etc.
//! **Constructors** (Con) represent types and type-level computation: `TFun`, `Named`, `Ffi`, `App`, etc.
//! **Patterns** bind variables in case expressions.
//! **Expressions** (Exp) are the value-level terms: `Prim`, `App`, `Case`, `Let`, `ServerCall`, etc.
//! **Declarations** (Decl) are top-level: `Con`, `Datatype`, `Val`, `Table`, `View`, etc.
//!
//! Mirrors `core.sml`.

pub mod dead_code_elimination;
pub mod effect_analysis;
pub mod environment;
pub mod export_tagging;
pub mod local_reduction;
pub mod rpc_elaboration;
pub mod untangling;
pub mod utilities;

use crate::datatype_kind::DatatypeKind;
use crate::error_types::Located;
use crate::export::ExportKind;
use crate::primitives::Prim;
use crate::settings::FailureMode;

// ---------------------------------------------------------------------------
// Kinds
// ---------------------------------------------------------------------------

/// Kind (type-level type) of a constructor or type parameter.
///
/// Mirrors the `Core.kind` datatype from `core.sml`.
#[derive(Debug, Clone)]
pub enum Kind {
    /// The kind of types (`Type`).
    Type,
    /// Arrow kind: domain → range.
    Arrow(Box<LocatedKind>, Box<LocatedKind>),
    /// Name kind (for row variables in records).
    Name,
    /// Record kind with a row.
    Record(Box<LocatedKind>),
    /// Unit kind.
    Unit,
    /// Tuple kind: sequence of kinds.
    Tuple(Vec<LocatedKind>),

    /// De Bruijn index for a kind variable.
    Rel(usize),
    /// Kind-level function: binder and body.
    Fun(String, Box<LocatedKind>),
}

/// A kind with source location.
pub type LocatedKind = Located<Kind>;

/// Verbose alias for `Kind` (kind of types).
pub type KindType = Kind;
/// Verbose alias for `LocatedKind` (kind with source location).
pub type LocatedKindType = LocatedKind;

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

/// Constructor (type-level term) representing types and type functions.
///
/// Mirrors the `Core.con` datatype from `core.sml`.
#[derive(Debug, Clone)]
pub enum Constructor {
    /// Function type: domain → range.
    TFun(Box<LocatedConstructor>, Box<LocatedConstructor>),
    /// Type-level lambda: (α :: k) → body.
    TCFun(String, Box<LocatedKind>, Box<LocatedConstructor>),
    /// Record type: { row }.
    TRecord(Box<LocatedConstructor>),

    /// De Bruijn index for a type/kind variable (inside TCFun/Abs).
    Rel(usize),
    /// Named type/constructor reference (globally unique id).
    Named(usize),
    /// FFI type: `(module, name)`
    Ffi(String, String),
    /// Type application: f x.
    App(Box<LocatedConstructor>, Box<LocatedConstructor>),
    /// Type-level lambda: fn α :: k => body.
    Abs(String, Box<LocatedKind>, Box<LocatedConstructor>),

    /// Kind-level abstraction: κ → body.
    KAbs(String, Box<LocatedConstructor>),
    /// Kind application: c k.
    KApp(Box<LocatedConstructor>, Box<LocatedKind>),
    /// Kind-polymorphic type: ∀κ. body.
    TKFun(String, Box<LocatedConstructor>),

    /// Field name literal: #Foo.
    Name(String),

    /// Row literal: [f1 = c1, f2 = c2, …].
    Record(
        Box<LocatedKind>,
        Vec<(LocatedConstructor, LocatedConstructor)>,
    ),
    /// Row concatenation: c1 ++ c2.
    Concat(Box<LocatedConstructor>, Box<LocatedConstructor>),
    /// Row map: maps a kind over a row.
    Map(Box<LocatedKind>, Box<LocatedKind>),

    /// Unit type.
    Unit,

    /// Tuple type: (c1, c2, …).
    Tuple(Vec<LocatedConstructor>),
    /// Projection: c.#n (nth field of tuple).
    Proj(Box<LocatedConstructor>, usize),
}

/// A constructor with source location.
pub type LocatedConstructor = Located<Constructor>;

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

/// Pattern constructor: variable or FFI constructor application.
#[derive(Debug, Clone)]
pub enum PatternConstructor {
    /// Variable pattern (de Bruijn index).
    Var(usize),
    /// FFI datatype constructor pattern.
    Ffi {
        module: String,
        datatyp: String,
        params: Vec<String>,
        con: String,
        arg: Option<LocatedConstructor>,
        kind: DatatypeKind,
    },
}

/// Pattern for case analysis and binding.
#[derive(Debug, Clone)]
pub enum Pattern {
    /// Variable binding: x : ty.
    Var(String, LocatedConstructor),
    /// Primitive literal pattern.
    Prim(Prim),
    /// Constructor pattern: C args of ty, optionally with nested sub-pattern.
    Constructor(
        DatatypeKind,
        PatternConstructor,
        Vec<LocatedConstructor>,
        Option<Box<LocatedPattern>>,
    ),
    /// Record pattern: { f1 = p1, … } with field types.
    Record(Vec<(String, LocatedPattern, LocatedConstructor)>),
}

/// A pattern with source location.
pub type LocatedPattern = Located<Pattern>;

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

/// Metadata for record field projection: the field type and rest type.
#[derive(Debug, Clone)]
pub struct FieldMeta {
    pub field: LocatedConstructor,
    pub rest: LocatedConstructor,
}

/// Metadata for record cut operations: the rest row type.
#[derive(Debug, Clone)]
pub struct RestMeta {
    pub rest: LocatedConstructor,
}

/// Metadata for case expressions: discriminant and result types.
#[derive(Debug, Clone)]
pub struct CaseMeta {
    pub disc: LocatedConstructor,
    pub result: LocatedConstructor,
}

/// Core expression after elaboration.
///
/// Mirrors the `Core.exp` datatype from `core.sml`.
#[derive(Debug, Clone)]
pub enum Expression {
    /// Primitive literal: 42, 3.14, "hello", 'x'.
    Prim(Prim),
    /// De Bruijn index (references lambda-bound variable).
    Rel(usize),
    /// Named value reference (globally unique id).
    Named(usize),
    Constructor(
        DatatypeKind,
        PatternConstructor,
        Vec<LocatedConstructor>,
        Option<Box<LocatedExpression>>,
    ),
    /// FFI value reference: `(module, name)`
    Ffi(String, String),
    /// FFI function call: `module.name(args)`
    FfiApp(String, String, Vec<(LocatedExpression, LocatedConstructor)>),
    /// Function application: f x.
    App(Box<LocatedExpression>, Box<LocatedExpression>),
    /// Lambda: fn x : dom => body (result type ran).
    Abs(
        String,
        LocatedConstructor,
        LocatedConstructor,
        Box<LocatedExpression>,
    ),
    /// Type application: e [c].
    CApp(Box<LocatedExpression>, LocatedConstructor),
    /// Type-level abstraction: fn α :: k => body.
    CAbs(String, Box<LocatedKind>, Box<LocatedExpression>),

    /// Kind-level abstraction: κ => body.
    KAbs(String, Box<LocatedExpression>),
    /// Kind application: e [k].
    KApp(Box<LocatedExpression>, Box<LocatedKind>),

    /// Record literal: { f1 = e1, … } with types.
    Record(Vec<(LocatedConstructor, LocatedExpression, LocatedConstructor)>),
    /// Field projection: e.#field.
    Field(Box<LocatedExpression>, LocatedConstructor, FieldMeta),
    /// Record concatenation: e1 ++ e2.
    Concat(
        Box<LocatedExpression>,
        LocatedConstructor,
        Box<LocatedExpression>,
        LocatedConstructor,
    ),
    /// Record cut: remove one field.
    Cut(Box<LocatedExpression>, LocatedConstructor, FieldMeta),
    /// Multi-field cut: remove several fields.
    CutMulti(Box<LocatedExpression>, LocatedConstructor, RestMeta),

    /// Case expression: match disc with arms.
    Case(
        Box<LocatedExpression>,
        Vec<(LocatedPattern, LocatedExpression)>,
        CaseMeta,
    ),

    /// Imperative write (transaction).
    Write(Box<LocatedExpression>),

    /// Closure (function id + captured environment).
    Closure(usize, Vec<LocatedExpression>),

    /// Let binding: let x : ty = e1 in e2.
    Let(
        String,
        LocatedConstructor,
        Box<LocatedExpression>,
        Box<LocatedExpression>,
    ),

    /// RPC call to server: ServerCall(id, args, result_ty, failure_mode).
    ServerCall(
        usize,
        Vec<LocatedExpression>,
        LocatedConstructor,
        FailureMode,
    ),
}

/// An expression with source location.
pub type LocatedExpression = Located<Expression>;

// ---------------------------------------------------------------------------
// Top-level declarations
// ---------------------------------------------------------------------------

/// Declaration of a datatype with its constructors.
#[derive(Debug, Clone)]
pub struct DatatypeDecl {
    pub name: String,
    pub id: usize,
    pub params: Vec<String>,
    pub constrs: Vec<(String, usize, Option<LocatedConstructor>)>,
}

/// Top-level declaration: types, values, tables, views, etc.
///
/// Mirrors the `Core.decl` datatype from `core.sml`.
#[derive(Debug, Clone)]
pub enum Declaration {
    /// Type/constructor synonym: con x (id) : k = c.
    Constructor(String, usize, LocatedKind, LocatedConstructor),
    /// Datatype declaration(s).
    Datatype(Vec<DatatypeDecl>),
    /// Value binding: val x (id) : ty = e.
    Val(
        String,
        usize,
        LocatedConstructor,
        LocatedExpression,
        String, /* comment */
    ),
    /// Mutually recursive value bindings.
    ValRec(Vec<(String, usize, LocatedConstructor, LocatedExpression, String)>),
    /// Export (page/action/RPC).
    Export(ExportKind, usize, bool /* has state */),
    /// SQL table declaration.
    Table {
        sql_name: String,
        id: usize,
        con: LocatedConstructor,
        sql_con: String,
        exp: LocatedExpression,
        pk_con: LocatedConstructor,
        pk_exp: LocatedExpression,
        unique_con: LocatedConstructor,
    },
    /// SQL sequence.
    Sequence(String, usize, String /* sql name */),
    /// SQL view.
    View(String, usize, String, LocatedExpression, LocatedConstructor),
    /// SQL index.
    Index(LocatedExpression, LocatedExpression),
    /// Database connection.
    Database(String),
    /// HTTP cookie.
    Cookie(String, usize, LocatedConstructor, String),
    /// CSS style class.
    Style(String, usize, String),
    /// Background task.
    Task(LocatedExpression, LocatedExpression),
    /// Access policy.
    Policy(LocatedExpression),
    /// Error handler.
    OnError(usize),
}

/// A declaration with source location.
pub type LocatedDeclaration = Located<Declaration>;

/// A Core file: a sequence of top-level declarations.
pub type File = Vec<LocatedDeclaration>;
