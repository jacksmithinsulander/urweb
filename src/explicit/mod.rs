//! Explicit elaborated AST — between elab and core.
//!
//! All module references resolved, implicit arguments made explicit. No
//! unification variables. Simplified form before Core.
//!
//! Mirrors `expl.sml`.

pub mod environment;
pub mod utilities;

use crate::datatype_kind::DatatypeKind;
use crate::error_types::Located;
use crate::primitives::Prim;
use crate::source::FfiMode;

// ---------------------------------------------------------------------------
// Kinds
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Kind {
    Type,
    Arrow(Box<LocatedKind>, Box<LocatedKind>),
    Name,
    Unit,
    Tuple(Vec<LocatedKind>),
    Record(Box<LocatedKind>),

    Rel(usize),
    Fun(String, Box<LocatedKind>),
}

pub type LocatedKind = Located<Kind>;

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Constructor {
    TFun(Box<LocatedConstructor>, Box<LocatedConstructor>),
    TCFun(String, Box<LocatedKind>, Box<LocatedConstructor>),
    TRecord(Box<LocatedConstructor>),

    Rel(usize),
    Named(usize),
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
    CAbs(String, Box<LocatedKind>, Box<LocatedExpression>),

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

    Write(Box<LocatedExpression>),

    Let(
        String,
        LocatedConstructor,
        Box<LocatedExpression>,
        Box<LocatedExpression>,
    ),
}

pub type LocatedExpression = Located<Expression>;

// ---------------------------------------------------------------------------
// Signature items & signatures
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
    Signature(String, usize, LocatedSignature),
    Structure(String, usize, LocatedSignature),
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
}

pub type LocatedStructure = Located<Structure>;

pub type File = Vec<LocatedDeclaration>;
