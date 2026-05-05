//! Source AST — the surface syntax of Ur/Web programs.
//!
//! Output of the parser. Contains kinds, constructors, expressions, patterns,
//! and signatures in their surface form (qualified names, wildcards, etc.).
//! All nodes are `Located<T>` for error reporting.
//!
//! Mirrors `source.sml` one-to-one.
//!
//! **Style:** new/edited Rust here follows [README.md](../../README.md) Rust code style (exceptions documented there).

mod span_attach;

pub(crate) use span_attach::attach_file_label_to_signature_items;
pub(crate) use span_attach::attach_file_label_to_source_file;

use crate::error_types::Located;
use crate::primitives::Prim;

// ---------------------------------------------------------------------------
// Kinds
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Kind {
    /// *
    Type,
    /// k1 → k2
    Arrow(Box<LocKind>, Box<LocKind>),
    /// `Name` (singleton kind for field names)
    Name,
    /// {k} (row kind)
    Record(Box<LocKind>),
    /// Unit kind
    Unit,
    /// (k1, …, kN) tuple kind
    Tuple(Vec<LocKind>),
    /// Wildcard (to be inferred)
    Wild,
    /// Kind-level abstraction: `fun α :: k`
    Fun(String, Box<LocKind>),
    /// Kind variable
    Var(String),
}

pub type LocKind = Located<Kind>;

// ---------------------------------------------------------------------------
// Constructors (types at kind `*`, but also type-level computations)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Explicitness {
    Explicit,
    Implicit,
}

#[derive(Debug, Clone)]
pub enum Con {
    /// Type annotation: `t : k`
    Annot(Box<LocCon>, Box<LocKind>),

    /// Function type: `t1 → t2`
    TFun(Box<LocCon>, Box<LocCon>),
    /// Constructor-level function: `(α :: k) → t` or `[α :: k] → t`
    TCFun(Explicitness, String, Box<LocKind>, Box<LocCon>),
    /// Record type: `{c}`
    TRecord(Box<LocCon>),
    /// Disjointness constraint: `[c1 ~ c2] => t`
    TDisjoint(Box<LocCon>, Box<LocCon>, Box<LocCon>),

    /// Variable reference (possibly qualified): `M.x`
    Var(Vec<String>, String),
    /// Application: `c1 c2`
    App(Box<LocCon>, Box<LocCon>),
    /// Constructor-level lambda: `fn α [:: k] => c`
    Abs(String, Option<Box<LocKind>>, Box<LocCon>),

    /// Kind-level abstraction
    KAbs(String, Box<LocCon>),
    /// Kind-universal type: `κ → c`
    TKFun(String, Box<LocCon>),

    /// Field name literal: `#Foo`
    Name(String),

    /// Row literal: `[f1 = c1, …]`
    Record(Vec<(LocCon, LocCon)>),
    /// Row concatenation: `c1 ++ c2`
    Concat(Box<LocCon>, Box<LocCon>),
    /// `map` constructor (fold over rows)
    Map,

    /// Unit constructor `()`
    Unit,

    /// Tuple: `(c1, …, cN)`
    Tuple(Vec<LocCon>),
    /// Projection from a tuple: `c.N`
    Proj(Box<LocCon>, usize),

    /// Anonymous sum type: `[Tag1 | Tag2 of Con1 * Con2 | ...]`
    ///
    /// Each arm is `(tag_name, arg_constructors)`. Zero arg constructors means
    /// a nullary (unit-payload) constructor arm.
    Enum(Vec<(String, Vec<LocCon>)>),

    /// Wildcard to be inferred (annotated with the expected kind)
    Wild(Box<LocKind>),
}

pub type LocCon = Located<Con>;

// ---------------------------------------------------------------------------
// Inference mode (for variable references in expressions)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Inference {
    Infer,
    DontInfer,
    TypesOnly,
}

// ---------------------------------------------------------------------------
// Signature items
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum SgnItem {
    ConAbs(String, Box<LocKind>),
    Con(String, Option<Box<LocKind>>, LocCon),
    Datatype(Vec<DatatypeDecl>),
    DatatypeImp(String, Vec<String>, String),
    Val(String, LocCon),
    Table(String, LocCon, LocExp, LocExp),
    Str(String, LocSgn),
    Sgn(String, LocSgn),
    Include(LocSgn),
    Constraint(LocCon, LocCon),
    ClassAbs(String, Box<LocKind>),
    Class(String, Box<LocKind>, LocCon),
    /// Functor in a signature: `functor Name(Arg : Sgn) : Sgn`
    Functor(String, String, Box<LocSgn>, Box<LocSgn>),
}

pub type LocSgnItem = Located<SgnItem>;

/// A single datatype declaration inside `datatype d and …`.
#[derive(Debug, Clone)]
pub struct DatatypeDecl {
    pub name: String,
    pub params: Vec<String>,
    pub constrs: Vec<(String, Option<LocCon>)>,
}

// ---------------------------------------------------------------------------
// Signatures
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Sgn {
    Const(Vec<LocSgnItem>),
    Var(String),
    Fun(String, Box<LocSgn>, Box<LocSgn>),
    Where(Box<LocSgn>, Vec<String>, String, LocCon),
    Proj(String, Vec<String>, String),
}

pub type LocSgn = Located<Sgn>;

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Pat {
    Var(String),
    Prim(Prim),
    Con(Vec<String>, String, Option<Box<LocPat>>),
    Record(Vec<(String, LocPat)>, bool /* open? */),
    Annot(Box<LocPat>, LocCon),
}

pub type LocPat = Located<Pat>;

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Exp {
    Annot(Box<LocExp>, LocCon),

    Prim(Prim),
    Var(Vec<String>, String, Inference),
    App(Box<LocExp>, Box<LocExp>),
    Abs(String, Option<LocCon>, Box<LocExp>),
    CApp(Box<LocExp>, LocCon),
    CAbs(Explicitness, String, Box<LocKind>, Box<LocExp>),
    Disjoint(LocCon, LocCon, Box<LocExp>),
    DisjointApp(Box<LocExp>),

    KAbs(String, Box<LocExp>),

    Record(Vec<(LocCon, LocExp)>, bool /* spread? */),
    Field(Box<LocExp>, LocCon),
    Concat(Box<LocExp>, Box<LocExp>),
    Cut(Box<LocExp>, LocCon),
    CutMulti(Box<LocExp>, LocCon),

    Wild,
    Hole,

    Case(Box<LocExp>, Vec<(LocPat, LocExp)>),

    Let(Vec<LocEDecl>, Box<LocExp>),

    /// Binary infix operator: `e1 op e2`
    /// The operator is the textual name ("+", "-", "*", "/", "%", "^",
    /// "=", "<>", "<", ">", "<=", ">=", "::")
    Infix(String, Box<LocExp>, Box<LocExp>),
}

pub type LocExp = Located<Exp>;

// ---------------------------------------------------------------------------
// Local declarations (inside `let`)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum EDecl {
    Val(LocPat, LocExp),
    ValRec(Vec<(String, Option<LocCon>, LocExp)>),
}

pub type LocEDecl = Located<EDecl>;

// ---------------------------------------------------------------------------
// FFI mode annotation
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum FfiMode {
    Effectful,
    BenignEffectful,
    ClientOnly,
    ServerOnly,
    JsFunc(String),
}

// ---------------------------------------------------------------------------
// Top-level declarations
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Decl {
    Con(String, Option<Box<LocKind>>, LocCon),
    Datatype(Vec<DatatypeDecl>),
    DatatypeImp(String, Vec<String>, String),
    Val(LocPat, LocExp),
    ValRec(Vec<(String, Option<LocCon>, LocExp)>),
    Sgn(String, LocSgn),
    Str(
        String,
        Option<LocSgn>,
        Option<std::time::SystemTime>,
        LocStr,
        bool, /* from -root? */
    ),
    FfiStr(String, LocSgn, Option<std::time::SystemTime>),
    Open(String, Vec<String>),
    Constraint(LocCon, LocCon),
    OpenConstraints(String, Vec<String>),
    Export(LocStr),
    Table(String, LocCon, LocExp, LocExp),
    Sequence(String),
    View(String, LocExp),
    Index(LocExp, LocExp, Option<LocCon>),
    Database(String),
    Cookie(String, LocCon),
    Style(String),
    Task(LocExp, LocExp),
    Policy(LocExp),
    OnError(String, Vec<String>, String),
    Ffi(String, Vec<FfiMode>, LocCon),
    /// Open with a functor application: `open Foo.Make(struct...end)`
    OpenStr(LocStr),
}

pub type LocDecl = Located<Decl>;

// ---------------------------------------------------------------------------
// Module structures
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Str {
    Const(Vec<LocDecl>),
    Var(String),
    Proj(Box<LocStr>, String),
    Fun(String, LocSgn, Option<LocSgn>, Box<LocStr>),
    App(Box<LocStr>, Box<LocStr>),
}

pub type LocStr = Located<Str>;

// ---------------------------------------------------------------------------
// A whole source file
// ---------------------------------------------------------------------------

pub type File = Vec<LocDecl>;
