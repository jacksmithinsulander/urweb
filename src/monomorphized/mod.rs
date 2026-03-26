//! Mono AST — monomorphised intermediate representation.
//!
//! Polymorphism eliminated. Types are `Typ`: Fun, Record, Datatype, Ffi,
//! Option, List, Source, Signal. Used for code generation.
//!
//! Mirrors `mono.sml`.
//!
//! **Style:** new/edited Rust here follows [README.md](../../README.md) Rust code style (exceptions documented there).

pub mod db_mode_check;
pub mod endpoints;
pub mod environment;
pub mod filecache;
pub mod fuse;
pub mod iflow;
pub mod jscomp;
pub mod mono_opt;
pub mod mono_reduce;
pub mod mono_shake;
pub mod monoize;
pub mod name_js;
pub mod path_check;
pub mod script_check;
pub mod side_check;
pub mod sig_check;
pub mod sqlcache;
pub mod untangle;
pub mod utilities;

use crate::datatype_kind::DatatypeKind;
use crate::error_types::Located;
use crate::export::{Effect, ExportKind};
use crate::primitives::Prim;
use crate::settings::FailureMode;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Typ {
    Fun(Box<LocTyp>, Box<LocTyp>),
    Record(Vec<(String, LocTyp)>),
    Datatype(usize, DatatypeRef),
    Ffi(String, String),
    Option(Box<LocTyp>),
    List(Box<LocTyp>),
    Source,
    Signal(Box<LocTyp>),
}

/// Shared mutable reference to a datatype definition (for recursive types).
pub type DatatypeRef = std::sync::Arc<std::sync::Mutex<DatatypeDef>>;

#[derive(Debug, Clone)]
pub struct DatatypeDef {
    pub kind: DatatypeKind,
    pub constrs: Vec<(String, usize, Option<LocTyp>)>,
}

pub type LocTyp = Located<Typ>;

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum PatCon {
    Var(usize),
    Ffi {
        module: String,
        datatyp: String,
        con: String,
        arg: Option<LocTyp>,
    },
}

#[derive(Debug, Clone)]
pub enum Pat {
    Var(String, LocTyp),
    Prim(Prim),
    Con(DatatypeKind, PatCon, Option<Box<LocPat>>),
    Record(Vec<(String, LocPat, LocTyp)>),
    None(LocTyp),
    Some(LocTyp, Box<LocPat>),
}

pub type LocPat = Located<Pat>;

// ---------------------------------------------------------------------------
// JavaScript compilation mode
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum JavaScriptMode {
    Attribute,
    Script,
    Source(LocTyp),
}

// ---------------------------------------------------------------------------
// Effect / export (re-exported from shared modules)
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinopIntness {
    Int,
    NotInt,
}

#[derive(Debug, Clone)]
pub struct QueryMeta {
    pub exps: Vec<(String, LocTyp)>,
    pub tables: Vec<(String, Vec<(String, LocTyp)>)>,
    pub state: LocTyp,
    pub query: Box<LocExp>,
    pub body: Box<LocExp>,
    pub initial: Box<LocExp>,
}

#[derive(Debug, Clone)]
pub struct CaseMeta {
    pub disc: LocTyp,
    pub result: LocTyp,
}

#[derive(Debug, Clone)]
pub enum Exp {
    Prim(Prim),
    Rel(usize),
    Named(usize),
    Con(DatatypeKind, PatCon, Option<Box<LocExp>>),
    None(LocTyp),
    Some(LocTyp, Box<LocExp>),
    Ffi(String, String),
    FfiApp(String, String, Vec<(LocExp, LocTyp)>),
    App(Box<LocExp>, Box<LocExp>),
    Abs(String, LocTyp, LocTyp, Box<LocExp>),

    Unop(String, Box<LocExp>),
    Binop(BinopIntness, String, Box<LocExp>, Box<LocExp>),

    Record(Vec<(String, LocExp, LocTyp)>),
    Field(Box<LocExp>, String),

    Case(Box<LocExp>, Vec<(LocPat, LocExp)>, CaseMeta),

    Strcat(Box<LocExp>, Box<LocExp>),

    Error(Box<LocExp>, LocTyp),
    ReturnBlob {
        blob: Option<Box<LocExp>>,
        mime_type: Box<LocExp>,
        t: LocTyp,
    },
    Redirect(Box<LocExp>, LocTyp),

    Write(Box<LocExp>),
    Seq(Box<LocExp>, Box<LocExp>),
    Let(String, LocTyp, Box<LocExp>, Box<LocExp>),

    Closure(usize, Vec<LocExp>),

    Query(QueryMeta),
    Dml(Box<LocExp>, FailureMode),
    Nextval(Box<LocExp>),
    Setval(Box<LocExp>, Box<LocExp>),

    Uurlify(Box<LocExp>, LocTyp, bool),

    JavaScript(JavaScriptMode, Box<LocExp>),

    SignalReturn(Box<LocExp>),
    SignalBind(Box<LocExp>, Box<LocExp>),
    SignalSource(Box<LocExp>),

    ServerCall(Box<LocExp>, LocTyp, Effect, FailureMode),
    Recv(Box<LocExp>, LocTyp),
    Sleep(Box<LocExp>),
    Spawn(Box<LocExp>),
}

pub type LocExp = Located<Exp>;

// ---------------------------------------------------------------------------
// Policies
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Policy {
    Client(LocExp),
    Insert(LocExp),
    Delete(LocExp),
    Update(LocExp),
    Sequence(LocExp),
}

// ---------------------------------------------------------------------------
// Index modes
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IndexMode {
    Equality,
    Trigram,
    Skipped,
}

// ---------------------------------------------------------------------------
// Sidedness / DB access mode (for exports)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sidedness {
    ServerOnly,
    ServerAndPull,
    ServerAndPullAndPush,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DbMode {
    NoDb,
    OneQuery,
    AnyDb,
}

// ---------------------------------------------------------------------------
// Top-level declarations
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct DatatypeDecl {
    pub name: String,
    pub id: usize,
    pub constrs: Vec<(String, usize, Option<LocTyp>)>,
}

#[derive(Debug, Clone)]
pub enum Decl {
    Datatype(Vec<DatatypeDecl>),
    Val(String, usize, LocTyp, LocExp, String),
    ValRec(Vec<(String, usize, LocTyp, LocExp, String)>),
    Export(ExportKind, String, usize, Vec<LocTyp>, LocTyp, bool),

    Table(String, Vec<(String, LocTyp)>, LocExp, LocExp),
    Sequence(String),
    View(String, Vec<(String, LocTyp)>, LocExp),
    Index(String, Vec<(String, IndexMode)>),
    Database {
        name: String,
        expunge: usize,
        initialize: usize,
        uses_similar: bool,
    },

    JavaScript(String),

    Cookie(String),
    Style(String),

    Task(LocExp, LocExp),

    Policy(Policy),
    OnError(usize),
}

pub type LocDecl = Located<Decl>;

/// An export record attached to the file: `(id, sidedness, dbmode)`.
pub type ExportInfo = (usize, Sidedness, DbMode);

pub type File = (Vec<LocDecl>, Vec<ExportInfo>);
