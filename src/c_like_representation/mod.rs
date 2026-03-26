//! CJR AST — C-like intermediate representation.
//!
//! One step before C emission. Types use struct ids, prepared statements for
//! SQL. Simplified control flow and data representation.
//!
//! Mirrors `cjr.sml`.
//!
//! **Style:** new/edited Rust here follows [README.md](../../README.md) Rust code style (exceptions documented there).

pub mod check_nest;
pub mod cjr_print;
pub mod cjrize;
pub mod db_drivers;
mod native_db_runtime;
pub mod prepare;
pub mod relational_sql_runtime;
pub mod sql_generate;

use crate::datatype_kind::DatatypeKind;
use crate::error_types::Located;
use crate::export::ExportKind;
use crate::monomorphized::{DbMode, IndexMode, Sidedness};
use crate::primitives::Prim;
use crate::settings::FailureMode;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A shared (lazily-filled) datatype descriptor (for recursive types).
pub type DatatypeRef = std::sync::Arc<std::sync::Mutex<Vec<(String, usize, Option<LocTyp>)>>>;

#[derive(Debug, Clone)]
pub enum Typ {
    Fun(Box<LocTyp>, Box<LocTyp>),
    /// Index into the struct table (DStruct declarations).
    Record(usize),
    Datatype(DatatypeKind, usize, DatatypeRef),
    Ffi(String, String),
    Option(Box<LocTyp>),
    List(Box<LocTyp>, usize /* struct id for the list node */),
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
// Prepared statement stubs
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct PreparedQuery {
    pub id: usize,
    pub query: String,
    pub nested: bool,
}

#[derive(Debug, Clone)]
pub struct PreparedDml {
    pub id: usize,
    pub dml: String,
}

#[derive(Debug, Clone)]
pub struct PreparedNextval {
    pub id: usize,
    pub query: String,
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct QueryMeta {
    pub exps: Vec<(String, LocTyp)>,
    pub tables: Vec<(String, Vec<(String, LocTyp)>)>,
    pub rnum: usize,
    pub state: LocTyp,
    pub query: Box<LocExp>,
    pub body: Box<LocExp>,
    pub initial: Box<LocExp>,
    pub prepared: Option<PreparedQuery>,
}

#[derive(Debug, Clone)]
pub struct DmlMeta {
    pub dml: Box<LocExp>,
    pub prepared: Option<PreparedDml>,
    pub mode: FailureMode,
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
    App(Box<LocExp>, Vec<LocExp>),

    Unop(String, Box<LocExp>),
    Binop(String, Box<LocExp>, Box<LocExp>),

    Record(usize, Vec<(String, LocExp)>),
    Field(Box<LocExp>, String),

    Case(Box<LocExp>, Vec<(LocPat, LocExp)>, CaseMeta),

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

    Query(QueryMeta),
    Dml(DmlMeta),
    Nextval {
        seq: Box<LocExp>,
        prepared: Option<PreparedNextval>,
    },
    Setval {
        seq: Box<LocExp>,
        count: Box<LocExp>,
    },
    Uurlify(Box<LocExp>, LocTyp, bool),
}

pub type LocExp = Located<Exp>;

// ---------------------------------------------------------------------------
// Task kinds
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Task {
    Initialize,
    ClientLeaves,
    Periodic(i64),
}

// ---------------------------------------------------------------------------
// Top-level declarations
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct DatatypeDecl {
    pub kind: DatatypeKind,
    pub name: String,
    pub id: usize,
    pub constrs: Vec<(String, usize, Option<LocTyp>)>,
}

#[derive(Debug, Clone)]
pub enum Decl {
    /// Struct definition (fields laid out flat).
    Struct(usize, Vec<(String, LocTyp)>),
    Datatype(Vec<DatatypeDecl>),
    DatatypeForward(DatatypeKind, String, usize),
    Val(String, usize, LocTyp, LocExp),
    Fun(String, usize, Vec<(String, LocTyp)>, LocTyp, LocExp),
    FunRec(Vec<(String, usize, Vec<(String, LocTyp)>, LocTyp, LocExp)>),

    Table(
        String,
        Vec<(String, LocTyp)>,
        String,                /* SQL */
        Vec<(String, String)>, /* constraints */
    ),
    Sequence(String),
    View(String, Vec<(String, LocTyp)>, String /* SQL */),
    Index(String /* table */, Vec<(String, IndexMode)>),
    Database {
        name: String,
        expunge: usize,
        initialize: usize,
        uses_similar: bool,
    },
    PreparedStatements(Vec<(String, usize)>),

    JavaScript(String),
    Cookie(String),
    Style(String),

    Task(
        Task,
        String, /* arg1 name */
        String, /* arg2 name */
        LocExp,
    ),
    OnError(usize),
}

pub type LocDecl = Located<Decl>;

/// Export entry in the CJR file.
pub type ExportEntry = (
    ExportKind,
    String, /* path */
    usize,  /* id */
    Vec<LocTyp>,
    LocTyp,
    Sidedness,
    DbMode,
    bool, /* has state */
);

pub type File = (Vec<LocDecl>, Vec<ExportEntry>);
