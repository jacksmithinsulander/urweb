//! # Ur/Web Compiler Library
//!
//! This crate implements the Ur/Web compiler, translating Ur/Web source files (`.ur`)
//! through a series of intermediate representations into C and SQL.
//!
//! ## Compilation Pipeline
//!
//! 1. **Parse** (`parse`, `source`) — Lex and parse `.ur`/`.urs` files into surface syntax.
//! 2. **Elaborate** (`elaborated`) — Type inference, unification, resolve modules.
//! 3. **Explify** (`explicit`) — Make implicit arguments explicit, resolve modules.
//! 4. **Core** (`core`) — Simplify to Core AST (named bindings only).
//! 5. **Core passes** — Untangle, reduce, shake, specialize, effectize, various checks.
//! 6. **Mono** (`monomorphized`) — Monomorphize (eliminate polymorphism).
//! 7. **Mono passes** — Untangle, fuse, reduce, opt, shake, inline.
//! 8. **CJR** (`c_like_representation`) — Convert to C-like IR and emit C + SQL.
//!
//! See `ARCHITECTURE.md` for a detailed module reference.

/// CJR AST — C-like IR, final stage before C emission.
pub mod c_like_representation;
/// Shared CLI helpers and templates.
pub mod cli_common;
/// Pipeline orchestration — wires all compilation phases.
pub mod compiler;
/// Core AST — simplified IR before monomorphization.
pub mod core;
/// Datatype representation kind (Enum, Option, Default).
pub mod datatype_kind;
/// Elaborated AST — after type inference, with unification variables.
pub mod elaborated;
/// Errors, spans, and source locations.
pub mod error_types;
/// Explicit AST — modules resolved, implicits made explicit.
pub mod explicit;
/// Effect and export annotations for pages/actions.
pub mod export;
/// File I/O and path resolution.
pub mod file_io;
/// Mono AST — monomorphised IR for code generation.
pub mod monomorphized;
/// Parser (lexer + LALRPOP grammar).
pub mod parse;
/// Primitive literals (Int, Float, String, Char).
pub mod primitives;
/// Compilation settings (from .urp files).
pub mod settings;
/// Source AST — surface syntax from the parser.
pub mod source;
/// Parser for `.urp` project files.
pub mod urp_parser;
