//! # Ur/Web Compiler Library
//!
//! This crate implements the Ur/Web compiler, translating Ur/Web source files (`.ur`)
//! through a series of intermediate representations into C and SQL.
//!
//! ## Compilation Pipeline
//!
//! 1. **Parse** (`parse`, `source`) — Lex and parse `.ur`/`.urs` files into surface syntax.
//!    Parsing is intentionally **strict**: LALRPOP must not emit conflicted tables;
//!    invalid tokens and broken parser invariants surface as errors rather than
//!    silent fixes. See [`parse::expr_langsec`] for the operator/application reference
//!    recognizer aligned with that discipline.
//! 2. **Elaborate** (`elaborated`) — Type inference, unification, resolve modules.
//! 3. **Explify** (`explicit`) — Make implicit arguments explicit, resolve modules.
//! 4. **Core** (`core`) — Simplify to Core AST (named bindings only).
//! 5. **Core passes** — Untangle, reduce, shake, specialize, effectize, various checks.
//! 6. **Mono** (`monomorphized`) — Monomorphize (eliminate polymorphism).
//! 7. **Mono passes** — Untangle, fuse, reduce, opt, shake, inline.
//! 8. **CJR** (`c_like_representation`) — Convert to C-like IR and emit C + SQL.
//!
//! See `ARCHITECTURE.md` for a detailed module reference.

/// Stack size (bytes) for the `ur-compile` worker thread (deep elaboration).
pub const COMPILE_THREAD_STACK_BYTES: usize = 512 * 1024 * 1024;

/// CJR AST — C-like IR, final stage before C emission.
pub mod c_like_representation;
/// Shared CLI helpers and templates.
pub mod cli_common;
/// Pipeline orchestration — wires all compilation phases.
pub mod compiler;
/// Shared compiler diagnostics (locks, ICE messages).
pub mod compiler_diagnostics;
/// Foundry-style verbosity and [`tracing`] setup for the batch driver.
pub mod compiler_tracing;
/// Project database choice (`ProjectDb`, SQL flavors, reserved backends, mangling, codegen gates).
pub mod db;
/// Canonical names for Basis-backed intrinsics (RPC, …) shared across compiler passes.
pub mod intrinsics;
/// Re-exports [`db`] for older `ur::dbms` paths.
pub mod dbms {
    pub use super::db::*;
}
/// Core AST — simplified IR before monomorphization.
pub mod core;
/// Datatype representation kind (Enum, Option, Default).
pub mod datatype_kind;
/// GDB/MI + Debug Adapter Protocol (`ur-debugger --dap`).
pub mod debugger;
/// Demo mode: build a combined demo application from a demo directory.
pub mod demo;
/// Localized diagnostic catalog (`DiagnosticId`, templates, [`DiagnosticPayload`]).
pub mod diagnostics;
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
/// Full-project parse + elaborate with overlay (LSP analysis).
pub mod lsp_analysis;
/// Semantic queries: hover, symbols, completion, tokens.
pub mod lsp_semantics;
/// Helpers for the `ur-lsp` binary (disconnect detection, etc.).
pub mod lsp_support;
/// Unused top-level value analysis for LSP warnings.
pub mod lsp_unused;
/// Workspace `.urp` discovery and URI → path for ur-lsp.
pub mod lsp_workspace;
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
/// Parse-validated whitespace layout for `ur-fmt` / LSP formatting.
pub mod ur_format;
/// Parser for `.urp` project files.
pub mod urp_parser;
