# Ur/Web Compiler Architecture

This document describes all modules in the Ur/Web compiler, how they interact, and the overall compilation pipeline. The compiler mirrors the structure of the original SML implementation.

## Compilation Pipeline Overview

The compiler transforms Ur/Web source code through several intermediate representations (IRs) before emitting C and SQL:

```
.ur/.urs source files
        │
        ▼
┌─────────────────┐
│  source         │  Surface syntax (parse tree)
│  parse          │  Lexer + LALRPOP parser
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  elaborated     │  Elaborated AST with type inference
│                 │  Unification variables, de Bruijn indices
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  explicit       │  Explicit AST — modules resolved, implicits solved
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  core           │  Core AST — simplified, before monomorphization
│  core::util     │  Traversal (map/fold/exists) over kinds, cons, exps, decls
│  core::env      │  Name resolution environment for Core
└────────┬────────┘
         │  [core_untangle, core_reduce_local, core_shake, core_reduce,
         │   core_especialize, core_unpoly, core_specialize, core_effectize,
         │   check_marshal, check_script, check_path, check_side, check_sig,
         │   check_dbmode, check_termination, check_nest]
         ▼
┌─────────────────┐
│  monomorphized  │  Monomorphised IR — no polymorphism, ready for codegen
│  mono::util     │  Traversal over mono types/patterns/expressions
│  mono::env      │  Environment for mono
└────────┬────────┘
         │  [mono_untangle, mono_fuse, mono_reduce, mono_opt, mono_shake, mono_inline]
         ▼
┌─────────────────┐
│  c_like_representation │  C-like IR — one step before C code
│                 │  Prepared statements, structs, simplified control flow
└────────┬────────┘
         │
         ▼
    C code + SQL
```

---

## Module Reference

### Foundation (shared types and utilities)

| Module | Purpose |
|--------|---------|
| **errors** | `Pos`, `Span`, `Located<T>`, `CompileError`, `ErrorReporter` — source locations and error handling. `Located` pairs any AST node with a `Span` for error messages. |
| **prim** | `Prim` (Int, Float, String, Char) — primitive literals. `StringMode` (Normal, Html) for string escaping. Used in all IRs. |
| **datatype_kind** | `DatatypeKind` (Enum, Option, Default) — classifies how a datatype is represented at runtime. Enum = all nullary; Option = exactly None+Some; Default = general. |
| **export** | `Effect` (ReadOnly, ReadCookieWrite, ReadWrite), `ExportKind` (Link, Action, Rpc, Extern) — annotations for exported pages/actions. |
| **settings** | Job configuration: URL prefix, database, FFI mappings, effectful annotations, SQL mangling, etc. Parsed from `.urp` files. |
| **fileio** | File I/O: `open_text`, `open_binary`, `resolve`, `most_recent_mod_time` — tracks modification times for incremental builds. |

### Parsing

| Module | Purpose |
|--------|---------|
| **parse** | Entry points `parse_ur` (`.ur` files) and `parse_urs` (`.urs` sig files). Calls LALRPOP-generated parser. |
| **parse::lexer** | Lexer (Logos) — tokens for identifiers, keywords, operators, literals. |
| **source** | `source::File` — surface syntax AST. Kinds, constructors, expressions, signatures. Mirrors `source.sml`. |

### Elaboration (type inference)

| Module | Purpose |
|--------|---------|
| **elaborated** | Elaborated AST with unification variables (`KUnif`, `CUnif`, `EUnif`), de Bruijn indices, `ModProj` for modules. Type inference fills in unknowns. Mirrors `elab.sml`. |
| **elaborated::util** | Traversal over elaborated kinds, constructors, expressions, declarations. |
| **elaborated::env** | Environment with relative and named bindings for type checking. |
| **elaborated::mod_db** | Module database for resolving qualified names. |
| **elaborated::error** | Elaboration-specific error types. |
| **elaborated::disjoint** | Disjointness constraints for records. |
| **elaborated::ops** | Operations on elaborated AST. |

### Explification (explicit AST)

| Module | Purpose |
|--------|---------|
| **explicit** | Explicit AST — modules resolved, implicits turned into explicits. No unification variables. Between elaborated and core. Mirrors `expl.sml`. |
| **explicit::util** | Traversal over explicit AST. |
| **explicit::env** | Environment for explicit. |

### Core (simplified IR)

| Module | Purpose |
|--------|---------|
| **core** | Core AST — after elaboration, before monomorphization. All names are globally-unique integers. FFI types/values use `Ffi(module, name)`. Types: `LocatedKind`, `LocatedConstructor`, `LocatedPattern`, `LocatedExpression`, `LocatedDeclaration`. Mirrors `core.sml`. |
| **core::util** | `classify_datatype`, `Binder`, and traversal: `kind::`, `constructor::`, `expression::`, `declaration::`, `file::`. Mirrors `core_util.sml`. |
| **core::env** | `Env` — named constructor/expression/datatype bindings. `decl_binds`, `bind_file`. `pat_binds_n`, `pat_binds_list`. Mirrors `core_env.sml`. |

### Monomorphization

| Module | Purpose |
|--------|---------|
| **monomorphized** | Mono AST — no polymorphism. Types are `Typ` (Fun, Record, Datatype, Ffi, Option, List, Source, Signal). Mirrors `mono.sml`. |
| **monomorphized::util** | Traversal over monomorphized types, patterns, expressions. |
| **monomorphized::env** | Environment for monomorphized. |

### C-like IR (code generation)

| Module | Purpose |
|--------|---------|
| **c_like_representation** | C-like IR. `Typ` uses struct ids, `PreparedQuery`, `PreparedDml`, `PreparedNextval` for SQL. Emits C code and SQL. Mirrors `cjr.sml`. |

### Pipeline orchestration

| Module | Purpose |
|--------|---------|
| **compiler** | `Job` (from `.urp`), `parse_urp`, `parse_sources`, `elaborate`, `explify`, `core_*`, `mono_*`, `cjr_print`, `sql_generate`, `compile` — wires all 24 phases together. Mirrors `compiler.sml`. |

---

## Core AST in Detail

The Core AST (`core::`) is the central simplified representation:

- **Kind**: `Type`, `Arrow`, `Name`, `Record`, `Unit`, `Tuple`, `Rel` (de Bruijn), `Fun`
- **Con** (constructor/type): `TFun`, `TCFun`, `TRecord`, `Rel`, `Named`, `Ffi`, `App`, `Abs`, `KAbs`, `KApp`, `TKFun`, `Name`, `Record`, `Concat`, `Map`, `Unit`, `Tuple`, `Proj`
- **Pat**: `Var`, `Prim`, `Con`, `Record`
- **Exp**: `Prim`, `Rel`, `Named`, `Con`, `Ffi`, `FfiApp`, `App`, `Abs`, `CApp`, `CAbs`, `KAbs`, `KApp`, `Record`, `Field`, `Concat`, `Cut`, `CutMulti`, `Case`, `Write`, `Closure`, `Let`, `ServerCall`
- **Decl**: `Con`, `Datatype`, `Val`, `ValRec`, `Export`, `Table`, `Sequence`, `View`, `Index`, `Database`, `Cookie`, `Style`, `Task`, `Policy`, `OnError`

All Core bindings use globally-unique `usize` ids. De Bruijn indices (`Rel`) appear only inside `CAbs`/`KAbs`/`Abs` for locally-bound variables.

---

## Testing

- **Unit and integration tests**: `cargo test`
- **Mutation testing**: `cargo mutants` (injects small bugs and checks that tests catch them)
- **Coverage (lcov, 100% line)**: `./scripts/coverage-rust.sh` — generates `lcov.info` and fails if line coverage is below 100%. Requires `cargo install cargo-llvm-cov` (Rust 1.87+; on Rust 1.81 use `cargo install cargo-llvm-cov --version 0.6.21`).

cargo-mutants requires Rust 1.87+ to install. With Rust 1.81, use `cargo +1.87 mutants`.
