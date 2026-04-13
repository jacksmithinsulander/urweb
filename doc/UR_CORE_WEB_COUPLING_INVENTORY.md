# Ur core vs Ur/Web — compiler coupling inventory

This document classifies where the Rust compiler knows about full-stack Ur/Web behavior versus plain ML-style Ur surface semantics. It supports the `LanguageCompilationProfile` split (`ur-web` default, `ur-core` experimental).

## Legend

- **Intrinsic (I)**: Behavior tied to a stable FFI or runtime contract; a future “intrinsic registry” should own these (canonical module/name pairs or resolved symbol ids).
- **Removable in ur-core (R)**: Gated or skipped when `LanguageCompilationProfile::UrCore` is active, or rejected at parse/validation.
- **Shared core (S)**: General-purpose compiler logic; not web-specific.

## Parse and surface

| Location | What | Class |
|----------|------|-------|
| [`src/parse/lexical_analyzer.rs`](../src/parse/lexical_analyzer.rs) `XmlAwareLexer`, `<xmlid>` / XML modes | XML literals and tag soup | R (XML disabled in ur-core user modules) |
| Same, `table` keyword | SQL `table` declarations | S (keyword stays; ur-core rejects `Decl::Table` in validation) |
| [`src/parse/grammar.lalrpop`](../src/parse/grammar.lalrpop) | XML productions | R |
| [`src/parse/xml_helpers.rs`](../src/parse/xml_helpers.rs) | Desugar tags, Basis FFI names in XML | I |
| [`src/parse/sql_compat.rs`](../src/parse/sql_compat.rs) | SQL placeholder repair | I |
| [`src/source/mod.rs`](../src/source/mod.rs) `Decl::{Export,Table,…}` | Top-level web/DB directives | R (rejected in ur-core user modules) |

## Elaboration and explification

| Location | What | Class |
|----------|------|-------|
| [`src/elaborated/elaborate.rs`](../src/elaborated/elaborate.rs) (many `Basis.*` paths) | Type checking against prelude / FFI | I / S |
| [`src/explicit/corify.rs`](../src/explicit/corify.rs) `get_page`, `transactify` | `transaction` / `page` shapes via Basis | I |

## Core IR

| Location | What | Class |
|----------|------|-------|
| [`src/core/rpc_elaboration.rs`](../src/core/rpc_elaboration.rs) | `Basis.rpc` / `Basis.tryRpc` → `EServerCall` | I (names centralized in [`src/intrinsics/web_ffi.rs`](../src/intrinsics/web_ffi.rs)) |
| [`src/core/export_tagging.rs`](../src/core/export_tagging.rs) | Export paths, Basis | I |
| [`src/core/effect_analysis.rs`](../src/core/effect_analysis.rs) | Effects, Basis | I |
| [`src/core/marshal_check.rs`](../src/core/marshal_check.rs) | Marshalling, Basis paths | I |
| [`src/core/global_reduction.rs`](../src/core/global_reduction.rs) | Monad / Basis helpers | I |

## Monomorphization and JS

| Location | What | Class |
|----------|------|-------|
| [`src/monomorphized/mono_opt.rs`](../src/monomorphized/mono_opt.rs) | `htmlify*`, `Basis.strcat`, writers | I |
| [`src/monomorphized/jscomp.rs`](../src/monomorphized/jscomp.rs) | Client JS, `urweb.js` | R (pass skipped when profile disables JS emission) |
| [`src/monomorphized/fuse.rs`](../src/monomorphized/fuse.rs) | `Basis.string` heuristics | I |
| [`src/monomorphized/side_check.rs`](../src/monomorphized/side_check.rs) | `Basis.getenv` | I |

## CJR, SQL, settings

| Location | What | Class |
|----------|------|-------|
| [`src/c_like_representation/cjr_print.rs`](../src/c_like_representation/cjr_print.rs), `cjrize.rs`, `prepare.rs`, `sql_generate.rs` | C + SQL emission, Basis C types | I |
| [`src/settings.rs`](../src/settings.rs) `basis_ffi_set`, `basis_js_map` | Wired Basis FFI classification | I |

## Pipeline orchestration

| Location | What | Class |
|----------|------|-------|
| [`src/compiler.rs`](../src/compiler.rs) | Injects `Decl::Export` for last module; `core_rpcify`; `js_compile` | I / R |
| [`src/db/`](../src/db/) | DB backend, LangSec parse profile | S / I |

## Ur-core profile behavior (summary)

- **Lexer**: User `.ur` modules use `XmlAwareLexer` with XML markup disabled so `<tag>` is not interpreted as XML.
- **Validation**: User modules and signatures reject web-only declarations (`export`, `table`, `cookie`, …).
- **Project glue**: No auto-`export` of the last source module; no `Decl::Database` injection from the job when ur-core; no `UrwebNative` shim injection.
- **Batch compile**: Full `compile` / `compile_to_outputs` abort with a catalog diagnostic until a dedicated ur-core codegen path exists.
- **Passes**: `core_rpcify` no-op; `js_compile` returns no script work under ur-core.

Further work: extend `_catalog_cli.py` help text as flags grow; move more `Basis.*` string checks into [`src/intrinsics/web_ffi.rs`](../src/intrinsics/web_ffi.rs) or a generated intrinsic table.
