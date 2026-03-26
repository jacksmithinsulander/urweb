# NatSpec-style documentation for Ur/Web

This document is a **design** for structured documentation comments in Ur/Web source, inspired by [Solidity NatSpec](https://docs.soliditylang.org/en/latest/natspec-format.html). Nothing here is final until the parser, AST, LSP, and optional doc generator implement it.

## Goals

- **User-facing** and **developer-facing** text attached to declarations (`val`, `fun`, `con`, `datatype`, signatures, page handlers, RPCs, tables, etc.).
- **Tooling:** hover text and completion docs in **`ur-lsp`**; optional **`ur doc`** (or similar) emitting HTML or Markdown for a package—aligned with Cargo / Foundry-style workflows.
- **LangSec-friendly** parsing: doc blocks are a **strict** grammar; unknown tags or malformed references produce **warnings** or errors (exact policy TBD).

## Syntax (proposal)

Use the existing nestable comment delimiter with a distinct prefix so ordinary `(* ... *)` comments stay unchanged:

```ur
(*|
  Create a greeting page for the given user name.

  @notice Shown to end users in the page title.
  @param name Display name; must be non-empty in valid callers.
  @return A transaction yielding an HTML page.
|*)
fun greet (name : string) : transaction page = ...
```

Alternative: single-line `(*!` prefixes or `@doc` attributes—**open for discussion**. The `(*| ... |*)` block mirrors “doc comments” in other languages while staying visually distinct from `(* ... *)`.

## Tags (NatSpec-aligned, extensible)

| Tag | Purpose |
|-----|---------|
| `@title` | Short one-line title for generated docs |
| `@notice` | End-user / outsider-readable description |
| `@dev` | Implementation notes for maintainers |
| `@param <name> ...` | Parameter description |
| `@return ...` | Return value / effect description |
| `@custom:<id> ...` | Extensibility hook (e.g. `@custom:security`, `@custom:deprecated`) |

Additional Ur-specific tags may appear later (e.g. `@page`, `@rpc`, `@sql`, `@table`).

## Compiler and IR

1. **Lexer/parser:** recognize doc blocks and attach them to the following declaration (or merge with adjacent comment rules—**TBD**).
2. **AST:** store documentation in a side table or on nodes to avoid bloating every variant.
3. **Elaboration:** optional pass to resolve `` `identifiers` `` or `@see Module.val` references and emit diagnostics.
4. **LSP:** map spans to hover markdown built from `@notice` / `@dev` / `@param` / `@return`.

## References

- [Solidity NatSpec format](https://docs.soliditylang.org/en/latest/natspec-format.html)
- [LangSec](https://langsec.org/) — strict input grammars for security-sensitive surfaces
