# Ur/Web – Claude AI Context

This file provides context for Claude and other AI assistants working with Ur/Web projects. Include it (e.g. via `@claude.md` or by reference) when editing Ur/Web code.

## Language Overview

- **Ur** is an ML/Haskell-style language: functional, pure, strict, statically typed
- **Ur/Web** = Ur + web/SQL standard library
- **Key guarantee:** Well-typed programs avoid code injection, invalid HTML, dead links, form/handler mismatches, invalid SQL, and marshaling errors

## Core Syntax

- **Types:** `transaction`, `page`, `source`, `xml`; records `{A = ..., B = ...}`; `con`, `val`, `datatype`
- **Type params:** `::` = explicit, `:::` = implicit
- **Comments:** `(* ... *)` (nestable)
- **Modules:** `structure X : S = M`; files `M.ur` (impl), `M.urs` (signature, optional)

## Web Constructs

- **Page handler:** `fun main () : transaction page = return <xml>...</xml>`
- **XML literals:** `<xml><body><h1>Hello</h1></body></xml>`; `{[e]}` for embedded expressions
- **Forms:** `<form>`, `<textbox{#Field}/>`, `<checkbox{#B}/>`, `<submit action={handler}/>`
- **Links:** `<a link={page}>`; **RPC:** `rpc` for client-to-server calls
- **Client reactivity:** `source`, `signal`, `get`/`set`, `<dyn signal={...}>` for dynamic fragments

## Database

- **Tables:** `table t : {Id : int, Name : string} PRIMARY KEY Id`
- **Sequences:** `sequence s`
- **Views:** `view v = ...`
- **Queries:** `query`, `insert`, `update`, `delete`

## Project Structure

- **`.urp` file:** Directives (`database`, `sql`, `prefix`, `rewrite`, etc.) + module list
- **Module M** → `M.ur` (required), `M.urs` (optional)
- **URLs** map to `Module/page`; use `rewrite url` to shorten paths

## Conventions

- Module names: capital first letter (e.g. `Hello`, `Main`)
- Entry point: `main` for the main page handler
- Single-file projects: `foo.ur` without `foo.urp` → implicit project named `foo`

## Sources to Read

- **Manual:** http://www.impredicative.com/ur/manual.pdf
- **Project site:** http://www.impredicative.com/ur/
- **Demo apps:** `demo/` in urweb source (hello, form, crud1, chat, etc.)
- **Standard library:** `lib/ur/` (basis.urs, top.ur, etc.)
