[![CI](https://github.com/jacksmithinsulander/urweb/actions/workflows/ci.yml/badge.svg)](https://github.com/jacksmithinsulander/urweb/actions/workflows/ci.yml)

# Ur/Web (Rust implementation)

This repository is a **Rust** reimplementation of the **Ur/Web** compiler and developer tooling: parsing and typechecking through intermediate representations to **C** and **SQL**, plus an orchestration CLI, **LSP**, formatter, and debugger. It tracks the structure of the [original MLton-based compiler](https://github.com/urweb/urweb) while targeting a modern toolchain and workflow (see [ARCHITECTURE.md](ARCHITECTURE.md)). It is **not** the official Ur/Web distribution; that remains the upstream project and OS packages listed under [Official upstream Ur/Web](#official-upstream-urweb).

## What Ur/Web is

**Ur** is a language in the ML and Haskell tradition with a rich type system, including row-based metaprogramming. It is functional, pure, strictly evaluated, and statically typed.

**Ur/Web** is Ur plus a standard library and compilation rules aimed at **dynamic web applications** backed by SQL databases. The standard library’s design is meant so that well-typed Ur/Web programs avoid a broad class of defects. In addition to ordinary safety during page generation, well-typed programs may not, for example:

- suffer common code-injection attacks;
- return invalid HTML;
- contain dead intra-application links;
- mismatch HTML forms against the handlers that consume them;
- ship client code that assumes the wrong RPC shape relative to the server;
- issue invalid SQL queries;
- misuse marshaling to or from SQL or between browser and server.

Ur/Web also supports metaprogramming that builds application pieces from types (for example, functor-generated admin interfaces whose safety follows from the table description).

The original compiler emits efficient **C** for the server (no garbage collection in that object code) and **JavaScript** for the client. See the [project site](http://www.impredicative.com/ur/) and [reference manual (PDF)](http://www.impredicative.com/ur/manual.pdf) for the full language definition.

## Original project (upstream)

The reference implementation and language design live in **[urweb/urweb](https://github.com/urweb/urweb)** and on **[The Ur Programming Language Family](http://www.impredicative.com/ur/)**. Upstream goals include end-to-end compilation to efficient server code, JavaScript for the browser, SQL integration, and a long-standing library and demo suite. **Ur/Web** as a *language* and its safety claims are due to **Adam Chlipala and contributors**; this repo is an additional implementation effort.

## Safety: Ur/Web guarantees and LangSec

We aim to preserve the **Ur/Web** type-and-library safety story for compiled programs and, on top of that, to apply **[Language-theoretic security (LangSec)](https://langsec.org/)** discipline in the **compiler and surrounding tools**: strict recognizers for untrusted inputs, avoiding parser ambiguity and silent repair, and documenting the boundary (see the compiler’s LangSec-oriented notes in the parser and `.urp` handling). A compact introduction is the **[LangSec “What is a hole?” BOF handout (PDF)](https://langsec.org/bof-handout.pdf)**.

## This repository

- **Language pipeline** mirrors the original compiler’s phases (surface → elaboration → core → monomorphization → C-like IR → **C + SQL**), described in [src/lib.rs](src/lib.rs) and [ARCHITECTURE.md](ARCHITECTURE.md).
- **Workspace:** crate `ur` with binaries `ur` (orchestrator), `ur-compile`, `ur-fmt`, `ur-new`, `ur-install`, `ur-daemon`, `ur-lsp`, `ur-debugger`; optional project-database backends in [crates/urweb-persy](crates/urweb-persy) and [crates/urweb-ndb](crates/urweb-ndb).
- **Projects** use an **`ur.toml`** manifest (Cargo/Foundry-inspired) alongside `.urp` job files. Example workflow: `ur new myapp`, `cd myapp`, `ur build`; `ur-compile` accepts the same style of arguments as when invoking the compiler directly.

Emitted server code may still use **pthreads** in some paths today; moving toward **CSP-style** concurrency is a **future** goal (see roadmap).

## Goals (in progress and delivered)

Direction and targets for this implementation (exact completion status varies by area; see tests and issues):

1. **Rust compiler** instead of an ML (SML/MLton-only) bootstrap for this codebase.
2. **Suckless-style habits:** stay DRY, keep third-party surface small, prefer smaller equivalent tools where swaps are practical.
3. **BearSSL** for TLS/crypto in the toolchain/runtime story (not OpenSSL).
4. **Portable, POSIX-minded CLI** with coherent commands and help.
5. **Upgraded repository layout** compared with purely legacy trees.
6. **Pluggable, portable database support** integrated with the compiler (including workspace crates such as `urweb-persy`, `urweb-ndb`).
7. **Package and project CLI** with **`ur.toml`** inspired by **Cargo** and **Foundry**-style developer experience.
8. **Fully static linking** for the toolchain and generated binaries **where platforms and dependencies allow** (details depend on link flags and libc).
9. **No C++** in the compiler implementation or in the linkage story for produced programs (**C only** on the native side).
10. **[cproc](https://github.com/michaelforney/cproc)** (or a compatible C compiler) supported alongside typical GCC/Clang-style drivers.
11. **Elm-inspired, user-friendly diagnostics** that are easy to debug.
12. **High-quality LSP** via `ur-lsp`.
13. **Backward compatibility** with the original compiler **where feasible** (accepted sources, project shape, observable behavior).
14. **Strong tests and mutation testing** (CI runs `cargo mutants` in shards after lint and tests).

## Roadmap (future work)

1. **Remove pthreads** in favor of **CSP-style** threading (likely more runtime logic in Rust or a redesigned C runtime).
2. **Pluggable UI backends** (like DB pluggability): default **web**; planned experiments include **Tcl/Tk**, **Nuklear**, and **Uxn/Varvara**.
3. **Multithreaded Rust compiler** and faster compile times.
4. **Mine and close legacy TODOs** from the original ML compiler where they add clear user value.
5. **Self-hosted Ur/Web:** a small bootstrap compiler plus building out the rest in Ur so integrations stay expressed in the language.
6. **`.urt` test files:** Foundry/Forge-style **unit, integration, and fuzz** tests in ordinary Ur syntax.
7. **Zenroom** and a native-feeling **plugin** story for optional libraries, with **[Zenroom](https://dev.zenroom.org/#/)** as a first target for cryptography-oriented apps.
8. **Two book-shaped guides:** a **TRPL-style** narrative guide and a **LYAH-style** tutorial—scaffolds live under [doc/guide](doc/guide) and [doc/tutorial](doc/tutorial); build with [mdBook](https://rust-lang.github.io/mdBook/) when authoring.
9. **NatSpec-style documentation comments** in Ur source—for design and planned tags, see [doc/NATSPEC.md](doc/NATSPEC.md) and [Solidity NatSpec](https://docs.soliditylang.org/en/latest/natspec-format.html) as the conceptual model.

## How this improves on the upstream *toolchain*

- **Rust ecosystem:** `cargo`, `rustfmt`, `clippy`, ordinary OSS contribution flow—no MLton requirement for hacking on *this* compiler.
- **First-party tools:** formatter, debugger, LSP, and project commands built next to the compiler.
- **Stricter engineering around untrusted inputs** (LangSec-aligned) in parsers and project files.
- **CI:** formatting, denied Clippy warnings, full workspace tests, and mutation testing (see [.github/workflows/ci.yml](.github/workflows/ci.yml)).

Feature parity with every corner of upstream is **not** guaranteed; behavior is anchored by tests and by mirroring the documented pipeline.

## Building and running (this repository)

**Requirements**

- **Rust** (stable), recent enough for the workspace.
- A **C toolchain** to compile and link the C emitted for applications (e.g. GCC, Clang, or [cproc](https://github.com/michaelforney/cproc) where supported).

**From a clone**

```sh
cargo build --release
# Binaries in target/release/: ur, ur-compile, ur-fmt, ur-new, ur-install, ur-daemon, ur-lsp, ur-debugger
```

Install onto your `PATH` (recommended so subcommands find each other):

```sh
cargo install --path .
```

If you run `ur` from `target/release/ur` without installing, ensure **`ur-compile`**, **`ur-fmt`**, and the other `ur-*` peers are on **`PATH`** as well (or use only `cargo run --bin ur-compile -- …` for compilation). The `ur` orchestrator invokes those binaries by name.

**Orchestrator quick reference**

```text
ur new <project-name>
ur new --lib <library-name>
ur build
ur fmt [options] [files...]
ur install <author/repo>
ur daemon [stop|start]
ur lsp
ur debugger [...]
ur [flags...] <project-name>    # forwards to ur-compile
```

Compiler flags (e.g. `-dbms`, `-output`, `-tc`) are available via `ur-compile -help` or `ur-compile --help` (and `ur -help` forwards to `ur-compile` when peers are on `PATH`).

**Tests (match CI)**

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --all-targets
```

## Documentation

- **[The Ur/Web Guide](doc/guide)** — TRPL-style narrative ([mdBook](https://rust-lang.github.io/mdBook/) scaffold); build with `cd doc/guide && mdbook build` (output in `doc/guide/built/`).
- **[Learn Ur/Web](doc/tutorial)** — informal, example-driven tutorial; `cd doc/tutorial && mdbook build`.
- **[NatSpec-style doc comments (design)](doc/NATSPEC.md)** — structured documentation in source, NatSpec-inspired.

## Contributing

Before sending a change, run the same checks as CI: `cargo fmt`, `cargo clippy` with `-D warnings`, and `cargo test --workspace --all-targets`. Large changes benefit from local [`cargo mutants`](https://github.com/sourcefrog/cargo-mutants) runs; CI shards mutation testing across jobs.

Read [ARCHITECTURE.md](ARCHITECTURE.md) for module-level detail.

## Official upstream Ur/Web

To install the **classic** Ur/Web compiler from your OS vendor (unchanged from upstream documentation):

**Debian/Ubuntu**

```sh
apt-get install urweb
```

**macOS (Homebrew)**

```sh
brew install urweb
```

## References and attribution

| Resource | URL |
|----------|-----|
| Ur/Web project site | [impredicative.com/ur](http://www.impredicative.com/ur/) |
| Reference manual (PDF) | [manual.pdf](http://www.impredicative.com/ur/manual.pdf) |
| Upstream sources | [github.com/urweb/urweb](https://github.com/urweb/urweb) |
| LangSec | [langsec.org](https://langsec.org/) |
| LangSec BOF handout (PDF) | [langsec.org/bof-handout.pdf](https://langsec.org/bof-handout.pdf) |

**Ur/Web** (language and original compiler) is the work of **Adam Chlipala and contributors**. This Rust implementation is maintained separately; see git history for authors here.
