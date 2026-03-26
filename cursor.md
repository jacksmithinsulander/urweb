# Ur/Web — Cursor context (this repository)

Use **`@cursor.md`** in Cursor chat when working on this repo. This file is **repo-specific**: a **Rust** compiler/workspace for **Ur/Web**, not a generic Ur tutorial. Official language + upstream compiler: [github.com/urweb/urweb](https://github.com/urweb/urweb), [impredicative.com/ur](http://www.impredicative.com/ur/), [manual.pdf](http://www.impredicative.com/ur/manual.pdf).

Optional: copy sections into [`.cursor/rules`](.cursor/rules) as `.mdc` files for always-on behavior.

---

## 1. Repository type (be precise)

| This repo | Upstream `urweb/urweb` |
|-----------|-------------------------|
| Rust 2021 workspace, `cargo build` / `cargo test` | Standard ML + MLton (or distro packages), `./configure && make` |
| Library crate **`ur`** + binaries `ur`, `ur-compile`, … | `urweb` binary from ML distribution |
| Manifest **`ur.toml`** (strict TOML) | Often `.urp` + distro paths; this repo adds `ur.toml` orchestration |
| [`ARCHITECTURE.md`](ARCHITECTURE.md) describes Rust modules | `src/*.sml` in upstream |

Feature parity with upstream is **aspirational**; **tests and `ARCHITECTURE.md`** are the ground truth for this implementation.

---

## 2. Compiler pipeline (where to look in Rust)

When debugging a bug, map the phase first:

| Phase | Directories / files |
|-------|---------------------|
| Lex + parse | [`src/parse/`](src/parse/) (Logos + LALRPOP), [`src/source/`](src/source/) |
| Typecheck / elaborate | [`src/elaborated/`](src/elaborated/) |
| Explicit / modules | [`src/explicit/`](src/explicit/) |
| Core IR + passes | [`src/core/`](src/core/) |
| Monomorphization | [`src/monomorphized/`](src/monomorphized/) (includes e.g. [`sqlcache.rs`](src/monomorphized/sqlcache.rs)) |
| C + SQL emission | [`src/c_like_representation/`](src/c_like_representation/) |
| Driver / settings | [`src/compiler.rs`](src/compiler.rs), [`src/settings.rs`](src/settings.rs), [`src/urp_parser.rs`](src/urp_parser.rs) |

High-level `//!` overview: [`src/lib.rs`](src/lib.rs).

---

## 3. CLI — binaries and `PATH`

All binaries are declared in root [`Cargo.toml`](Cargo.toml) under `[[bin]]`.

| Command | Source | Notes |
|---------|--------|------|
| `ur` | [src/bin/ur.rs](src/bin/ur.rs) | Delegates to `ur-compile`, `ur-fmt`, `ur-new`, … **by executable name** |
| `ur-compile` | [src/bin/ur_compile.rs](src/bin/ur_compile.rs) | Main compiler entry; `-dbms`, `-db`, `-sql`, `-tc`, `-boot`, etc. |
| `ur-lsp` | [src/bin/ur_lsp.rs](src/bin/ur_lsp.rs) | LSP on stdio |
| `ur-fmt`, `ur-new`, `ur-install`, `ur-daemon`, `ur-debugger` | `src/bin/*.rs` | Matching names |

**After `cargo build`:** either

```sh
export PATH="$PWD/target/debug:$PATH"   # or target/release
```

or install once:

```sh
cargo install --path .
```

Otherwise `ur build` / `ur -help` fails with **`ur-compile not found in PATH`**.

**`ur` routing (explicit):**

- First arg `new`, `build`, `fmt`, `install`, `daemon`, `lsp`, `debugger` → dedicated tool.
- Anything else → **`exec_peer_bin("ur-compile", args)`** (full argv tail).

---

## 4. `ur.toml` strict manifest

Defined in [`src/cli_common.rs`](src/cli_common.rs) as `UrTomlStrict` with **`deny_unknown_fields`** on each table.

Required/minimal concepts:

- `[package].kind` — e.g. `app` or `lib`.
- `[build].entry` — **required** non-empty string (module / entry name).
- `[build].db` — DB **engine** for `-dbms`, validated; default `"sqlite"`.
- `[build].ccompiler`, `boot` — forwarded to compiler when set.
- `[style]` — optional `scss` / `css` for app projects; `.libs` typically omit entirely.

Unknown keys **must error** — do not suggest “just add a random key” without extending the serde structs.

---

## 5. LangSec and parsers

This project claims **[LangSec](https://langsec.org/)**-aligned handling for **untrusted inputs** (sources, `.urp`, configs): explicit grammars, no silent coercion. Introduction: [langsec.org/bof-handout.pdf](https://langsec.org/bof-handout.pdf).

When touching parsing or project file handling:

- Read existing comments in [`src/urp_parser.rs`](src/urp_parser.rs) and [`src/parse/mod.rs`](src/parse/mod.rs).
- Return **`Result` / `CompileError`** style failures instead of swallowing garbage.
- LALRPOP tables should remain **conflict-free** (see [`src/lib.rs`](src/lib.rs) parser notes).

---

## 6. CI — what must pass for Rust changes

From [`.github/workflows/ci.yml`](.github/workflows/ci.yml):

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --all-targets
```

Mutation testing (`cargo mutants`, sharded) runs after these succeed.

---

## 7. Ur/Web source files (what Cursor is often editing)

- **Extensions:** `.ur` (impl), `.urs` (sig).
- **Type params:** `::` explicit, `:::` implicit.
- **Comments:** `(* ... *)`.
- **Core patterns:** `transaction page`, XML literals, forms with `{#Field}`, `rpc`, `table` / `query` / SQL DML—full detail in the [PDF manual](http://www.impredicative.com/ur/manual.pdf).

**Planned:** NatSpec-style documentation blocks; design only in [doc/NATSPEC.md](doc/NATSPEC.md); reference: [Solidity NatSpec](https://docs.soliditylang.org/en/latest/natspec-format.html).

---

## 8. Extra workspace members

- [`crates/urweb-persy/`](crates/urweb-persy/)
- [`crates/urweb-ndb/`](crates/urweb-ndb/)

Use `cargo check -p urweb-persy` (etc.) when iterating on one crate.

---

## 9. Docs scaffolds (mdBook)

| Book | Directory | Build |
|------|-----------|--------|
| TRPL-style guide | [doc/guide/](doc/guide/) | `cd doc/guide && mdbook build` → output `doc/guide/built/` |
| LYAH-style tutorial | [doc/tutorial/](doc/tutorial/) | `cd doc/tutorial && mdbook build` |

Requires [`mdbook`](https://rust-lang.github.io/mdBook/) installed separately.

---

## 10. Rules of thumb for edits

1. **Smallest diff** that satisfies the task; no unrelated renames or “cleanup.”
2. **Follow surrounding code** in the file you touch (error handling, `anyhow` vs `Result`, etc.).
3. **Compatibility:** Prefer not to break existing Ur programs that already compile here; extend tests in [`tests/`](tests/).
4. **Runtime reality:** Generated C may use **pthreads** today—see README roadmap; do not rip out threading without a coordinated design.
5. **Roadmap ≠ shipped:** Zenroom, `.urt`, self-hosting, pluggable UI—these are **goals**; verify in code before assuming they exist ([Zenroom docs](https://dev.zenroom.org/#/) for future crypto plugin context).

For an expanded duplicate of tables (pipeline, `ur.toml`, LangSec), see [claude.md](claude.md).
