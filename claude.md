# Ur/Web — Claude context (this repository)

Treat this file as **project truth for AI assistants** when editing this tree. This is **not** the upstream Standard ML + MLton [urweb/urweb](https://github.com/urweb/urweb) repo; it is a **Rust** workspace that reimplements the compiler and ships extra tooling.

---

## 1. What you are editing

| Artifact | Meaning |
|----------|---------|
| `*.ur` | Ur/Web implementation file (required per module) |
| `*.urs` | Ur/Web signature file (optional) |
| `*.urp` | Project/job file: directives + module list; parsed into a `Job` ([src/urp_parser.rs](src/urp_parser.rs)) |
| **`ur.toml`** | **Strict** project manifest at repo/project root: unknown TOML keys are rejected (`serde(deny_unknown_fields)` on [`UrTomlStrict`](src/cli_common.rs)). Filename is exactly `ur.toml` (not `urweb.toml`). |
| `*.rs` | Rust: compiler, CLI, LSP, tests |

**Authoritative language definition** (semantics, standard library): [Ur/Web manual (PDF)](http://www.impredicative.com/ur/manual.pdf), [project site](http://www.impredicative.com/ur/). **Implementation map:** [ARCHITECTURE.md](ARCHITECTURE.md).

---

## 2. Compilation pipeline (this codebase)

Order and main Rust modules (mirrors upstream phases):

1. **Parse** — [`src/parse/`](src/parse/), [`src/source/`](src/source/) — Lex (Logos) + LALRPOP; goal is **unambiguous** grammars, errors not silent fixes.
2. **Elaborate** — [`src/elaborated/`](src/elaborated/) — Types, inference, unification.
3. **Explify** — [`src/explicit/`](src/explicit/) — Implicits resolved, modules explicit.
4. **Core** — [`src/core/`](src/core/) — Simplified AST; many passes (specialize, effectize, checks, …).
5. **Monomorphize** — [`src/monomorphized/`](src/monomorphized/) — Erase polymorphism; SQL/cache-related code lives here too (e.g. `sqlcache.rs`).
6. **CJR** — [`src/c_like_representation/`](src/c_like_representation/) — C-like IR; emits **C** and **SQL**.

**Orchestration:** [`src/compiler.rs`](src/compiler.rs) wires phases; library root overview: [`src/lib.rs`](src/lib.rs) (`//!` module docs).

---

## 3. Binaries (Cargo `[[bin]]`) → source

| Installed name | Rust entry | Role |
|----------------|------------|------|
| `ur` | [src/bin/ur.rs](src/bin/ur.rs) | Subcommand router; calls other binaries by **executable name** on `PATH` |
| `ur-compile` | [src/bin/ur_compile.rs](src/bin/ur_compile.rs) | Full compile driver; flags like `-dbms`, `-tc`, `-o` |
| `ur-fmt` | [src/bin/ur_fmt.rs](src/bin/ur_fmt.rs) | Format `.ur` / `.urs` |
| `ur-new` | [src/bin/ur_new.rs](src/bin/ur_new.rs) | Scaffold projects |
| `ur-install` | [src/bin/ur_install.rs](src/bin/ur_install.rs) | Dependency/install helper |
| `ur-daemon` | [src/bin/ur_daemon.rs](src/bin/ur_daemon.rs) | Dev daemon |
| `ur-lsp` | [src/bin/ur_lsp.rs](src/bin/ur_lsp.rs) | LSP server (stdio) |
| `ur-debugger` | [src/bin/ur_debugger.rs](src/bin/ur_debugger.rs) | Debugger CLI |

**Critical:** `ur` uses `exec_peer_bin("ur-compile", …)` etc. If you only `cargo build` and run `./target/debug/ur`, peers are **not** on `PATH` unless you **`cargo install --path .`** or export `PATH="$PWD/target/debug:$PATH"` (or `release`). Otherwise you get `ur-compile not found in PATH`.

---

## 4. `ur` orchestrator — explicit dispatch

From [src/bin/ur.rs](src/bin/ur.rs) / [cli_common::UR_ORCHESTRATOR_USAGE_LINES](src/cli_common.rs):

- `ur new <name>` → `ur-new`
- `ur new --lib <name>` → `ur-new`
- `ur build` → reads `ur.toml`, may run SCSS, then `ur-compile` with derived args
- `ur fmt …` → `ur-fmt`
- `ur install <author/repo>` → `ur-install`
- `ur daemon start|stop` → `ur-daemon`
- `ur lsp` → `ur-lsp` (no extra args)
- `ur debugger …` → `ur-debugger`
- **Any other first token** (e.g. `ur ProjectName` or `ur -dbms sqlite MyApp`) → forwarded wholesale to **`ur-compile`**

Help: `ur --help` / `ur -h` prints orchestrator usage; compiler flag help: `ur-compile -help` / `ur-compile --help` (or `ur -help` if `ur-compile` is on `PATH`).

---

## 5. `ur.toml` (strict manifest)

Parsed by [`UrTomlStrict`](src/cli_common.rs). **Extra keys in `[package]`, `[build]`, or `[style]` are errors.** Shape:

```toml
[package]
name = "optional"
kind = "app"   # or "lib"

[build]
entry = "MyApp"       # required: module / project entry name
db = "sqlite"         # passed through as -dbms (validated); not the SQL connection string
ccompiler = ""        # optional; forwarded when non-empty
boot = false          # forwarded as -boot when true

[style]               # optional; omit entirely for libs
scss = "styles/main.scss"
css = "static/main.css"
```

Database **engine** strings must match what [`validate_manifest_db_engine`](src/db.rs) allows (e.g. `sqlite`, `mysql`, `postgres`, and others listed in `ur-compile -help` output such as `persy`, `rocksdb`, `ndb`, `tigerbeetle`).

---

## 6. Safety and LangSec (explicit expectations)

- **Ur/Web (language):** Well-typed programs exclude a large class of bugs: injection, invalid HTML, broken links, form/handler mismatch, bad RPC assumptions, invalid SQL, bad marshaling—see [README.md](README.md).
- **This compiler:** We **still** aim to preserve those guarantees for accepted programs.
- **Additional discipline:** **[LangSec](https://langsec.org/)** — treat `.urp`, source text, and other inputs with **strict** grammars and explicit failures; avoid “helpful” parsing that hides attacks. Read [langsec.org/bof-handout.pdf](https://langsec.org/bof-handout.pdf). In code, look for LangSec / inventory comments in [`src/urp_parser.rs`](src/urp_parser.rs), [`src/parse/mod.rs`](src/parse/mod.rs), and related modules.

When adding parsers or config, **do not** silently ignore malformed input; match existing error-reporting patterns.

---

## 7. Workspace crates (not only root `ur`)

| Path | Purpose |
|------|---------|
| [crates/urweb-persy/](crates/urweb-persy/) | Persy-backed project DB integration |
| [crates/urweb-ndb/](crates/urweb-ndb/) | NDB-related backend integration |

Root [Cargo.toml](Cargo.toml) lists `members`; run **`cargo *` from workspace root** unless you know a crate is isolated.

---

## 8. Commands you should run before proposing Rust changes

Match the **`lint` + `test` jobs** in [`.github/workflows/ci.yml`](.github/workflows/ci.yml):

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --all-targets
```

CI also runs **mutation testing** (`cargo mutants`) in shards after the above pass; for risky edits, run mutants locally if feasible.

---

## 8a. User-facing diagnostics vs observability (`tracing`)

- **Diagnostics channel:** Text meant for Ur/Web authors and tool users (compiler stderr, `ur` / `ur-compile` failures, LSP startup lines on stderr, DAP error bodies you expect editors to show) should use the **diagnostic catalog** ([`DiagnosticId`](src/diagnostics/ids.rs), [`cli_diagnostic_text`](src/cli_common.rs), [`ur.toml` `[package] language`](src/cli_common.rs) / environment). Prefer stable IDs and templates in [`scripts/_catalog_cli.py`](scripts/_catalog_cli.py) over ad-hoc English.
- **Observability channel:** [`tracing`](https://docs.rs/tracing) events in the compiler and pipeline should stay **English**, structured, and grep-friendly for developers and CI. Do not move routine `tracing::debug!` / `info!` message templates into the translation catalog. Optionally attach a catalog **`DiagnosticId`** (or similar) in fields when a log line corresponds to a user-visible diagnostic.
- **Demo / internal tools:** [`src/demo.rs`](src/demo.rs) and other maintainer-oriented entrypoints may still use plain English until tightened; **user-installed binaries** (`ur-*`) should prefer the catalog for any message that reaches the terminal.

---

## 9. Rust code style (mandatory)

Applies to all **Rust** under `src/`, `crates/`, `tests/`, and `examples/`. Details also in [README.md](README.md) (Contributing → Rust code style).

1. **Identifiers** — Prefer **full, long, descriptive names**. Do **not** introduce new **abbreviations** or **unexplained acronyms** in names. Readers should infer meaning from the name alone (for example `monomorphized_expression` rather than `me` or `mono_exp`).
2. **Line-level comments** — **Every executable line** of Rust you add or change should have a **`//` comment** (end-of-line or immediately above) that **states what that line does**, even if it looks obvious. Empty lines and lone `}` may stay uncommented when the opening of the block is already documented and the brace adds no new behavior.
3. **Rustdoc on every function** — Each **`fn`** (module function or `impl` method, `pub` or private) must have a **`///`** block: purpose, parameters, return value, and errors/panics when not clear from types alone.

Legacy code may not yet comply; **new work** and **substantive edits** must move touched code toward this standard.

**Exceptions (same as README):** allowed domain acronyms (`CJR`, `LSP`, …) where standard; **no hand-editing generated `.rs`**; **trait impls** may use one `///` on the `impl` or module `//!`; **`#[test]`** functions need not each have `///`; **structural `}`** and dense `match` arms may use section or arm comments instead of a comment on every pattern line; **tests/** naming rules still ban new opaque abbreviations.

---

## 10. Ur/Web syntax reminder (for `*.ur` / `*.urs`)

- **Kinds / types:** `transaction`, `page`, `source`, `xml`; records `{ Label = t, ... }`; declarations `con`, `val`, `datatype`, `fun`.
- **Type parameters:** `::` explicit, `:::` implicit.
- **Comments:** `(* ... *)` nestable.
- **Structures:** `structure X : S = M`; file pair `M.ur` + optional `M.urs`.
- **Web:** `fun main () : transaction page = …`; XML `<xml>…</xml>`; `{"[e]"}` splices; forms (`<textbox{#F}/>`, etc.); `<a link={…}>`; `rpc`; `source` / `signal`.
- **SQL:** `table`, `sequence`, `view`, `query`, DML forms.
- **Conventions:** capitalized module names; entry `main` for main page; lone `Foo.ur` implies project `Foo` without `Foo.urp`.

**Planned doc syntax:** NatSpec-inspired blocks — spec in [doc/NATSPEC.md](doc/NATSPEC.md); analogy [Solidity NatSpec](https://docs.soliditylang.org/en/latest/natspec-format.html).

---

## 11. Documentation artifacts in this repo

| Path | Purpose |
|------|---------|
| [README.md](README.md) | User-facing project description, goals, roadmap |
| [doc/guide/](doc/guide/) | mdBook scaffold, TRPL-style guide — `cd doc/guide && mdbook build` |
| [doc/tutorial/](doc/tutorial/) | mdBook scaffold, LYAH-style tutorial |
| [doc/NATSPEC.md](doc/NATSPEC.md) | Design for structured doc comments |

---

## 12. Editing discipline (for Claude)

- **Stay inside the user’s task**; avoid drive-by refactors and unrelated formatting.
- **Rust:** Follow **section 9** (names, per-line comments, `///` on every function) for all Rust you add or materially edit; that takes precedence over sparse legacy style in untouched lines.
- **Preserve backward compatibility** with upstream Ur/Web where the project already does; when in doubt, add tests rather than changing accepted programs silently.
- **Emitted C** may still use **pthreads** in some runtime paths; replacing that is a **roadmap** item, not something to “fix” opportunistically without a design.
- **Upstream demos** (`demo/` on [github.com/urweb/urweb](https://github.com/urweb/urweb)) may not exist in this clone; do not assume paths from the official repo exist here.

---

## 13. Future / roadmap (context only)

Summarized in [README.md](README.md): CSP instead of pthreads, pluggable UI backends, faster parallel compiler, self-hosting, `.urt` tests, **[Zenroom](https://dev.zenroom.org/#/)** plugin story, richer books, full NatSpec implementation.

Do **not** treat roadmap items as already implemented unless code and tests prove it.
