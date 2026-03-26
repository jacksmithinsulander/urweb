## Canonical references (language semantics)

Use these for **correct** Ur/Web syntax and stdlib behavior—do not invent APIs from other languages.

| Resource | URL |
|----------|-----|
| **Reference manual (PDF)** | <http://www.impredicative.com/ur/manual.pdf> |
| **Project site** | <http://www.impredicative.com/ur/> |
| **Upstream compiler and `lib/` sources** | <https://github.com/urweb/urweb> |

The **Rust** reimplementation of the compiler (if you use it) lives in a **different** repository; it implements the same **language**. Still cite the **manual** for what Ur/Web *means*.

---

## LangSec (compiler / toolchain context)

If you are hacking the **Rust** compiler: inputs (sources, `.urp`, configs) are treated with strict grammars where the implementation follows [Language-theoretic security](https://langsec.org/) discipline—see also [this LangSec BOF handout (PDF)](https://langsec.org/bof-handout.pdf). That does **not** replace reading the Ur/Web manual for **end-user** program syntax.

---

## What this folder is

| File / pattern | Role |
|----------------|------|
| `ur.toml` | **Strict** project manifest: unknown keys are rejected by strict toolchains. `[build].entry` is the **module base name** (must match `Entry.ur`). |
| `*.urp` | Compiler job: **directive lines** at top (e.g. `file`, `database`, `prefix`), then a **blank line**, then **one module stem per line** (no `.ur` suffix). |
| `Name.ur` | Implementation for module `Name` (capitalized module convention). |
| `Name.urs` | Optional signature (common in **libraries**). |

**Build:** from this directory, `ur build`. That requires `ur`, `ur-compile`, and related `ur-*` tools on your **`PATH`** (for the Rust toolchain: run `cargo install --path .` from the compiler clone, or prepend `target/release` during development).

---

## Language snapshot (Ur/Web)

- **Paradigm:** strict, pure, statically typed; ML/Haskell flavor; **row types** and metaprogramming.
- **Type parameters:** `::` = explicit, `:::` = implicit.
- **Comments:** `(* ... *)` only; nestable. Ur has **no** `//` line comments like C++ or Rust.
- **Modules:** `structure X : S = M`; filenames `M.ur` + optional `M.urs`.
- **Main page (apps):** handler named `main` with type `transaction page`.

### Tiny page example (verify with manual)

```ur
fun main () : transaction page =
    return <xml>
      <body><h1>Hello</h1></body>
    </xml>
```

### XML value embed (easy to get wrong)

```ur
(* embed expression expr in XML: curly braces PLUS square brackets *)
<p>{[ 1 + 1 ]}</p>
```

Wrong LLM output to avoid: `{ 1 + 1 }` without inner `[ … ]` where a value splice is required.

### Signals and client code

`source`, `signal`, `get`, `set`, `<dyn signal={…}/>`, and `onclick={{ … }}` are **Ur/Web constructs** with server/client staging rules. **Do not** rewrite them as plain React hooks or DOM APIs—copy from **this project** or from **`demo/`** in [github.com/urweb/urweb](https://github.com/urweb/urweb).

### SQL / web safety (why types matter)

Well-typed Ur/Web code rules out many **HTML**, **RPC**, **form**, **SQL**, and **marshaling** mismatches by construction. That is a **language** guarantee, not something you get if you bypass the FFI or embed raw strings unsafely.

---

## `ur.toml` (strict — gotchas for LLMs)

Rust-based `ur` uses **closed** tables: stray keys are a **hard error**.

Typical **app**:

```toml
[package]
name = "myapp"
kind = "app"

[build]
entry     = "myapp"    # must match myapp.ur on disk (see capitalization rules below)
db        = "sqlite"   # value passed as -dbms; not free-form SQL
ccompiler = "gcc"
boot      = false

[style]
scss = "style/scss/main.scss"
css  = "style/css/main.css"
```

**Library** projects: usually `kind = "lib"`, **no** `[style]` section, still need `[build].entry`.

If you add undocumented keys (for example guessing `dependencies.foo`), **strict parse fails**—extend the toolchain only when you actually control it.

---

## `.urp` sketch (matches `ur new` app layout)

```text
file /style/css/main.css style/css/main.css text/css

myapp
```

- First section: **directives** (`file`, `database`, `sql`, `prefix`, `rewrite`, `library`, …).
- **Blank line** separates directives from the **module list**.
- List entries are **one module name per line**, no path, no `.ur`.

---

## Naming gotcha: `ur new` and module case

`ur new myapp` generates **`myapp.ur`** on disk but the **module** inside is **capitalized** (`Myapp`) to match Ur conventions. `[build].entry = "myapp"` is the **file stem** in the scaffold; the **fun** inside still lives in module **`Myapp`**. When you are unsure, open the generated `*.ur` and **match what is already there**.

---

## LLM gotchas (read before generating Ur)

1. **Verify in the manual** before shipping syntax; Ur is **not** Haskell, OCaml, Rust, or JavaScript.
2. **XML is typed:** arbitrary HTML blobs rarely type-check where XML fragments are required.
3. **RPCs, forms, tables:** align names across tiers; “fix at runtime” is often a **type error** waiting to happen.
4. **Do not strip `transaction` or effects** to “make it simpler”—you change semantics.
5. **String concatenation** uses `^` for many string types—not `+`.
6. **`ur.toml` / `.urp`:** keep directives and blank lines exactly where the format requires.
7. **Tool mismatch:** classic `urweb` CLI vs Rust `ur` share **language** but not always ** wiring**; when in doubt, use the manual and the project files **already in this directory** as ground truth.

---

## Optional: Cursor rules

Copy sections into `.cursor/rules/*.mdc` with `globs` like `*.ur`, `*.urs`, `*.urp`, `ur.toml` so the model always sees this context.

---

## Planned documentation syntax

**NatSpec-style** structured comments for Ur are **not** guaranteed in every compiler build—ordinary `(* ... *)` only unless your toolchain’s docs say otherwise. Conceptual model: [Solidity NatSpec](https://docs.soliditylang.org/en/latest/natspec-format.html).

---

## If you hack the Rust compiler (not Ur application code)

When editing the **Ur/Web Rust toolchain** repository itself (`src/**/*.rs`, `crates/**/*.rs`), the maintainers expect:

1. **Descriptive names only** — no new cryptic abbreviations or unexplained acronyms in identifiers (standard terms like `LSP` / `CJR` where they are the usual name are fine).
2. **A comment on (almost) every executable line** — structural closing braces and trivial `match` `|` rows can rely on section or arm comments; **do not hand-edit LALRPOP-generated `.rs`**.
3. **`///` rustdoc on every function** — except **`#[test]`** functions (optional `///`) and obvious **trait forwarders** if the whole `impl` is documented once.

See **Contributing → Rust code style** and **Exceptions and definitions** in that repo’s `README.md` (and root `claude.md` / `cursor.md`).
