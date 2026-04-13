# IR and service-layer type review (Track H + Track L)

This document records the **datatype / struct / enum design review** for the Rust compiler: baseline notes, metrics commands, invariants, and bounded code changes. It is maintained so future work (interning, arenas, enum splits) has an explicit checklist.

## Track H — Baseline (service layer, smaller blast radius)

### Settings ([`src/settings.rs`](../src/settings.rs))

- **`Settings`** is `Clone` and holds many `String`, `Vec`, and `BTreeSet`/`BTreeMap` fields. Cloning duplicates the full job configuration; that is intentional for thread boundaries and snapshot semantics—avoid extra clones at call sites when a `&Settings` suffices.
- **`Ffi`** is `(String, String)`; membership in `BTreeSet`/`BTreeMap` keys implies deterministic ordering for codegen and effect checks.

### LSP ([`src/lsp_workspace.rs`](../src/lsp_workspace.rs), [`src/lsp_analysis.rs`](../src/lsp_analysis.rs))

- **`ProjectState`** bundles `root`, `urp_path`, `Job`, and `Settings`—one clone per open project is expected; per-request analysis uses `&self` and builds `AnalysisSnapshot` without cloning `ProjectState` wholesale.
- **Workspace discovery errors** use `detail: String` in enums; `to_diagnostic_text` moves those strings into catalog vectors (small cardinality).
- **Implemented:** `workspace_root_from_initialize` reads `InitializeParams::root_uri` directly when `workspace_folders` is absent, avoiding a `serde_json` round-trip while preserving `uri_to_file_path` LangSec filtering (`file:` only).

### Database ([`src/db/`](../src/db/mod.rs))

- **`ProjectDb`** / **`SqlFlavor`** drive parsing, mangling, and linker flags; `match` arms must stay exhaustive when adding backends (see `KNOWN_DB_NAMES`, test matrix).

### Debugger ([`src/debugger/`](../src/debugger/mod.rs))

- Session state is split across DAP framing, GDB/MI, and shared helpers; bounded loops in MI/DAP paths are documented in subsystem modules.

### CJR / emission

- Treat allocation tuning as **profile-guided** after `cargo build --timings` and (when needed) `perf` / heap profiling on a representative `ur-compile` invocation.

---

## Track L — IR inventory (solver vs codegen)

See **[ARCHITECTURE.md](../ARCHITECTURE.md) — “IR representation invariants”** for the canonical table (`Located`, unification, Core `FfiIdent`, `ModProj` paths).

**Planned pilots (at most one per release cycle):**

1. **Done (wrapper):** [`FfiIdent`](../src/core/ffi_ident.rs) in Core — single construction path for simple FFI refs on `Constructor::Ffi`, `Expression::Ffi`, and `Expression::FfiApp` (corify builds `FfiIdent::new`). **Deferred:** **string interning** for those strings (or a shared pool) until `dhat` / heap profile on a large compile justifies it.
2. **Arena allocation** in a single pass (e.g. monomorphized reduce) behind a narrow API.
3. **Sub-enum splits** only where variants form a natural domain boundary (e.g. web/SQL declarations) and tests cover every `match`.

Do not replace [`Located<T>`](../src/error_types.rs) with span-less nodes without a side-table design and diagnostic regression tests.

---

## Metrics (repeatable commands)

### Compile-time (workspace)

```sh
cargo build --workspace --timings
```

Cargo writes an HTML timing report under `target/cargo-timings/` (path printed at end of the build). Use it to compare before/after for large refactors.

### CPU / allocation (representative project)

After building release or debug binaries:

```sh
perf record -g -- cargo run -p ur --bin ur-compile -- …
perf report
```

For allocation-heavy experiments, use `dhat`, `heaptrack`, or `cargo llvm-lines` as appropriate on a fixed input `.urp`.

Record the **date**, **commit**, **command**, and **input project** next to any numbers you rely on in reviews or PRs.

---

## Exit criteria (from review plan)

| Criterion | Notes |
|-----------|--------|
| Clippy / tests | `cargo clippy --workspace --all-targets -- -D warnings`; `cargo test --workspace --all-targets` |
| Track H changes | No intentional semantic change; optional before/after timing note |
| Track L pilots | Metrics gate + one vertical slice + rollback story |
