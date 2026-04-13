# Sketch: `ur_lang` vs `urweb_compiler` workspace split

This is a **design sketch** only — no crate split is implemented yet. It records a plausible boundary once `LanguageCompilationProfile` and the intrinsic registry mature.

## Goals

- **`ur_lang` crate**: Parse → elaborate → explify → corify → most core reductions/checks that do not assume HTTP, JS bundling, or SQL DDL emission.
- **`urweb_compiler` crate** (or `urweb`): Depends on `ur_lang`; owns monomorphization tuned for the web runtime, `jscomp`, CJR, `sql_generate`, project DB resolution, and `.urp` job glue.

## Shared foundation crate (optional)

Extract into `ur_compiler_foundation` (names illustrative):

- `error_types`, `primitives`, `diagnostics` ids/locale (or keep ids in `ur_lang` only),
- `Located`, `Span`, `datatype_kind`.

Both pipelines import this to avoid circular dependencies.

## API boundary

1. **`ur_lang::compile_to_core(settings, source_file) -> Result<CoreFile, …>`**  
   Stops after `core_specialize` (or after corify + a documented subset of passes). `Settings` would move to foundation or be split: `LangSettings` vs `WebSettings`.

2. **`urweb::compile_job(urp, full_settings)`**  
   Calls `ur_lang` for the front half, then runs mono/CJR/js passes.

## Hard parts (why this is not trivial)

- **Single `source::Decl` enum**: Web directives live in the same AST as structures; `ur_lang` would still parse them unless grammar is split or validated late (current ur-core approach).
- **Elaboration vs Basis**: The elaborator resolves `Basis` and `transaction` types; “Ur without Basis” needs a different prelude story.
- **`Settings`**: Today one struct mixes URL rules, SQL, and JS maps; a split requires `WebCodegenSettings` extending `LangSettings`.

## Suggested order of work

1. Finish **intrinsic registry** coverage (RPC, marshalling, mono_opt writer names).
2. Introduce **`LangSettings`** as a subset field group inside `Settings` (no crate split yet).
3. Move **`jscomp` + `c_like_representation`** behind a trait `CodegenBackend` with one `UrWebCjrBackend` implementation.
4. Only then **cargo new** `ur_lang` and move modules with `pub use` shims from the root crate for one release cycle.
