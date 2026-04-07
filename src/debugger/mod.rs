//! Debug Adapter Protocol server backed by **GDB/MI** or **lldb-mi** (same wire protocol).
#![allow(clippy::result_large_err)] // [`crate::error_types::CompileError`] is the intentional shared `Err` type (catalog + I/O).
//!
//! Native binaries must be built with debug symbols: enable **`debug`** in the `.urp` or pass
//! **`ur-compile -debug`** so [`crate::compiler::cc_and_link`] adds **`-g`** to compile and link.
//! Launch/config: `MIMode` `\"gdb\"` (default) or `\"lldb\"`; `gdbPath` / `miDebuggerPath` for the debugger executable.
//! DAP also exposes **`loadedSources`**, reading **`source` by path**, **`exceptionInfo`** after signal stops,
//! and **`setExceptionBreakpoints`** filters (`fatal-signals`, `all-signals`, `cpp-throw`) mapped to GDB catchpoints where supported.
//! **`breakpointLocations`**: GDB `-break-insert` probe per line (≤128 lines) for bound line + `instructionReference`, else heuristic.
//! **`modules`**: `-file-list-shared-libraries` with a fallback MI spelling, plus the launch **`program`** as an `executable` row when missing.
//! **`loadedSource`**: `=library-loaded` / `=library-unloaded` (MI async on GDB) while the inferior runs, plus a
//! **`-file-list-exec-source-files`** diff after stops for lldb / fallback.
//!
//! **Style:** new/edited Rust here follows [README.md](../../README.md) Rust code style (exceptions documented there).

pub mod dap_framing;
mod dap_session;
mod dap_shared;
mod diagnostic_locale;
mod gdb_session;
mod mi_parse;

pub use dap_session::run_dap_stdio;
