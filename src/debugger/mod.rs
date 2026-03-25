//! Debug Adapter Protocol server backed by GDB/MI (for native Ur/Web binaries built with `-debug`).

mod dap_framing;
mod dap_session;
mod gdb_session;
mod mi_parse;

pub use dap_session::run_dap_stdio;
