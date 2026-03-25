//! Shared diagnostics for production compiler paths: mutex poisoning and internal errors.
//!
//! **Poison policy**: if a `Mutex` is poisoned, we print a clear message to stderr, then call
//! [`std::sync::PoisonError::into_inner`] so compilation can continue best-effort (matching typical
//! “recover from poison” behavior). Pure ICE paths should use [`internal_compiler_error`] at
//! boundaries that return `anyhow::Result`.

use std::fmt::Display;
use std::sync::{Mutex, MutexGuard};

/// Lock a mutex used during compilation. On poison, explain to stderr and recover via
/// [`PoisonError::into_inner`](std::sync::PoisonError::into_inner).
pub fn lock_for_compile<'a, T>(mutex: &'a Mutex<T>, context: &str) -> MutexGuard<'a, T> {
    match mutex.lock() {
        Ok(guard) => guard,
        Err(poisoned) => {
            eprintln!(
                "The compiler hit an internal lock problem ({context}).\n\
                 This usually means an earlier pass panicked while holding this lock.\n\
                 Try rebuilding from a clean state. If it keeps happening, please report a bug."
            );
            poisoned.into_inner()
        }
    }
}

/// Build an `anyhow` error for an internal compiler assumption that failed (ICE-style).
pub fn internal_compiler_error(context: &str, detail: impl Display) -> anyhow::Error {
    anyhow::anyhow!(
        "Internal compiler problem ({context}): {detail}\n\
         This is unexpected — your project may have triggered a compiler bug.\n\
         Please report this with a small example if you can reproduce it."
    )
}
