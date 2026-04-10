//! Shared diagnostics for production compiler paths: mutex poisoning and internal errors.
//!
//! **Poison policy**: if a `Mutex` is poisoned, we print a clear message to stderr, then call
//! [`std::sync::PoisonError::into_inner`] so compilation can continue best-effort (matching typical
//! “recover from poison” behavior). Pure ICE paths should use [`internal_compiler_error`] at
//! boundaries that return [`InternalCompilerError`] (displayed like `anyhow`, and convertible).

use std::fmt::Display;
use std::io::Write as _;
use std::ops::{Deref, DerefMut};
use std::sync::{Mutex, MutexGuard};

use crate::cli_common::{cli_diagnostic_text, diagnostic_locale_for_cli};
use crate::diagnostics::{DiagnosticId, DiagnosticLocale, DiagnosticPayload};
use crate::error_types::{format_compile_error_for_terminal, CompileError, ErrorReporter, Span};

#[cfg(test)]
/// Serializes [`std::env::set_current_dir`] across unit tests (cwd is process-global).
pub static TEST_CWD_LOCK: Mutex<()> = Mutex::new(());

/// Wrapper so `cargo-mutants` can substitute `Default::default()` (unviable for [`anyhow::Error`]).
#[derive(Debug)]
pub struct InternalCompilerError(anyhow::Error);

impl std::fmt::Display for InternalCompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}

/// [`std::error::Error::source`] is not overridden; full context is in [`Display`](std::fmt::Display) via the wrapped [`anyhow::Error`].
impl std::error::Error for InternalCompilerError {}

impl Default for InternalCompilerError {
    fn default() -> Self {
        Self(anyhow::anyhow!(""))
    }
}

/// RAII handle for a [`Mutex`] acquired through [`lock_for_compile`].
///
/// Carries a [`Default`] [`CompileLockGuard::NeverLocked`] variant so `cargo-mutants` can substitute
/// degenerate whole-function bodies on [`lock_for_compile`] without breaking the build; any use of
/// that sentinel panics instead of silently skipping locking.
#[derive(Default)]
pub enum CompileLockGuard<'a, T> {
    /// Active guard from a successful (or recovered poison) lock.
    Held(MutexGuard<'a, T>),
    /// Only used via [`Default::default()`] (e.g. mutants); [`lock_for_compile`] never returns this.
    #[default]
    NeverLocked,
}

impl<'a, T> Deref for CompileLockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            CompileLockGuard::Held(guard) => guard,
            CompileLockGuard::NeverLocked => {
                panic!(
                    "CompileLockGuard::NeverLocked: lock_for_compile was replaced or misused (cargo-mutants / internal bug)"
                )
            }
        }
    }
}

impl<'a, T> DerefMut for CompileLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            CompileLockGuard::Held(guard) => guard,
            CompileLockGuard::NeverLocked => {
                panic!(
                    "CompileLockGuard::NeverLocked: lock_for_compile was replaced or misused (cargo-mutants / internal bug)"
                )
            }
        }
    }
}

/// Lock a mutex used during compilation. On poison, explain to stderr and recover via
/// [`PoisonError::into_inner`](std::sync::PoisonError::into_inner).
///
/// Returns [`CompileLockGuard`] (not raw [`MutexGuard`]) so return types implement [`Default`] and
/// mutation tools emit **viable** builds; bogus defaults still fail loudly via [`Deref`].
pub fn lock_for_compile<'a, T>(mutex: &'a Mutex<T>, context: &str) -> CompileLockGuard<'a, T> {
    match mutex.lock() {
        Ok(guard) => CompileLockGuard::Held(guard),
        Err(poisoned) => {
            let locale = diagnostic_locale_for_cli(None); // Mutex helpers run without a manifest handle.
            let text = cli_diagnostic_text(
                DiagnosticId::CompilerInternalLockPoisoned,
                vec![context.to_string()],
                locale,
            ); // Same body as [`format_diagnostic_payload_for_user`] with env/manifest locale.
            let mut lock = std::io::stderr().lock(); // User-visible stderr for poison recovery.
            let _ = writeln!(lock, "{text}"); // Matches other catalog-driven stderr lines.
            CompileLockGuard::Held(poisoned.into_inner())
        }
    }
}

/// Build an error for an internal compiler assumption that failed (ICE-style).
///
/// Returns a [`InternalCompilerError`] so mutation tests can use `Default::default()` without orphan-rule issues on [`anyhow::Error`].
pub fn internal_compiler_error(context: &str, detail: impl Display) -> InternalCompilerError {
    let locale = diagnostic_locale_for_cli(None); // Read URWEB_LANG env var; default English when absent.
    let rendered = cli_diagnostic_text(
        DiagnosticId::CompilerInternalBug,
        vec![context.to_string(), detail.to_string()],
        locale,
    ); // Catalog-rendered and localized ICE message with context and detail substituted.
    InternalCompilerError(anyhow::anyhow!("{rendered}"))
}

/// Record a recoverable internal assumption failure in a Core pass, or print the same catalog message if no reporter is threaded (unit tests and thin wrappers).
///
/// # Arguments
///
/// * `errors` — Slot holding the active compilation reporter when available (reborrowed across recursive passes).
/// * `span` — Best-effort source span for the surrounding construct.
/// * `payload` — Catalog id and template arguments.
/// * `locale_fallback` — Locale for stderr when `errors` is `None` (use English in tests).
pub fn report_core_recovery(
    errors: &mut Option<&mut ErrorReporter>,
    span: Span,
    payload: DiagnosticPayload,
    locale_fallback: DiagnosticLocale,
) {
    let compile_error = CompileError::warning_at(span, payload);
    match errors.as_mut() {
        Some(reporter) => reporter.report(compile_error),
        None => {
            let text = format_compile_error_for_terminal(&compile_error, locale_fallback); // Same shape as [`ErrorReporter::report`].
            let mut lock = std::io::stderr().lock(); // Fallback when no reporter owns stderr sequencing.
            let _ = writeln!(lock, "{text}"); // Catalog-formatted warning/recovery line.
            let _ = writeln!(lock); // Trailing blank line for terminal readability.
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn internal_compiler_error_message_lists_context_and_detail() {
        let message = internal_compiler_error("phase", "widget missing").to_string();
        assert!(
            message.contains("phase") && message.contains("widget missing"),
            "Default/empty mutant must not match real ICE text: {message:?}"
        );
    }

    #[test]
    #[should_panic(expected = "CompileLockGuard::NeverLocked")]
    fn compile_lock_guard_default_panics_on_deref() {
        let sentinel: CompileLockGuard<'_, u8> = CompileLockGuard::default();
        let _ = *sentinel;
    }

    #[test]
    fn lock_for_compile_holds_mutex_content() {
        let mutex = Mutex::new(7_i32);
        let guard = lock_for_compile(&mutex, "unit test");
        assert_eq!(*guard, 7);
    }
}
