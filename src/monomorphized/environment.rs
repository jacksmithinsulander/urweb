//! Mono environment: tracks bound variables and named definitions.
//!
//! Ports `mono_env.sml`.

#![allow(dead_code, unused_variables, unused_imports)]

use std::collections::HashMap;

use crate::error_types::Span;
use crate::monomorphized::{LocExp, LocTyp};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct UnboundError {
    pub kind: UnboundKind,
    pub index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnboundKind {
    Rel,
    Named,
}

impl std::fmt::Display for UnboundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            UnboundKind::Rel => write!(f, "unbound relative variable {}", self.index),
            UnboundKind::Named => write!(f, "unbound named variable {}", self.index),
        }
    }
}

impl std::error::Error for UnboundError {}

// ---------------------------------------------------------------------------
// Env
// ---------------------------------------------------------------------------

/// A Mono type-checking / interpretation environment.
///
/// Mirrors the SML `env` record in `mono_env.sml`, but omits the
/// `datatypes` / `constructors` maps that are handled separately in the
/// Rust port (those live on `DatatypeRef`).
#[derive(Debug, Clone)]
pub struct Env {
    /// Stack of relative bindings (de Bruijn, most-recent at index 0).
    ///
    /// Each entry is `(name, type)`.  The SML also carries an `exp option`
    /// for inlining; we omit that here.
    rel_e: Vec<(String, LocTyp)>,

    /// Named (top-level) expression bindings, keyed by unique id.
    ///
    /// Value: `(name, type)`.
    named_e: HashMap<usize, (String, LocTyp)>,
}

impl Env {
    // -----------------------------------------------------------------------
    // Construction
    // -----------------------------------------------------------------------

    pub fn empty() -> Self {
        Env {
            rel_e: Vec::new(),
            named_e: HashMap::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Relative (lambda / let) bindings
    // -----------------------------------------------------------------------

    /// Push a new relative binding onto the front of the rel stack.
    ///
    /// The returned `Env` is a clone with the new binding prepended.
    #[must_use]
    pub fn push_rel(&self, x: &str, t: LocTyp) -> Env {
        let mut env = self.clone();
        env.rel_e.insert(0, (x.to_string(), t));
        env
    }

    /// Look up the `n`th de Bruijn relative variable.
    pub fn lookup_rel(&self, n: usize) -> Result<&(String, LocTyp), UnboundError> {
        self.rel_e.get(n).ok_or(UnboundError {
            kind: UnboundKind::Rel,
            index: n,
        })
    }

    /// How many relative bindings are currently in scope.
    pub fn rel_len(&self) -> usize {
        self.rel_e.len()
    }

    // -----------------------------------------------------------------------
    // Named (top-level) bindings
    // -----------------------------------------------------------------------

    /// Register a named binding.
    #[must_use]
    pub fn push_named(&self, x: &str, n: usize, t: LocTyp) -> Env {
        let mut env = self.clone();
        env.named_e.insert(n, (x.to_string(), t));
        env
    }

    /// Look up a named binding by its unique id.
    pub fn lookup_named(&self, n: usize) -> Result<&(String, LocTyp), UnboundError> {
        self.named_e.get(&n).ok_or(UnboundError {
            kind: UnboundKind::Named,
            index: n,
        })
    }
}

impl Default for Env {
    fn default() -> Self {
        Env::empty()
    }
}
