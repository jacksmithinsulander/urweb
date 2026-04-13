//! Shared DAP transport state (sequence numbers + stdout) for the main server and MI async hooks.

use std::collections::HashSet;
use std::io;
use std::sync::{Arc, Mutex};

use serde_json::{json, Value};

use crate::error_types::CompileError;

use super::dap_framing::{bump_seq, write_dap_message};
use super::mi_parse::{classify_mi_line, mi_get_str, MiRecord};

/// DAP notifier helpers box [`CompileError`] so Clippy does not flag large `Err` payloads on hot paths.
type Result<T> = std::result::Result<T, Box<CompileError>>;

/// Convert a poisoned mutex into a boxed [`CompileError`]; the poison context string is included for diagnostics.
fn mutex_poison_error(context: &str) -> Box<CompileError> {
    Box::new(CompileError::Io(std::io::Error::other(context.to_string()))) // wrap poison message in I/O error for CompileError::Io
}

pub struct DapState {
    pub seq: i64,
    pub out: io::Stdout,
}

pub struct LoadedSourceNotifier {
    pub dap: Arc<Mutex<DapState>>,
    pub known_paths: Arc<Mutex<HashSet<String>>>,
}

impl LoadedSourceNotifier {
    /// Handle MI2/MI3 async notifications: `=library-loaded`, `=library-unloaded` (with `mi-async` on GDB).
    pub fn on_mi_line(&self, line: &str) -> Result<()> {
        let tl = line.trim();
        let Some(MiRecord::StatusAsync { class, .. }) = classify_mi_line(tl) else {
            return Ok(());
        };
        match class {
            "library-loaded" => self.on_library_loaded(tl),
            "library-unloaded" => self.on_library_unloaded(tl),
            _ => Ok(()),
        }
    }

    fn on_library_loaded(&self, tl: &str) -> Result<()> {
        let Some(path) = library_record_path(tl) else {
            return Ok(());
        };
        let mut known = self
            .known_paths
            .lock() // acquire the loaded-paths mutex
            .map_err(|_| mutex_poison_error("known_paths mutex poisoned"))?; // convert PoisonError to boxed CompileError
        if !known.insert(path.clone()) {
            return Ok(());
        }
        drop(known);
        self.emit_loaded_source("new", &path)
    }

    fn on_library_unloaded(&self, tl: &str) -> Result<()> {
        let Some(path) = library_record_path(tl) else {
            return Ok(());
        };
        self.known_paths
            .lock() // acquire the loaded-paths mutex
            .map_err(|_| mutex_poison_error("known_paths mutex poisoned"))? // convert PoisonError to CompileError
            .remove(&path); // remove path from the set
        self.emit_loaded_source("removed", &path)
    }

    fn emit_loaded_source(&self, reason: &str, path: &str) -> Result<()> {
        let mut st = self
            .dap
            .lock() // acquire the DAP transport mutex
            .map_err(|_| mutex_poison_error("dap transport mutex poisoned"))?; // convert PoisonError to boxed CompileError
        let body: Value = json!({
            "reason": reason,
            "source": { "name": path, "path": path },
        });
        let msg = json!({
            "seq": bump_seq(&mut st.seq),
            "type": "event",
            "event": "loadedSource",
            "body": body,
        });
        write_dap_message(&mut st.out, &msg).map_err(|io_error| {
            Box::new(CompileError::from(io_error)) // surface stdio write failures as catalog-compatible I/O errors
        })?;
        Ok(())
    }
}

fn library_record_path(mi_line: &str) -> Option<String> {
    mi_get_str(mi_line, "host")
        .map(str::to_string)
        .or_else(|| mi_get_str(mi_line, "target-name").map(str::to_string))
        .or_else(|| mi_get_str(mi_line, "id").map(str::to_string))
}
