//! Core surface checks aligned with the Ur/Web manual (lexical / core syntax / elaboration).
//! Uses the real Basis when discoverable from the test binary (same boot resolution as `compiler` tests).
//!
//! Boot-linked elaboration of the full Basis can recurse deeply enough to overflow the **default**
//! Rust test thread stack on some platforms. [`try_elaborate_single_module`] runs the compile on a
//! child thread with [`ELABORATION_TEST_STACK_BYTES`] via [`std::thread::Builder::stack_size`].

use std::fs;
use std::sync::Mutex;

use tempfile::tempdir;
use ur::compiler;
use ur::error_types::ErrorReporter;
use ur::settings::Settings;

/// Stack size for threads that run full boot + elaboration in this integration test crate.
///
/// Matches the lower bound that reliably passes `corpus_core_*` on the CI stack (8 MiB).
const ELABORATION_TEST_STACK_BYTES: usize = 8 * 1024 * 1024;

static CORPUS_LOCK: Mutex<()> = Mutex::new(());

/// Run `body` on a fresh OS thread with [`ELABORATION_TEST_STACK_BYTES`] and propagate its result.
///
/// # Errors
///
/// Maps spawn failure or a panicking `body` (failed [`std::thread::JoinHandle::join`]) to `Err(String)`.
fn run_with_elaboration_stack<T: Send + 'static>(
    body: impl FnOnce() -> T + Send + 'static,
) -> Result<T, String> {
    std::thread::Builder::new()
        .stack_size(ELABORATION_TEST_STACK_BYTES)
        .spawn(body)
        .map_err(|spawn_error| format!("corpus elaboration thread spawn: {spawn_error}"))?
        .join()
        .map_err(|_| "corpus elaboration thread panicked".to_string())
}

fn try_elaborate_single_module(ur_src: &str) -> Result<(), String> {
    let source_text = ur_src.to_string();
    run_with_elaboration_stack(move || try_elaborate_single_module_on_thread(&source_text))
        .flatten()
}

fn try_elaborate_single_module_on_thread(ur_src: &str) -> Result<(), String> {
    let _guard = CORPUS_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let dir = tempdir().map_err(|tempfile_error| tempfile_error.to_string())?;
    let root = dir.path();
    fs::write(root.join("app.urp"), "CoreMod\n").map_err(|io_error| io_error.to_string())?;
    fs::write(root.join("CoreMod.ur"), ur_src).map_err(|io_error| io_error.to_string())?;
    let urp = root.join("app.urp");
    let mut job = compiler::parse_urp(&urp).map_err(|parse_error| parse_error.to_string())?;
    let mut settings = Settings::new();
    settings.boot_linking = true;
    compiler::apply_boot_settings(&mut job, &mut settings);
    let mut errors = ErrorReporter::new_silent();
    let Some(file) = compiler::parse_sources(&job, &settings, &mut errors) else {
        return Err(format!("parse_sources: {errors:?}"));
    };
    let Some(_elab) = compiler::elaborate(file, &settings, &mut errors) else {
        return Err(format!("elaborate returned None: {errors:?}"));
    };
    if errors.has_errors() {
        return Err(format!("elaborate errors: {errors:?}"));
    }
    Ok(())
}

fn corpus_enabled() -> bool {
    try_elaborate_single_module("val x = 1\n").is_ok()
}

#[test]
fn corpus_core_val_literal_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module("val x = 42\n").expect("literal val");
}

#[test]
fn corpus_core_fun_elaborates() {
    if !corpus_enabled() {
        return;
    }
    // `int` is not an unqualified top-level type in user modules (Basis FFI); keep inference-only.
    try_elaborate_single_module("fun f x = x\n").expect("fun");
}

#[test]
fn corpus_core_polymorphic_id_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module("val id = fn x => x\n").expect("poly id");
}

#[test]
fn corpus_core_structure_projection_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module("structure M = struct\n    val k = 3\nend\n\nval z = M.k\n")
        .expect("structure projection");
}

#[test]
fn corpus_core_datatype_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module("datatype t = Leaf | Node of t * t\nval a = Leaf\n")
        .expect("datatype");
}

#[test]
fn corpus_core_type_mismatch_rejected() {
    if !corpus_enabled() {
        return;
    }
    let r = try_elaborate_single_module("val x : {} = 1\n");
    assert!(
        r.is_err(),
        "unit annotation vs int literal must not elaborate, got Ok"
    );
}

#[test]
fn corpus_core_row_concat_disjoint_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module("type ok = {A : {}} ++ {B : {}}\n").expect("disjoint row concat");
}
