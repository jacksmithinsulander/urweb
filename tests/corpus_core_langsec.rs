//! Core surface checks aligned with the Ur/Web manual (lexical / core syntax / elaboration).
//! Uses the real Basis when discoverable from the test binary (same boot resolution as `compiler` tests).
//!
//! Boot-linked elaboration of the full Basis can recurse deeply enough to overflow the **default**
//! Rust test thread stack on some platforms. [`try_elaborate_single_module`] runs the compile on a
//! child thread with [`ELABORATION_TEST_STACK_BYTES`] via [`std::thread::Builder::stack_size`].
//!
//! **Disjointness / boot progress:** [`corpus_boot_elaboration_disjointness_progress`] ratchets
//! [`DiagnosticId::ElabUnresolvedDisjointness`] during boot-only elaboration. Print counts and
//! sample rows with `URWEB_TEST_BOOT_PROGRESS=1`. Full boot [`DiagnosticId`] buckets:
//! `boot_elab_diagnostic_id_histogram` in `src/elaborated/elaborate.rs` with `URWEB_TEST_BOOT_HIST=1`.

use std::fs;
use std::sync::Mutex;

use tempfile::tempdir;
use ur::compiler;
use ur::diagnostics::DiagnosticId;
use ur::error_types::{CompileError, ErrorReporter};
use ur::settings::Settings;

/// Stack size for threads that run typical `corpus_core_*` modules (small user programs + boot).
///
/// Matches the lower bound that reliably passes `corpus_core_*` on the CI stack (8 MiB).
const ELABORATION_TEST_STACK_BYTES: usize = 8 * 1024 * 1024;

/// Stack for boot-only elaboration of the full `lib/ur` tree (matches `ur-compile`, deep recursion).
const BOOT_ONLY_ELABORATION_STACK_BYTES: usize = ur::COMPILE_THREAD_STACK_BYTES;

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

/// Elaborate one synthetic module in a temp dir (locked, larger stack via caller).
///
/// # Errors
///
/// I/O, parse, boot settings, `parse_sources`, elaboration, or reported hard errors as `String`.
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
    // Temp `.urp` jobs have no `lib/ur` beside them; pin boot root to this crate so Basis resolves in CI.
    let workspace_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_basis = workspace_root.join("lib/ur/basis.urs");
    let previous_boot_root = std::env::var_os("URWEB_BOOT_ROOT");
    if workspace_basis.is_file() {
        std::env::set_var("URWEB_BOOT_ROOT", &workspace_root); // Point boot discovery at the repo tree.
    }
    let boot_apply = compiler::apply_boot_settings(&mut job, &mut settings); // May require `URWEB_BOOT_ROOT` when job has no local `lib/ur`.
    match &previous_boot_root {
        None => std::env::remove_var("URWEB_BOOT_ROOT"), // Avoid leaking boot override into other tests.
        Some(value) => std::env::set_var("URWEB_BOOT_ROOT", value), // Restore prior env for test isolation.
    }
    boot_apply?; // Propagate missing Basis / invalid boot root as a clear failure.
    let mut errors = ErrorReporter::new_silent();
    let Some(file) = compiler::parse_sources(&job, &settings, &mut errors) else {
        return Err(format!("parse_sources: {errors:?}"));
    };
    let Some(_elab) = compiler::elaborate(file, &settings, &mut errors) else {
        return Err(format!("elaborate returned None: {errors:?}"));
    };
    if errors.has_hard_errors() {
        return Err(format!("elaborate errors: {errors:?}"));
    }
    Ok(())
}

fn corpus_enabled() -> bool {
    try_elaborate_single_module("val x = 1\n").is_ok()
}

/// Run boot-only `body` on a thread with [`BOOT_ONLY_ELABORATION_STACK_BYTES`].
fn run_boot_only_elaboration_stack<T: Send + 'static>(
    body: impl FnOnce() -> T + Send + 'static,
) -> Result<T, String> {
    std::thread::Builder::new()
        .stack_size(BOOT_ONLY_ELABORATION_STACK_BYTES)
        .spawn(body)
        .map_err(|spawn_error| format!("boot-only elaboration thread spawn: {spawn_error}"))?
        .join()
        .map_err(|_| "boot-only elaboration thread panicked".to_string())
}

/// Hard upper bound on boot-only [`DiagnosticId::ElabUnresolvedDisjointness`] diagnostics.
///
/// **Ratchet:** lower only when disjointness parity improves. Print samples with
/// `URWEB_TEST_BOOT_PROGRESS=1`.
///
/// **Baseline (2026-04):** full boot histogram reported **zero** unresolved disjointness; keep `0`
/// so regressions fail CI.
const BOOT_UNRESOLVED_DISJOINTNESS_DIAGNOSTICS_MAX: usize = 0;

/// Boot-only elaboration: count `ElabUnresolvedDisjointness` and type errors (integration mirror of
/// `boot_elab_diagnostic_id_histogram_body`).
fn boot_only_elaboration_disjointness_and_type_error_counts_on_thread(
) -> Result<(usize, usize), String> {
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let lib_dir = manifest_dir.join("lib/ur");
    if !lib_dir.join("basis.urs").is_file() {
        return Ok((0, 0));
    }
    let job = compiler::Job {
        sources: vec![],
        basis_lib_dir: Some(lib_dir),
        ..Default::default()
    };
    let settings = Settings::new();
    let mut parse_errors = ErrorReporter::new_silent();
    let Some(source_file) = compiler::parse_sources(&job, &settings, &mut parse_errors) else {
        return Err(format!("parse_sources failed: {parse_errors:?}"));
    };
    let mut elab_errors = ErrorReporter::new_silent();
    let _elaborated = compiler::elaborate(source_file, &settings, &mut elab_errors);
    let unresolved_disjointness_count = elab_errors
        .errors
        .iter()
        .filter(|error| {
            matches!(
                error,
                CompileError::TypeError { payload, .. }
                    if payload.id == DiagnosticId::ElabUnresolvedDisjointness
            )
        })
        .count();
    let type_error_count = elab_errors
        .errors
        .iter()
        .filter(|error| matches!(error, CompileError::TypeError { .. }))
        .count();
    if std::env::var("URWEB_TEST_BOOT_PROGRESS").ok().as_deref() == Some("1") {
        eprintln!(
            "boot-only elaboration progress: type_errors={type_error_count} \
             ElabUnresolvedDisjointness={unresolved_disjointness_count}"
        );
        for err in elab_errors.errors.iter().filter(|error| {
            matches!(
                error,
                CompileError::TypeError { payload, .. }
                    if payload.id == DiagnosticId::ElabUnresolvedDisjointness
            )
        }) {
            if let CompileError::TypeError { span, payload } = err {
                eprintln!(
                    "  disjoint {:?}  {}:{}-{}  args={:?}",
                    payload.id, span.file, span.first.line, span.first.col, payload.args
                );
            }
        }
    }
    Ok((unresolved_disjointness_count, type_error_count))
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

/// Full Basis boot (no user modules): ratchet [`DiagnosticId::ElabUnresolvedDisjointness`].
#[test]
fn corpus_boot_elaboration_disjointness_progress() {
    if !corpus_enabled() {
        return;
    }
    let (disjoint_count, _type_errors) = run_boot_only_elaboration_stack(
        boot_only_elaboration_disjointness_and_type_error_counts_on_thread,
    )
    .expect("boot disjointness progress thread")
    .expect("boot-only elaboration");
    assert!(
        (0..=BOOT_UNRESOLVED_DISJOINTNESS_DIAGNOSTICS_MAX).contains(&disjoint_count),
        "ElabUnresolvedDisjointness count {disjoint_count} exceeds cap {} — \
         lower the cap only after fixing disjointness; \
         print details with URWEB_TEST_BOOT_PROGRESS=1 on this test",
        BOOT_UNRESOLVED_DISJOINTNESS_DIAGNOSTICS_MAX
    );
}
