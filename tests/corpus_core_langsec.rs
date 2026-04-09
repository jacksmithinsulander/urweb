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
use std::sync::OnceLock;

use tempfile::tempdir;
use ur::compiler;
use ur::diagnostics::DiagnosticId;
use ur::error_types::{CompileError, ErrorReporter};
use ur::settings::Settings;

/// Stack size for threads that run `corpus_core_*` elaboration checks.
///
/// Keep this aligned with the real compile-thread stack so focused corpus slices reproduce the
/// same higher-order constructor behavior as boot elaboration, instead of failing earlier with
/// test-harness-only stack overflows.
const ELABORATION_TEST_STACK_BYTES: usize = ur::COMPILE_THREAD_STACK_BYTES;

/// Stack for boot-only elaboration of the full `lib/ur` tree (matches `ur-compile`, deep recursion).
const BOOT_ONLY_ELABORATION_STACK_BYTES: usize = ur::COMPILE_THREAD_STACK_BYTES;

/// Workspace root for corpus elaboration tests, computed once per process.
///
/// Stores `Some(path)` when `lib/ur/basis.urs` exists under `CARGO_MANIFEST_DIR`, `None` otherwise.
/// Using a `OnceLock` rather than per-test env-var mutation means corpus tests can run fully in
/// parallel without any global lock.
static CORPUS_WORKSPACE_ROOT: OnceLock<Option<std::path::PathBuf>> = OnceLock::new();

/// Return the workspace root if `lib/ur/basis.urs` is present, or `None` when the Basis is absent.
///
/// Initialises [`CORPUS_WORKSPACE_ROOT`] on first call. All subsequent calls are lock-free reads.
fn corpus_workspace_root() -> Option<&'static std::path::PathBuf> {
    CORPUS_WORKSPACE_ROOT
        .get_or_init(|| {
            let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")); // Compile-time workspace root.
            if root.join("lib/ur/basis.urs").is_file() {
                Some(root) // Basis is present — corpus tests can run.
            } else {
                None // No Basis tree in this build environment; corpus tests will skip.
            }
        })
        .as_ref() // Borrow the stored Option<PathBuf> as Option<&PathBuf>.
}

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

fn try_elaborate_named_module(module_name: &str, ur_src: &str) -> Result<(), String> {
    let module_name_owned = module_name.to_string(); // Clone for the spawned thread's closure.
    let implementation_text = ur_src.to_string(); // Clone for the spawned thread's closure.
    run_with_elaboration_stack(move || {
        let dir = tempdir().map_err(|tempfile_error| tempfile_error.to_string())?; // Isolated temp dir per test invocation.
        let project_root = dir.path(); // Short-lived alias for the temp directory path.
        fs::write(
            project_root.join("app.urp"),
            format!("{module_name_owned}\n"),
        )
        .map_err(|io_error| io_error.to_string())?; // Project descriptor listing the single module.
        fs::write(
            project_root.join(format!("{module_name_owned}.ur")),
            &implementation_text,
        )
        .map_err(|io_error| io_error.to_string())?; // Implementation source.
        let urp = project_root.join("app.urp"); // Path to the project descriptor.
        let mut job = compiler::parse_urp(&urp).map_err(|parse_error| parse_error.to_string())?; // Parse project descriptor into a Job.
        let mut settings = Settings::new(); // Default settings; boot_linking toggled below.
        settings.boot_linking = true; // Enable Basis linking so the standard library is available.
        let boot_root = corpus_workspace_root()
            .ok_or_else(|| "corpus boot root not found (lib/ur/basis.urs missing)".to_string())?; // Use the once-computed workspace root; fail fast when Basis is absent.
        compiler::apply_boot_settings_with_explicit_root(&mut job, &mut settings, boot_root)?; // Apply boot paths without env-var mutation — safe for concurrent tests.
        let mut errors = ErrorReporter::new_silent(); // Silent reporter: errors are returned as Err strings.
        let Some(file) = compiler::parse_sources(&job, &settings, &mut errors) else {
            return Err(format!("parse_sources: {errors:?}")); // Source parsing failed; surface diagnostics.
        };
        let Some(_elab) = compiler::elaborate(file, &settings, &mut errors) else {
            return Err(format!("elaborate returned None: {errors:?}")); // Elaboration produced no output; surface diagnostics.
        };
        if errors.has_hard_errors() {
            return Err(format!("elaborate errors: {errors:?}")); // Elaboration completed but emitted hard errors.
        }
        Ok(())
    })
    .flatten()
}

/// Elaborate one synthetic module/signature pair in a temp dir.
///
/// # Errors
///
/// I/O, parse, boot settings, `parse_sources`, elaboration, or reported hard errors as `String`.
fn try_elaborate_module_pair(ur_src: &str, urs_src: &str) -> Result<(), String> {
    try_elaborate_named_module_pair("CoreMod", ur_src, urs_src)
}

/// Elaborate one synthetic named module/signature pair in a temp dir.
///
/// # Errors
///
/// I/O, parse, boot settings, `parse_sources`, elaboration, or reported hard errors as `String`.
fn try_elaborate_named_module_pair(
    module_name: &str,
    ur_src: &str,
    urs_src: &str,
) -> Result<(), String> {
    let module_name_owned = module_name.to_string();
    let implementation_text = ur_src.to_string();
    let signature_text = urs_src.to_string();
    run_with_elaboration_stack(move || {
        try_elaborate_named_module_pair_on_thread(
            &module_name_owned,
            &implementation_text,
            &signature_text,
        )
    })
    .flatten()
}

/// Elaborate a synthetic multi-module project in a temp dir.
///
/// `modules` is a list of `(module_name, implementation_source, optional_signature_source)` tuples.
fn try_elaborate_project(
    modules: &[(&str, &str, Option<&str>)],
    urp_lines: &[&str],
) -> Result<(), String> {
    let owned_modules: Vec<(String, String, Option<String>)> = modules
        .iter()
        .map(|(module_name, implementation_source, signature_source)| {
            (
                (*module_name).to_string(),
                (*implementation_source).to_string(),
                signature_source.map(|source| source.to_string()),
            )
        })
        .collect();
    let owned_urp = urp_lines
        .iter()
        .map(|line| (*line).to_string())
        .collect::<Vec<_>>();
    run_with_elaboration_stack(move || {
        let dir = tempdir().map_err(|tempfile_error| tempfile_error.to_string())?; // Isolated temp dir per test invocation.
        let project_root = dir.path(); // Short-lived alias for the temp directory path.
        let urp_text = owned_urp.join("\n") + "\n"; // Reconstruct project descriptor text from lines.
        fs::write(project_root.join("app.urp"), urp_text)
            .map_err(|io_error| io_error.to_string())?; // Write project descriptor.
        for (module_name, implementation_source, signature_source) in &owned_modules {
            fs::write(
                project_root.join(format!("{module_name}.ur")),
                implementation_source,
            )
            .map_err(|io_error| io_error.to_string())?; // Write each module's implementation.
            match signature_source {
                Some(signature_text) => fs::write(
                    project_root.join(format!("{module_name}.urs")),
                    signature_text,
                )
                .map_err(|io_error| io_error.to_string())?, // Write optional module signature.
                None => {} // No signature file for this module.
            }
        }
        let urp = project_root.join("app.urp"); // Path to the project descriptor parsed next.
        let mut job = compiler::parse_urp(&urp).map_err(|parse_error| parse_error.to_string())?; // Parse project descriptor into a Job.
        let mut settings = Settings::new(); // Default settings; boot_linking toggled below.
        settings.boot_linking = true; // Enable Basis linking so the standard library is available.
        let boot_root = corpus_workspace_root()
            .ok_or_else(|| "corpus boot root not found (lib/ur/basis.urs missing)".to_string())?; // Use the once-computed workspace root; fail fast when Basis is absent.
        compiler::apply_boot_settings_with_explicit_root(&mut job, &mut settings, boot_root)?; // Apply boot paths without env-var mutation — safe for concurrent tests.
        let mut errors = ErrorReporter::new_silent(); // Silent reporter: errors are returned as Err strings.
        let Some(file) = compiler::parse_sources(&job, &settings, &mut errors) else {
            return Err(format!("parse_sources: {errors:?}")); // Source parsing failed; surface diagnostics.
        };
        let Some(_elab) = compiler::elaborate(file, &settings, &mut errors) else {
            return Err(format!("elaborate returned None: {errors:?}")); // Elaboration produced no output; surface diagnostics.
        };
        if errors.has_hard_errors() {
            return Err(format!("elaborate errors: {errors:?}")); // Elaboration completed but emitted hard errors.
        }
        Ok(())
    })
    .flatten()
}

/// Elaborate one synthetic module in a temp dir (larger stack supplied by caller).
///
/// No global lock is acquired: each invocation creates its own temp directory and applies the
/// pre-computed workspace root via [`compiler::apply_boot_settings_with_explicit_root`], so
/// multiple elaboration threads can run concurrently.
///
/// # Errors
///
/// I/O, parse, boot settings, `parse_sources`, elaboration, or reported hard errors as `String`.
fn try_elaborate_single_module_on_thread(ur_src: &str) -> Result<(), String> {
    let dir = tempdir().map_err(|tempfile_error| tempfile_error.to_string())?; // Isolated temp dir per test invocation.
    let project_root = dir.path(); // Short-lived alias for the temp directory path.
    fs::write(project_root.join("app.urp"), "CoreMod\n")
        .map_err(|io_error| io_error.to_string())?; // Minimal single-module project file.
    fs::write(project_root.join("CoreMod.ur"), ur_src).map_err(|io_error| io_error.to_string())?; // Write the source under test.
    let urp = project_root.join("app.urp"); // Path to the project descriptor parsed next.
    let mut job = compiler::parse_urp(&urp).map_err(|parse_error| parse_error.to_string())?; // Parse project descriptor into a Job.
    let mut settings = Settings::new(); // Default settings; boot_linking toggled below.
    settings.boot_linking = true; // Enable Basis linking so the standard library is available.
    let boot_root = corpus_workspace_root()
        .ok_or_else(|| "corpus boot root not found (lib/ur/basis.urs missing)".to_string())?; // Use the once-computed workspace root; fail fast when Basis is absent.
    compiler::apply_boot_settings_with_explicit_root(&mut job, &mut settings, boot_root)?; // Apply boot paths without touching env vars — safe for concurrent tests.
    let mut errors = ErrorReporter::new_silent(); // Silent reporter: errors are returned as Err strings.
    let Some(file) = compiler::parse_sources(&job, &settings, &mut errors) else {
        return Err(format!("parse_sources: {errors:?}")); // Source parsing failed; surface diagnostics.
    };
    let Some(_elab) = compiler::elaborate(file, &settings, &mut errors) else {
        return Err(format!("elaborate returned None: {errors:?}")); // Elaboration produced no output; surface diagnostics.
    };
    if errors.has_hard_errors() {
        return Err(format!("elaborate errors: {errors:?}")); // Elaboration completed but emitted hard errors.
    }
    Ok(())
}

/// Elaborate one synthetic named module/signature pair in a temp dir (larger stack supplied by caller).
///
/// No global lock is acquired. Concurrent invocations are safe because each writes to its own
/// temp directory and uses the pre-computed workspace root via
/// [`compiler::apply_boot_settings_with_explicit_root`].
///
/// # Errors
///
/// I/O, parse, boot settings, `parse_sources`, elaboration, or reported hard errors as `String`.
fn try_elaborate_named_module_pair_on_thread(
    module_name: &str,
    ur_src: &str,
    urs_src: &str,
) -> Result<(), String> {
    let dir = tempdir().map_err(|tempfile_error| tempfile_error.to_string())?; // Isolated temp dir per test invocation.
    let project_root = dir.path(); // Short-lived alias for the temp directory path.
    fs::write(project_root.join("app.urp"), format!("{module_name}\n"))
        .map_err(|io_error| io_error.to_string())?; // Project descriptor listing the single module.
    fs::write(project_root.join(format!("{module_name}.ur")), ur_src)
        .map_err(|io_error| io_error.to_string())?; // Implementation source.
    fs::write(project_root.join(format!("{module_name}.urs")), urs_src)
        .map_err(|io_error| io_error.to_string())?; // Signature source.
    let urp = project_root.join("app.urp"); // Path to the project descriptor.
    let mut job = compiler::parse_urp(&urp).map_err(|parse_error| parse_error.to_string())?; // Parse project descriptor into a Job.
    let mut settings = Settings::new(); // Default settings; boot_linking toggled below.
    settings.boot_linking = true; // Enable Basis linking so the standard library is available.
    let boot_root = corpus_workspace_root()
        .ok_or_else(|| "corpus boot root not found (lib/ur/basis.urs missing)".to_string())?; // Use the once-computed workspace root; fail fast when Basis is absent.
    compiler::apply_boot_settings_with_explicit_root(&mut job, &mut settings, boot_root)?; // Apply boot paths without env-var mutation — safe for concurrent tests.
    let mut errors = ErrorReporter::new_silent(); // Silent reporter: errors are returned as Err strings.
    let Some(file) = compiler::parse_sources(&job, &settings, &mut errors) else {
        return Err(format!("parse_sources: {errors:?}")); // Source parsing failed; surface diagnostics.
    };
    let Some(_elab) = compiler::elaborate(file, &settings, &mut errors) else {
        return Err(format!("elaborate returned None: {errors:?}")); // Elaboration produced no output; surface diagnostics.
    };
    if errors.has_hard_errors() {
        return Err(format!("elaborate errors: {errors:?}")); // Elaboration completed but emitted hard errors.
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

#[test]
fn corpus_core_folder_map0_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun useFolder [r ::: {Type}] (fl : folder r) =\n",
        "    fl [fn r :: {Type} => $(map (fn _ :: Type => option) r)]\n",
        "       (fn [nm :: Name] [t :: Type] [rest :: {Type}] [[nm] ~ rest] acc =>\n",
        "           acc ++ {nm = None})\n",
        "       {}\n",
    ))
    .expect("folder map0-style elaboration");
}

#[test]
fn corpus_core_show_option_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localShowOption [t ::: Type] (_ : show t) =\n",
        "    mkShow (fn opt : option t =>\n",
        "               case opt of\n",
        "                   None => \"\"\n",
        "                 | Some x => show x)\n",
    ))
    .expect("show_option-style elaboration");
}

#[test]
fn corpus_core_show_option_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_module_pair(
        concat!(
            "fun show_option [t ::: Type] (_ : show t) =\n",
            "    mkShow (fn opt : option t =>\n",
            "               case opt of\n",
            "                   None => \"\"\n",
            "                 | Some x => show x)\n",
        ),
        "val show_option : t ::: Type -> show t -> show (option t)\n",
    )
    .expect("show_option signature-pair elaboration");
}

#[test]
fn corpus_core_top_prefix_through_show_option_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let top_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("lib/ur/top.ur");
    let Ok(top_source) = fs::read_to_string(top_path) else {
        return;
    };
    let prefix: String = top_source
        .lines()
        .take_while(|line| !line.starts_with("fun read_option "))
        .map(|line| format!("{line}\n"))
        .collect();
    try_elaborate_single_module(&prefix).expect("Top prefix through show_option elaboration");
}

#[test]
fn corpus_core_top_named_prefix_through_show_option_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let top_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("lib/ur/top.ur");
    let Ok(top_source) = fs::read_to_string(top_path) else {
        return;
    };
    let prefix: String = top_source
        .lines()
        .take_while(|line| !line.starts_with("fun read_option "))
        .map(|line| format!("{line}\n"))
        .collect();
    try_elaborate_named_module("Top", &prefix)
        .expect("Top-named prefix through show_option elaboration");
}

#[test]
fn corpus_core_top_named_prefix_through_show_option_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let top_impl_path = manifest_dir.join("lib/ur/top.ur");
    let top_sig_path = manifest_dir.join("lib/ur/top.urs");
    let (Ok(top_impl_source), Ok(top_sig_source)) = (
        fs::read_to_string(top_impl_path),
        fs::read_to_string(top_sig_path),
    ) else {
        return;
    };
    let implementation_prefix: String = top_impl_source
        .lines()
        .take_while(|line| !line.starts_with("fun read_option "))
        .map(|line| format!("{line}\n"))
        .collect();
    let signature_prefix: String = top_sig_source
        .lines()
        .take_while(|line| !line.starts_with("val read_option "))
        .map(|line| format!("{line}\n"))
        .collect();
    try_elaborate_named_module_pair("Top", &implementation_prefix, &signature_prefix)
        .expect("Top-named prefix through show_option signature elaboration");
}

#[test]
fn corpus_core_top_named_prefix_through_query_xi_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let top_impl_path = manifest_dir.join("lib/ur/top.ur");
    let top_sig_path = manifest_dir.join("lib/ur/top.urs");
    let (Ok(top_impl_source), Ok(top_sig_source)) = (
        fs::read_to_string(top_impl_path),
        fs::read_to_string(top_sig_path),
    ) else {
        return;
    };
    let implementation_prefix: String = top_impl_source
        .lines()
        .take_while(|line| !line.starts_with("fun hasRows "))
        .map(|line| format!("{line}\n"))
        .collect();
    let signature_prefix: String = top_sig_source
        .lines()
        .take_while(|line| !line.starts_with("val hasRows "))
        .map(|line| format!("{line}\n"))
        .collect();
    try_elaborate_named_module_pair("Top", &implementation_prefix, &signature_prefix)
        .expect("Top-named prefix through queryXI signature elaboration");
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapux_rev_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let top_impl_path = manifest_dir.join("lib/ur/top.ur");
    let top_sig_path = manifest_dir.join("lib/ur/top.urs");
    let (Ok(top_impl_source), Ok(top_sig_source)) = (
        fs::read_to_string(top_impl_path),
        fs::read_to_string(top_sig_path),
    ) else {
        return;
    };
    let implementation_prefix: String = top_impl_source
        .lines()
        .take_while(|line| !line.starts_with("fun mapUX2 "))
        .map(|line| format!("{line}\n"))
        .collect();
    let signature_prefix: String = top_sig_source
        .lines()
        .take_while(|line| !line.starts_with("val mapUX2 "))
        .map(|line| format!("{line}\n"))
        .collect();
    try_elaborate_named_module_pair("Top", &implementation_prefix, &signature_prefix)
        .expect("Top exact prefix through mapUX_rev signature elaboration");
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapx4_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let top_impl_path = manifest_dir.join("lib/ur/top.ur");
    let top_sig_path = manifest_dir.join("lib/ur/top.urs");
    let (Ok(top_impl_source), Ok(top_sig_source)) = (
        fs::read_to_string(top_impl_path),
        fs::read_to_string(top_sig_path),
    ) else {
        return;
    };
    let implementation_prefix: String = top_impl_source
        .lines()
        .take_while(|line| !line.starts_with("val queryL "))
        .map(|line| format!("{line}\n"))
        .collect();
    let signature_prefix: String = top_sig_source
        .lines()
        .take_while(|line| !line.starts_with("val queryL "))
        .map(|line| format!("{line}\n"))
        .collect();
    try_elaborate_named_module_pair("Top", &implementation_prefix, &signature_prefix)
        .expect("Top exact prefix through mapX4 signature elaboration");
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapux2_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let top_impl_path = manifest_dir.join("lib/ur/top.ur");
    let top_sig_path = manifest_dir.join("lib/ur/top.urs");
    let (Ok(top_impl_source), Ok(top_sig_source)) = (
        fs::read_to_string(top_impl_path),
        fs::read_to_string(top_sig_path),
    ) else {
        return;
    };
    let implementation_prefix: String = top_impl_source
        .lines()
        .take_while(|line| !line.starts_with("fun mapX2 "))
        .map(|line| format!("{line}\n"))
        .collect();
    let signature_prefix: String = top_sig_source
        .lines()
        .take_while(|line| !line.starts_with("val mapX2 "))
        .map(|line| format!("{line}\n"))
        .collect();
    try_elaborate_named_module_pair("Top", &implementation_prefix, &signature_prefix)
        .expect("Top exact prefix through mapUX2 signature elaboration");
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapx2_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let top_impl_path = manifest_dir.join("lib/ur/top.ur");
    let top_sig_path = manifest_dir.join("lib/ur/top.urs");
    let (Ok(top_impl_source), Ok(top_sig_source)) = (
        fs::read_to_string(top_impl_path),
        fs::read_to_string(top_sig_path),
    ) else {
        return;
    };
    let implementation_prefix: String = top_impl_source
        .lines()
        .take_while(|line| !line.starts_with("fun mapX3 "))
        .map(|line| format!("{line}\n"))
        .collect();
    let signature_prefix: String = top_sig_source
        .lines()
        .take_while(|line| !line.starts_with("val mapX3 "))
        .map(|line| format!("{line}\n"))
        .collect();
    try_elaborate_named_module_pair("Top", &implementation_prefix, &signature_prefix)
        .expect("Top exact prefix through mapX2 signature elaboration");
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapx3_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let top_impl_path = manifest_dir.join("lib/ur/top.ur");
    let top_sig_path = manifest_dir.join("lib/ur/top.urs");
    let (Ok(top_impl_source), Ok(top_sig_source)) = (
        fs::read_to_string(top_impl_path),
        fs::read_to_string(top_sig_path),
    ) else {
        return;
    };
    let implementation_prefix: String = top_impl_source
        .lines()
        .take_while(|line| !line.starts_with("fun mapX4 "))
        .map(|line| format!("{line}\n"))
        .collect();
    let signature_prefix: String = top_sig_source
        .lines()
        .take_while(|line| !line.starts_with("val mapX4 "))
        .map(|line| format!("{line}\n"))
        .collect();
    try_elaborate_named_module_pair("Top", &implementation_prefix, &signature_prefix)
        .expect("Top exact prefix through mapX3 signature elaboration");
}

#[test]
fn corpus_core_top_named_full_module_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let top_impl_path = manifest_dir.join("lib/ur/top.ur");
    let top_sig_path = manifest_dir.join("lib/ur/top.urs");
    let (Ok(top_impl_source), Ok(top_sig_source)) = (
        fs::read_to_string(top_impl_path),
        fs::read_to_string(top_sig_path),
    ) else {
        return;
    };
    try_elaborate_named_module_pair("Top", &top_impl_source, &top_sig_source)
        .expect("Top full module/signature elaboration");
}

#[test]
fn corpus_core_read_option_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localReadOption [t ::: Type] (_ : read t) =\n",
        "    mkRead (fn s =>\n",
        "               case s of\n",
        "                   \"\" => None\n",
        "                 | _ => Some (readError s : t))\n",
        "           (fn s =>\n",
        "               case s of\n",
        "                   \"\" => Some None\n",
        "                 | _ => case read s of\n",
        "                            None => None\n",
        "                          | v => Some v)\n",
    ))
    .expect("read_option-style elaboration");
}

#[test]
fn corpus_core_query1_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localQuery1 [t ::: Name] [fs ::: {Type}] [state ::: Type]\n",
        "    (q : sql_query [] [] [t = fs] [])\n",
        "    (f : $fs -> state -> transaction state)\n",
        "    (i : state) =\n",
        "    query q (fn r => f r.t) i\n",
    ))
    .expect("query1-style elaboration");
}

#[test]
fn corpus_core_query1_prime_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localQuery1Prime [t ::: Name] [fs ::: {Type}] [state ::: Type]\n",
        "    (q : sql_query [] [] [t = fs] [])\n",
        "    (f : $fs -> state -> state) (i : state) =\n",
        "    query q (fn r s => return (f r.t s)) i\n",
    ))
    .expect("query1'-style elaboration");
}

#[test]
fn corpus_core_query1_prime_followed_by_val_rev_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localQuery1Prime [t ::: Name] [fs ::: {Type}] [state ::: Type]\n",
        "    (q : sql_query [] [] [t = fs] [])\n",
        "    (f : $fs -> state -> state) (i : state) =\n",
        "    query q (fn r s => return (f r.t s)) i\n",
        "\n",
        "val rev = fn [a] =>\n",
        "    let\n",
        "        fun rev' acc (ls : list a) =\n",
        "            case ls of\n",
        "                [] => acc\n",
        "              | x :: rest => rev' (x :: acc) rest\n",
        "    in\n",
        "        rev' []\n",
        "    end\n",
    ))
    .expect("query1'-then-val-rev elaboration");
}

#[test]
fn corpus_core_rev_with_list_cons_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "val rev = fn [a] =>\n",
        "    let\n",
        "        fun rev' acc (ls : list a) =\n",
        "            case ls of\n",
        "                [] => acc\n",
        "              | x :: rest => rev' (x :: acc) rest\n",
        "    in\n",
        "        rev' []\n",
        "    end\n",
    ))
    .expect("rev/list-cons elaboration");
}

#[test]
fn corpus_core_top_level_val_binding_visible_to_later_decl() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "val id = fn [t] => fn (x : t) => x\n",
        "\n",
        "fun applyId (n : int) = id n\n",
    ))
    .expect("top-level val binding should remain visible");
}

#[test]
fn corpus_core_query_i1_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localQueryI1 [nm ::: Name] [fs ::: {Type}]\n",
        "    (q : sql_query [] [] [nm = fs] [])\n",
        "    (f : $fs -> transaction unit) =\n",
        "    query q\n",
        "          (fn fs _ => f fs.nm)\n",
        "          ()\n",
    ))
    .expect("queryI1-style elaboration");
}

#[test]
fn corpus_core_query_xi_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localRev [a] (ls : list a) : list a =\n",
        "    let\n",
        "        fun rev' ls acc =\n",
        "            case ls of\n",
        "                [] => acc\n",
        "              | x :: rest => rev' rest (x :: acc)\n",
        "    in\n",
        "        rev' ls []\n",
        "    end\n",
        "\n",
        "fun localQueryXI [tables ::: {{Type}}] [exps ::: {Type}] [ctx ::: {Unit}] [inp ::: {Type}]\n",
        "    [tables ~ exps] (q : sql_query [] [] tables exps)\n",
        "    (f : int -> $(exps ++ map (fn fields :: {Type} => $fields) tables)\n",
        "         -> xml ctx inp []) =\n",
        "    let\n",
        "        fun qxi ls i =\n",
        "            case ls of\n",
        "                [] => <xml/>\n",
        "              | x :: rest => <xml>{f i x}{qxi rest (i+1)}</xml>\n",
        "    in\n",
        "        ls <- queryL q;\n",
        "        return (qxi (localRev ls) 0)\n",
        "    end\n",
    ))
    .expect("queryXI-style elaboration");
}

#[test]
fn corpus_core_query_l_with_val_rev_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "val rev = fn [a] =>\n",
        "    let\n",
        "        fun rev' acc (ls : list a) =\n",
        "            case ls of\n",
        "                [] => acc\n",
        "              | x :: rest => rev' (x :: acc) rest\n",
        "    in\n",
        "        rev' []\n",
        "    end\n",
        "\n",
        "fun localQueryL [tables] [exps] [tables ~ exps]\n",
        "    (q : sql_query [] [] tables exps) =\n",
        "    ls <- query q (fn r ls => return (r :: ls)) [];\n",
        "    return (rev ls)\n",
    ))
    .expect("queryL-with-val-rev elaboration");
}

#[test]
fn corpus_core_query_l1_with_val_rev_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "val rev = fn [a] =>\n",
        "    let\n",
        "        fun rev' acc (ls : list a) =\n",
        "            case ls of\n",
        "                [] => acc\n",
        "              | x :: rest => rev' (x :: acc) rest\n",
        "    in\n",
        "        rev' []\n",
        "    end\n",
        "\n",
        "fun localQueryL1 [t ::: Name] [fs ::: {Type}]\n",
        "    (q : sql_query [] [] [t = fs] []) =\n",
        "    ls <- query q (fn r ls => return (r.t :: ls)) [];\n",
        "    return (rev ls)\n",
    ))
    .expect("queryL1-with-val-rev elaboration");
}

#[test]
fn corpus_core_query_i_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localQueryI [tables ::: {{Type}}] [exps ::: {Type}]\n",
        "    [tables ~ exps] (q : sql_query [] [] tables exps)\n",
        "    (f : $(exps ++ map (fn fields :: {Type} => $fields) tables)\n",
        "         -> transaction unit) =\n",
        "    query q\n",
        "          (fn fs _ => f fs)\n",
        "          ()\n",
    ))
    .expect("queryI-style elaboration");
}

#[test]
fn corpus_core_one_or_no_rows1_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localOneOrNoRows1 [nm ::: Name] [fs ::: {Type}]\n",
        "    (q : sql_query [] [] [nm = fs] []) =\n",
        "    query q\n",
        "          (fn rows _ => return (Some rows.nm))\n",
        "          None\n",
    ))
    .expect("oneOrNoRows1-style elaboration");
}

#[test]
fn corpus_core_one_row1_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localOneOrNoRows1 [nm ::: Name] [fs ::: {Type}]\n",
        "    (q : sql_query [] [] [nm = fs] []) =\n",
        "    query q\n",
        "          (fn rows _ => return (Some rows.nm))\n",
        "          None\n",
        "\n",
        "fun localOneRow1 [nm ::: Name] [fs ::: {Type}]\n",
        "    (q : sql_query [] [] [nm = fs] []) =\n",
        "    result <- localOneOrNoRows1 q;\n",
        "    return (case result of\n",
        "                None => error <xml>Query returned no rows</xml>\n",
        "              | Some row => row)\n",
    ))
    .expect("oneRow1-style elaboration");
}

#[test]
fn corpus_core_existential_intro_elim_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con ex = K ==> fn tf :: (K -> Type) =>\n",
        "            res ::: Type -> (choice :: K -> tf choice -> res) -> res\n",
        "\n",
        "fun ex_intro [K] [tf :: K -> Type] [choice :: K] (body : tf choice) : ex tf =\n",
        " fn [res] (f : choice :: K -> tf choice -> res) =>\n",
        "    f [choice] body\n",
        "\n",
        "fun ex_elim [K] [tf ::: K -> Type] (v : ex tf) [res ::: Type] = @@v [res]\n",
    ))
    .expect("existential intro/elim elaboration");
}

#[test]
fn corpus_core_existential_intro_elim_after_constructor_alias_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con foo = fn t :: Type => t\n",
        "\n",
        "con ex = K ==> fn tf :: (K -> Type) =>\n",
        "            res ::: Type -> (choice :: K -> tf choice -> res) -> res\n",
        "\n",
        "fun ex_intro [K] [tf :: K -> Type] [choice :: K] (body : tf choice) : ex tf =\n",
        " fn [res] (f : choice :: K -> tf choice -> res) =>\n",
        "    f [choice] body\n",
        "\n",
        "fun ex_elim [K] [tf ::: K -> Type] (v : ex tf) [res ::: Type] = @@v [res]\n",
    ))
    .expect("existential intro/elim after constructor alias elaboration");
}

#[test]
fn corpus_core_mapx_via_foldr_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun localMapX [K] [tf :: K -> Type] [ctx :: {Unit}]\n",
        "               (f : nm :: Name -> t :: K -> rest :: {K}\n",
        "                    -> [[nm] ~ rest] =>\n",
        "                    tf t -> xml ctx [] []) =\n",
        "    @@foldR [tf] [fn _ => xml ctx [] []]\n",
        "      (fn [nm :: Name] [t :: K] [rest :: {K}] [[nm] ~ rest] r acc =>\n",
        "          <xml>{f [nm] [t] [rest] r}{acc}</xml>)\n",
        "      <xml/>\n",
    ))
    .expect("mapX-style foldR elaboration");
}

#[test]
fn corpus_core_mapx_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_module_pair(
        concat!(
            "fun localMapX [K] [tf :: K -> Type] [ctx :: {Unit}]\n",
            "               (f : nm :: Name -> t :: K -> rest :: {K}\n",
            "                    -> [[nm] ~ rest] =>\n",
            "                    tf t -> xml ctx [] []) =\n",
            "    @@foldR [tf] [fn _ => xml ctx [] []]\n",
            "      (fn [nm :: Name] [t :: K] [rest :: {K}] [[nm] ~ rest] r acc =>\n",
            "          <xml>{f [nm] [t] [rest] r}{acc}</xml>)\n",
            "      <xml/>\n",
        ),
        concat!(
            "val localMapX : K --> tf :: (K -> Type) -> ctx :: {Unit}\n",
            "                -> (nm :: Name -> t :: K -> rest :: {K}\n",
            "                    -> [[nm] ~ rest] =>\n",
            "                    tf t -> xml ctx [] [])\n",
            "                -> r ::: {K} -> folder r -> $(map tf r) -> xml ctx [] []\n",
        ),
    )
    .expect("mapX-style signature elaboration");
}

#[test]
fn corpus_core_local_folder_foldr_mapx_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_module_pair(
        concat!(
            "con folder = K ==> fn r :: {K} =>\n",
            "                  tf :: ({K} -> Type)\n",
            "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
            "                      tf r -> tf ([nm = v] ++ r))\n",
            "                  -> tf [] -> tf r\n",
            "\n",
            "fun foldR [K] [tf :: K -> Type] [tr :: {K} -> Type]\n",
            "          (f : nm :: Name -> t :: K -> rest :: {K}\n",
            "               -> [[nm] ~ rest] =>\n",
            "               tf t -> tr rest -> tr ([nm = t] ++ rest))\n",
            "          (i : tr []) [r ::: {K}] (fl : folder r) =\n",
            "    fl [fn r :: {K} => $(map tf r) -> tr r]\n",
            "       (fn [nm :: Name] [t :: K] [rest :: {K}] [[nm] ~ rest] (acc : _ -> tr rest) r =>\n",
            "           f [nm] [t] [rest] r.nm (acc (r -- nm)))\n",
            "       (fn _ => i)\n",
            "\n",
            "fun mapX [K] [tf :: K -> Type] [ctx :: {Unit}]\n",
            "          (f : nm :: Name -> t :: K -> rest :: {K}\n",
            "               -> [[nm] ~ rest] =>\n",
            "               tf t -> xml ctx [] []) =\n",
            "    @@foldR [tf] [fn _ => xml ctx [] []]\n",
            "      (fn [nm :: Name] [t :: K] [rest :: {K}] [[nm] ~ rest] r acc =>\n",
            "          <xml>{f [nm] [t] [rest] r}{acc}</xml>)\n",
            "      <xml/>\n",
        ),
        concat!(
            "con folder :: K --> {K} -> Type\n",
            "val foldR : K --> tf :: (K -> Type) -> tr :: ({K} -> Type)\n",
            "            -> (nm :: Name -> t :: K -> rest :: {K}\n",
            "                -> [[nm] ~ rest] =>\n",
            "                tf t -> tr rest -> tr ([nm = t] ++ rest))\n",
            "            -> tr [] -> r ::: {K} -> folder r -> $(map tf r) -> tr r\n",
            "val mapX : K --> tf :: (K -> Type) -> ctx :: {Unit}\n",
            "           -> (nm :: Name -> t :: K -> rest :: {K}\n",
            "               -> [[nm] ~ rest] =>\n",
            "               tf t -> xml ctx [] [])\n",
            "           -> r ::: {K} -> folder r -> $(map tf r) -> xml ctx [] []\n",
        ),
    )
    .expect("local folder/foldR/mapX signature elaboration");
}

#[test]
fn corpus_core_top_named_folder_foldr_mapx_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_named_module_pair(
        "Top",
        concat!(
            "con folder = K ==> fn r :: {K} =>\n",
            "                  tf :: ({K} -> Type)\n",
            "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
            "                      tf r -> tf ([nm = v] ++ r))\n",
            "                  -> tf [] -> tf r\n",
            "\n",
            "fun foldR [K] [tf :: K -> Type] [tr :: {K} -> Type]\n",
            "          (f : nm :: Name -> t :: K -> rest :: {K}\n",
            "               -> [[nm] ~ rest] =>\n",
            "               tf t -> tr rest -> tr ([nm = t] ++ rest))\n",
            "          (i : tr []) [r ::: {K}] (fl : folder r) =\n",
            "    fl [fn r :: {K} => $(map tf r) -> tr r]\n",
            "       (fn [nm :: Name] [t :: K] [rest :: {K}] [[nm] ~ rest] (acc : _ -> tr rest) r =>\n",
            "           f [nm] [t] [rest] r.nm (acc (r -- nm)))\n",
            "       (fn _ => i)\n",
            "\n",
            "fun mapX [K] [tf :: K -> Type] [ctx :: {Unit}]\n",
            "          (f : nm :: Name -> t :: K -> rest :: {K}\n",
            "               -> [[nm] ~ rest] =>\n",
            "               tf t -> xml ctx [] []) =\n",
            "    @@foldR [tf] [fn _ => xml ctx [] []]\n",
            "      (fn [nm :: Name] [t :: K] [rest :: {K}] [[nm] ~ rest] r acc =>\n",
            "          <xml>{f [nm] [t] [rest] r}{acc}</xml>)\n",
            "      <xml/>\n",
        ),
        concat!(
            "con folder :: K --> {K} -> Type\n",
            "val foldR : K --> tf :: (K -> Type) -> tr :: ({K} -> Type)\n",
            "            -> (nm :: Name -> t :: K -> rest :: {K}\n",
            "                -> [[nm] ~ rest] =>\n",
            "                tf t -> tr rest -> tr ([nm = t] ++ rest))\n",
            "            -> tr [] -> r ::: {K} -> folder r -> $(map tf r) -> tr r\n",
            "val mapX : K --> tf :: (K -> Type) -> ctx :: {Unit}\n",
            "           -> (nm :: Name -> t :: K -> rest :: {K}\n",
            "               -> [[nm] ~ rest] =>\n",
            "               tf t -> xml ctx [] [])\n",
            "           -> r ::: {K} -> folder r -> $(map tf r) -> xml ctx [] []\n",
        ),
    )
    .expect("Top-named local folder/foldR/mapX signature elaboration");
}

#[test]
fn corpus_core_top_named_foldr4_mapux_mapx_prefix_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_named_module_pair(
        "Top",
        concat!(
            "con folder = K ==> fn r :: {K} =>\n",
            "                  tf :: ({K} -> Type)\n",
            "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
            "                      tf r -> tf ([nm = v] ++ r))\n",
            "                  -> tf [] -> tf r\n",
            "\n",
            "fun foldR [K] [tf :: K -> Type] [tr :: {K} -> Type]\n",
            "          (f : nm :: Name -> t :: K -> rest :: {K}\n",
            "               -> [[nm] ~ rest] =>\n",
            "               tf t -> tr rest -> tr ([nm = t] ++ rest))\n",
            "          (i : tr []) [r ::: {K}] (fl : folder r) =\n",
            "    fl [fn r :: {K} => $(map tf r) -> tr r]\n",
            "       (fn [nm :: Name] [t :: K] [rest :: {K}] [[nm] ~ rest] (acc : _ -> tr rest) r =>\n",
            "           f [nm] [t] [rest] r.nm (acc (r -- nm)))\n",
            "       (fn _ => i)\n",
            "\n",
            "fun foldR4 [K] [tf1 :: K -> Type] [tf2 :: K -> Type]\n",
            "           [tf3 :: K -> Type] [tf4 :: K -> Type] [tr :: {K} -> Type]\n",
            "           (f : nm :: Name -> t :: K -> rest :: {K}\n",
            "                -> [[nm] ~ rest] =>\n",
            "                tf1 t -> tf2 t -> tf3 t -> tf4 t -> tr rest -> tr ([nm = t] ++ rest))\n",
            "           (i : tr []) [r ::: {K}] (fl : folder r) =\n",
            "    fl [fn r :: {K} => $(map tf1 r) -> $(map tf2 r) -> $(map tf3 r) -> $(map tf4 r) -> tr r]\n",
            "       (fn [nm :: Name] [t :: K] [rest :: {K}] [[nm] ~ rest]\n",
            "                        (acc : _ -> _ -> _ -> _ -> tr rest) r1 r2 r3 r4 =>\n",
            "           f [nm] [t] [rest] r1.nm r2.nm r3.nm r4.nm\n",
            "             (acc (r1 -- nm) (r2 -- nm) (r3 -- nm) (r4 -- nm)))\n",
            "       (fn _ _ _ _ => i)\n",
            "\n",
            "fun mapUX [tf :: Type] [ctx :: {Unit}]\n",
            "          (f : nm :: Name -> rest :: {Unit} -> [[nm] ~ rest] => tf -> xml ctx [] []) =\n",
            "    @@foldR [fn _ => tf] [fn _ => xml ctx [] []]\n",
            "      (fn [nm :: Name] [u :: Unit] [rest :: {Unit}] [[nm] ~ rest] r acc =>\n",
            "          <xml>{f [nm] [rest] r}{acc}</xml>)\n",
            "      <xml/>\n",
            "\n",
            "fun mapX [K] [tf :: K -> Type] [ctx :: {Unit}]\n",
            "          (f : nm :: Name -> t :: K -> rest :: {K}\n",
            "               -> [[nm] ~ rest] => tf t -> xml ctx [] []) =\n",
            "    @@foldR [tf] [fn _ => xml ctx [] []]\n",
            "      (fn [nm :: Name] [t :: K] [rest :: {K}] [[nm] ~ rest] r acc =>\n",
            "          <xml>{f [nm] [t] [rest] r}{acc}</xml>)\n",
            "      <xml/>\n",
        ),
        concat!(
            "con folder :: K --> {K} -> Type\n",
            "val foldR : K --> tf :: (K -> Type) -> tr :: ({K} -> Type)\n",
            "            -> (nm :: Name -> t :: K -> rest :: {K}\n",
            "                -> [[nm] ~ rest] =>\n",
            "                tf t -> tr rest -> tr ([nm = t] ++ rest))\n",
            "            -> tr [] -> r ::: {K} -> folder r -> $(map tf r) -> tr r\n",
            "val foldR4 : K --> tf1 :: (K -> Type) -> tf2 :: (K -> Type)\n",
            "             -> tf3 :: (K -> Type) -> tf4 :: (K -> Type) -> tr :: ({K} -> Type)\n",
            "             -> (nm :: Name -> t :: K -> rest :: {K}\n",
            "                 -> [[nm] ~ rest] =>\n",
            "                 tf1 t -> tf2 t -> tf3 t -> tf4 t -> tr rest -> tr ([nm = t] ++ rest))\n",
            "             -> tr [] -> r ::: {K} -> folder r\n",
            "             -> $(map tf1 r) -> $(map tf2 r) -> $(map tf3 r) -> $(map tf4 r) -> tr r\n",
            "val mapUX : tf :: Type -> ctx :: {Unit}\n",
            "            -> (nm :: Name -> rest :: {Unit} -> [[nm] ~ rest] => tf -> xml ctx [] [])\n",
            "            -> r ::: {Unit} -> folder r -> $(mapU tf r) -> xml ctx [] []\n",
            "val mapX : K --> tf :: (K -> Type) -> ctx :: {Unit}\n",
            "           -> (nm :: Name -> t :: K -> rest :: {K}\n",
            "               -> [[nm] ~ rest] => tf t -> xml ctx [] [])\n",
            "           -> r ::: {K} -> folder r -> $(map tf r) -> xml ctx [] []\n",
        ),
    )
    .expect("Top-named foldR4/mapUX/mapX prefix elaboration");
}

#[test]
fn corpus_core_local_folder_foldur2_mapux2_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_module_pair(
        concat!(
            "con folder = K ==> fn r :: {K} =>\n",
            "                  tf :: ({K} -> Type)\n",
            "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
            "                      tf r -> tf ([nm = v] ++ r))\n",
            "                  -> tf [] -> tf r\n",
            "\n",
            "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
            "\n",
            "fun foldUR2 [tf1 :: Type] [tf2 :: Type] [tr :: {Unit} -> Type]\n",
            "            (f : nm :: Name -> rest :: {Unit}\n",
            "                 -> [[nm] ~ rest] =>\n",
            "                 tf1 -> tf2 -> tr rest -> tr ([nm] ++ rest))\n",
            "            (i : tr []) [r ::: {Unit}] (fl : folder r) =\n",
            "    fl [fn r :: {Unit} => $(mapU tf1 r) -> $(mapU tf2 r) -> tr r]\n",
            "       (fn [nm :: Name] [t :: Unit] [rest :: {Unit}] [[nm] ~ rest] acc r1 r2 =>\n",
            "           f [nm] [rest] r1.nm r2.nm (acc (r1 -- nm) (r2 -- nm)))\n",
            "       (fn _ _ => i)\n",
            "\n",
            "fun mapUX2 [tf1 :: Type] [tf2 :: Type] [ctx :: {Unit}]\n",
            "           (f : nm :: Name -> rest :: {Unit}\n",
            "                -> [[nm] ~ rest] =>\n",
            "                tf1 -> tf2 -> xml ctx [] []) =\n",
            "    @@foldUR2 [tf1] [tf2] [fn _ => xml ctx [] []]\n",
            "      (fn [nm :: Name] [rest :: {Unit}] [[nm] ~ rest] v1 v2 acc =>\n",
            "          <xml>{f [nm] [rest] v1 v2}{acc}</xml>)\n",
            "      <xml/>\n",
        ),
        concat!(
            "con folder :: K --> {K} -> Type\n",
            "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
            "val foldUR2 : tf1 :: Type -> tf2 :: Type -> tr :: ({Unit} -> Type)\n",
            "              -> (nm :: Name -> rest :: {Unit}\n",
            "                  -> [[nm] ~ rest] =>\n",
            "                  tf1 -> tf2 -> tr rest -> tr ([nm] ++ rest))\n",
            "              -> tr [] -> r ::: {Unit} -> folder r -> $(mapU tf1 r) -> $(mapU tf2 r) -> tr r\n",
            "val mapUX2 : tf1 :: Type -> tf2 :: Type -> ctx :: {Unit}\n",
            "             -> (nm :: Name -> rest :: {Unit}\n",
            "                 -> [[nm] ~ rest] => tf1 -> tf2 -> xml ctx [] [])\n",
            "             -> r ::: {Unit} -> folder r -> $(mapU tf1 r) -> $(mapU tf2 r) -> xml ctx [] []\n",
        ),
    )
    .expect("local folder/foldUR2/mapUX2 signature elaboration");
}

#[test]
fn corpus_core_local_folder_foldur2_mapux2_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con folder = K ==> fn r :: {K} =>\n",
        "                  tf :: ({K} -> Type)\n",
        "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
        "                      tf r -> tf ([nm = v] ++ r))\n",
        "                  -> tf [] -> tf r\n",
        "\n",
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "\n",
        "fun foldUR2 [tf1 :: Type] [tf2 :: Type] [tr :: {Unit} -> Type]\n",
        "            (f : nm :: Name -> rest :: {Unit}\n",
        "                 -> [[nm] ~ rest] =>\n",
        "                 tf1 -> tf2 -> tr rest -> tr ([nm] ++ rest))\n",
        "            (i : tr []) [r ::: {Unit}] (fl : folder r) =\n",
        "    fl [fn r :: {Unit} => $(mapU tf1 r) -> $(mapU tf2 r) -> tr r]\n",
        "       (fn [nm :: Name] [t :: Unit] [rest :: {Unit}] [[nm] ~ rest] acc r1 r2 =>\n",
        "           f [nm] [rest] r1.nm r2.nm (acc (r1 -- nm) (r2 -- nm)))\n",
        "       (fn _ _ => i)\n",
        "\n",
        "fun mapUX2 [tf1 :: Type] [tf2 :: Type] [ctx :: {Unit}]\n",
        "           (f : nm :: Name -> rest :: {Unit}\n",
        "                -> [[nm] ~ rest] =>\n",
        "                tf1 -> tf2 -> xml ctx [] []) =\n",
        "    @@foldUR2 [tf1] [tf2] [fn _ => xml ctx [] []]\n",
        "      (fn [nm :: Name] [rest :: {Unit}] [[nm] ~ rest] v1 v2 acc =>\n",
        "          <xml>{f [nm] [rest] v1 v2}{acc}</xml>)\n",
        "      <xml/>\n",
    ))
    .expect("local folder/foldUR2/mapUX2 elaboration");
}

#[test]
fn corpus_core_local_folder_foldur2_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con folder = K ==> fn r :: {K} =>\n",
        "                  tf :: ({K} -> Type)\n",
        "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
        "                      tf r -> tf ([nm = v] ++ r))\n",
        "                  -> tf [] -> tf r\n",
        "\n",
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "\n",
        "fun foldUR2 [tf1 :: Type] [tf2 :: Type] [tr :: {Unit} -> Type]\n",
        "            (f : nm :: Name -> rest :: {Unit}\n",
        "                 -> [[nm] ~ rest] =>\n",
        "                 tf1 -> tf2 -> tr rest -> tr ([nm] ++ rest))\n",
        "            (i : tr []) [r ::: {Unit}] (fl : folder r) =\n",
        "    fl [fn r :: {Unit} => $(mapU tf1 r) -> $(mapU tf2 r) -> tr r]\n",
        "       (fn [nm :: Name] [t :: Unit] [rest :: {Unit}] [[nm] ~ rest] acc r1 r2 =>\n",
        "           f [nm] [rest] r1.nm r2.nm (acc (r1 -- nm) (r2 -- nm)))\n",
        "       (fn _ _ => i)\n",
    ))
    .expect("local folder/foldUR2 elaboration");
}

#[test]
fn corpus_core_local_folder_foldur2_partial_constructor_application_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con folder = K ==> fn r :: {K} =>\n",
        "                  tf :: ({K} -> Type)\n",
        "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
        "                      tf r -> tf ([nm = v] ++ r))\n",
        "                  -> tf [] -> tf r\n",
        "\n",
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "\n",
        "fun partial [tf1 :: Type] [tf2 :: Type] [tr :: {Unit} -> Type] [r ::: {Unit}]\n",
        "            (fl : folder r) =\n",
        "    fl [fn r :: {Unit} => $(mapU tf1 r) -> $(mapU tf2 r) -> tr r]\n",
    ))
    .expect("foldUR2 partial constructor application elaboration");
}

#[test]
fn corpus_core_mapu_binary_row_transform_constructor_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "con localTf = tf1 :: Type => tf2 :: Type => tr :: ({Unit} -> Type)\n",
        "              => fn r :: {Unit} => $(mapU tf1 r) -> $(mapU tf2 r) -> tr r\n",
    ))
    .expect("binary mapU row transform constructor elaboration");
}

#[test]
fn corpus_core_mapu_unary_row_transform_constructor_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "con localTf = tf1 :: Type => fn r :: {Unit} => $(mapU tf1 r)\n",
    ))
    .expect("unary mapU row transform constructor elaboration");
}

#[test]
fn corpus_core_mapu_row_constructor_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "con localRow = tf1 :: Type => fn r :: {Unit} => mapU tf1 r\n",
    ))
    .expect("mapU row constructor elaboration");
}

#[test]
fn corpus_core_mapu_partial_constructor_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "con localMap = tf1 :: Type => mapU tf1\n",
    ))
    .expect("mapU partial constructor elaboration");
}

#[test]
fn corpus_core_trecord_unit_row_constructor_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module("con localRecord = fn r :: {Type} => $r\n")
        .expect("trecord constructor elaboration");
}

#[test]
fn corpus_core_local_folder_foldur2_partial_callback_application_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con folder = K ==> fn r :: {K} =>\n",
        "                  tf :: ({K} -> Type)\n",
        "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
        "                      tf r -> tf ([nm = v] ++ r))\n",
        "                  -> tf [] -> tf r\n",
        "\n",
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "\n",
        "fun partial [tf1 :: Type] [tf2 :: Type] [tr :: {Unit} -> Type] [r ::: {Unit}]\n",
        "            (f : nm :: Name -> rest :: {Unit}\n",
        "                 -> [[nm] ~ rest] =>\n",
        "                 tf1 -> tf2 -> tr rest -> tr ([nm] ++ rest))\n",
        "            (fl : folder r) =\n",
        "    fl [fn r :: {Unit} => $(mapU tf1 r) -> $(mapU tf2 r) -> tr r]\n",
        "       (fn [nm :: Name] [t :: Unit] [rest :: {Unit}] [[nm] ~ rest] acc r1 r2 =>\n",
        "           f [nm] [rest] r1.nm r2.nm (acc (r1 -- nm) (r2 -- nm)))\n",
    ))
    .expect("foldUR2 partial callback application elaboration");
}

#[test]
fn corpus_core_local_folder_foldur2_mapux2_acc_only_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con folder = K ==> fn r :: {K} =>\n",
        "                  tf :: ({K} -> Type)\n",
        "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
        "                      tf r -> tf ([nm = v] ++ r))\n",
        "                  -> tf [] -> tf r\n",
        "\n",
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "\n",
        "fun foldUR2 [tf1 :: Type] [tf2 :: Type] [tr :: {Unit} -> Type]\n",
        "            (f : nm :: Name -> rest :: {Unit}\n",
        "                 -> [[nm] ~ rest] =>\n",
        "                 tf1 -> tf2 -> tr rest -> tr ([nm] ++ rest))\n",
        "            (i : tr []) [r ::: {Unit}] (fl : folder r) =\n",
        "    fl [fn r :: {Unit} => $(mapU tf1 r) -> $(mapU tf2 r) -> tr r]\n",
        "       (fn [nm :: Name] [t :: Unit] [rest :: {Unit}] [[nm] ~ rest] acc r1 r2 =>\n",
        "           f [nm] [rest] r1.nm r2.nm (acc (r1 -- nm) (r2 -- nm)))\n",
        "       (fn _ _ => i)\n",
        "\n",
        "fun mapUX2 [tf1 :: Type] [tf2 :: Type] [ctx :: {Unit}]\n",
        "           (f : nm :: Name -> rest :: {Unit}\n",
        "                -> [[nm] ~ rest] =>\n",
        "                tf1 -> tf2 -> xml ctx [] []) =\n",
        "    @@foldUR2 [tf1] [tf2] [fn _ => xml ctx [] []]\n",
        "      (fn [nm :: Name] [rest :: {Unit}] [[nm] ~ rest] v1 v2 acc => acc)\n",
        "      <xml/>\n",
    ))
    .expect("local folder/foldUR2/mapUX2 acc-only elaboration");
}

#[test]
fn corpus_core_local_folder_foldur2_mapux2_no_acc_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "con folder = K ==> fn r :: {K} =>\n",
        "                  tf :: ({K} -> Type)\n",
        "                  -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>\n",
        "                      tf r -> tf ([nm = v] ++ r))\n",
        "                  -> tf [] -> tf r\n",
        "\n",
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "\n",
        "fun foldUR2 [tf1 :: Type] [tf2 :: Type] [tr :: {Unit} -> Type]\n",
        "            (f : nm :: Name -> rest :: {Unit}\n",
        "                 -> [[nm] ~ rest] =>\n",
        "                 tf1 -> tf2 -> tr rest -> tr ([nm] ++ rest))\n",
        "            (i : tr []) [r ::: {Unit}] (fl : folder r) =\n",
        "    fl [fn r :: {Unit} => $(mapU tf1 r) -> $(mapU tf2 r) -> tr r]\n",
        "       (fn [nm :: Name] [t :: Unit] [rest :: {Unit}] [[nm] ~ rest] acc r1 r2 =>\n",
        "           f [nm] [rest] r1.nm r2.nm (acc (r1 -- nm) (r2 -- nm)))\n",
        "       (fn _ _ => i)\n",
        "\n",
        "fun mapUX2 [tf1 :: Type] [tf2 :: Type] [ctx :: {Unit}]\n",
        "           (f : nm :: Name -> rest :: {Unit}\n",
        "                -> [[nm] ~ rest] =>\n",
        "                tf1 -> tf2 -> xml ctx [] []) =\n",
        "    @@foldUR2 [tf1] [tf2] [fn _ => xml ctx [] []]\n",
        "      (fn [nm :: Name] [rest :: {Unit}] [[nm] ~ rest] v1 v2 acc =>\n",
        "          f [nm] [rest] v1 v2)\n",
        "      <xml/>\n",
    ))
    .expect("local folder/foldUR2/mapUX2 no-acc elaboration");
}

#[test]
fn corpus_core_sql_nonempty_and_eqnullable_elaborate() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun oneOrNoRows [tabs ::: {{Type}}] [exps ::: {Type}] [tables ~ exps]\n",
        "                (q : sql_query [] [] tables exps) = return None\n",
        "\n",
        "fun oneRowE1 [tabs ::: {Unit}] [nm ::: Name] [t ::: Type] [tabs ~ [nm]]\n",
        "             (q : sql_query [] [] (mapU [] tabs) [nm = t]) =\n",
        "    o <- oneOrNoRows q;\n",
        "    return (case o of None => error <xml>Query returned no rows</xml> | Some r => r.nm)\n",
        "\n",
        "fun nonempty [fs] [us] (t : sql_table fs us) =\n",
        "    oneRowE1 (SELECT COUNT( * ) > 0 AS B FROM t)\n",
        "\n",
        "fun eqNullable [tables ::: {{Type}}] [agg ::: {{Type}}] [exps ::: {Type}]\n",
        "    [t ::: Type] (_ : sql_injectable (option t))\n",
        "    (e1 : sql_exp tables agg exps (option t))\n",
        "    (e2 : sql_exp tables agg exps (option t)) =\n",
        "    (SQL ({e1} IS NULL AND {e2} IS NULL) OR {e1} = {e2})\n",
        "\n",
        "fun eqNullable' [tables ::: {{Type}}] [agg ::: {{Type}}] [exps ::: {Type}]\n",
        "    [t ::: Type] (_ : sql_injectable (option t))\n",
        "    (e1 : sql_exp tables agg exps (option t))\n",
        "    (e2 : option t) =\n",
        "    case e2 of\n",
        "        None => (SQL {e1} IS NULL)\n",
        "      | Some _ => sql_binary sql_eq e1 (sql_inject e2)\n",
    ))
    .expect("narrow SQL surface elaboration");
}

#[test]
fn corpus_core_sql_count_star_placeholder_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun oneOrNoRows [tabs ::: {{Type}}] [exps ::: {Type}] [tables ~ exps]\n",
        "                (q : sql_query [] [] tables exps) = return None\n",
        "\n",
        "fun oneRowE1 [tabs ::: {Unit}] [nm ::: Name] [t ::: Type] [tabs ~ [nm]]\n",
        "             (q : sql_query [] [] (mapU [] tabs) [nm = t]) =\n",
        "    o <- oneOrNoRows q;\n",
        "    return (case o of None => error <xml>Query returned no rows</xml> | Some r => r.nm)\n",
        "\n",
        "fun nonempty [fs] [us] (t : sql_table fs us) =\n",
        "    oneRowE1 (SELECT COUNT(sql_star) > 0 AS B FROM t)\n",
    ))
    .expect("sql_star placeholder elaboration");
}

#[test]
fn corpus_core_sql_default_table_field_where_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "functor Make(M : sig\n",
        "                 type data\n",
        "                 val inj : sql_injectable data\n",
        "             end) = struct\n",
        "\n",
        "    type ref = int\n",
        "\n",
        "    sequence s\n",
        "    table t : { Id : int, Data : M.data }\n",
        "      PRIMARY KEY Id\n",
        "\n",
        "    fun new d =\n",
        "        id <- nextval s;\n",
        "        dml (INSERT INTO t (Id, Data) VALUES ({[id]}, {[d]}));\n",
        "        return id\n",
        "\n",
        "    fun read r =\n",
        "        o <- oneOrNoRows (SELECT t.Data FROM t WHERE t.Id = {[r]});\n",
        "        case o of\n",
        "            None => error <xml>gone</xml>\n",
        "          | Some row => return row.T.Data\n",
        "\n",
        "    fun write r d =\n",
        "        dml (UPDATE t SET Data = {[d]} WHERE Id = {[r]})\n",
        "\n",
        "    fun delete r =\n",
        "        dml (DELETE FROM t WHERE Id = {[r]})\n",
        "\n",
        "end\n",
    ))
    .expect("default-table SQL field compatibility");
}

#[test]
fn corpus_core_sql_single_selected_field_preserves_type_shape() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "table channels : { Client : client, Channel : channel (string * int * float) }\n",
        "  PRIMARY KEY Client\n",
        "\n",
        "fun writeBack v =\n",
        "    me <- self;\n",
        "    r <- oneRow (SELECT channels.Channel FROM channels WHERE channels.Client = {[me]});\n",
        "    send r.Channels.Channel v\n",
    ))
    .expect("single selected SQL field keeps wildcard type information");
}

#[test]
fn corpus_core_recursive_user_list_datatype_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "datatype list t = Nil | Cons of t * list t\n",
        "\n",
        "fun length [t] (ls : list t) =\n",
        "    let\n",
        "        fun length' (ls : list t) (acc : int) =\n",
        "            case ls of\n",
        "                Nil => acc\n",
        "              | Cons (_, ls') => length' ls' (acc + 1)\n",
        "    in\n",
        "        length' ls 0\n",
        "    end\n",
        "\n",
        "fun rev [t] (ls : list t) =\n",
        "    let\n",
        "        fun rev' (ls : list t) (acc : list t) =\n",
        "            case ls of\n",
        "                Nil => acc\n",
        "              | Cons (x, ls') => rev' ls' (Cons (x, acc))\n",
        "    in\n",
        "        rev' ls Nil\n",
        "    end\n",
    ))
    .expect("recursive user-defined list datatype elaboration");
}

#[test]
fn corpus_core_demo_list_signature_pair_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_module_pair(
        concat!(
            "datatype list t = Nil | Cons of t * list t\n",
            "\n",
            "fun length [t] (ls : list t) =\n",
            "    let\n",
            "        fun length' (ls : list t) (acc : int) =\n",
            "            case ls of\n",
            "                Nil => acc\n",
            "              | Cons (_, ls') => length' ls' (acc + 1)\n",
            "    in\n",
            "        length' ls 0\n",
            "    end\n",
            "\n",
            "fun rev [t] (ls : list t) =\n",
            "    let\n",
            "        fun rev' (ls : list t) (acc : list t) =\n",
            "            case ls of\n",
            "                Nil => acc\n",
            "              | Cons (x, ls') => rev' ls' (Cons (x, acc))\n",
            "    in\n",
            "        rev' ls Nil\n",
            "    end\n",
        ),
        concat!(
            "datatype list t = Nil | Cons of t * list t\n",
            "\n",
            "val length : t ::: Type -> list t -> int\n",
            "\n",
            "val rev : t ::: Type -> list t -> list t\n",
        ),
    )
    .expect("demo list signature pair elaboration");
}

#[test]
fn corpus_core_demo_list_shop_project_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_project(
        &[
            (
                "List",
                concat!(
                    "datatype list t = Nil | Cons of t * list t\n",
                    "\n",
                    "fun length [t] (ls : list t) =\n",
                    "    let\n",
                    "        fun length' (ls : list t) (acc : int) =\n",
                    "            case ls of\n",
                    "                Nil => acc\n",
                    "              | Cons (_, ls') => length' ls' (acc + 1)\n",
                    "    in\n",
                    "        length' ls 0\n",
                    "    end\n",
                    "\n",
                    "fun rev [t] (ls : list t) =\n",
                    "    let\n",
                    "        fun rev' (ls : list t) (acc : list t) =\n",
                    "            case ls of\n",
                    "                Nil => acc\n",
                    "              | Cons (x, ls') => rev' ls' (Cons (x, acc))\n",
                    "    in\n",
                    "        rev' ls Nil\n",
                    "    end\n",
                ),
                Some(concat!(
                    "datatype list t = Nil | Cons of t * list t\n",
                    "\n",
                    "val length : t ::: Type -> list t -> int\n",
                    "\n",
                    "val rev : t ::: Type -> list t -> list t\n",
                )),
            ),
            (
                "ListFun",
                concat!(
                    "open List\n",
                    "\n",
                    "functor Make(M : sig\n",
                    "                 type t\n",
                    "                 val toString : t -> string\n",
                    "                 val fromString : string -> option t\n",
                    "             end) = struct\n",
                    "    fun toXml (ls : list M.t) =\n",
                    "        case ls of\n",
                    "            Nil => <xml>[]</xml>\n",
                    "          | Cons (x, ls') => <xml>{[M.toString x]} :: {toXml ls'}</xml>\n",
                    "\n",
                    "    fun console (ls : list M.t) =\n",
                    "        let\n",
                    "            fun cons (r : {X : string}) =\n",
                    "                case M.fromString r.X of\n",
                    "                    None => return <xml><body>Invalid string!</body></xml>\n",
                    "                  | Some v => console (Cons (v, ls))\n",
                    "        in\n",
                    "            return <xml><body>\n",
                    "              Current list: {toXml ls}<br/>\n",
                    "              Reversed list: {toXml (rev ls)}<br/>\n",
                    "              Length: {[length ls]}<br/>\n",
                    "              <br/>\n",
                    "\n",
                    "              <form>\n",
                    "                Add element: <textbox{#X}/> <submit action={cons}/>\n",
                    "              </form>\n",
                    "            </body></xml>\n",
                    "        end\n",
                    "\n",
                    "    fun main () = console Nil\n",
                    "end\n",
                ),
                Some(concat!(
                    "functor Make(M : sig\n",
                    "                 type t\n",
                    "                 val toString : t -> string\n",
                    "                 val fromString : string -> option t\n",
                    "             end) : sig\n",
                    "    val main : unit -> transaction page\n",
                    "end\n",
                )),
            ),
            (
                "ListShop",
                concat!(
                    "structure I = struct\n",
                    "    type t = int\n",
                    "    val toString = show\n",
                    "    val fromString = read\n",
                    "end\n",
                    "\n",
                    "structure S = struct\n",
                    "    type t = string\n",
                    "    val toString = show\n",
                    "    val fromString = read\n",
                    "end\n",
                    "\n",
                    "structure IL = ListFun.Make(I)\n",
                    "structure SL = ListFun.Make(S)\n",
                    "\n",
                    "fun main () = return <xml><body>\n",
                    "  Pick your poison:<br/>\n",
                    "  <li> <a link={IL.main ()}>Integers</a></li>\n",
                    "  <li> <a link={SL.main ()}>Strings</a></li>\n",
                    "</body></xml>\n",
                ),
                Some("val main : unit -> transaction page\n"),
            ),
        ],
        &["List", "ListFun", "ListShop"],
    )
    .expect("demo listShop project elaboration");
}

#[test]
fn corpus_core_top_one_row1_and_one_rowe1_elaborate() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun query [tables ::: {{Type}}] [exps ::: {Type}] [state ::: Type]\n",
        "          (q : sql_query [] [] tables exps)\n",
        "          (f : $(exps ++ map (fn fields :: {Type} => $fields) tables) -> state -> transaction state)\n",
        "          (initial : state) = return initial\n",
        "\n",
        "fun oneOrNoRows [tables ::: {{Type}}] [exps ::: {Type}]\n",
        "                [tables ~ exps]\n",
        "                (q : sql_query [] [] tables exps) =\n",
        "    query q\n",
        "          (fn fs _ => return (Some fs))\n",
        "          None\n",
        "\n",
        "fun oneRow1 [nm ::: Name] [fs ::: {Type}] (q : sql_query [] [] [nm = fs] []) =\n",
        "    o <- oneOrNoRows q;\n",
        "    return (case o of\n",
        "                None => error <xml>Query returned no rows</xml>\n",
        "              | Some r => r.nm)\n",
        "\n",
        "fun oneRowE1 [tabs ::: {Unit}] [nm ::: Name] [t ::: Type] [tabs ~ [nm]]\n",
        "             (q : sql_query [] [] (mapU [] tabs) [nm = t]) =\n",
        "    o <- oneOrNoRows q;\n",
        "    return (case o of\n",
        "                None => error <xml>Query returned no rows</xml>\n",
        "              | Some r => r.nm)\n",
    ))
    .expect("Top oneRow1/oneRowE1 elaboration");
}

#[test]
fn corpus_core_top_post_fields_elaborates() {
    if !corpus_enabled() {
        return;
    }
    try_elaborate_single_module(concat!(
        "fun postFields pb =\n",
        "    let\n",
        "        fun postFields' s =\n",
        "            case firstFormField s of\n",
        "                None => []\n",
        "              | Some f => (fieldName f, fieldValue f) :: postFields' (remainingFields f)\n",
        "    in\n",
        "        case postType pb of\n",
        "            \"application/x-www-form-urlencoded\" => postFields' (postData pb)\n",
        "          | _ => error <xml>Tried to get POST fields, but MIME type is not \"application/x-www-form-urlencoded\"</xml>\n",
        "    end\n",
    ))
    .expect("Top postFields elaboration");
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
