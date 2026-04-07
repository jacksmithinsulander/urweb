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

fn try_elaborate_named_module(module_name: &str, ur_src: &str) -> Result<(), String> {
    let module_name_owned = module_name.to_string();
    let implementation_text = ur_src.to_string();
    run_with_elaboration_stack(move || {
        let _guard = CORPUS_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let dir = tempdir().map_err(|tempfile_error| tempfile_error.to_string())?;
        let root = dir.path();
        fs::write(root.join("app.urp"), format!("{module_name_owned}\n"))
            .map_err(|io_error| io_error.to_string())?;
        fs::write(
            root.join(format!("{module_name_owned}.ur")),
            &implementation_text,
        )
        .map_err(|io_error| io_error.to_string())?;
        let urp = root.join("app.urp");
        let mut job = compiler::parse_urp(&urp).map_err(|parse_error| parse_error.to_string())?;
        let mut settings = Settings::new();
        settings.boot_linking = true;
        let workspace_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let workspace_basis = workspace_root.join("lib/ur/basis.urs");
        let previous_boot_root = std::env::var_os("URWEB_BOOT_ROOT");
        if workspace_basis.is_file() {
            std::env::set_var("URWEB_BOOT_ROOT", &workspace_root);
        }
        let boot_apply = compiler::apply_boot_settings(&mut job, &mut settings);
        match &previous_boot_root {
            None => std::env::remove_var("URWEB_BOOT_ROOT"),
            Some(value) => std::env::set_var("URWEB_BOOT_ROOT", value),
        }
        boot_apply?;
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

/// Elaborate one synthetic named module/signature pair in a temp dir (locked, larger stack via caller).
///
/// # Errors
///
/// I/O, parse, boot settings, `parse_sources`, elaboration, or reported hard errors as `String`.
fn try_elaborate_named_module_pair_on_thread(
    module_name: &str,
    ur_src: &str,
    urs_src: &str,
) -> Result<(), String> {
    let _guard = CORPUS_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let dir = tempdir().map_err(|tempfile_error| tempfile_error.to_string())?;
    let root = dir.path();
    fs::write(root.join("app.urp"), format!("{module_name}\n"))
        .map_err(|io_error| io_error.to_string())?;
    fs::write(root.join(format!("{module_name}.ur")), ur_src)
        .map_err(|io_error| io_error.to_string())?;
    fs::write(root.join(format!("{module_name}.urs")), urs_src)
        .map_err(|io_error| io_error.to_string())?;
    let urp = root.join("app.urp");
    let mut job = compiler::parse_urp(&urp).map_err(|parse_error| parse_error.to_string())?;
    let mut settings = Settings::new();
    settings.boot_linking = true;
    let workspace_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_basis = workspace_root.join("lib/ur/basis.urs");
    let previous_boot_root = std::env::var_os("URWEB_BOOT_ROOT");
    if workspace_basis.is_file() {
        std::env::set_var("URWEB_BOOT_ROOT", &workspace_root);
    }
    let boot_apply = compiler::apply_boot_settings(&mut job, &mut settings);
    match &previous_boot_root {
        None => std::env::remove_var("URWEB_BOOT_ROOT"),
        Some(value) => std::env::set_var("URWEB_BOOT_ROOT", value),
    }
    boot_apply?;
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
