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

use anyhow::{anyhow, Context as _};
use std::collections::HashMap;
use std::fs;
use std::sync::OnceLock; // error construction and chaining in tests

use ur::compiler;
use ur::diagnostics::DiagnosticId;
use ur::error_types::{CompileError, ErrorReporter, Located, Span};
use ur::settings::Settings;
use ur::source;
use ur::source::File as SourceFile;

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

/// Basis + Top source declarations parsed once and shared across all corpus elaboration tests.
///
/// Caching avoids reading and parsing `lib/ur/basis.urs` / `lib/ur/top.ur` from disk on every test
/// invocation. Each test clones this and appends its own module declarations before calling
/// [`compiler::elaborate`]. `OnceLock` guarantees the parse runs exactly once even under parallel test execution.
static CACHED_BASIS_SOURCES: OnceLock<Option<SourceFile>> = OnceLock::new();

/// Return a reference to the cached Basis+Top source declarations, or `None` when the Basis is absent.
///
/// Initialises [`CACHED_BASIS_SOURCES`] on first call by calling [`compiler::parse_basis_sources`].
/// All subsequent calls return immediately without any I/O or locking.
fn get_cached_basis_sources() -> Option<&'static SourceFile> {
    CACHED_BASIS_SOURCES
        .get_or_init(|| {
            let root = corpus_workspace_root()?; // Use the same workspace root as other corpus helpers.
            let settings = Settings::new(); // Default settings for Basis-only parse.
            let mut errors = ErrorReporter::new_silent(); // Discard parse errors (None return signals failure).
            compiler::parse_basis_sources(root, &settings, &mut errors) // Parse Basis+Top once.
        })
        .as_ref() // Borrow the stored Option<SourceFile> as Option<&SourceFile>.
}

/// Frozen `Basis` / `Top` elaboration snapshot shared across corpus tests.
///
/// This avoids re-elaborating the full boot library on every `try_elaborate_single_module*`
/// invocation while still rebuilding a fresh user-module environment per test.
static CACHED_BOOT_ELABORATION_SNAPSHOT: OnceLock<Option<compiler::BootElaborationSnapshot>> =
    OnceLock::new();

#[derive(Clone)]
struct CachedTopSources {
    implementation: String,
    signature: String,
}

#[derive(Clone)]
struct CachedTopPrefixResults {
    top_prefix_show_option: Result<(), String>,
    top_named_prefix_show_option_signature_pair: Result<(), String>,
    top_named_prefix_query_xi_signature_pair: Result<(), String>,
    top_named_prefix_mapux_rev_signature_pair: Result<(), String>,
    top_named_prefix_mapx4_signature_pair: Result<(), String>,
    top_named_prefix_mapux2_signature_pair: Result<(), String>,
    top_named_prefix_mapx2_signature_pair: Result<(), String>,
    top_named_prefix_mapx3_signature_pair: Result<(), String>,
    top_named_full_module_pair: Result<(), String>,
}

static CACHED_TOP_SOURCES: OnceLock<Result<Option<CachedTopSources>, String>> = OnceLock::new();
static CACHED_TOP_PREFIX_RESULTS: OnceLock<Result<Option<CachedTopPrefixResults>, String>> =
    OnceLock::new();

/// Return the cached boot elaboration snapshot, or `None` when the Basis is absent or boot
/// elaboration itself fails.
fn get_cached_boot_elaboration_snapshot() -> Option<&'static compiler::BootElaborationSnapshot> {
    CACHED_BOOT_ELABORATION_SNAPSHOT
        .get_or_init(|| {
            let cached_boot = get_cached_basis_sources()?;
            let mut errors = ErrorReporter::new_silent();
            compiler::elaborate_boot_snapshot(cached_boot, &mut errors)
        })
        .as_ref()
}

fn get_cached_top_sources() -> Result<Option<&'static CachedTopSources>, String> {
    match CACHED_TOP_SOURCES.get_or_init(|| {
        let root = match corpus_workspace_root() {
            Some(root) => root,
            None => return Ok(None),
        };
        let implementation = fs::read_to_string(root.join("lib/ur/top.ur"))
            .map_err(|io_error| format!("read lib/ur/top.ur: {io_error}"))?;
        let signature = fs::read_to_string(root.join("lib/ur/top.urs"))
            .map_err(|io_error| format!("read lib/ur/top.urs: {io_error}"))?;
        Ok(Some(CachedTopSources {
            implementation,
            signature,
        }))
    }) {
        Ok(Some(cached_sources)) => Ok(Some(cached_sources)),
        Ok(None) => Ok(None),
        Err(error) => Err(error.clone()),
    }
}

fn prefix_before_line(source_text: &str, stop_prefix: &str) -> String {
    source_text
        .lines()
        .take_while(|line| !line.starts_with(stop_prefix))
        .map(|line| format!("{line}\n"))
        .collect()
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

fn parse_optional_signature(
    module_name: &str,
    urs_src: Option<&str>,
) -> Result<Option<Located<source::Sgn>>, String> {
    match urs_src {
        None => Ok(None),
        Some(signature_text) => {
            let mut signature_errors = ErrorReporter::new_silent();
            let signature_items = match ur::parse::parse_urs(
                &format!("{module_name}.urs"),
                signature_text,
                &mut signature_errors,
            ) {
                Some(signature_items) => signature_items,
                None => return Err(format!("parse_urs failed: {signature_errors:?}")),
            };
            if signature_errors.has_hard_errors() {
                return Err(format!("parse_urs errors: {signature_errors:?}"));
            }
            let signature_span = Span {
                file: format!("{module_name}.urs"),
                ..Span::dummy()
            };
            Ok(Some(Located::new(
                source::Sgn::Const(signature_items),
                signature_span,
            )))
        }
    }
}

fn parse_module_declarations(module_name: &str, ur_src: &str) -> Result<SourceFile, String> {
    let mut errors = ErrorReporter::new_silent();
    let implementation_file = format!("{module_name}.ur");
    let declarations = match ur::parse::parse_ur(
        &implementation_file,
        ur_src,
        &mut errors,
        ur::db::ProjectDb::default(),
    ) {
        Some(declarations) => declarations,
        None => return Err(format!("parse_ur failed: {errors:?}")),
    };
    if errors.has_hard_errors() {
        return Err(format!("parse_ur errors: {errors:?}"));
    }
    Ok(declarations)
}

fn build_in_memory_module_decl(
    module_name: &str,
    ur_src: &str,
    urs_src: Option<&str>,
) -> Result<source::LocDecl, String> {
    let signature = parse_optional_signature(module_name, urs_src)?;
    let declarations = parse_module_declarations(module_name, ur_src)?;
    let implementation_span = Span {
        file: format!("{module_name}.ur"),
        ..Span::dummy()
    };
    let structure = Located::new(
        source::Str::Const(declarations),
        implementation_span.clone(),
    );
    Ok(Located::new(
        source::Decl::Str(module_name.to_string(), signature, None, structure, false),
        implementation_span,
    ))
}

fn build_module_export_decl(module_name: &str) -> source::LocDecl {
    let export_span = Span::dummy();
    let exported_module = Located::new(
        source::Str::Var(module_name.to_string()),
        export_span.clone(),
    );
    Located::new(source::Decl::Export(exported_module), export_span)
}

fn elaborate_user_file_on_cached_boot_snapshot(file: SourceFile) -> Result<(), String> {
    let boot_snapshot = get_cached_boot_elaboration_snapshot()
        .ok_or_else(|| "corpus boot root not found (lib/ur/basis.urs missing)".to_string())?;
    let mut errors = ErrorReporter::new_silent();
    let elaborated =
        ur::elaborated::elaborate::elab_file_from_boot_snapshot(boot_snapshot, file, &mut errors);
    match elaborated {
        Some(_) if !errors.has_hard_errors() => Ok(()),
        Some(_) => Err(format!("elaborate errors: {errors:?}")),
        None => Err(format!("elaborate returned None: {errors:?}")),
    }
}

fn parse_signature_source(module_name: &str, urs_src: &str) -> Result<source::LocSgn, String> {
    let mut errors = ErrorReporter::new_silent();
    let signature_items =
        match ur::parse::parse_urs(&format!("{module_name}.urs"), urs_src, &mut errors) {
            Some(signature_items) => signature_items,
            None => return Err(format!("parse_urs failed: {errors:?}")),
        };
    if errors.has_hard_errors() {
        return Err(format!("parse_urs errors: {errors:?}"));
    }
    let signature_span = Span {
        file: format!("{module_name}.urs"),
        ..Span::dummy()
    };
    Ok(Located::new(
        source::Sgn::Const(signature_items),
        signature_span,
    ))
}

fn get_cached_top_prefix_results() -> Result<Option<&'static CachedTopPrefixResults>, String> {
    match CACHED_TOP_PREFIX_RESULTS.get_or_init(|| {
        let top_sources = match get_cached_top_sources()? {
            Some(top_sources) => top_sources,
            None => return Ok(None),
        };
        let boot_snapshot = match get_cached_boot_elaboration_snapshot() {
            Some(boot_snapshot) => boot_snapshot,
            None => {
                return Err("corpus boot root not found (lib/ur/basis.urs missing)".to_string());
            }
        };
        let full_top_decls = parse_module_declarations("Top", &top_sources.implementation)?;

        let show_option_impl_prefix =
            prefix_before_line(&top_sources.implementation, "fun read_option ");
        let show_option_sig_prefix = prefix_before_line(&top_sources.signature, "val read_option ");
        let query_xi_impl_prefix = prefix_before_line(&top_sources.implementation, "fun hasRows ");
        let query_xi_sig_prefix = prefix_before_line(&top_sources.signature, "val hasRows ");
        let mapux_rev_impl_prefix = prefix_before_line(&top_sources.implementation, "fun mapUX2 ");
        let mapux_rev_sig_prefix = prefix_before_line(&top_sources.signature, "val mapUX2 ");
        let mapx4_impl_prefix = prefix_before_line(&top_sources.implementation, "val queryL ");
        let mapx4_sig_prefix = prefix_before_line(&top_sources.signature, "val queryL ");
        let mapux2_impl_prefix = prefix_before_line(&top_sources.implementation, "fun mapX2 ");
        let mapux2_sig_prefix = prefix_before_line(&top_sources.signature, "val mapX2 ");
        let mapx2_impl_prefix = prefix_before_line(&top_sources.implementation, "fun mapX3 ");
        let mapx2_sig_prefix = prefix_before_line(&top_sources.signature, "val mapX3 ");
        let mapx3_impl_prefix = prefix_before_line(&top_sources.implementation, "fun mapX4 ");
        let mapx3_sig_prefix = prefix_before_line(&top_sources.signature, "val mapX4 ");
        let show_option_decl_count =
            parse_module_declarations("Top", &show_option_impl_prefix)?.len();
        let query_xi_decl_count = parse_module_declarations("Top", &query_xi_impl_prefix)?.len();
        let mapux_rev_decl_count = parse_module_declarations("Top", &mapux_rev_impl_prefix)?.len();
        let mapx4_decl_count = parse_module_declarations("Top", &mapx4_impl_prefix)?.len();
        let mapux2_decl_count = parse_module_declarations("Top", &mapux2_impl_prefix)?.len();
        let mapx2_decl_count = parse_module_declarations("Top", &mapx2_impl_prefix)?.len();
        let mapx3_decl_count = parse_module_declarations("Top", &mapx3_impl_prefix)?.len();

        let checkpoints = vec![
            ur::elaborated::elaborate::StructurePrefixCheckpoint {
                declaration_count: show_option_decl_count,
                ascribed_signature: None,
            },
            ur::elaborated::elaborate::StructurePrefixCheckpoint {
                declaration_count: show_option_decl_count,
                ascribed_signature: Some(parse_signature_source("Top", &show_option_sig_prefix)?),
            },
            ur::elaborated::elaborate::StructurePrefixCheckpoint {
                declaration_count: query_xi_decl_count,
                ascribed_signature: Some(parse_signature_source("Top", &query_xi_sig_prefix)?),
            },
            ur::elaborated::elaborate::StructurePrefixCheckpoint {
                declaration_count: mapux_rev_decl_count,
                ascribed_signature: Some(parse_signature_source("Top", &mapux_rev_sig_prefix)?),
            },
            ur::elaborated::elaborate::StructurePrefixCheckpoint {
                declaration_count: mapx4_decl_count,
                ascribed_signature: Some(parse_signature_source("Top", &mapx4_sig_prefix)?),
            },
            ur::elaborated::elaborate::StructurePrefixCheckpoint {
                declaration_count: mapux2_decl_count,
                ascribed_signature: Some(parse_signature_source("Top", &mapux2_sig_prefix)?),
            },
            ur::elaborated::elaborate::StructurePrefixCheckpoint {
                declaration_count: mapx2_decl_count,
                ascribed_signature: Some(parse_signature_source("Top", &mapx2_sig_prefix)?),
            },
            ur::elaborated::elaborate::StructurePrefixCheckpoint {
                declaration_count: mapx3_decl_count,
                ascribed_signature: Some(parse_signature_source("Top", &mapx3_sig_prefix)?),
            },
            ur::elaborated::elaborate::StructurePrefixCheckpoint {
                declaration_count: full_top_decls.len(),
                ascribed_signature: Some(parse_signature_source("Top", &top_sources.signature)?),
            },
        ];
        let mut results =
            ur::elaborated::elaborate::elab_structure_prefix_checkpoints_from_boot_snapshot(
                boot_snapshot,
                &full_top_decls,
                &checkpoints,
            )
            .into_iter();

        let top_prefix_show_option = match results.next() {
            Some(result) => result,
            None => {
                return Err(
                    "missing cached top prefix result for show_option elaboration".to_string(),
                );
            }
        };
        let top_named_prefix_show_option_signature_pair = match results.next() {
            Some(result) => result,
            None => {
                return Err(
                    "missing cached top prefix result for show_option signature elaboration"
                        .to_string(),
                );
            }
        };
        let top_named_prefix_query_xi_signature_pair = match results.next() {
            Some(result) => result,
            None => {
                return Err(
                    "missing cached top prefix result for query_xi signature elaboration"
                        .to_string(),
                );
            }
        };
        let top_named_prefix_mapux_rev_signature_pair = match results.next() {
            Some(result) => result,
            None => {
                return Err(
                    "missing cached top prefix result for mapux_rev signature elaboration"
                        .to_string(),
                );
            }
        };
        let top_named_prefix_mapx4_signature_pair = match results.next() {
            Some(result) => result,
            None => {
                return Err(
                    "missing cached top prefix result for mapx4 signature elaboration".to_string(),
                );
            }
        };
        let top_named_prefix_mapux2_signature_pair = match results.next() {
            Some(result) => result,
            None => {
                return Err(
                    "missing cached top prefix result for mapux2 signature elaboration".to_string(),
                );
            }
        };
        let top_named_prefix_mapx2_signature_pair = match results.next() {
            Some(result) => result,
            None => {
                return Err(
                    "missing cached top prefix result for mapx2 signature elaboration".to_string(),
                );
            }
        };
        let top_named_prefix_mapx3_signature_pair = match results.next() {
            Some(result) => result,
            None => {
                return Err(
                    "missing cached top prefix result for mapx3 signature elaboration".to_string(),
                );
            }
        };
        let top_named_full_module_pair = match results.next() {
            Some(result) => result,
            None => {
                return Err(
                    "missing cached top prefix result for full module signature elaboration"
                        .to_string(),
                );
            }
        };

        Ok(Some(CachedTopPrefixResults {
            top_prefix_show_option,
            top_named_prefix_show_option_signature_pair,
            top_named_prefix_query_xi_signature_pair,
            top_named_prefix_mapux_rev_signature_pair,
            top_named_prefix_mapx4_signature_pair,
            top_named_prefix_mapux2_signature_pair,
            top_named_prefix_mapx2_signature_pair,
            top_named_prefix_mapx3_signature_pair,
            top_named_full_module_pair,
        }))
    }) {
        Ok(Some(cached_results)) => Ok(Some(cached_results)),
        Ok(None) => Ok(None),
        Err(error) => Err(error.clone()),
    }
}

fn cached_top_prefix_results_for_test() -> anyhow::Result<Option<&'static CachedTopPrefixResults>> {
    match get_cached_top_prefix_results() {
        Ok(results) => Ok(results),
        Err(error) => Err(anyhow!("cache top prefix results: {error}")),
    }
}

fn ensure_cached_top_prefix_result(
    result: &Result<(), String>,
    context: &str,
) -> anyhow::Result<()> {
    match result {
        Ok(()) => Ok(()),
        Err(error) => Err(anyhow!("{context}: {error}")),
    }
}

fn try_elaborate_project_on_thread(
    modules: &[(String, String, Option<String>)],
    urp_lines: &[String],
) -> Result<(), String> {
    let mut modules_by_name: HashMap<&str, (&str, Option<&str>)> = HashMap::new();
    for (module_name, implementation_source, signature_source) in modules {
        let replaced = modules_by_name.insert(
            module_name.as_str(),
            (implementation_source.as_str(), signature_source.as_deref()),
        );
        if replaced.is_some() {
            return Err(format!(
                "duplicate in-memory project module `{module_name}`"
            ));
        }
    }

    let ordered_module_names: Vec<&str> = if urp_lines.is_empty() {
        modules
            .iter()
            .map(|(module_name, _, _)| module_name.as_str())
            .collect()
    } else {
        urp_lines.iter().map(String::as_str).collect()
    };

    let mut file = Vec::with_capacity(ordered_module_names.len() * 2);
    for module_name in ordered_module_names {
        let (implementation_source, signature_source) = match modules_by_name.get(module_name) {
            Some(module_sources) => *module_sources,
            None => {
                return Err(format!(
                    "in-memory project order references unknown module `{module_name}`"
                ));
            }
        };
        file.push(build_in_memory_module_decl(
            module_name,
            implementation_source,
            signature_source,
        )?);
        file.push(build_module_export_decl(module_name));
    }

    elaborate_user_file_on_cached_boot_snapshot(file)
}

fn try_elaborate_single_module(ur_src: &str) -> anyhow::Result<()> {
    let source_text = ur_src.to_string();
    match run_with_elaboration_stack(move || try_elaborate_single_module_on_thread(&source_text))
        .flatten()
    {
        Ok(()) => Ok(()),
        Err(error) => Err(anyhow!("{error}")),
    }
}

/// Elaborate one synthetic module/signature pair in a temp dir.
///
/// # Errors
///
/// I/O, parse, boot settings, `parse_sources`, elaboration, or reported hard errors as `String`.
fn try_elaborate_module_pair(ur_src: &str, urs_src: &str) -> anyhow::Result<()> {
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
) -> anyhow::Result<()> {
    let module_name_owned = module_name.to_string();
    let implementation_text = ur_src.to_string();
    let signature_text = urs_src.to_string();
    match run_with_elaboration_stack(move || {
        try_elaborate_named_module_pair_on_thread(
            &module_name_owned,
            &implementation_text,
            &signature_text,
        )
    })
    .flatten()
    {
        Ok(()) => Ok(()),
        Err(error) => Err(anyhow!("{error}")),
    }
}

/// Elaborate a synthetic multi-module project in a temp dir.
///
/// `modules` is a list of `(module_name, implementation_source, optional_signature_source)` tuples.
fn try_elaborate_project(
    modules: &[(&str, &str, Option<&str>)],
    urp_lines: &[&str],
) -> anyhow::Result<()> {
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
    match run_with_elaboration_stack(move || {
        try_elaborate_project_on_thread(&owned_modules, &owned_urp)
    })
    .flatten()
    {
        Ok(()) => Ok(()),
        Err(error) => Err(anyhow!("{error}")),
    }
}

/// Elaborate one synthetic anonymous module using cached Basis sources (larger stack supplied by caller).
///
/// Uses the cached boot elaboration snapshot so user modules only pay for their own declarations,
/// not a fresh `Basis` / `Top` elaboration on every invocation.
///
/// # Errors
///
/// Missing Basis, parse failure, elaboration failure, or reported hard errors as `String`.
fn try_elaborate_single_module_on_thread(ur_src: &str) -> Result<(), String> {
    let boot_snapshot = get_cached_boot_elaboration_snapshot()
        .ok_or_else(|| "corpus boot root not found (lib/ur/basis.urs missing)".to_string())?; // Fail fast when Basis is absent.
    let settings = Settings::new();
    let mut errors = ErrorReporter::new_silent(); // Silent reporter: errors are returned as Err strings.
    compiler::elaborate_module_on_cached_boot_snapshot(
        boot_snapshot, // Pre-elaborated Basis+Top — no repeated boot elaboration.
        "CoreMod",
        ur_src,
        None,
        &settings,
        &mut errors,
    )
}

fn try_parse_single_module(ur_src: &str) -> Result<SourceFile, String> {
    let mut errors = ErrorReporter::new_silent();
    match ur::parse::parse_ur(
        "CoreMod.ur",
        ur_src,
        &mut errors,
        ur::db::ProjectDb::default(),
    ) {
        Some(file) => {
            if errors.has_hard_errors() {
                Err(format!("parse errors: {errors:?}"))
            } else {
                Ok(file)
            }
        }
        None => Err(format!("parse_ur failed: {errors:?}")),
    }
}

fn collect_sql_field_refs_in_expression(
    expression: &ur::source::LocExp,
    refs: &mut Vec<(String, String)>,
) {
    use ur::source::{Con, Exp};

    if let Exp::CApp(function_with_table, field_name) = &expression.node {
        if let Exp::CApp(function_expression, table_name) = &function_with_table.node {
            if let Exp::Var(module_path, function_name, _) = &function_expression.node {
                if module_path.len() == 1
                    && module_path[0] == "Basis"
                    && function_name == "sql_field"
                {
                    if let (Con::Name(table_name), Con::Name(field_name)) =
                        (&table_name.node, &field_name.node)
                    {
                        refs.push((table_name.clone(), field_name.clone()));
                    }
                }
            }
        }
    }

    match &expression.node {
        Exp::Annot(inner, _)
        | Exp::CApp(inner, _)
        | Exp::DisjointApp(inner)
        | Exp::Field(inner, _)
        | Exp::Cut(inner, _)
        | Exp::CutMulti(inner, _) => collect_sql_field_refs_in_expression(inner, refs),
        Exp::App(function_expression, argument_expression)
        | Exp::Concat(function_expression, argument_expression)
        | Exp::Infix(_, function_expression, argument_expression) => {
            collect_sql_field_refs_in_expression(function_expression, refs);
            collect_sql_field_refs_in_expression(argument_expression, refs);
        }
        Exp::Abs(_, _, body)
        | Exp::CAbs(_, _, _, body)
        | Exp::Disjoint(_, _, body)
        | Exp::KAbs(_, body) => collect_sql_field_refs_in_expression(body, refs),
        Exp::Record(fields, _) => {
            for (_, field_expression) in fields {
                collect_sql_field_refs_in_expression(field_expression, refs);
            }
        }
        Exp::Case(scrutinee, branches) => {
            collect_sql_field_refs_in_expression(scrutinee, refs);
            for (_, branch_expression) in branches {
                collect_sql_field_refs_in_expression(branch_expression, refs);
            }
        }
        Exp::Let(declarations, body) => {
            for declaration in declarations {
                match &declaration.node {
                    ur::source::EDecl::Val(_, bound_expression) => {
                        collect_sql_field_refs_in_expression(bound_expression, refs)
                    }
                    ur::source::EDecl::ValRec(bindings) => {
                        for (_, _, bound_expression) in bindings {
                            collect_sql_field_refs_in_expression(bound_expression, refs);
                        }
                    }
                }
            }
            collect_sql_field_refs_in_expression(body, refs);
        }
        Exp::Prim(_) | Exp::Var(_, _, _) | Exp::Wild | Exp::Hole => {}
    }
}

fn collect_sql_field_refs_in_declaration(
    declaration: &ur::source::LocDecl,
    refs: &mut Vec<(String, String)>,
) {
    match &declaration.node {
        ur::source::Decl::Val(_, expression)
        | ur::source::Decl::View(_, expression)
        | ur::source::Decl::Policy(expression) => {
            collect_sql_field_refs_in_expression(expression, refs)
        }
        ur::source::Decl::ValRec(bindings) => {
            for (_, _, expression) in bindings {
                collect_sql_field_refs_in_expression(expression, refs);
            }
        }
        ur::source::Decl::Table(_, _, primary_key_expression, secondary_expression)
        | ur::source::Decl::Index(primary_key_expression, secondary_expression, _)
        | ur::source::Decl::Task(primary_key_expression, secondary_expression) => {
            collect_sql_field_refs_in_expression(primary_key_expression, refs);
            collect_sql_field_refs_in_expression(secondary_expression, refs);
        }
        ur::source::Decl::Str(_, _, _, structure_expression, _)
        | ur::source::Decl::OpenStr(structure_expression)
        | ur::source::Decl::Export(structure_expression) => {
            collect_sql_field_refs_in_structure(structure_expression, refs);
        }
        ur::source::Decl::Con(_, _, _)
        | ur::source::Decl::Datatype(_)
        | ur::source::Decl::DatatypeImp(_, _, _)
        | ur::source::Decl::Sgn(_, _)
        | ur::source::Decl::FfiStr(_, _, _)
        | ur::source::Decl::Open(_, _)
        | ur::source::Decl::Constraint(_, _)
        | ur::source::Decl::OpenConstraints(_, _)
        | ur::source::Decl::Sequence(_)
        | ur::source::Decl::Database(_)
        | ur::source::Decl::Cookie(_, _)
        | ur::source::Decl::Style(_)
        | ur::source::Decl::OnError(_, _, _)
        | ur::source::Decl::Ffi(_, _, _) => {}
    }
}

fn collect_sql_field_refs_in_structure(
    structure_expression: &ur::source::LocStr,
    refs: &mut Vec<(String, String)>,
) {
    match &structure_expression.node {
        ur::source::Str::Const(declarations) => {
            for declaration in declarations {
                collect_sql_field_refs_in_declaration(declaration, refs);
            }
        }
        ur::source::Str::Proj(inner, _) => collect_sql_field_refs_in_structure(inner, refs),
        ur::source::Str::Fun(_, _, _, body) => collect_sql_field_refs_in_structure(body, refs),
        ur::source::Str::App(left, right) => {
            collect_sql_field_refs_in_structure(left, refs);
            collect_sql_field_refs_in_structure(right, refs);
        }
        ur::source::Str::Var(_) => {}
    }
}

/// Elaborate one synthetic named module/signature pair using cached Basis sources (larger stack supplied by caller).
///
/// Uses the cached boot elaboration snapshot so impl/signature pairs only elaborate their own
/// module contents.
///
/// # Errors
///
/// Missing Basis, parse failure, elaboration failure, or reported hard errors as `String`.
fn try_elaborate_named_module_pair_on_thread(
    module_name: &str,
    ur_src: &str,
    urs_src: &str,
) -> Result<(), String> {
    let boot_snapshot = get_cached_boot_elaboration_snapshot()
        .ok_or_else(|| "corpus boot root not found (lib/ur/basis.urs missing)".to_string())?; // Fail fast when Basis is absent.
    let settings = Settings::new();
    let mut errors = ErrorReporter::new_silent(); // Silent reporter: errors are returned as Err strings.
    compiler::elaborate_module_on_cached_boot_snapshot(
        boot_snapshot,
        module_name,
        ur_src,
        Some(urs_src),
        &settings,
        &mut errors,
    )
}

fn corpus_enabled() -> bool {
    corpus_workspace_root().is_some()
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
    let Some(source_file) = get_cached_basis_sources().cloned() else {
        return Ok((0, 0));
    };
    let settings = Settings::new();
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
fn corpus_core_val_literal_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module("val x = 42\n").with_context(|| "literal val")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_fun_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    // `int` is not an unqualified top-level type in user modules (Basis FFI); keep inference-only.
    try_elaborate_single_module("fun f x = x\n").with_context(|| "fun")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_polymorphic_id_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module("val id = fn x => x\n").with_context(|| "poly id")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_structure_projection_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module("structure M = struct\n    val k = 3\nend\n\nval z = M.k\n")
        .with_context(|| "structure projection")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_datatype_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module("datatype t = Leaf | Node of t * t\nval a = Leaf\n") {
        Ok(()) => {}
        Err(error) => panic!("datatype: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_type_mismatch_rejected() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let r = try_elaborate_single_module("val x : {} = 1\n");
    assert!(
        r.is_err(),
        "unit annotation vs int literal must not elaborate, got Ok"
    );
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_row_concat_disjoint_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module("type ok = {A : {}} ++ {B : {}}\n")
        .with_context(|| "disjoint row concat")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_folder_map0_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(
        "fun useMap0 [r ::: {Type}] (fl : folder r) : $(map option r) =\n    @map0 [option] (fn [t ::_] => None) fl\n",
    ) {
        Ok(()) => {}
        Err(error) => panic!("folder map0-style elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_show_option_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module(concat!(
        "fun localShowOption [t ::: Type] (_ : show t) =\n",
        "    mkShow (fn opt : option t =>\n",
        "               case opt of\n",
        "                   None => \"\"\n",
        "                 | Some x => show x)\n",
    ))
    .with_context(|| "show_option-style elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_show_option_signature_pair_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "show_option signature-pair elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_prefix_through_show_option_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_prefix_show_option,
        "Top prefix through show_option elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_prefix_through_show_option_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_prefix_show_option,
        "Top-named prefix through show_option elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_prefix_through_show_option_signature_pair_elaborates() -> anyhow::Result<()>
{
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_named_prefix_show_option_signature_pair,
        "Top-named prefix through show_option signature elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_prefix_through_query_xi_signature_pair_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_named_prefix_query_xi_signature_pair,
        "Top-named prefix through queryXI signature elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapux_rev_signature_pair_elaborates(
) -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_named_prefix_mapux_rev_signature_pair,
        "Top exact prefix through mapUX_rev signature elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapx4_signature_pair_elaborates() -> anyhow::Result<()>
{
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_named_prefix_mapx4_signature_pair,
        "Top exact prefix through mapX4 signature elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapux2_signature_pair_elaborates(
) -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_named_prefix_mapux2_signature_pair,
        "Top exact prefix through mapUX2 signature elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapx2_signature_pair_elaborates() -> anyhow::Result<()>
{
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_named_prefix_mapx2_signature_pair,
        "Top exact prefix through mapX2 signature elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_exact_prefix_through_mapx3_signature_pair_elaborates() -> anyhow::Result<()>
{
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_named_prefix_mapx3_signature_pair,
        "Top exact prefix through mapX3 signature elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_full_module_pair_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let top_results = match cached_top_prefix_results_for_test()? {
        Some(top_results) => top_results,
        None => return Ok(()),
    };
    ensure_cached_top_prefix_result(
        &top_results.top_named_full_module_pair,
        "Top full module/signature elaboration",
    )?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_read_option_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "read_option-style elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_query1_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module(concat!(
        "fun localQuery1 [t ::: Name] [fs ::: {Type}] [state ::: Type]\n",
        "    (q : sql_query [] [] [t = fs] [])\n",
        "    (f : $fs -> state -> transaction state)\n",
        "    (i : state) =\n",
        "    query q (fn r => f r.t) i\n",
    ))
    .with_context(|| "query1-style elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_query1_prime_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module(concat!(
        "fun localQuery1Prime [t ::: Name] [fs ::: {Type}] [state ::: Type]\n",
        "    (q : sql_query [] [] [t = fs] [])\n",
        "    (f : $fs -> state -> state) (i : state) =\n",
        "    query q (fn r s => return (f r.t s)) i\n",
    ))
    .with_context(|| "query1'-style elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_query1_prime_followed_by_val_rev_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "query1'-then-val-rev elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_rev_with_list_cons_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "rev/list-cons elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_level_val_binding_visible_to_later_decl() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module(concat!(
        "val id = fn [t] => fn (x : t) => x\n",
        "\n",
        "fun applyId (n : int) = id n\n",
    ))
    .with_context(|| "top-level val binding should remain visible")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_query_i1_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module(concat!(
        "fun localQueryI1 [nm ::: Name] [fs ::: {Type}]\n",
        "    (q : sql_query [] [] [nm = fs] [])\n",
        "    (f : $fs -> transaction unit) =\n",
        "    query q\n",
        "          (fn fs _ => f fs.nm)\n",
        "          ()\n",
    ))
    .with_context(|| "queryI1-style elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_query_xi_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "queryXI-style elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_query_l_with_val_rev_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "queryL-with-val-rev elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_query_l1_with_val_rev_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "queryL1-with-val-rev elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_disjoint_abstraction_infers_tdisjoint_type() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_named_module_pair(
        "DisjointWrap",
        "fun consLike [K] [r ::: {K}] [nm :: Name] [v :: K] [[nm] ~ r] (x : int) = x\n",
        "val consLike : K --> r ::: {K} -> nm :: Name -> v :: K -> [[nm] ~ r] => int -> int\n",
    ) {
        Ok(()) => {}
        Err(error) => panic!("disjoint abstraction should retain its TDisjoint type: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_query_i_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "queryI-style elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_one_or_no_rows1_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module(concat!(
        "fun localOneOrNoRows1 [nm ::: Name] [fs ::: {Type}]\n",
        "    (q : sql_query [] [] [nm = fs] []) =\n",
        "    query q\n",
        "          (fn rows _ => return (Some rows.nm))\n",
        "          None\n",
    ))
    .with_context(|| "oneOrNoRows1-style elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_one_row1_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "oneRow1-style elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_existential_intro_elim_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(concat!(
        "con ex = K ==> fn tf :: (K -> Type) =>\n",
        "            res ::: Type -> (choice :: K -> tf choice -> res) -> res\n",
        "\n",
        "fun ex_intro [K] [tf :: K -> Type] [choice :: K] (body : tf choice) : ex tf =\n",
        " fn [res] (f : choice :: K -> tf choice -> res) =>\n",
        "    f [choice] body\n",
        "\n",
        "fun ex_elim [K] [tf ::: K -> Type] (v : ex tf) [res ::: Type] = @@v [res]\n",
    )) {
        Ok(()) => {}
        Err(error) => panic!("existential intro/elim elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_existential_intro_elim_after_constructor_alias_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(concat!(
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
    )) {
        Ok(()) => {}
        Err(error) => panic!("existential intro/elim after constructor alias elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_mapx_via_foldr_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "mapX-style foldR elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_mapx_signature_pair_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "mapX-style signature elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_local_folder_foldr_mapx_pair_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "local folder/foldR/mapX signature elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_folder_foldr_mapx_pair_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "Top-named local folder/foldR/mapX signature elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_named_foldr4_mapux_mapx_prefix_pair_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "Top-named foldR4/mapUX/mapX prefix elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_local_folder_foldur2_mapux2_pair_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "local folder/foldUR2/mapUX2 signature elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_local_folder_foldur2_mapux2_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "local folder/foldUR2/mapUX2 elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_local_folder_foldur2_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "local folder/foldUR2 elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_local_folder_foldur2_partial_constructor_application_elaborates(
) -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "foldUR2 partial constructor application elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_mapu_binary_row_transform_constructor_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(concat!(
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "con localTf = fn tf1 :: Type => fn tf2 :: Type => fn tr :: ({Unit} -> Type)\n",
        "              => fn r :: {Unit} => $(mapU tf1 r) -> $(mapU tf2 r) -> tr r\n",
    )) {
        Ok(()) => {}
        Err(error) => panic!("binary mapU row transform constructor elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_mapu_unary_row_transform_constructor_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(concat!(
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "con localTf = fn tf1 :: Type => fn r :: {Unit} => $(mapU tf1 r)\n",
    )) {
        Ok(()) => {}
        Err(error) => panic!("unary mapU row transform constructor elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_mapu_row_constructor_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(concat!(
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "con localRow = fn tf1 :: Type => fn r :: {Unit} => mapU tf1 r\n",
    )) {
        Ok(()) => {}
        Err(error) => panic!("mapU row constructor elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_mapu_partial_constructor_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(concat!(
        "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
        "con localMap = fn tf1 :: Type => mapU tf1\n",
    )) {
        Ok(()) => {}
        Err(error) => panic!("mapU partial constructor elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_trecord_unit_row_constructor_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    try_elaborate_single_module("con localRecord = fn r :: {Type} => $r\n")
        .with_context(|| "trecord constructor elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_local_folder_foldur2_partial_callback_application_elaborates() -> anyhow::Result<()>
{
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "foldUR2 partial callback application elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_local_folder_foldur2_mapux2_acc_only_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "local folder/foldUR2/mapUX2 acc-only elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_local_folder_foldur2_mapux2_no_acc_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "local folder/foldUR2/mapUX2 no-acc elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_sql_nonempty_and_eqnullable_elaborate() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(concat!(
        "fun localNonempty [fs] [us] (t : sql_table fs us) =\n",
        "    oneRowE1 (SELECT COUNT( * ) > 0 AS B FROM t)\n",
        "\n",
        "fun localEqNullable [tables ::: {{Type}}] [agg ::: {{Type}}] [exps ::: {Type}]\n",
        "    [t ::: Type] (_ : sql_injectable (option t))\n",
        "    (e1 : sql_exp tables agg exps (option t))\n",
        "    (e2 : sql_exp tables agg exps (option t)) =\n",
        "    (SQL ({e1} IS NULL AND {e2} IS NULL) OR {e1} = {e2})\n",
        "\n",
        "fun localEqNullable' [tables ::: {{Type}}] [agg ::: {{Type}}] [exps ::: {Type}]\n",
        "    [t ::: Type] (_ : sql_injectable (option t))\n",
        "    (e1 : sql_exp tables agg exps (option t))\n",
        "    (e2 : option t) =\n",
        "    case e2 of\n",
        "        None => (SQL {e1} IS NULL)\n",
        "      | Some _ => sql_binary sql_eq e1 (sql_inject e2)\n",
    )) {
        Ok(()) => {}
        Err(error) => panic!("narrow SQL surface elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_sql_count_star_placeholder_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(
        "fun localNonempty [fs] [us] (t : sql_table fs us) =\n    oneRowE1 (SELECT COUNT(sql_star) > 0 AS B FROM t)\n",
    ) {
        Ok(()) => {}
        Err(error) => panic!("sql_star placeholder elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_sql_default_table_field_where_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_parse_single_module("val q = (SELECT t.Ch FROM t WHERE A = {[id]})\n") {
        Ok(file) => {
            let mut refs = Vec::new();
            for declaration in &file {
                collect_sql_field_refs_in_declaration(declaration, &mut refs);
            }
            assert!(
                refs.iter()
                    .any(|(table_name, field_name)| table_name == "T" && field_name == "A"),
                "default-table WHERE field should desugar to Basis.sql_field T A, got {refs:?}"
            );
            assert!(
                refs.iter().all(|(table_name, field_name)| !(table_name == "t" && field_name == "A")),
                "unqualified WHERE field should not stay bound to the source table name, got {refs:?}"
            );
        }
        Err(error) => panic!("default-table SQL field compatibility: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_sql_single_selected_field_preserves_type_shape() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(concat!(
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
        "\n",
        "fun writeBack\n",
        "    (q : sql_query [] [] [Channels = [Channel = channel (string * int * float)]] [])\n",
        "    (msg : string * int * float) =\n",
        "    row <- localOneRow1 q;\n",
        "    send row.Channel msg\n",
    )) {
        Ok(()) => {}
        Err(error) => panic!("single selected SQL field keeps wildcard type information: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_recursive_user_list_datatype_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_single_module(concat!(
        "datatype demo_list t = Empty | Link of t * demo_list t\n",
        "\n",
        "fun length [t] (ls : demo_list t) =\n",
        "    let\n",
        "        fun length' (ls : demo_list t) (acc : int) =\n",
        "            case ls of\n",
        "                Empty => acc\n",
        "              | Link (_, ls') => length' ls' (acc + 1)\n",
        "    in\n",
        "        length' ls 0\n",
        "    end\n",
        "\n",
        "fun rev [t] (ls : demo_list t) =\n",
        "    let\n",
        "        fun rev' (ls : demo_list t) (acc : demo_list t) =\n",
        "            case ls of\n",
        "                Empty => acc\n",
        "              | Link (x, ls') => rev' ls' (Link (x, acc))\n",
        "    in\n",
        "        rev' ls Empty\n",
        "    end\n",
    )) {
        Ok(()) => {}
        Err(error) => panic!("recursive user-defined list datatype elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_demo_list_signature_pair_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_project(
        &[(
            "List",
            concat!(
                "fun length [t] (ls : list t) =\n",
                "    let\n",
                "        fun length' (ls : list t) (acc : int) =\n",
                "            case ls of\n",
                "                [] => acc\n",
                "              | x :: ls' => length' ls' (acc + 1)\n",
                "    in\n",
                "        length' ls 0\n",
                "    end\n",
                "\n",
                "fun rev [t] (ls : list t) =\n",
                "    let\n",
                "        fun rev' (ls : list t) (acc : list t) =\n",
                "            case ls of\n",
                "                [] => acc\n",
                "              | x :: ls' => rev' ls' (x :: acc)\n",
                "    in\n",
                "        rev' ls []\n",
                "    end\n",
            ),
            Some(concat!(
                "val length : t ::: Type -> list t -> int\n",
                "\n",
                "val rev : t ::: Type -> list t -> list t\n",
            )),
        )],
        &["List"],
    ) {
        Ok(()) => {}
        Err(error) => panic!("demo list signature pair elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_demo_list_shop_project_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    match try_elaborate_project(
        &[
            (
                "List",
                concat!(
                    "fun length [t] (ls : list t) =\n",
                    "    let\n",
                    "        fun length' (ls : list t) (acc : int) =\n",
                    "            case ls of\n",
                    "                [] => acc\n",
                    "              | x :: ls' => length' ls' (acc + 1)\n",
                    "    in\n",
                    "        length' ls 0\n",
                    "    end\n",
                    "\n",
                    "fun rev [t] (ls : list t) =\n",
                    "    let\n",
                    "        fun rev' (ls : list t) (acc : list t) =\n",
                    "            case ls of\n",
                    "                [] => acc\n",
                    "              | x :: ls' => rev' ls' (x :: acc)\n",
                    "    in\n",
                    "        rev' ls []\n",
                    "    end\n",
                ),
                Some(concat!(
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
                    "    fun main () =\n",
                    "        let\n",
                    "            val empty : list M.t = []\n",
                    "            val reversed = rev empty\n",
                    "            val count = length reversed\n",
                    "            val parsedBlank =\n",
                    "                case M.fromString \"\" of\n",
                    "                    None => \"none\"\n",
                    "                  | Some v => M.toString v\n",
                    "        in\n",
                    "            return <xml><body>\n",
                    "              Length: {[count]}<br/>\n",
                    "              Parsed blank: {[parsedBlank]}\n",
                    "            </body></xml>\n",
                    "        end\n",
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
                    "structure IL = ListFun.Make(I)\n",
                    "\n",
                    "fun main () = IL.main ()\n",
                ),
                Some("val main : unit -> transaction page\n"),
            ),
        ],
        &["List", "ListFun", "ListShop"],
    ) {
        Ok(()) => {}
        Err(error) => panic!("demo listShop project elaboration: {error}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_one_row1_and_one_rowe1_elaborate() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "Top oneRow1/oneRowE1 elaboration")?;
    Ok(()) // return success to the test harness
}

#[test]
fn corpus_core_top_post_fields_elaborates() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
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
    .with_context(|| "Top postFields elaboration")?;
    Ok(()) // return success to the test harness
}

/// Full Basis boot (no user modules): ratchet [`DiagnosticId::ElabUnresolvedDisjointness`].
#[test]
fn corpus_boot_elaboration_disjointness_progress() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if !corpus_enabled() {
        return Ok(()); // return early with success
    }
    let boot_counts = match run_boot_only_elaboration_stack(
        boot_only_elaboration_disjointness_and_type_error_counts_on_thread,
    ) {
        Ok(counts) => counts,
        Err(error) => panic!("boot disjointness progress thread: {error}"),
    };
    let (disjoint_count, _type_errors) = match boot_counts {
        Ok(counts) => counts,
        Err(error) => panic!("boot-only elaboration: {error}"),
    };
    assert!(
        (0..=BOOT_UNRESOLVED_DISJOINTNESS_DIAGNOSTICS_MAX).contains(&disjoint_count),
        "ElabUnresolvedDisjointness count {disjoint_count} exceeds cap {} — \
         lower the cap only after fixing disjointness; \
         print details with URWEB_TEST_BOOT_PROGRESS=1 on this test",
        BOOT_UNRESOLVED_DISJOINTNESS_DIAGNOSTICS_MAX
    );
    Ok(()) // return success to the test harness
}
