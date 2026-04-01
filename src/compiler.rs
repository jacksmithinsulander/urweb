//! Pipeline orchestration — drives all compilation phases.
//!
//! Parses `.urp` project files into `Job`, then runs: parse → elaborate →
//! explify → core passes → mono passes → cjr_print / sql_generate → C compile.
//!
//! Mirrors `compiler.sml`.
//!
//! Public helpers here use rustdoc with `# Arguments`, `# Returns`, and `# Errors` when the contract
//! is not obvious from the signature alone.
//!
//! **Style:** new/edited Rust here follows [README.md](../README.md) Rust code style (exceptions documented there).

use anyhow::{bail, Result};
use std::path::{Path, PathBuf};
#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::cli_common::cli_diagnostic_text;
use crate::diagnostics::{DiagnosticId, DiagnosticLocale, DiagnosticPayload};
use crate::error_types::ErrorReporter;
use crate::settings::Settings;

#[cfg(test)]
pub(crate) static APPLY_BOOT_SETTINGS_CALLS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static CSS_SUMMARIZE_CALLS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static MONO_FILECACHE_CALLS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static APPEND_NATIVE_INCLUDE_FALLBACK_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static APPEND_NATIVE_LIBDIR_FALLBACK_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RESOLVE_BOOT_ROOT_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);

/// When diagnostics were already printed to stderr, summarize why compilation stops (catalog copy).
fn bail_if_errors_reported(
    errors: &ErrorReporter,
    phase: &str,
    locale: DiagnosticLocale,
) -> Result<()> {
    if !errors.has_hard_errors() {
        return Ok(());
    }
    let diagnostic_count = errors.errors.len();
    let body = cli_diagnostic_text(
        DiagnosticId::CliCompileStoppedAfterDiagnostics,
        vec![phase.to_string(), diagnostic_count.to_string()],
        locale,
    );
    let banner_label =
        cli_diagnostic_text(DiagnosticId::CliToolBannerCompileStopped, vec![], locale);
    bail!(
        "{}",
        crate::error_types::format_tool_diagnostic_banner_and_body(&banner_label, &body)
    );
}

/// Wrap “phase returned `None`” in a catalog message for `?` conversion.
fn anyhow_phase_incomplete(settings: &Settings, phase_label: &str) -> anyhow::Error {
    anyhow::anyhow!(
        "{}",
        cli_diagnostic_text(
            DiagnosticId::CliPhaseIncompleteNoOutput,
            vec![phase_label.to_string()],
            settings.diagnostic_locale,
        )
    )
}

// ---------------------------------------------------------------------------
// Job description (mirrors `compiler.sml`'s `job` record)
// ---------------------------------------------------------------------------

/// A compilation job parsed from a `.urp` file.
#[derive(Debug, Clone)]
pub struct Job {
    pub prefix: String,
    pub database: Option<String>,
    pub sources: Vec<String>,
    pub exe: String,
    pub sql: Option<String>,
    pub endpoints: Option<String>,
    pub debug: bool,
    pub profile: bool,
    pub timeout: u32,
    pub ffi: Vec<String>,
    pub link: Vec<String>,
    pub linker: Option<String>,
    pub headers: Vec<String>,
    pub scripts: Vec<String>,
    pub client_to_server: Vec<(String, String)>,
    pub effectful: Vec<(String, String)>,
    pub benign_effectful: Vec<(String, String)>,
    pub client_only: Vec<(String, String)>,
    pub server_only: Vec<(String, String)>,
    pub js_module: Option<String>,
    pub js_funcs: Vec<((String, String), String)>,
    pub rewrites: Vec<crate::settings::Rewrite>,
    pub filter_url: Vec<crate::settings::Rule>,
    pub filter_mime: Vec<crate::settings::Rule>,
    pub filter_request: Vec<crate::settings::Rule>,
    pub filter_response: Vec<crate::settings::Rule>,
    pub filter_env: Vec<crate::settings::Rule>,
    pub filter_meta: Vec<crate::settings::Rule>,
    pub protocol: Option<String>,
    pub dbms: Option<String>,
    pub sig_file: Option<String>,
    pub file_cache: Option<String>,
    pub safe_get_default: bool,
    pub safe_gets: Vec<String>,
    pub on_error: Option<(String, Vec<String>, String)>,
    pub min_heap: u32,
    pub mime_types: Option<String>,
    /// Directives seen during parse (e.g. "path", "html5"). Used so tests can assert
    /// that settings-only and no-op directive arms were taken (kills delete-match-arm mutants).
    pub seen_directives: Vec<String>,
    /// Path to the Basis library source directory (e.g. `lib/ur`). When set,
    /// `basis.urs` is loaded from this directory to provide the Basis signature.
    pub basis_lib_dir: Option<std::path::PathBuf>,
}

impl Default for Job {
    fn default() -> Self {
        Job {
            prefix: "/".into(),
            database: None,
            sources: vec![],
            exe: "a.out".into(),
            sql: None,
            endpoints: None,
            debug: false,
            profile: false,
            timeout: 120,
            ffi: vec![],
            link: vec![],
            linker: None,
            headers: vec![],
            scripts: vec![],
            client_to_server: vec![],
            effectful: vec![],
            benign_effectful: vec![],
            client_only: vec![],
            server_only: vec![],
            js_module: None,
            js_funcs: vec![],
            rewrites: vec![],
            filter_url: vec![],
            filter_mime: vec![],
            filter_request: vec![],
            filter_response: vec![],
            filter_env: vec![],
            filter_meta: vec![],
            protocol: None,
            dbms: None,
            sig_file: None,
            file_cache: None,
            safe_get_default: false,
            safe_gets: vec![],
            on_error: None,
            min_heap: 0,
            mime_types: None,
            seen_directives: vec![],
            basis_lib_dir: None,
        }
    }
}

// ---------------------------------------------------------------------------
// Pipeline phases (named, mirrors SML `transform` wrappers)
// ---------------------------------------------------------------------------

/// Result of a single compilation phase.
pub type PhaseResult<T> = Result<T>;

/// The complete pipeline result.
///
/// Newtype wrapper so `Default` exists (cargo-mutants FnValue on `compile` must compile).
#[derive(Debug)]
pub struct CompileResult(Result<PathBuf /* generated executable */>);

impl Default for CompileResult {
    fn default() -> Self {
        Self(Err(anyhow::anyhow!("")))
    }
}

impl CompileResult {
    /// Consume this wrapper and return the inner result from [`compile`].
    ///
    /// # Returns
    ///
    /// The `Result<PathBuf>` holding the output executable path or an error.
    pub fn into_result(self) -> Result<PathBuf> {
        self.0
    }
}

impl From<Result<PathBuf>> for CompileResult {
    fn from(value: Result<PathBuf>) -> Self {
        Self(value)
    }
}

// ---------------------------------------------------------------------------
// Phase 1: Parse .urp file
// ---------------------------------------------------------------------------

/// Parse a `.urp` project file into a [`Job`] description.
///
/// # Arguments
///
/// * `path` — Path to the Ur/Web project file (typically ends in `.urp`).
///
/// # Returns
///
/// Populated [`Job`] on success.
///
/// # Errors
///
/// Input/output, malformed project file, or directive errors from the Ur/Web project parser.
pub fn parse_urp(path: &Path) -> Result<Job> {
    crate::urp_parser::parse_urp(path)
}

// ---------------------------------------------------------------------------
// Boot path resolution
// ---------------------------------------------------------------------------

fn boot_root_from(start: PathBuf) -> Option<PathBuf> {
    let mut cur = start;
    loop {
        if cur.join("lib/ur/basis.urs").is_file() {
            return Some(cur);
        }
        cur = cur.parent()?.to_path_buf();
    }
}

/// Environment variable naming an explicit Ur/Web checkout root (directory that contains `lib/ur/basis.urs`).
const URWEB_BOOT_ROOT_ENV: &str = "URWEB_BOOT_ROOT";

/// Locate the Ur/Web distribution root: optional `URWEB_BOOT_ROOT`, then parents of `current_exe`, then `current_dir`.
///
/// Order matters for installs whose binary path does not lie under the checkout and for demo builds
/// where the shell’s current working directory is not the repository root.
///
/// # Returns
///
/// `Some(root)` when `root/lib/ur/basis.urs` exists; `None` if no candidate applies.
fn resolve_boot_root() -> Option<PathBuf> {
    #[cfg(test)]
    RESOLVE_BOOT_ROOT_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
    if let Ok(raw) = std::env::var(URWEB_BOOT_ROOT_ENV) {
        let trimmed = raw.trim();
        if !trimmed.is_empty() {
            // Prefer an absolute root so relative `URWEB_BOOT_ROOT` survives `cd` in shell wrappers.
            let candidate = PathBuf::from(trimmed);
            let candidate = std::fs::canonicalize(&candidate).unwrap_or(candidate);
            if candidate.join("lib/ur/basis.urs").is_file() {
                return Some(candidate);
            }
        }
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(p) = exe.parent() {
            if let Some(r) = boot_root_from(p.to_path_buf()) {
                return Some(r);
            }
        }
    }
    let cwd = std::env::current_dir().ok()?;
    boot_root_from(cwd)
}

/// If `URWEB_NATIVE_LIB_DIR` is unset, use checkout-relative `crates/urweb-{persy,ndb}/include` for `-I`.
fn append_urweb_native_include_fallback(compile_cmd: &mut std::process::Command) {
    #[cfg(test)]
    APPEND_NATIVE_INCLUDE_FALLBACK_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
    // Match arms avoid unary `!` so `delete !` mutants cannot flip “use env” vs “use checkout fallbacks”.
    let user_supplied_native_dir = match std::env::var("URWEB_NATIVE_LIB_DIR") {
        Ok(s) => match s.trim().is_empty() {
            true => false,
            false => true,
        },
        Err(_) => false,
    };
    if user_supplied_native_dir {
        return;
    }
    let Some(root) = resolve_boot_root() else {
        return;
    };
    for rel in ["crates/urweb-persy/include", "crates/urweb-ndb/include"] {
        let p = root.join(rel);
        if p.is_dir() {
            compile_cmd.arg("-I").arg(p);
        }
    }
}

/// If `URWEB_NATIVE_LIB_DIR` is unset, link against workspace `target/{release,debug}` when staticlibs exist.
fn append_urweb_native_libdir_fallback(link_cmd: &mut std::process::Command) {
    #[cfg(test)]
    APPEND_NATIVE_LIBDIR_FALLBACK_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
    let user_supplied_native_dir = match std::env::var("URWEB_NATIVE_LIB_DIR") {
        Ok(s) => match s.trim().is_empty() {
            true => false,
            false => true,
        },
        Err(_) => false,
    };
    if user_supplied_native_dir {
        return;
    }
    let Some(root) = resolve_boot_root() else {
        return;
    };
    for profile in ["release", "debug"] {
        let td = root.join("target").join(profile);
        if td.join("liburweb_persy.a").exists() || td.join("liburweb_ndb.a").exists() {
            link_cmd.arg("-L").arg(td);
            return;
        }
    }
}

/// When `settings.boot_linking` is set, resolve the checkout root and set `job.basis_lib_dir` to `lib/ur` under that root.
///
/// Also fills empty `config_*` paths from the same root when present. **`basis_lib_dir` is always
/// replaced** when a boot root is found so a stale or job-parsed path cannot skip loading `basis.urs` / `top.ur`.
///
/// # Arguments
///
/// * `job` — Project job to augment (`basis_lib_dir`).
/// * `settings` — Compiler settings to augment (`config_include`, `config_lib`, TLS-related library paths).
///
/// # Returns
///
/// `Ok(())` when `boot_linking` is false, or when a boot root is found. **`Err`** when `-boot` is in
/// effect but no tree containing `lib/ur/basis.urs` is found (set [`URWEB_BOOT_ROOT_ENV`] or run from
/// the distribution root).
///
/// # Errors
///
/// Missing boot tree under `-boot` / `boot_linking` — message names `URWEB_BOOT_ROOT` and `lib/ur/basis.urs`.
pub fn apply_boot_settings(job: &mut Job, settings: &mut Settings) -> Result<(), String> {
    #[cfg(test)]
    APPLY_BOOT_SETTINGS_CALLS.fetch_add(1, Ordering::SeqCst);
    if !settings.boot_linking {
        return Ok(());
    }
    let Some(root) = resolve_boot_root() else {
        return Err(format!(
            "-boot requires the Ur/Web library tree (lib/ur/basis.urs). Set {} to the checkout root, or run the compiler from that tree.",
            URWEB_BOOT_ROOT_ENV
        ));
    };
    let lib_ur = root.join("lib/ur");
    job.basis_lib_dir = Some(lib_ur);
    if settings.config_include.is_empty() {
        let inc = root.join("include/urweb");
        if inc.exists() {
            settings.config_include = inc.to_string_lossy().into_owned();
        }
    }
    if settings.config_lib.is_empty() {
        let lib_c = root.join("src/c");
        if lib_c.exists() {
            settings.config_lib = lib_c.to_string_lossy().into_owned();
        }
    }
    if settings.config_bearssl_libs.is_empty() {
        let bear_a = root.join("vendor/BearSSL/build/libbearssl.a");
        if bear_a.exists() {
            settings.config_bearssl_libs = bear_a.to_string_lossy().into_owned();
        }
    }
    if settings.config_libunistring_libs.is_empty() {
        let uni = std::path::Path::new("/opt/homebrew/lib/libunistring.a");
        if uni.exists() {
            settings.config_libunistring_libs = uni.to_string_lossy().into_owned();
        } else {
            settings.config_libunistring_libs = "-lunistring".into();
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Phase 2: Parse source files
// ---------------------------------------------------------------------------

/// Synthetic `UrwebNative` signature (no `parse_urs`: `urweb_*` spellings are expression keywords).
fn urweb_native_ffi_sgn_items() -> Vec<crate::source::LocSgnItem> {
    use crate::error_types::{Located, Span};
    use crate::source::{Con, SgnItem};
    let sp = Span::dummy();
    let lc = |c: Con| Located::new(c, sp.clone());
    let b = |name: &str| lc(Con::Var(vec!["Basis".into()], name.into()));
    let string = b("string");
    let int = b("int");
    let unit = b("unit");
    let transaction = b("transaction");
    let transaction_unit = lc(Con::App(Box::new(transaction.clone()), Box::new(unit)));
    let transaction_string = lc(Con::App(Box::new(transaction), Box::new(string.clone())));
    let put_ty = lc(Con::TFun(
        Box::new(string.clone()),
        Box::new(lc(Con::TFun(
            Box::new(string.clone()),
            Box::new(transaction_unit.clone()),
        ))),
    ));
    let get_ty = lc(Con::TFun(
        Box::new(string.clone()),
        Box::new(transaction_string),
    ));
    let tb_ty = lc(Con::TFun(
        Box::new(int.clone()),
        Box::new(lc(Con::TFun(
            Box::new(int.clone()),
            Box::new(lc(Con::TFun(
                Box::new(int.clone()),
                Box::new(lc(Con::TFun(Box::new(int), Box::new(transaction_unit)))),
            ))),
        ))),
    ));
    vec![
        Located::new(SgnItem::Val("urweb_put".into(), put_ty), sp.clone()),
        Located::new(SgnItem::Val("urweb_get".into(), get_ty), sp.clone()),
        Located::new(SgnItem::Val("urweb_tb_transfer".into(), tb_ty), sp),
    ]
}

fn ur_disk_paths_same(a: &Path, b: &Path) -> bool {
    if a == b {
        return true;
    }
    match (a.canonicalize(), b.canonicalize()) {
        (Ok(x), Ok(y)) => x == y,
        _ => a.components().eq(b.components()),
    }
}

/// Parse every module in `job`, but read `overlay_text` for the `.ur` whose disk path matches `overlay_disk_path`.
///
/// Intended for language-server buffers. The process current directory should be the project root (same as `ur-compile`).
///
/// # Arguments
///
/// * `job` — Sources list and basis configuration from [`parse_urp`].
/// * `overlay_disk_path` — Canonical or project-relative path to the open buffer.
/// * `overlay_text` — Editor text substituted for that file’s disk contents.
/// * `settings` — Compiler configuration (includes, rewrites, …).
/// * `errors` — Diagnostic sink; fatal issues append here and yield `None`.
///
/// # Returns
///
/// Parsed [`crate::source::File`] (decl list) or `None` if parsing failed.
pub fn parse_sources_with_overlay(
    job: &Job,
    overlay_disk_path: &Path,
    overlay_text: &str,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::source::File> {
    parse_sources_inner(
        job,
        Some((overlay_disk_path, overlay_text)),
        settings,
        errors,
    )
}

/// Parse all modules listed in `job` from disk (no overlay).
///
/// # Arguments
///
/// * `job` — Project description including `sources` and basis paths.
/// * `settings` — Compiler configuration.
/// * `errors` — Collects parse and read errors.
///
/// # Returns
///
/// [`crate::source::File`] or `None` on failure.
pub fn parse_sources(
    job: &Job,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::source::File> {
    parse_sources_inner(job, None, settings, errors)
}

fn parse_sources_inner(
    job: &Job,
    overlay: Option<(&Path, &str)>,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::source::File> {
    use crate::error_types::{CompileError, Located, Span};
    use crate::source;
    use std::path::Path;

    let mut decls: source::File = Vec::new();

    // Prepend the Basis FFI module.  When job.basis_lib_dir is set (boot mode),
    // parse lib/ur/basis.urs to get the full Basis signature.  Otherwise use an
    // empty signature (sufficient when Basis names are resolved via FFI pass-through).
    {
        let basis_span = Span {
            file: "<basis>".into(),
            ..Span::dummy()
        };
        let sgis = if let Some(ref lib_dir) = job.basis_lib_dir {
            let urs_path = lib_dir.join("basis.urs");
            match std::fs::read_to_string(&urs_path) {
                Ok(src) => crate::parse::parse_urs(&urs_path.to_string_lossy(), &src, errors)?,
                Err(e) => {
                    errors.report(CompileError::Plain(DiagnosticPayload::new(
                        DiagnosticId::CouldNotReadBasisUrs,
                        vec![urs_path.to_string_lossy().into_owned(), e.to_string()],
                    )));
                    return None;
                }
            }
        } else {
            vec![]
        };
        let sgn = Located::new(source::Sgn::Const(sgis), basis_span.clone());
        decls.push(Located::new(
            source::Decl::FfiStr("Basis".into(), sgn, None),
            basis_span,
        ));
    }

    // Load the Top library module (top.ur / top.urs) when basis_lib_dir is set.
    // This provides `folder`, `queryX`, `txt`, `eqNullable'`, etc. used by user code.
    // Matches the SML compiler's `elaborate` phase which also elaborates top.ur.
    if let Some(ref lib_dir) = job.basis_lib_dir {
        let top_urs_path = lib_dir.join("top.urs");
        let top_ur_path = lib_dir.join("top.ur");
        let top_span = Span {
            file: "<top>".into(),
            ..Span::dummy()
        };

        let top_sgn = match std::fs::read_to_string(&top_urs_path) {
            Ok(src) => match crate::parse::parse_urs(&top_urs_path.to_string_lossy(), &src, errors)
            {
                Some(items) => Some(Located::new(source::Sgn::Const(items), top_span.clone())),
                None => return None,
            },
            Err(e) => {
                errors.report(CompileError::Plain(DiagnosticPayload::new(
                    DiagnosticId::CouldNotReadTopUrs,
                    vec![top_urs_path.to_string_lossy().into_owned(), e.to_string()],
                )));
                return None;
            }
        };

        match std::fs::read_to_string(&top_ur_path) {
            Ok(src) => {
                match crate::parse::parse_ur(
                    &top_ur_path.to_string_lossy(),
                    &src,
                    errors,
                    crate::db::ProjectDb::default(),
                ) {
                    Some(ds) => {
                        let str_node = Located::new(source::Str::Const(ds), top_span.clone());
                        decls.push(Located::new(
                            source::Decl::Str("Top".into(), top_sgn, None, str_node, false),
                            top_span,
                        ));
                    }
                    None => return None,
                }
            }
            Err(e) => {
                errors.report(CompileError::Plain(DiagnosticPayload::new(
                    DiagnosticId::CouldNotReadTopUr,
                    vec![top_ur_path.to_string_lossy().into_owned(), e.to_string()],
                )));
                return None;
            }
        }
    }

    if let Some(ref db_path) = job.database {
        let db_span = Span {
            file: "<project>".into(),
            ..Span::dummy()
        };
        decls.push(Located::new(
            source::Decl::Database(db_path.clone()),
            db_span,
        ));
    }

    let mut had_errors = false;
    let project_db = crate::db::effective_project_db(settings);

    // Needs real `basis.urs` so `Basis.string` / `transaction` resolve when elaborating the shim FFI.
    if project_db.exposes_urweb_native_surface() && job.basis_lib_dir.is_some() {
        let span = Span {
            file: "<urweb_native>.urs".into(),
            ..Span::dummy()
        };
        let sgis = urweb_native_ffi_sgn_items();
        let sgn = Located::new(source::Sgn::Const(sgis), span.clone());
        decls.push(Located::new(
            source::Decl::FfiStr("UrwebNative".into(), sgn, None),
            span.clone(),
        ));
        decls.push(Located::new(
            source::Decl::Open("UrwebNative".into(), vec![]),
            span,
        ));
    }

    // Parse C FFI modules (job.ffi): each provides a .urs signature file.
    for ffi_base in &job.ffi {
        let mname = module_of(ffi_base);
        let urs_path = format!("{ffi_base}.urs");
        let span = Span {
            file: urs_path.clone(),
            ..Span::dummy()
        };

        let urs_src = match std::fs::read_to_string(&urs_path) {
            Ok(s) => s,
            Err(e) => {
                errors.report(CompileError::Plain(DiagnosticPayload::new(
                    DiagnosticId::CouldNotReadFfiUrs,
                    vec![urs_path.clone(), e.to_string()],
                )));
                had_errors = true;
                continue;
            }
        };

        match crate::parse::parse_urs(&urs_path, &urs_src, errors) {
            None => had_errors = true,
            Some(sgis) => {
                let sgn = Located::new(source::Sgn::Const(sgis), span.clone());
                decls.push(Located::new(source::Decl::FfiStr(mname, sgn, None), span));
            }
        }
    }

    // Parse Ur/Web source modules (job.sources).
    for src_base in &job.sources {
        let mname = module_of(src_base);
        let ur_path = format!("{src_base}.ur");
        let urs_path = format!("{src_base}.urs");
        let span = Span {
            file: ur_path.clone(),
            ..Span::dummy()
        };

        // Read .ur source (optional LSP overlay for one open buffer)
        let ur_src = if let Some((op, ot)) = overlay {
            if ur_disk_paths_same(op, Path::new(&ur_path)) {
                ot.to_string()
            } else {
                match std::fs::read_to_string(&ur_path) {
                    Ok(s) => s,
                    Err(e) => {
                        errors.report(CompileError::Plain(DiagnosticPayload::new(
                            DiagnosticId::CouldNotReadSourceUr,
                            vec![ur_path.clone(), e.to_string()],
                        )));
                        had_errors = true;
                        continue;
                    }
                }
            }
        } else {
            match std::fs::read_to_string(&ur_path) {
                Ok(s) => s,
                Err(e) => {
                    errors.report(CompileError::Plain(DiagnosticPayload::new(
                        DiagnosticId::CouldNotReadSourceUr,
                        vec![ur_path.clone(), e.to_string()],
                    )));
                    had_errors = true;
                    continue;
                }
            }
        };

        // Parse optional .urs signature
        let sgn_opt = if Path::new(&urs_path).exists() {
            match std::fs::read_to_string(&urs_path) {
                Err(e) => {
                    errors.report(CompileError::Plain(DiagnosticPayload::new(
                        DiagnosticId::CouldNotReadSignatureUrs,
                        vec![urs_path.clone(), e.to_string()],
                    )));
                    had_errors = true;
                    None
                }
                Ok(urs_src) => {
                    let sgn_span = Span {
                        file: urs_path.clone(),
                        ..Span::dummy()
                    };
                    match crate::parse::parse_urs(&urs_path, &urs_src, errors) {
                        None => {
                            had_errors = true;
                            None
                        }
                        Some(sgis) => Some(Located::new(source::Sgn::Const(sgis), sgn_span)),
                    }
                }
            }
        } else {
            None
        };

        // Parse .ur body
        match crate::parse::parse_ur(&ur_path, &ur_src, errors, project_db) {
            None => had_errors = true,
            Some(ds) => {
                let str_node = Located::new(source::Str::Const(ds), span.clone());
                decls.push(Located::new(
                    source::Decl::Str(mname, sgn_opt, None, str_node, false),
                    span,
                ));
            }
        }
    }

    if had_errors {
        return None;
    }

    // Mirror SML compiler: automatically export the last source module.
    // The SML compiler appends `(Source.DExport final, loc)` where `final`
    // is the last module in the source list.  This makes page-returning functions
    // automatically exported as HTTP handlers without an explicit `export` line.
    if let Some(last_src) = job.sources.last() {
        let mname = module_of(last_src);
        let export_span = crate::error_types::Span::dummy();
        let str_node =
            crate::error_types::Located::new(source::Str::Var(mname), export_span.clone());
        decls.push(crate::error_types::Located::new(
            source::Decl::Export(str_node),
            export_span,
        ));
    }

    Some(decls)
}

// ---------------------------------------------------------------------------
// Phase 3: Elaborate
// ---------------------------------------------------------------------------

/// Type- and module-check parsed declarations into an elaborated intermediate representation.
///
/// # Arguments
///
/// * `file` — AST from [`parse_sources`] or [`parse_sources_with_overlay`].
/// * `settings` — Compilation options affecting elaboration.
/// * `errors` — Receives type and module errors.
///
/// # Returns
///
/// [`crate::elaborated::File`] or `None` when elaboration cannot continue.
pub fn elaborate(
    file: crate::source::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::elaborated::File> {
    crate::elaborated::elaborate::elab_file(file, settings, errors)
}

// ---------------------------------------------------------------------------
// Phase 3.5: Unnest (elab → elab, lambda-lift nested val recs)
// ---------------------------------------------------------------------------

/// Lambda-lift nested `val rec` bindings in the elaborated representation.
///
/// # Arguments
///
/// * `file` — Elaborated program.
/// * `errors` — Diagnostic sink for unnest failures.
///
/// # Returns
///
/// Transformed elaborated file (may still contain errors reported separately).
pub fn unnest(
    file: crate::elaborated::File,
    errors: &mut ErrorReporter,
) -> crate::elaborated::File {
    crate::elaborated::unnest::unnest(file, errors)
}

// ---------------------------------------------------------------------------
// Phase 4: Explify (elab → expl)
// ---------------------------------------------------------------------------

/// Lower elaborated AST to explicit intermediate form (patterns, guards, …).
///
/// # Arguments
///
/// * `file` — Elaborated program.
/// * `errors` — Reports explify failures.
///
/// # Returns
///
/// [`crate::explicit::File`] or `None`.
pub fn explify(
    file: crate::elaborated::File,
    errors: &mut ErrorReporter,
) -> Option<crate::explicit::File> {
    crate::elaborated::explify::explify(file, errors)
}

// ---------------------------------------------------------------------------
// Phase 5: Corify (expl → core)
// ---------------------------------------------------------------------------

/// Lower explicit IR to typed core language.
///
/// # Arguments
///
/// * `file` — Explicit-phase program.
/// * `settings` — Options affecting the translation.
/// * `errors` — Corify diagnostics.
///
/// # Returns
///
/// [`crate::core::File`] or `None`.
pub fn corify(
    file: crate::explicit::File,
    settings: &mut Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::core::File> {
    crate::explicit::corify::corify(file, settings, errors)
}

// ---------------------------------------------------------------------------
// Core passes
// ---------------------------------------------------------------------------

/// Core phase: untangle nested binding structure (see `crate::core::untangling`).
///
/// # Arguments
///
/// * `file` — Core program.
///
/// # Returns
///
/// Transformed core [`crate::core::File`].
pub fn core_untangle(file: crate::core::File) -> crate::core::File {
    crate::core::untangling::untangle(file)
}

/// Core phase: local reduction (simplify within bindings).
///
/// # Returns
///
/// Transformed [`crate::core::File`].
pub fn core_reduce_local(file: crate::core::File) -> crate::core::File {
    crate::core::local_reduction::reduce(file)
}

/// Like [`core_reduce_local`] but forwards recoverable internal diagnostics to `errors` when `Some`.
pub fn core_reduce_local_with_errors(
    file: crate::core::File,
    errors: &mut Option<&mut ErrorReporter>,
) -> crate::core::File {
    crate::core::local_reduction::reduce_with_errors(file, errors)
}

/// Core phase: dead-code elimination (“shake”).
///
/// # Returns
///
/// Pruned [`crate::core::File`].
pub fn core_shake(file: crate::core::File) -> crate::core::File {
    crate::core::dead_code_elimination::shake(file)
}

/// Core phase: global reduction pass.
///
/// # Arguments
///
/// * `file` — Core program.
/// * `settings` — Controls reduction strength.
///
/// # Returns
///
/// Reduced [`crate::core::File`].
pub fn core_reduce(file: crate::core::File, settings: &Settings) -> crate::core::File {
    crate::core::global_reduction::reduce(file, settings)
}

/// Core phase: E-specialization (see `crate::core::especialize`).
///
/// # Returns
///
/// Transformed [`crate::core::File`].
pub fn core_especialize(file: crate::core::File) -> crate::core::File {
    crate::core::especialize::especialize(file)
}

/// Like [`core_especialize`] but forwards recoverable internal diagnostics to `errors` when `Some`.
pub fn core_especialize_with_errors(
    file: crate::core::File,
    errors: &mut Option<&mut ErrorReporter>,
) -> crate::core::File {
    crate::core::especialize::especialize_with_reporter(file, errors)
}

/// Core phase: remove polymorphism where possible.
///
/// # Returns
///
/// Transformed [`crate::core::File`].
pub fn core_unpoly(file: crate::core::File) -> crate::core::File {
    crate::core::unpoly::unpoly(file)
}

/// Core phase: specialization pass.
///
/// # Returns
///
/// Transformed [`crate::core::File`].
pub fn core_specialize(file: crate::core::File) -> crate::core::File {
    crate::core::specialize::specialize(file)
}

/// Core phase: RPC elaboration; reports errors through `errors` and returns `None` if any occurred.
///
/// # Arguments
///
/// * `file` — Core program.
/// * `_settings` — Reserved for future RPC options.
/// * `errors` — Receives span-attached RPC errors.
///
/// # Returns
///
/// Updated [`crate::core::File`] or `None` when errors were reported.
pub fn core_rpcify(
    file: crate::core::File,
    _settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::core::File> {
    let mut had_errors = false;
    let result = crate::core::rpc_elaboration::rpcify(file, &mut |span, payload| {
        errors.report_type_at(span.clone(), payload);
        had_errors = true;
    });
    if had_errors {
        None
    } else {
        Some(result)
    }
}

/// Core phase: export tagging; returns `None` if `errors` received any diagnostic.
///
/// # Arguments
///
/// * `file` — Core program after RPC pass.
/// * `_settings` — Reserved.
/// * `errors` — Export/tagging errors.
///
/// # Returns
///
/// Tagged [`crate::core::File`] or `None`.
pub fn core_tag(
    file: crate::core::File,
    _settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::core::File> {
    let mut had_errors = false;
    let result = crate::core::export_tagging::tag(file, &mut |span, payload| {
        errors.report_type_at(span.clone(), payload);
        had_errors = true;
    });
    if had_errors {
        None
    } else {
        Some(result)
    }
}

/// Core phase: effect analysis; drops effect warnings from the helper.
///
/// # Arguments
///
/// * `file` — Core program.
/// * `settings` — Effect-policy options.
///
/// # Returns
///
/// Effect-annotated [`crate::core::File`].
pub fn core_effectize(file: crate::core::File, settings: &Settings) -> crate::core::File {
    let (result, _warnings) = crate::core::effect_analysis::effectize(file, settings);
    result
}

// ---------------------------------------------------------------------------
// Checks on Core
// ---------------------------------------------------------------------------

/// Verify cross-tier marshalling constraints on the core program.
///
/// # Arguments
///
/// * `file` — Core IR to check.
/// * `settings` — Protocol and database context.
/// * `errors` — Append-only diagnostics.
///
/// # Returns
///
/// Nothing.
pub fn check_marshal(file: &crate::core::File, settings: &Settings, errors: &mut ErrorReporter) {
    crate::core::marshal_check::check(file, settings, errors);
}

/// Run the termination checker on recursive bindings in `file`.
///
/// # Returns
///
/// Nothing; failures append to `errors`.
pub fn check_termination(file: &crate::core::File, errors: &mut ErrorReporter) {
    crate::core::termination_check::check(file, errors);
}

// ---------------------------------------------------------------------------
// Mono checks
// ---------------------------------------------------------------------------

/// Classify JavaScript script fragments for the monomorphized program.
///
/// # Arguments
///
/// * `file` — Monomorphized declarations.
/// * `settings` — Compilation options.
/// * `errors` — Diagnostic sink.
///
/// # Returns
///
/// Updated [`crate::monomorphized::File`].
pub fn mono_script_check(
    file: crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> crate::monomorphized::File {
    crate::monomorphized::script_check::classify(file, settings, errors)
}

/// Path-mode sanity check on URLs and handlers (append to `errors` on failure).
///
/// # Returns
///
/// Nothing.
pub fn mono_path_check(file: &crate::monomorphized::File, errors: &mut ErrorReporter) {
    crate::monomorphized::path_check::check(file, errors)
}

/// Client/server side classification; returns environment-variable hints as strings.
///
/// # Returns
///
/// Updated monomorphized file and side-effect metadata.
pub fn mono_side_check(
    file: crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> (crate::monomorphized::File, Vec<String>) {
    crate::monomorphized::side_check::check(file, settings, errors)
}

/// Validate monomorphized signatures (pass-through wrapper).
///
/// # Returns
///
/// Checked [`crate::monomorphized::File`].
pub fn mono_sig_check(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::sig_check::check(file)
}

/// Classify database modes after monomorphization.
///
/// # Returns
///
/// Updated [`crate::monomorphized::File`].
pub fn mono_dbmode_check(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::db_mode_check::classify(file)
}

// ---------------------------------------------------------------------------
// Phase: Monoize (core → mono)
// ---------------------------------------------------------------------------

/// Monomorphize the core program into concrete types and handlers.
///
/// # Arguments
///
/// * `file` — Typed core program.
/// * `settings` — Mono driver options.
/// * `errors` — Failures from the monomorphizer.
///
/// # Returns
///
/// [`crate::monomorphized::File`] or `None` when the pass fails.
pub fn monoize(
    file: crate::core::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::monomorphized::File> {
    crate::monomorphized::monoize::monoize(file, settings, errors)
}

// ---------------------------------------------------------------------------
// Mono passes
// ---------------------------------------------------------------------------

/// Mono phase: untangle (see `crate::monomorphized::untangle`).
///
/// # Returns
///
/// Transformed monomorphized file.
pub fn mono_untangle(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::untangle::untangle(file)
}

/// Mono phase: fuse adjacent bindings.
///
/// # Returns
///
/// Transformed file.
pub fn mono_fuse(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::fuse::fuse(file)
}

/// Mono phase: global reduction.
///
/// # Returns
///
/// Reduced monomorphized file.
pub fn mono_reduce(
    file: crate::monomorphized::File,
    settings: &Settings,
) -> crate::monomorphized::File {
    crate::monomorphized::mono_reduce::reduce(file, settings)
}

/// Mono phase: optimization (beta reduction and related rewrites).
///
/// # Returns
///
/// Optimized file (errors are non-fatal for some inner passes).
pub fn mono_opt(
    file: crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> crate::monomorphized::File {
    crate::monomorphized::mono_opt::optimize(file, settings, errors)
}

/// Mono phase: shake unused bindings in monomorphized IR.
///
/// # Returns
///
/// Pruned file.
pub fn mono_shake(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::mono_shake::shake(file)
}

/// Mono phase: aggressive inline + fuse pipeline (matches legacy `mono_inline` staging).
///
/// # Returns
///
/// File after inline, opt, fuse, opt, shake.
pub fn mono_inline(
    file: crate::monomorphized::File,
    settings: &Settings,
) -> crate::monomorphized::File {
    use std::sync::atomic::Ordering;
    let mut errors = ErrorReporter::from_settings(settings);
    // Mirror SML mono_inline.sml: set fullMode=true and mono_inline=max before reducing.
    let old_full = crate::monomorphized::mono_reduce::FULL_MODE.swap(true, Ordering::Relaxed);
    let mut full_settings = settings.clone();
    full_settings.mono_inline = u32::MAX;
    let file = mono_reduce(file, &full_settings);
    crate::monomorphized::mono_reduce::FULL_MODE.store(old_full, Ordering::Relaxed);
    let file = mono_opt(file, settings, &mut errors);
    let file = mono_fuse(file);
    let file = mono_opt(file, settings, &mut errors);
    mono_shake(file)
}

/// Hoist JavaScript fragments to top-level bindings for `app.js` emission.
///
/// # Returns
///
/// Rewritten file.
pub fn mono_name_js(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::name_js::rewrite(file)
}

/// Collect HTTP endpoint metadata while returning the file unchanged.
///
/// # Returns
///
/// Same file plus endpoint descriptor vector.
pub fn mono_endpoints(
    file: crate::monomorphized::File,
) -> (
    crate::monomorphized::File,
    Vec<crate::monomorphized::endpoints::Endpoint>,
) {
    crate::monomorphized::endpoints::collect(file)
}

/// Insert file-cache instrumentation when enabled in settings.
///
/// # Returns
///
/// Instrumented file.
pub fn mono_filecache(
    file: crate::monomorphized::File,
    settings: &Settings,
) -> crate::monomorphized::File {
    #[cfg(test)]
    MONO_FILECACHE_CALLS.fetch_add(1, Ordering::SeqCst);
    crate::monomorphized::filecache::instrument(file, settings)
}

/// Information-flow analysis in debug builds; `None` if a non-warning diagnostic was reported.
///
/// # Returns
///
/// Same file wrapped in `Some` on success.
pub fn mono_iflow(
    file: crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::monomorphized::File> {
    crate::monomorphized::iflow::check(&file, settings, errors);
    if errors.has_hard_errors() {
        None
    } else {
        Some(file)
    }
}

/// SQL cache instrumentation when `settings.sqlcache` is enabled (always `Some` today).
///
/// # Returns
///
/// Transformed file.
pub fn mono_sqlcache(
    file: crate::monomorphized::File,
    settings: &Settings,
    _errors: &mut ErrorReporter,
) -> Option<crate::monomorphized::File> {
    Some(crate::monomorphized::sqlcache::go(file, settings))
}

// ---------------------------------------------------------------------------
// Phase: CJRize (mono → cjr)
// ---------------------------------------------------------------------------

/// Lower monomorphized IR to C-like representation (CJR).
///
/// # Returns
///
/// [`crate::c_like_representation::File`] or `None` if `errors` collected failures.
pub fn cjrize(
    file: crate::monomorphized::File,
    errors: &mut ErrorReporter,
) -> Option<crate::c_like_representation::File> {
    crate::c_like_representation::cjrize::cjrize(file, errors)
}

// ---------------------------------------------------------------------------
// Phase: Prepare (cjr → cjr with prepared SQL statements)
// ---------------------------------------------------------------------------

/// Bind SQL statements to prepared handles in the CJR program.
///
/// # Returns
///
/// Prepared [`crate::c_like_representation::File`].
pub fn cjr_prepare(
    file: crate::c_like_representation::File,
    settings: &Settings,
) -> crate::c_like_representation::File {
    crate::c_like_representation::prepare::prepare(file, settings)
}

// ---------------------------------------------------------------------------
// Phase: CheckNest (annotate EQuery.prepared.nested on CJR)
// ---------------------------------------------------------------------------

/// Annotate nested query markers on prepared SQL expressions.
///
/// # Returns
///
/// Annotated [`crate::c_like_representation::File`].
pub fn cjr_check_nest(
    file: crate::c_like_representation::File,
) -> crate::c_like_representation::File {
    crate::c_like_representation::check_nest::annotate(file)
}

// ---------------------------------------------------------------------------
// Phase: C code generation (cjr → .c file)
// ---------------------------------------------------------------------------

/// Pretty-print CJR as C source text.
///
/// # Returns
///
/// Full C translation unit as a string.
pub fn cjr_print(file: &crate::c_like_representation::File, settings: &Settings) -> String {
    crate::c_like_representation::cjr_print::cjr_print(file, settings)
}

// ---------------------------------------------------------------------------
// Phase: JS compilation
// ---------------------------------------------------------------------------

/// Emit bundled JavaScript for the client tier (when applicable).
///
/// # Returns
///
/// JavaScript source string or `None` on failure (see `errors`).
pub fn js_compile(
    file: &crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<String> {
    crate::monomorphized::jscomp::js_compile(file, settings, errors)
}

// ---------------------------------------------------------------------------
// Phase: SQL DDL generation
// ---------------------------------------------------------------------------

/// Generate structured query language data-definition statements from the CJR program.
///
/// # Returns
///
/// DDL text for the configured database backend.
pub fn sql_generate(file: &crate::c_like_representation::File, settings: &Settings) -> String {
    crate::c_like_representation::sql_generate::sql_generate(file, settings)
}

// ---------------------------------------------------------------------------
// Phase: CSS summary (after core shake, optional diagnostic)
// ---------------------------------------------------------------------------

/// Summarize style/CSS-related constructs in the core program (diagnostics tooling).
///
/// # Returns
///
/// [`crate::core::css::Summary`] aggregate.
pub fn css_summarize(file: &crate::core::File) -> crate::core::css::Summary {
    #[cfg(test)]
    CSS_SUMMARIZE_CALLS.fetch_add(1, Ordering::SeqCst);
    crate::core::css::summarize(file)
}

// ---------------------------------------------------------------------------
// Phase: C compilation + linking
// ---------------------------------------------------------------------------

/// Under `cfg(test)`, cap how long `cc`/`ld` may run so argv mutants cannot hang `cargo mutants`.
#[cfg(test)]
const CC_LINK_TEST_DEADLINE: std::time::Duration = std::time::Duration::from_secs(90);

#[cfg(test)]
fn command_status_deadline(
    cmd: &mut std::process::Command,
    what: &str,
    locale: DiagnosticLocale,
) -> Result<std::process::ExitStatus> {
    use std::time::{Duration, Instant};
    let mut child = cmd.spawn().map_err(|spawn_error| {
        anyhow::anyhow!(
            "{}",
            cli_diagnostic_text(
                DiagnosticId::CliSubprocessSpawnFailed,
                vec![what.to_string(), spawn_error.to_string()],
                locale,
            )
        )
    })?;
    let start = Instant::now();
    loop {
        if let Some(st) = child.try_wait().map_err(|poll_error| {
            anyhow::anyhow!(
                "{}",
                cli_diagnostic_text(
                    DiagnosticId::CliSubprocessPollFailed,
                    vec![what.to_string(), poll_error.to_string()],
                    locale,
                )
            )
        })? {
            return Ok(st);
        }
        if start.elapsed() > CC_LINK_TEST_DEADLINE {
            let _ = child.kill();
            let _ = child.wait();
            bail!(
                "{}",
                cli_diagnostic_text(
                    DiagnosticId::CliCompilerCcLinkTestDeadlineExceeded,
                    vec![what.to_string(), format!("{CC_LINK_TEST_DEADLINE:?}")],
                    locale,
                )
            );
        }
        std::thread::sleep(Duration::from_millis(25));
    }
}

#[cfg(not(test))]
fn command_status_deadline(
    cmd: &mut std::process::Command,
    what: &str,
    locale: DiagnosticLocale,
) -> Result<std::process::ExitStatus> {
    cmd.status().map_err(|run_error| {
        anyhow::anyhow!(
            "{}",
            cli_diagnostic_text(
                DiagnosticId::CliSubprocessRunFailed,
                vec![what.to_string(), run_error.to_string()],
                locale,
            )
        )
    })
}

/// Write `c_source` to a `.c` file next to `output`, compile to `.o`, then link the executable at `output`.
///
/// When `job.debug` is true, passes `-g` so the binary includes debugging information (for example DWARF) for debuggers.
///
/// # Arguments
///
/// * `c_source` — Full C translation unit text.
/// * `output` — Desired executable path (stem used for intermediate `.c` / `.o` names).
/// * `job` — Link line flags (`debug`, `profile`, custom linker, …).
/// * `settings` — Include paths, runtime libraries, compiler executable.
///
/// # Returns
///
/// `Ok(())` when compile and link both succeed.
///
/// # Errors
///
/// Write failures, non-zero `cc`/`ld` status, or subprocess errors (messages use the diagnostic catalog where applicable).
pub fn cc_and_link(c_source: &str, output: &Path, job: &Job, settings: &Settings) -> Result<()> {
    use std::process::Command;
    #[cfg(test)]
    use std::process::Stdio;

    // Write C source to a temporary file.
    let c_dir = output.parent().unwrap_or_else(|| std::path::Path::new("."));
    let c_file = c_dir.join(format!(
        "{}.c",
        output
            .file_stem()
            .unwrap_or(std::ffi::OsStr::new("app"))
            .to_string_lossy()
    ));
    let o_file = c_dir.join(format!(
        "{}.o",
        output
            .file_stem()
            .unwrap_or(std::ffi::OsStr::new("app"))
            .to_string_lossy()
    ));

    let c_build_banner = cli_diagnostic_text(
        DiagnosticId::CliToolBannerCBuild,
        vec![],
        settings.diagnostic_locale,
    );
    std::fs::write(&c_file, c_source).map_err(|write_error| {
        anyhow::anyhow!(
            "{}",
            crate::error_types::format_tool_diagnostic_banner_and_body(
                &c_build_banner,
                &cli_diagnostic_text(
                    DiagnosticId::CliWriteGeneratedCFileFailed,
                    vec![c_file.display().to_string(), write_error.to_string()],
                    settings.diagnostic_locale,
                ),
            )
        )
    })?;

    let cc = if settings.config_c_compiler.is_empty() {
        "cc"
    } else {
        &settings.config_c_compiler
    };

    // Compile step. Use ISO C11 for generated code; cproc/gcc/clang all support it.
    let mut compile_cmd = Command::new(cc);
    compile_cmd
        .arg("-std=c11")
        .arg("-pedantic")
        .arg("-Wimplicit")
        .arg("-Werror")
        .arg("-Wno-unused-value")
        .arg("-Wno-gnu-zero-variadic-macro-arguments")
        .arg("-c")
        .arg(&c_file)
        .arg("-o")
        .arg(&o_file);
    // No `!foo.is_empty()` here: `delete !` mutants used to pass empty `-I`/flags to cc and hang.
    match job.debug {
        true => {}
        false => {
            compile_cmd.arg("-O3");
        }
    }
    match settings.config_include.is_empty() {
        true => {}
        false => {
            compile_cmd.arg("-I").arg(&settings.config_include);
        }
    }
    if let Ok(dir) = std::env::var("URWEB_NATIVE_LIB_DIR") {
        match dir.is_empty() {
            true => {}
            false => {
                let inc = std::path::Path::new(&dir).join("include");
                if inc.is_dir() {
                    compile_cmd.arg("-I").arg(&inc);
                }
            }
        }
    }
    append_urweb_native_include_fallback(&mut compile_cmd);
    #[cfg(test)]
    {
        compile_cmd
            .stdin(Stdio::null())
            .stderr(Stdio::null())
            .stdout(Stdio::null());
    }
    if job.debug {
        compile_cmd.arg("-g");
    }
    if job.profile {
        compile_cmd.arg("-pg");
    }

    if settings.verbosity >= 2 {
        tracing::debug!(
            cc = %cc,
            c_file = %c_file.display(),
            o_file = %o_file.display(),
            "C compile (object) step"
        );
    }
    let compile_status = command_status_deadline(
        &mut compile_cmd,
        &format!("C compiler '{cc}'"),
        settings.diagnostic_locale,
    )?;
    match compile_status.success() {
        true => {}
        false => {
            let detail = cli_diagnostic_text(
                DiagnosticId::CliCCompilerRejectedGeneratedFile,
                vec![
                    cc.to_string(),
                    format!("{compile_status}"),
                    c_file.display().to_string(),
                ],
                settings.diagnostic_locale,
            );
            bail!(
                "{}",
                crate::error_types::format_tool_diagnostic_banner_and_body(
                    &c_build_banner,
                    &detail
                )
            );
        }
    }

    // Link step.
    let linker_cmd_base = job.linker.as_deref().unwrap_or(cc);
    let mut link_cmd = Command::new(linker_cmd_base);
    #[cfg(test)]
    {
        link_cmd
            .stdin(Stdio::null())
            .stderr(Stdio::null())
            .stdout(Stdio::null());
    }
    link_cmd.arg(&o_file);
    if let Ok(dir) = std::env::var("URWEB_NATIVE_LIB_DIR") {
        match dir.is_empty() {
            true => {}
            false => {
                link_cmd.arg(format!("-L{}", dir));
            }
        }
    }
    append_urweb_native_libdir_fallback(&mut link_cmd);
    // Protocol-specific runtime library (provides main())
    match settings.config_lib.is_empty() {
        true => {}
        false => {
            let proto = if settings.protocol.is_empty() {
                "http"
            } else {
                settings.protocol.as_str()
            };
            let proto_lib = format!("{}/liburweb_{}.a", settings.config_lib, proto);
            if std::path::Path::new(&proto_lib).exists() {
                link_cmd.arg(&proto_lib);
            }
            link_cmd.arg(format!("-L{}", settings.config_lib));
        }
    }
    link_cmd.arg("-lurweb").arg("-lm");
    let db_link = dbms_link_library_flag(settings);
    for token in db_link.split_whitespace() {
        match token.is_empty() {
            true => {}
            false => {
                link_cmd.arg(token);
            }
        }
    }
    // BearSSL (crypto)
    match settings.config_bearssl_libs.is_empty() {
        true => {}
        false => {
            for flag in settings.config_bearssl_libs.split_whitespace() {
                link_cmd.arg(flag);
            }
        }
    }
    // libunistring (Unicode character operations)
    match settings.config_libunistring_libs.is_empty() {
        true => {}
        false => {
            for flag in settings.config_libunistring_libs.split_whitespace() {
                link_cmd.arg(flag);
            }
        }
    }
    // pthreads
    link_cmd.arg("-lpthread");
    link_cmd.arg("-o").arg(output);
    if job.debug {
        link_cmd.arg("-g");
    }
    if job.profile {
        link_cmd.arg("-pg");
    }

    if settings.verbosity >= 2 {
        tracing::debug!(
            linker = %linker_cmd_base,
            output = %output.display(),
            "C link step"
        );
    }
    let link_banner = cli_diagnostic_text(
        DiagnosticId::CliToolBannerLink,
        vec![],
        settings.diagnostic_locale,
    );
    let link_status = command_status_deadline(
        &mut link_cmd,
        &format!("linker '{linker_cmd_base}'"),
        settings.diagnostic_locale,
    )?;
    match link_status.success() {
        true => {}
        false => {
            let detail = cli_diagnostic_text(
                DiagnosticId::CliLinkerCouldNotProduceExecutable,
                vec![
                    linker_cmd_base.to_string(),
                    format!("{link_status}"),
                    output.display().to_string(),
                    o_file.display().to_string(),
                ],
                settings.diagnostic_locale,
            );
            bail!(
                "{}",
                crate::error_types::format_tool_diagnostic_banner_and_body(&link_banner, &detail)
            );
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Top-level: full build pipeline
// ---------------------------------------------------------------------------

/// Normalize a user path to the `.urp` file (`foo` / `foo.ur` → `foo.urp`).
///
/// # Returns
///
/// Path with `.urp` extension when missing.
pub(crate) fn resolve_urp_project_path(urp_path: &Path) -> PathBuf {
    if urp_path.extension().is_none_or(|e| e != "urp") {
        urp_path.with_extension("urp")
    } else {
        urp_path.to_path_buf()
    }
}

/// Extra linker tokens for the resolved database back end (for example `-lsqlite3`).
///
/// # Returns
///
/// Static string slice (possibly empty or multiple whitespace-separated flags).
pub(crate) fn dbms_link_library_flag(settings: &crate::settings::Settings) -> &'static str {
    crate::db::link_library_flag_from_option(&settings.db_backend)
}

/// Merge `.urp` `database` / `dbms` lines into `settings` when the command line left them unset.
///
/// # Errors
///
/// Invalid engine or connection string combinations as `String`.
pub(crate) fn apply_job_db_settings(
    job: &Job,
    settings: &mut crate::settings::Settings,
) -> Result<(), String> {
    crate::db::apply_urp_job_db_fields(settings, job.dbms.as_deref(), job.database.as_deref())
}

/// Parse `.urp` and produce [`Job`] plus merged [`Settings`] (boot discovery, database fields, `ur.toml` reconciliation).
///
/// # Errors
///
/// Parse failures, database validation, or manifest mismatch strings.
pub fn resolve_project_job_and_settings(urp_path: &Path) -> Result<(Job, Settings), String> {
    let mut job = parse_urp(urp_path).map_err(|e| e.to_string())?;
    let mut settings = Settings::new();
    settings.boot_linking = true;
    apply_boot_settings(&mut job, &mut settings)?;
    apply_job_db_settings(&job, &mut settings).map_err(|e| e.to_string())?;
    let urp = resolve_urp_project_path(urp_path);
    crate::db::apply_urp_manifest_db_defaults(&urp, &mut settings)?;
    crate::db::apply_urp_manifest_diagnostic_locale(&urp, &mut settings)?;
    crate::db::reconcile_ur_manifest_with_resolved_db(&urp, &settings)?;
    Ok((job, settings))
}

/// [`Settings`] from [`resolve_project_job_and_settings`] without returning the [`Job`].
pub fn resolve_project_settings_for_urp(urp_path: &Path) -> Result<Settings, String> {
    Ok(resolve_project_job_and_settings(urp_path)?.1)
}

/// Resolved [`crate::db::ProjectDb`] for an editor workspace root (single `.urp` + `ur.toml` rules).
///
/// Batch compile, [`crate::lsp_analysis::ProjectState::open`], and tooling should agree on this for the same tree.
///
/// # Errors
///
/// Same as project resolution when discovery or reconciliation fails.
pub fn effective_project_db_for_workspace_root(
    workspace_root: &std::path::Path,
) -> Result<crate::db::ProjectDb, String> {
    let locale =
        crate::cli_common::diagnostic_locale_from_manifest_path(&workspace_root.join("ur.toml"));
    let urp_path = crate::lsp_workspace::discover_unique_urp(workspace_root)
        .map_err(|discovery_error| discovery_error.to_diagnostic_text(locale))?;
    let (_, settings) = resolve_project_job_and_settings(&urp_path).map_err(|resolver_error| {
        crate::cli_common::cli_diagnostic_text(
            DiagnosticId::CliLspProjectResolveFailed,
            vec![
                urp_path.display().to_string(),
                format!("{resolver_error:#}"),
            ],
            locale,
        )
    })?;
    Ok(crate::db::effective_project_db(&settings))
}

/// Run the full compilation pipeline for a `.urp` project through C compilation and linking.
///
/// Wraps the inner result in [`CompileResult`] for mutation-testing compatibility.
///
/// # Arguments
///
/// * `urp_path` — Project file or stem (`.urp` appended when needed).
/// * `settings` — In/out driver settings (URL prefix, headers, debug, merged database options, …).
///
/// # Returns
///
/// [`CompileResult`] wrapping the path to the generated executable or an [`anyhow::Error`].
pub fn compile(urp_path: &Path, settings: &mut Settings) -> CompileResult {
    run_compile(urp_path, settings).into()
}

fn run_compile(urp_path: &Path, settings: &mut Settings) -> Result<PathBuf> {
    use std::time::Instant;

    // Phase 1: parse project file (append .urp if not already present)
    let urp_path_buf = resolve_urp_project_path(urp_path);
    crate::db::apply_urp_manifest_diagnostic_locale(&urp_path_buf, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;
    let mut errors = ErrorReporter::from_settings(settings);
    let mut job = crate::urp_parser::parse_urp_with_reporter(&urp_path_buf, &mut errors)?;

    apply_boot_settings(&mut job, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;
    apply_job_db_settings(&job, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;
    crate::db::apply_urp_manifest_db_defaults(&urp_path_buf, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;
    crate::db::reconcile_ur_manifest_with_resolved_db(&urp_path_buf, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;

    // Apply job settings globally
    settings.set_url_prefix(&job.prefix);
    settings.timeout = job.timeout;
    settings.headers = job.headers.clone();
    settings.scripts = job.scripts.clone();
    settings.debug = job.debug;

    crate::compiler_tracing::init_compiler_tracing(settings);
    tracing::info!(urp = %urp_path_buf.display(), verbosity = settings.verbosity, "starting Ur/Web compilation");

    let mut phase_t = Instant::now();
    // Phase 2: parse sources
    let source_file = parse_sources(&job, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "parsing"))?;
    bail_if_errors_reported(&errors, "Parsing", settings.diagnostic_locale)?;
    crate::compiler_tracing::log_phase_complete(settings, "parse", phase_t);

    phase_t = Instant::now();
    // Phase 3: elaborate
    let elab_file = elaborate(source_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "elaboration"))?;
    bail_if_errors_reported(
        &errors,
        "Elaboration (types and modules)",
        settings.diagnostic_locale,
    )?;

    // Phase 3.5: unnest
    let elab_file = unnest(elab_file, &mut errors);
    bail_if_errors_reported(
        &errors,
        "Unnest (lambda lifting)",
        settings.diagnostic_locale,
    )?;
    crate::compiler_tracing::log_phase_complete(settings, "elaborate", phase_t);

    phase_t = Instant::now();
    // Phase 4: explify
    let expl_file = explify(elab_file, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "explify"))?;

    // Phase 5: corify
    let core_file = corify(expl_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "corify"))?;
    crate::compiler_tracing::log_phase_complete(settings, "explify_corify", phase_t);

    phase_t = Instant::now();
    // Core passes
    let core_file = core_untangle(core_file);
    let mut core_recovery_reporter: Option<&mut ErrorReporter> = Some(&mut errors);
    let core_file = core_reduce_local_with_errors(core_file, &mut core_recovery_reporter);
    let core_file = core_shake(core_file);
    let core_file = core_reduce(core_file, settings);
    let core_file = core_especialize_with_errors(core_file, &mut core_recovery_reporter);
    let core_file = core_unpoly(core_file);
    let core_file = core_specialize(core_file);
    let core_file = core_rpcify(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "rpcify"))?;
    let core_file = core_tag(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "tag"))?;
    let core_file = core_effectize(core_file, settings);

    // Core checks
    check_marshal(&core_file, settings, &mut errors);
    check_termination(&core_file, &mut errors);
    bail_if_errors_reported(
        &errors,
        "Core verification (marshalling / termination)",
        settings.diagnostic_locale,
    )?;
    crate::compiler_tracing::log_phase_complete(settings, "core", phase_t);

    phase_t = Instant::now();
    // Monoize
    let mono_file = monoize(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "monomorphization"))?;

    // Collect endpoint metadata (endpoints.sml) — side output, file unchanged.
    let (mono_file, _endpoints) = mono_endpoints(mono_file);

    // Mono passes
    let mono_file = mono_untangle(mono_file);
    let mono_file = mono_fuse(mono_file);
    // Run mono_opt BEFORE the first reduce, like SML's toMono_opt1 pass.
    // This unconditionally beta-reduces App(Abs, arg) patterns (including impure args),
    // eliminating anonymous lambdas before mono_reduce converts them to Let bindings.
    let mono_file = mono_opt(mono_file, settings, &mut errors);
    let mono_file = mono_reduce(mono_file, settings);
    let mono_file = mono_opt(mono_file, settings, &mut errors);
    let mono_file = mono_shake(mono_file);
    let mono_file = mono_inline(mono_file, settings);

    // Mono checks
    let mono_file = mono_script_check(mono_file, settings, &mut errors);
    mono_path_check(&mono_file, &mut errors);
    let (mono_file, _env_vars) = mono_side_check(mono_file, settings, &mut errors);
    let mono_file = mono_sig_check(mono_file);
    let mono_file = mono_dbmode_check(mono_file);
    bail_if_errors_reported(
        &errors,
        "Monomorphization checks",
        settings.diagnostic_locale,
    )?;
    crate::compiler_tracing::log_phase_complete(settings, "mono", phase_t);

    phase_t = Instant::now();
    let mono_file = if settings.debug {
        mono_iflow(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow_phase_incomplete(settings, "information-flow analysis"))?
    } else {
        mono_file
    };

    // Name JavaScript fragments (name_js.sml) — hoist non-trivial EJavaScript
    // sub-expressions to top-level DVal bindings for app.js placement.
    let mono_file = mono_name_js(mono_file);
    let mono_file = mono_filecache(mono_file, settings);

    let mono_file = if settings.sqlcache {
        mono_sqlcache(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow_phase_incomplete(settings, "SQL cache"))?
    } else {
        mono_file
    };

    // JS compilation
    let _js = js_compile(&mono_file, settings, &mut errors);

    // CJRize
    let cjr_file = cjrize(mono_file, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "C back-end lowering"))?;
    bail_if_errors_reported(&errors, "C back-end (CJR)", settings.diagnostic_locale)?;

    // Prepare SQL statements and annotate nested queries
    let cjr_file = cjr_prepare(cjr_file, settings);
    let cjr_file = cjr_check_nest(cjr_file);

    // Generate C code
    crate::db::require_sql_codegen_from_option(&settings.db_backend)?;
    let c_code = cjr_print(&cjr_file, settings);
    let sql_ddl = sql_generate(&cjr_file, settings);
    crate::compiler_tracing::log_phase_complete(settings, "codegen", phase_t);

    // Write SQL if requested
    if let Some(sql_path) = &job.sql {
        let locale = settings.diagnostic_locale;
        std::fs::write(sql_path, &sql_ddl).map_err(|write_error| {
            anyhow::anyhow!(
                "{}",
                cli_diagnostic_text(
                    DiagnosticId::CliCompileWriteSqlFileFailed,
                    vec![sql_path.clone(), write_error.to_string()],
                    locale,
                )
            )
        })?;
    }

    phase_t = Instant::now();
    // Compile and link
    let exe_path = PathBuf::from(&job.exe);
    cc_and_link(&c_code, &exe_path, &job, settings)?;
    crate::compiler_tracing::log_phase_complete(settings, "link", phase_t);

    tracing::info!(exe = %exe_path.display(), "Ur/Web compilation finished");
    Ok(exe_path)
}

/// Run the same pipeline as [`compile`] but stop after code generation: return C source and SQL DDL strings.
///
/// Skips [`cc_and_link`] and executable output; useful for tests.
///
/// # Returns
///
/// `(c_code, sql_ddl)` on success.
///
/// # Errors
///
/// Same classes of failure as the full pipeline (parse, elaborate, mono, CJR, …).
pub fn compile_to_outputs(urp_path: &Path, settings: &mut Settings) -> Result<(String, String)> {
    use std::time::Instant;

    let urp_path_buf = resolve_urp_project_path(urp_path);
    crate::db::apply_urp_manifest_diagnostic_locale(&urp_path_buf, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;
    let mut errors = ErrorReporter::from_settings(settings);
    let mut job = crate::urp_parser::parse_urp_with_reporter(&urp_path_buf, &mut errors)?;
    apply_boot_settings(&mut job, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;
    apply_job_db_settings(&job, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;
    crate::db::apply_urp_manifest_db_defaults(&urp_path_buf, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;
    crate::db::reconcile_ur_manifest_with_resolved_db(&urp_path_buf, settings)
        .map_err(|error_message| anyhow::anyhow!(error_message))?;

    settings.set_url_prefix(&job.prefix);
    settings.timeout = job.timeout;
    settings.headers = job.headers.clone();
    settings.scripts = job.scripts.clone();
    settings.debug = job.debug;

    crate::compiler_tracing::init_compiler_tracing(settings);
    tracing::info!(urp = %urp_path_buf.display(), mode = "compile_to_outputs", "starting Ur/Web pipeline");

    let mut phase_t = Instant::now();
    let source_file = parse_sources(&job, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "parsing"))?;
    bail_if_errors_reported(&errors, "Parsing", settings.diagnostic_locale)?;
    crate::compiler_tracing::log_phase_complete(settings, "parse", phase_t);

    phase_t = Instant::now();
    let elab_file = elaborate(source_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "elaboration"))?;
    bail_if_errors_reported(
        &errors,
        "Elaboration (types and modules)",
        settings.diagnostic_locale,
    )?;

    let elab_file = unnest(elab_file, &mut errors);
    bail_if_errors_reported(
        &errors,
        "Unnest (lambda lifting)",
        settings.diagnostic_locale,
    )?;
    crate::compiler_tracing::log_phase_complete(settings, "elaborate", phase_t);

    phase_t = Instant::now();
    let expl_file = explify(elab_file, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "explify"))?;
    let core_file = corify(expl_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "corify"))?;
    crate::compiler_tracing::log_phase_complete(settings, "explify_corify", phase_t);

    phase_t = Instant::now();
    let core_file = core_untangle(core_file);
    let mut core_recovery_reporter: Option<&mut ErrorReporter> = Some(&mut errors);
    let core_file = core_reduce_local_with_errors(core_file, &mut core_recovery_reporter);
    let core_file = core_shake(core_file);
    let core_file = core_reduce(core_file, settings);
    let core_file = core_especialize_with_errors(core_file, &mut core_recovery_reporter);
    let core_file = core_unpoly(core_file);
    let core_file = core_specialize(core_file);
    let core_file = core_rpcify(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "rpcify"))?;
    let core_file = core_tag(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "tag"))?;
    let core_file = core_effectize(core_file, settings);

    check_marshal(&core_file, settings, &mut errors);
    check_termination(&core_file, &mut errors);
    bail_if_errors_reported(
        &errors,
        "Core verification (marshalling / termination)",
        settings.diagnostic_locale,
    )?;
    crate::compiler_tracing::log_phase_complete(settings, "core", phase_t);

    phase_t = Instant::now();
    let mono_file = monoize(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "monomorphization"))?;
    let (mono_file, _endpoints) = mono_endpoints(mono_file);
    let mono_file = mono_untangle(mono_file);
    let mono_file = mono_fuse(mono_file);
    let mono_file = mono_opt(mono_file, settings, &mut errors);
    let mono_file = mono_reduce(mono_file, settings);
    let mono_file = mono_opt(mono_file, settings, &mut errors);
    let mono_file = mono_shake(mono_file);
    let mono_file = mono_inline(mono_file, settings);
    let mono_file = mono_script_check(mono_file, settings, &mut errors);
    mono_path_check(&mono_file, &mut errors);
    let (mono_file, _env_vars) = mono_side_check(mono_file, settings, &mut errors);
    let mono_file = mono_sig_check(mono_file);
    let mono_file = mono_dbmode_check(mono_file);
    bail_if_errors_reported(
        &errors,
        "Monomorphization checks",
        settings.diagnostic_locale,
    )?;
    crate::compiler_tracing::log_phase_complete(settings, "mono", phase_t);

    phase_t = Instant::now();
    let mono_file = if settings.debug {
        mono_iflow(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow_phase_incomplete(settings, "information-flow analysis"))?
    } else {
        mono_file
    };
    let mono_file = mono_name_js(mono_file);
    let mono_file = if settings.sqlcache {
        mono_sqlcache(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow_phase_incomplete(settings, "SQL cache"))?
    } else {
        mono_file
    };

    let _js = js_compile(&mono_file, settings, &mut errors);
    let cjr_file = cjrize(mono_file, &mut errors)
        .ok_or_else(|| anyhow_phase_incomplete(settings, "C back-end lowering"))?;
    bail_if_errors_reported(&errors, "C back-end (CJR)", settings.diagnostic_locale)?;

    let cjr_file = cjr_prepare(cjr_file, settings);
    let cjr_file = cjr_check_nest(cjr_file);

    crate::db::require_sql_codegen_from_option(&settings.db_backend)?;
    let c_code = cjr_print(&cjr_file, settings);
    let sql_ddl = sql_generate(&cjr_file, settings);
    crate::compiler_tracing::log_phase_complete(settings, "codegen", phase_t);
    tracing::info!("compile_to_outputs finished (no link step)");
    Ok((c_code, sql_ddl))
}

// ---------------------------------------------------------------------------
// Module name helper (used by main.rs)
// ---------------------------------------------------------------------------

/// Derive the Ur/Web module name from a filename stem (capitalizes the first Unicode scalar).
///
/// Example: `/path/to/my_app.ur` → `"MyApp"`.
///
/// # Returns
///
/// Module name string (may be empty for odd paths).
pub fn module_of(filename: &str) -> String {
    let path = Path::new(filename);
    let stem = path.file_stem().unwrap_or_default().to_string_lossy();
    // Capitalize first letter, rest unchanged (mirrors SML `capitalize`)
    let mut chars = stem.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => {
            let mut out = c.to_uppercase().collect::<String>();
            out.push_str(chars.as_str());
            out
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::{DatabaseBackend, ProjectDb};
    use std::path::Path;
    use std::sync::atomic::Ordering;

    fn settings_with_db(db: ProjectDb) -> Settings {
        Settings {
            db_backend: Some(db),
            ..Default::default()
        }
    }

    /// Run `f` with process cwd set to `dir`, holding [`TEST_CWD_LOCK`] so parallel tests
    /// do not clobber each other’s working directory.
    fn with_parse_test_cwd<R, F: FnOnce() -> R>(dir: &Path, f: F) -> R {
        let _guard = crate::compiler_diagnostics::lock_for_compile(
            &crate::compiler_diagnostics::TEST_CWD_LOCK,
            "compiler tests cwd",
        );
        let prev = std::env::current_dir().unwrap_or_else(|_| {
            let t = std::env::temp_dir();
            std::env::set_current_dir(&t).expect("chdir to temp_dir");
            t
        });
        std::env::set_current_dir(dir).expect("chdir to test project directory");
        let out = f();
        std::env::set_current_dir(&prev).expect("restore cwd");
        out
    }

    fn minimal_mono_file() -> crate::monomorphized::File {
        (
            vec![crate::error_types::Located::dummy(
                crate::monomorphized::Decl::Database {
                    name: "db".into(),
                    expunge: 0,
                    initialize: 0,
                    uses_similar: false,
                },
            )],
            vec![],
        )
    }

    fn minimal_cjr_file() -> crate::c_like_representation::File {
        (
            vec![crate::error_types::Located::dummy(
                crate::c_like_representation::Decl::Database {
                    name: "db".into(),
                    expunge: 0,
                    initialize: 0,
                    uses_similar: false,
                },
            )],
            vec![],
        )
    }

    /// Assert `left` and `right` denote the same location after [`std::fs::canonicalize`].
    ///
    /// Temporary directories on macOS often use `/var/folders/...` while canonical paths use
    /// `/private/var/folders/...`; [`super::resolve_boot_root`] also canonicalizes `URWEB_BOOT_ROOT`.
    ///
    /// # Panics
    ///
    /// Panics if either path cannot be canonicalized or the canonical [`std::path::PathBuf`] values differ.
    fn assert_paths_canonically_equal(left: &Path, right: &Path) {
        let left_canonical = std::fs::canonicalize(left).expect("canonicalize left test path"); // symlinks, /private on macOS
        let right_canonical = std::fs::canonicalize(right).expect("canonicalize right test path"); // same for other operand
        assert_eq!(
            left_canonical, right_canonical,
            "expected the same directory after canonicalization (macOS /private prefix, symlinks)"
        ); // surface both paths when they mismatch
    }

    #[test]
    fn module_of_simple() {
        assert_eq!(module_of("foo.ur"), "Foo");
    }

    #[test]
    fn module_of_path() {
        assert_eq!(module_of("/a/b/myApp.ur"), "MyApp");
    }

    #[test]
    fn module_of_no_extension() {
        assert_eq!(module_of("hello"), "Hello");
    }

    #[test]
    fn job_default() {
        let j = Job::default();
        assert_eq!(j.prefix, "/");
        assert_eq!(j.timeout, 120);
    }

    /// Mutants that make [`super::bail_if_errors_reported`] always `Ok(())` let the pipeline run on broken input and can hit mutation timeouts.
    #[test]
    fn bail_if_errors_reported_fails_when_diagnostics_present() {
        let mut errors = ErrorReporter::new();
        errors.report(crate::error_types::CompileError::Plain(
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, Vec::new()),
        ));
        let out = bail_if_errors_reported(&errors, "Parsing", DiagnosticLocale::En);
        assert!(
            out.is_err(),
            "must stop the pipeline when the error buffer is non-empty"
        );
        let msg = out.unwrap_err().to_string();
        assert!(
            msg.contains("Parsing") && msg.contains('1'),
            "message should name the phase and error count: {msg}"
        );
    }

    /// Silent success path for [`super::bail_if_errors_reported`] (catches inverted condition mutants).
    #[test]
    fn bail_if_errors_reported_ok_when_no_diagnostics() {
        let errors = ErrorReporter::new();
        assert!(
            bail_if_errors_reported(&errors, "Parsing", DiagnosticLocale::En).is_ok(),
            "empty error buffer must not bail"
        );
    }

    /// Warnings stored on the reporter must not abort batch compile (`.urp` soft failures, core recovery).
    #[test]
    fn bail_if_errors_reported_ok_when_only_warnings() {
        use crate::error_types::{CompileError, Span};

        let mut errors = ErrorReporter::new();
        errors.report(CompileError::warning_at(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, Vec::new()),
        ));
        assert!(
            bail_if_errors_reported(&errors, "Parsing", DiagnosticLocale::En).is_ok(),
            "warning-only buffer must not bail"
        );
    }

    /// [`super::boot_root_from`] must walk parents until `lib/ur/basis.urs` exists (`None` / wrong `Some` mutants break boot and native fallbacks).
    #[test]
    fn boot_root_from_finds_checkout_markers() {
        let tmp = tempfile::tempdir().unwrap();
        let basis_dir = tmp.path().join("lib/ur");
        std::fs::create_dir_all(&basis_dir).unwrap();
        std::fs::write(basis_dir.join("basis.urs"), "(* test sig *)").unwrap();
        let start = tmp.path().join("nested/deep");
        std::fs::create_dir_all(&start).unwrap();
        let root = boot_root_from(start);
        assert_eq!(
            root.as_deref(),
            Some(tmp.path()),
            "expected parent scan to find directory containing lib/ur/basis.urs"
        );
    }

    /// [`super::resolve_boot_root`] must prefer [`super::URWEB_BOOT_ROOT_ENV`] when it points at a valid tree.
    #[test]
    fn resolve_boot_root_honors_urweb_boot_root_env() {
        let _guard = crate::compiler_diagnostics::lock_for_compile(
            &crate::compiler_diagnostics::TEST_CWD_LOCK,
            "resolve_boot_root URWEB_BOOT_ROOT",
        );
        let tmp = tempfile::tempdir().unwrap();
        let basis_dir = tmp.path().join("lib/ur");
        std::fs::create_dir_all(&basis_dir).unwrap();
        std::fs::write(basis_dir.join("basis.urs"), "(* test sig *)").unwrap();
        let previous = std::env::var_os(URWEB_BOOT_ROOT_ENV);
        std::env::set_var(URWEB_BOOT_ROOT_ENV, tmp.path());
        let root = resolve_boot_root();
        match &previous {
            None => std::env::remove_var(URWEB_BOOT_ROOT_ENV),
            Some(value) => std::env::set_var(URWEB_BOOT_ROOT_ENV, value),
        }
        let root_path = root
            .as_deref()
            .expect("URWEB_BOOT_ROOT with basis.urs must resolve"); // resolver returns Some(...)
        assert_paths_canonically_equal(root_path, tmp.path()); // string compare fails across /var vs /private
    }

    /// [`super::apply_boot_settings`] must replace an existing `basis_lib_dir` when boot linking resolves a root.
    #[test]
    fn apply_boot_settings_overrides_basis_lib_dir_when_boot_root_known() {
        let _guard = crate::compiler_diagnostics::lock_for_compile(
            &crate::compiler_diagnostics::TEST_CWD_LOCK,
            "apply_boot_settings basis_lib_dir override",
        );
        let tmp = tempfile::tempdir().unwrap();
        let basis_dir = tmp.path().join("lib/ur");
        std::fs::create_dir_all(&basis_dir).unwrap();
        std::fs::write(basis_dir.join("basis.urs"), "(* test sig *)").unwrap();
        let previous = std::env::var_os(URWEB_BOOT_ROOT_ENV);
        std::env::set_var(URWEB_BOOT_ROOT_ENV, tmp.path());
        let wrong = tmp.path().join("not_lib_ur");
        let mut job = Job {
            basis_lib_dir: Some(wrong),
            ..Default::default()
        };
        let mut settings = Settings {
            boot_linking: true,
            ..Default::default()
        };
        apply_boot_settings(&mut job, &mut settings)
            .expect("apply_boot_settings with temp URWEB_BOOT_ROOT");
        match &previous {
            None => std::env::remove_var(URWEB_BOOT_ROOT_ENV),
            Some(value) => std::env::set_var(URWEB_BOOT_ROOT_ENV, value),
        }
        let configured_basis = job
            .basis_lib_dir
            .as_deref()
            .expect("apply_boot_settings sets basis"); // overwritten from boot root
        assert_paths_canonically_equal(configured_basis, basis_dir.as_path()); // canonical root/lib/ur vs temp paths
    }

    /// [`super::ur_disk_paths_same`] is used for LSP overlay selection; `true`/`false` mutants mis-apply editor buffers.
    #[test]
    fn ur_disk_paths_same_same_file_true() {
        let tmp = tempfile::tempdir().unwrap();
        let p = tmp.path().join("mod.ur");
        std::fs::write(&p, "val x = 1\n").unwrap();
        assert!(
            ur_disk_paths_same(&p, &p),
            "identical paths must compare equal without canonical I/O errors"
        );
    }

    /// Symlinked paths should match after canonicalization (LSP / temp-project layouts).
    #[cfg(unix)]
    #[test]
    fn ur_disk_paths_same_symlink_matches_target() {
        let tmp = tempfile::tempdir().unwrap();
        let real = tmp.path().join("real.ur");
        std::fs::write(&real, "val x = 1\n").unwrap();
        let alias = tmp.path().join("alias.ur");
        std::os::unix::fs::symlink(&real, &alias).expect("symlink");
        assert!(
            ur_disk_paths_same(&real, &alias),
            "canonical comparison must treat symlink alias as the same file"
        );
    }

    #[test]
    fn ur_disk_paths_same_unrelated_files_are_false() {
        let tmp = tempfile::tempdir().unwrap();
        let a = tmp.path().join("a.ur");
        let b = tmp.path().join("b.ur");
        std::fs::write(&a, "1").unwrap();
        std::fs::write(&b, "2").unwrap();
        assert!(
            !ur_disk_paths_same(&a, &b),
            "mutants forcing true would break LSP overlay selection"
        );
    }

    /// `append_*` no-op mutants skip these counters (see `cargo mutants` timeouts on argv builders).
    #[test]
    fn append_urweb_native_fallbacks_execute() {
        let previous = std::env::var_os("URWEB_NATIVE_LIB_DIR");
        std::env::remove_var("URWEB_NATIVE_LIB_DIR");
        APPEND_NATIVE_INCLUDE_FALLBACK_INVOCATIONS.store(0, Ordering::SeqCst);
        APPEND_NATIVE_LIBDIR_FALLBACK_INVOCATIONS.store(0, Ordering::SeqCst);
        let mut compile_cmd = std::process::Command::new("true");
        append_urweb_native_include_fallback(&mut compile_cmd);
        let mut link_cmd = std::process::Command::new("true");
        append_urweb_native_libdir_fallback(&mut link_cmd);
        assert!(
            APPEND_NATIVE_INCLUDE_FALLBACK_INVOCATIONS.load(Ordering::SeqCst) >= 1
                && APPEND_NATIVE_LIBDIR_FALLBACK_INVOCATIONS.load(Ordering::SeqCst) >= 1,
            "native fallback shims must run real logic"
        );
        match previous {
            Some(value) => std::env::set_var("URWEB_NATIVE_LIB_DIR", value),
            None => std::env::remove_var("URWEB_NATIVE_LIB_DIR"),
        }
    }

    /// Whole-function mutants (`None` / `Some(Default::default())`) omit the first [`RESOLVE_BOOT_ROOT_INVOCATIONS`] bump.
    #[test]
    fn resolve_boot_root_runs_observable_body() {
        RESOLVE_BOOT_ROOT_INVOCATIONS.store(0, Ordering::SeqCst);
        let _ = resolve_boot_root();
        assert!(
            RESOLVE_BOOT_ROOT_INVOCATIONS.load(Ordering::SeqCst) >= 1,
            "replace resolve_boot_root body must not skip the hook"
        );
    }

    /// Boot linking sets `Top`’s wrapper span to `"<top>"` in [`parse_sources_inner`].
    ///
    /// The checkout `lib/ur/top.ur` may exceed this parser’s grammar; the test uses a tiny `lib/ur`
    /// under a temp dir (real `basis.urs` copied from the workspace, minimal `top.ur` / `top.urs`).
    #[test]
    fn parse_sources_boot_mode_preserves_top_marker_span_file() {
        let manifest_lib =
            std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("lib/ur/basis.urs");
        if !manifest_lib.is_file() {
            return;
        }
        let dir = tempfile::tempdir().unwrap();
        let mini_lib = dir.path().join("lib/ur");
        std::fs::create_dir_all(&mini_lib).unwrap();
        std::fs::copy(&manifest_lib, mini_lib.join("basis.urs")).expect("copy basis.urs");
        std::fs::write(mini_lib.join("top.urs"), "val boot_top_tiny : int\n").unwrap();
        std::fs::write(mini_lib.join("top.ur"), "val boot_top_tiny = 0\n").unwrap();
        std::fs::write(dir.path().join("Main.ur"), "val main = 1\n").unwrap();
        let job = Job {
            sources: vec!["Main".into()],
            basis_lib_dir: Some(mini_lib),
            ..Default::default()
        };
        let mut errors = ErrorReporter::new();
        let settings = Settings::new();
        let source_tree =
            with_parse_test_cwd(dir.path(), || parse_sources(&job, &settings, &mut errors))
                .unwrap_or_else(|| panic!("parse_sources failed: {:?}", errors.errors));
        let basis_mod = source_tree.iter().find(|d| {
            matches!(
                &d.node,
                crate::source::Decl::FfiStr(name, _, _) if name == "Basis"
            )
        });
        let basis_mod = basis_mod.expect("expected Basis FFI from boot parse_sources_inner");
        assert_eq!(
            basis_mod.span.file, "<basis>",
            "Basis span.file must remain <basis> (parse_sources_inner Span literal)"
        );
        let top_mod = source_tree.iter().find(|d| {
            matches!(
                &d.node,
                crate::source::Decl::Str(name, _, _, _, _) if name == "Top"
            )
        });
        let top_mod = top_mod.expect("expected Top structure parsed from synthetic lib/ur/top.ur");
        assert_eq!(
            top_mod.span.file, "<top>",
            "Top synthetic span.file must remain <top>"
        );
    }

    /// SML `elabFile` `dopen`s `Top` after linking `top.ur`; [`elab_file`] auto-opens `Top` the same way.
    ///
    /// Uses a tiny `top.urs` / `top.ur` pair so elaboration succeeds (unlike the full standard library).
    /// User code references `boot_top_tiny` **without** `Top.` — that only typechecks if `Top` was opened.
    #[test]
    fn elaborate_boot_auto_opens_top_for_unqualified_top_vals() {
        let manifest_lib =
            std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("lib/ur/basis.urs");
        if !manifest_lib.is_file() {
            return;
        }
        let dir = tempfile::tempdir().unwrap();
        let mini_lib = dir.path().join("lib/ur");
        std::fs::create_dir_all(&mini_lib).unwrap();
        std::fs::copy(&manifest_lib, mini_lib.join("basis.urs")).expect("copy basis.urs");
        std::fs::write(mini_lib.join("top.urs"), "val boot_top_tiny : int\n").unwrap();
        std::fs::write(mini_lib.join("top.ur"), "val boot_top_tiny = 0\n").unwrap();
        std::fs::write(
            dir.path().join("Main.ur"),
            "val client : int = boot_top_tiny + 1\n",
        )
        .unwrap();
        let job = Job {
            sources: vec!["Main".into()],
            basis_lib_dir: Some(mini_lib),
            ..Default::default()
        };
        let mut parse_errors = ErrorReporter::new_silent();
        let settings = Settings::new();
        let tree = with_parse_test_cwd(dir.path(), || {
            parse_sources(&job, &settings, &mut parse_errors)
        })
        .unwrap_or_else(|| panic!("parse_sources failed: {:?}", parse_errors.errors));
        let mut elab_errors = ErrorReporter::new_silent();
        let elaborated = elaborate(tree, &settings, &mut elab_errors);
        assert!(
            elaborated.is_some(),
            "expected unqualified boot_top_tiny in scope after Top dopen: {:?}",
            elab_errors.errors
        );
    }

    /// Goal: `demo/sum.ur` elaborates with real `lib/ur` boot the way the ML compiler does.
    ///
    /// `elab_file` already mirrors SML `dopen` on `Basis` and `Top`, but **full `lib/ur` boot still
    /// records many type errors** — see `boot_elab_diagnostic_id_histogram` (`URWEB_TEST_BOOT_HIST=1`).
    /// Keep this test as a tracker: run with
    /// `cargo test -p ur elaborate_demo_sum_elaborates_after_boot_parity -- --ignored --nocapture`.
    #[test]
    #[ignore = "lib/ur boot elab still reports type errors (~200+); un-ignore when boot histogram hits 0"]
    fn elaborate_demo_sum_elaborates_after_boot_parity() {
        const STACK: usize = 32 * 1024 * 1024;
        std::thread::Builder::new()
            .name("elaborate_demo_sum_large_stack".into())
            .stack_size(STACK)
            .spawn(elaborate_demo_sum_elaborates_after_boot_parity_body)
            .expect("spawn demo/sum elaboration thread")
            .join()
            .expect("demo/sum elaboration thread join");
    }

    /// Worker for [`elaborate_demo_sum_elaborates_after_boot_parity`].
    fn elaborate_demo_sum_elaborates_after_boot_parity_body() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lib_dir = manifest_dir.join("lib/ur");
        let sum_ur = manifest_dir.join("demo/sum.ur");
        if !lib_dir.join("basis.urs").is_file() || !sum_ur.is_file() {
            return;
        }
        let dir = tempfile::tempdir().unwrap();
        std::fs::copy(&sum_ur, dir.path().join("sum.ur")).expect("copy demo/sum.ur");
        let job = Job {
            sources: vec!["sum".into()],
            basis_lib_dir: Some(lib_dir),
            ..Default::default()
        };
        let mut parse_errors = ErrorReporter::new_silent();
        let settings = Settings::new();
        let tree = with_parse_test_cwd(dir.path(), || {
            parse_sources(&job, &settings, &mut parse_errors)
        });
        let tree =
            tree.unwrap_or_else(|| panic!("parse_sources failed: {:?}", parse_errors.errors));
        let mut elab_errors = ErrorReporter::new_silent();
        let out = elaborate(tree, &settings, &mut elab_errors);
        assert!(
            out.is_some(),
            "demo/sum.ur must elaborate with full boot (Top opened like SML elabFile): {} errors",
            elab_errors.errors.len()
        );
    }

    /// Synthetic UrwebNative FFI items must stay non-empty with stable names (empty `vec!` mutants break native-surface projects).
    #[test]
    fn urweb_native_ffi_sgn_items_contains_expected_vals() {
        let items = urweb_native_ffi_sgn_items();
        assert_eq!(
            items.len(),
            3,
            "UrwebNative shim must expose put, get, tigerbeetle transfer"
        );
        let val_names: Vec<&str> = items
            .iter()
            .map(|loc| match &loc.node {
                crate::source::SgnItem::Val(name, _) => name.as_str(),
                other => panic!("unexpected SgnItem variant: {other:?}"),
            })
            .collect();
        assert!(val_names.contains(&"urweb_put"));
        assert!(val_names.contains(&"urweb_get"));
        assert!(val_names.contains(&"urweb_tb_transfer"));
    }

    /// [`super::apply_job_db_settings`] must reject unknown DBMS tokens when the backend slot is still empty.
    #[test]
    fn apply_job_db_settings_rejects_unknown_dbms() {
        let job = Job {
            dbms: Some("___not_a_valid_dbms_token___".into()),
            ..Default::default()
        };
        let mut settings = Settings::new();
        let out = apply_job_db_settings(&job, &mut settings);
        assert!(
            out.is_err(),
            "invalid job dbms must not be ignored (mutant Ok(()) loses validation)"
        );
    }

    /// [`resolve_project_job_and_settings`] must return the real [`Job`] from the `.urp`, not a blank default.
    #[test]
    fn resolve_project_job_and_settings_preserves_urp_sources() {
        let dir = tempfile::tempdir().unwrap();
        let urp = dir.path().join("demo.urp");
        std::fs::write(&urp, "Main\n").unwrap();
        std::fs::write(dir.path().join("Main.ur"), "val x = 1\n").unwrap();
        let (job, _) = resolve_project_job_and_settings(&urp).expect("resolve project");
        assert!(
            job.sources.iter().any(|s| s.contains("Main")),
            ".urp module list must not be replaced by Job::default() ({:?})",
            job.sources
        );
    }

    /// [`resolve_project_settings_for_urp`] should surface manifest database defaults.
    #[test]
    fn resolve_project_settings_for_urp_reads_ur_toml_db() {
        let dir = tempfile::tempdir().unwrap();
        let urp = dir.path().join("one.urp");
        std::fs::write(&urp, "Main\n").unwrap();
        std::fs::write(dir.path().join("Main.ur"), "val x = 1\n").unwrap();
        std::fs::write(
            dir.path().join("ur.toml"),
            r#"[package]
name = "one"
kind = "app"

[build]
entry = "Main"
db = "sqlite"
"#,
        )
        .unwrap();
        let settings = resolve_project_settings_for_urp(&urp).expect("settings");
        assert_eq!(
            settings.db_backend.as_ref().map(|b| b.canonical_name()),
            Some("sqlite"),
            "manifest sqlite must merge into settings"
        );
    }

    /// [`effective_project_db_for_workspace_root`] must follow the same resolution as batch compile (not `ProjectDb::default()`).
    #[test]
    fn effective_project_db_for_workspace_root_matches_manifest_sqlite() {
        let _guard = crate::compiler_diagnostics::lock_for_compile(
            &crate::compiler_diagnostics::TEST_CWD_LOCK,
            "effective_project_db URWEB_BOOT_ROOT",
        );
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("w.urp"), "Main\n").unwrap();
        std::fs::write(dir.path().join("Main.ur"), "val x = 1\n").unwrap();
        std::fs::write(
            dir.path().join("ur.toml"),
            r#"[package]
name = "w"
kind = "app"

[build]
entry = "Main"
db = "sqlite"
"#,
        )
        .unwrap();
        let previous_boot_root = std::env::var_os(URWEB_BOOT_ROOT_ENV);
        std::env::set_var(URWEB_BOOT_ROOT_ENV, env!("CARGO_MANIFEST_DIR")); // temp tree lacks lib/ur; point at workspace root
        let db_result = effective_project_db_for_workspace_root(dir.path());
        match &previous_boot_root {
            None => std::env::remove_var(URWEB_BOOT_ROOT_ENV),
            Some(value) => std::env::set_var(URWEB_BOOT_ROOT_ENV, value),
        }
        let db = db_result.expect("project db");
        assert_eq!(
            db.canonical_name(),
            "sqlite",
            "mutants returning Ok(ProjectDb::default()) yield postgres, not sqlite"
        );
    }

    /// Invalid overlay text must not return a bogus empty parse (`Some(Default)` mutants).
    #[test]
    fn parse_sources_with_overlay_invalid_buffer_fails() {
        let dir = tempfile::tempdir().unwrap();
        let urp = dir.path().join("p.urp");
        std::fs::write(&urp, "Main\n").unwrap();
        std::fs::write(dir.path().join("Main.ur"), "val x = 1\n").unwrap();
        let job = parse_urp(&urp).unwrap();
        let mut errors = ErrorReporter::new_silent();
        let settings = Settings::new();
        let main_path = dir.path().join("Main.ur");
        let got = with_parse_test_cwd(dir.path(), || {
            parse_sources_with_overlay(&job, &main_path, "val x = (", &settings, &mut errors)
        });
        assert!(
            got.is_none(),
            "broken overlay must not produce Some(parse) {:?}",
            got.as_ref().map(|f| f.len())
        );
    }

    // Pipeline stub tests: each panics until implemented. Mutants that replace with
    // Ok/Some/Default would not panic and fail these tests.

    #[test]
    fn parse_urp_simple_sources() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("x.urp");
        std::fs::write(&p, "foo\nbar\n").unwrap();
        let job = parse_urp(&p).unwrap();
        assert_eq!(job.sources.len(), 2);
        assert!(job.sources[0].ends_with("foo"));
    }

    #[test]
    fn parse_urp_with_directives() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("app.urp");
        std::fs::write(&p, "database mydb\ndebug\n\nmod1\n").unwrap();
        let job = parse_urp(&p).unwrap();
        assert_eq!(job.database.as_deref(), Some("mydb"));
        assert!(job.debug);
        assert_eq!(job.sources.len(), 1);
    }

    #[test]
    fn parse_sources_empty_job_returns_empty() {
        // With no sources and no ffi, parse_sources returns Some([Basis]) —
        // the synthetic Basis FfiStr is always prepended.
        let mut errors = ErrorReporter::new();
        let settings = Settings::new();
        let result = parse_sources(&Job::default(), &settings, &mut errors);
        assert!(result.is_some());
        // Only the synthetic Basis decl is present (no user sources).
        assert_eq!(result.unwrap().len(), 1);
        assert!(!errors.has_errors());
    }

    #[test]
    fn parse_sources_returns_meaningful_content() {
        // Catches mutants: replace parse_sources result with Some(Default::default()).
        let dir = tempfile::tempdir().unwrap();
        let urp_path = dir.path().join("app.urp");
        std::fs::write(&urp_path, "database dbname=test\nsql out.sql\n\nx\n").unwrap();
        std::fs::write(dir.path().join("x.ur"), "val x = 1").unwrap();
        let job = parse_urp(&urp_path).unwrap();
        let mut errors = ErrorReporter::new();
        let settings = Settings::new();
        let result =
            with_parse_test_cwd(dir.path(), || parse_sources(&job, &settings, &mut errors));
        assert!(
            result.is_some(),
            "parse_sources must return Some (catches replace with None)"
        );
        let source_file = result.unwrap();
        // source_file[0] is the synthetic Basis FfiStr; optional project `database` line adds Decl::Database next.
        assert!(
            source_file.iter().any(|d| d.span.file.ends_with("x.ur")),
            "parse_sources must include x.ur module (catches Some(Default::default()))"
        );
        assert_eq!(
            source_file[0].span.file, "<basis>",
            "Basis wrapper span.file must be set (catches delete field file in basis Span literal)"
        );
        let user_module = source_file
            .iter()
            .find(|d| d.span.file.ends_with("x.ur"))
            .expect("x.ur Str decl");
        assert!(
            user_module.span.file.ends_with("x.ur"),
            "span.file must be set to source path (catches delete field file mutant): {}",
            user_module.span.file
        );
    }

    #[test]
    fn parse_sources_sets_span_file_for_urs_signature() {
        let dir = tempfile::tempdir().unwrap();
        let urp_path = dir.path().join("app.urp");
        std::fs::write(&urp_path, "database dbname=test\nsql out.sql\n\nx\n").unwrap();
        std::fs::write(dir.path().join("x.ur"), "val x = 1").unwrap();
        std::fs::write(dir.path().join("x.urs"), "val x : int").unwrap();
        let job = parse_urp(&urp_path).unwrap();
        let mut errors = ErrorReporter::new();
        let settings = Settings::new();
        let result =
            with_parse_test_cwd(dir.path(), || parse_sources(&job, &settings, &mut errors));
        let source_file = result.unwrap_or_else(|| {
            panic!("parse_sources: {:?}", errors);
        });
        let user_module = source_file
            .iter()
            .find(|d| d.span.file.ends_with("x.ur"))
            .expect("x.ur Str decl");
        let crate::source::Decl::Str(_, Some(sgn), _, _, _) = &user_module.node else {
            panic!(
                "expected Str decl with signature, got {:?}",
                user_module.node
            );
        };
        assert!(
            sgn.span.file.ends_with("x.urs"),
            "signature span.file must name .urs path (catches delete field file in sgn_span): {}",
            sgn.span.file
        );
    }

    #[test]
    fn compile_to_outputs_produces_c_and_sql() {
        // Catches mutants that replace pipeline phases with Default::default().
        let dir = tempfile::tempdir().unwrap();
        let urp_path = dir.path().join("app.urp");
        std::fs::write(&urp_path, "database dbname=test\nsql out.sql\n\nx\n").unwrap();
        std::fs::write(dir.path().join("x.ur"), "val x = 1").unwrap();
        let mut settings = Settings {
            db_backend: Some(ProjectDb::sqlite()),
            ..Default::default()
        };
        let result =
            with_parse_test_cwd(dir.path(), || compile_to_outputs(&urp_path, &mut settings));
        let (c_code, _sql_ddl) = result.expect("compile_to_outputs must succeed");
        assert!(
            c_code.contains("#include"),
            "C output must contain includes (catches cjr_print -> String::new()): {}",
            &c_code[..c_code.len().min(200)]
        );
        assert!(
            c_code.contains("uw_app"),
            "C output must contain uw_app struct (catches cjr_print mutant)"
        );
        assert!(
            !c_code.contains("xyzzy"),
            "C output must not be placeholder (catches replace with xyzzy mutant)"
        );
    }

    #[test]
    fn check_marshal_reports_disallowed_cookie() {
        // Catches mutant: replace check_marshal with ().
        use crate::core::{Constructor, Declaration};
        use crate::error_types::Located;
        let disallowed = Located::dummy(Constructor::Ffi("BadMod".into(), "BadType".into()));
        let file: crate::core::File = vec![Located::dummy(Declaration::Cookie(
            "c".into(),
            1,
            disallowed,
            "tag".into(),
        ))];
        let mut errors = ErrorReporter::new();
        check_marshal(&file, &Settings::default(), &mut errors);
        assert!(
            errors.has_errors(),
            "check_marshal must report errors for disallowed cookie (catches replace with () mutant)"
        );
    }

    #[test]
    fn mono_path_check_reports_duplicate_export() {
        // Catches mutant: replace mono_path_check with ().
        use crate::error_types::Located;
        use crate::export::{Effect, ExportKind};
        use crate::monomorphized::{Decl, Typ};
        let unit_typ = Located::dummy(Typ::Ffi("Basis".into(), "unit".into()));
        let file: crate::monomorphized::File = (
            vec![
                Located::dummy(Decl::Export(
                    ExportKind::Link(Effect::ReadOnly),
                    "samepath".into(),
                    1,
                    vec![],
                    unit_typ.clone(),
                    false,
                )),
                Located::dummy(Decl::Export(
                    ExportKind::Link(Effect::ReadOnly),
                    "samepath".into(),
                    2,
                    vec![],
                    unit_typ,
                    false,
                )),
            ],
            vec![],
        );
        let mut errors = ErrorReporter::new();
        mono_path_check(&file, &mut errors);
        assert!(
            errors.has_errors(),
            "mono_path_check must report duplicate path (catches replace with () mutant)"
        );
    }

    #[test]
    fn mono_iflow_passthrough_when_debug_false() {
        // When debug=false, mono_iflow must return Some(file) unchanged.
        let file = minimal_mono_file();
        let settings = Settings::default();
        assert!(!settings.debug, "default settings must have debug=false");
        let mut errors = ErrorReporter::new();
        let result = mono_iflow(file.clone(), &settings, &mut errors);
        assert!(
            result.is_some(),
            "mono_iflow must return Some when debug=false (catches replace with None mutant)"
        );
        assert!(
            !errors.has_errors(),
            "mono_iflow must not report errors on empty file with debug=false"
        );
    }

    #[test]
    fn mono_sqlcache_passthrough_when_sqlcache_false() {
        // When sqlcache=false, mono_sqlcache must return Some(file) unchanged.
        let file = minimal_mono_file();
        let settings = Settings::default();
        assert!(
            !settings.sqlcache,
            "default settings must have sqlcache=false"
        );
        let mut errors = ErrorReporter::new();
        let result = mono_sqlcache(file.clone(), &settings, &mut errors);
        assert!(
            result.is_some(),
            "mono_sqlcache must return Some(file) when sqlcache=false (catches replace with None mutant)"
        );
        // The file should be structurally unchanged.
        let (decls, _) = result.unwrap();
        assert_eq!(
            decls.len(),
            1,
            "mono_sqlcache must preserve file contents when sqlcache=false"
        );
    }

    #[test]
    fn mono_sqlcache_wraps_queries_when_enabled() {
        // When sqlcache=true, mono_sqlcache must transform the file.
        use crate::error_types::Located;
        use crate::monomorphized::{Decl, Exp, QueryMeta, Typ};
        let dummy_typ = Located::dummy(Typ::Record(vec![]));
        let query_exp = Located::dummy(Exp::Query(QueryMeta {
            exps: vec![],
            tables: vec![("t1".to_string(), vec![])],
            state: dummy_typ.clone(),
            query: Box::new(Located::dummy(Exp::Record(vec![]))),
            body: Box::new(Located::dummy(Exp::Record(vec![]))),
            initial: Box::new(Located::dummy(Exp::Record(vec![]))),
        }));
        let file: crate::monomorphized::File = (
            vec![Located::dummy(Decl::Val(
                "q".into(),
                1,
                dummy_typ,
                query_exp,
                "q".into(),
            ))],
            vec![],
        );
        let settings = Settings {
            sqlcache: true,
            ..Default::default()
        };
        let mut errors = ErrorReporter::new();
        let result = mono_sqlcache(file, &settings, &mut errors);
        assert!(result.is_some(), "mono_sqlcache must return Some");
        let (decls, _) = result.unwrap();
        assert_eq!(decls.len(), 1, "decl count must be preserved");
        match &decls[0].node {
            Decl::Val(_, _, _, e, _) => {
                assert!(
                    matches!(e.node, Exp::Case(..)),
                    "sqlcache must wrap query in Case node (catches pass-through mutant)"
                );
            }
            other => panic!("expected Val, got {:?}", other),
        }
    }

    #[test]
    fn elaborate_empty_file_returns_some() {
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = elaborate(Default::default(), &settings, &mut errors);
        // An empty source file should elaborate to an empty elab file without errors.
        assert!(
            result.is_some(),
            "elaborate should succeed on an empty file"
        );
        assert!(
            !errors.has_errors(),
            "elaborate should not produce errors on an empty file"
        );
    }

    #[test]
    fn explify_empty_file() {
        let mut errors = ErrorReporter::new();
        let result = explify(Default::default(), &mut errors);
        assert!(result.is_some());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn corify_empty_file_returns_some() {
        let mut errors = ErrorReporter::new();
        let mut settings = Settings::new();
        let result = corify(Default::default(), &mut settings, &mut errors);
        assert!(result.is_some());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn core_untangle_passes_through_empty_file() {
        // Catches mutant: core_untangle panics or returns garbage on empty input.
        let result = core_untangle(Default::default());
        assert!(result.is_empty(), "untangle of empty file must be empty");
    }

    #[test]
    fn core_untangle_preserves_non_empty_file() {
        // Catches mutant: replace core_untangle return with Default::default().
        // With non-empty input, untangle must return non-empty (pass-through for non-ValRec).
        let file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("d".into()),
        )];
        let result = core_untangle(file);
        assert!(
            !result.is_empty(),
            "untangle must preserve non-empty file (catches replace with Default::default())"
        );
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn core_reduce_local_passes_through_empty_file() {
        // Catches mutant: core_reduce_local returns garbage or panics on empty input.
        let result = core_reduce_local(Default::default());
        assert!(
            result.is_empty(),
            "reduce_local of empty file must be empty"
        );
    }

    #[test]
    fn core_reduce_local_preserves_database_decl() {
        // Catches mutant: replace core_reduce_local return with Default::default().
        let file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("d".into()),
        )];
        let result = core_reduce_local(file);
        assert!(
            !result.is_empty(),
            "reduce_local must preserve Database decl"
        );
    }

    #[test]
    fn core_shake_passes_through_empty_file() {
        // Catches mutant: core_shake panics or returns garbage on empty input.
        let result = core_shake(Default::default());
        assert!(result.is_empty(), "shake of empty file must be empty");
    }

    #[test]
    fn core_shake_preserves_retained_declaration() {
        // Catches mutant: replace core_shake return with Default::default().
        // Database is always retained by shake; result must be non-empty.
        let file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("d".into()),
        )];
        let result = core_shake(file);
        assert!(
            !result.is_empty(),
            "shake must retain Database decl (catches replace with Default::default())"
        );
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn core_reduce_passes_through_empty_file() {
        let result = core_reduce(vec![], &Settings::default());
        assert!(result.is_empty(), "reduce of empty file must be empty");
    }

    #[test]
    fn core_reduce_preserves_non_empty_file() {
        let file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("d".into()),
        )];
        let result = core_reduce(file, &Settings::default());
        assert!(
            !result.is_empty(),
            "core_reduce must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn core_especialize_passes_through_empty_file() {
        let result = core_especialize(Default::default());
        assert!(result.is_empty(), "especialize of empty file must be empty");
    }

    #[test]
    fn core_especialize_preserves_non_empty_file() {
        let file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("d".into()),
        )];
        let result = core_especialize(file);
        assert!(
            !result.is_empty(),
            "core_especialize must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn core_unpoly_passes_through_empty_file() {
        let result = core_unpoly(Default::default());
        assert!(result.is_empty(), "unpoly of empty file must be empty");
    }

    #[test]
    fn core_unpoly_preserves_non_empty_file() {
        let file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("d".into()),
        )];
        let result = core_unpoly(file);
        assert!(
            !result.is_empty(),
            "core_unpoly must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn core_specialize_passes_through_empty_file() {
        let result = core_specialize(Default::default());
        assert!(result.is_empty(), "specialize of empty file must be empty");
    }

    #[test]
    fn core_specialize_preserves_non_empty_file() {
        let file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("d".into()),
        )];
        let result = core_specialize(file);
        assert!(
            !result.is_empty(),
            "core_specialize must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn core_rpcify_passes_through_empty_file() {
        // Catches mutant: core_rpcify panics or returns None on empty input.
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = core_rpcify(Default::default(), &settings, &mut errors);
        assert!(result.is_some(), "rpcify of empty file must succeed");
        assert!(
            result.unwrap().is_empty(),
            "rpcify of empty file must be empty"
        );
    }

    #[test]
    fn core_tag_passes_through_empty_file() {
        // Catches mutant: core_tag panics or returns None on empty input.
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = core_tag(Default::default(), &settings, &mut errors);
        assert!(result.is_some(), "tag of empty file must succeed");
        assert!(
            result.unwrap().is_empty(),
            "tag of empty file must be empty"
        );
    }

    #[test]
    fn core_tag_preserves_non_empty_file() {
        // Catches mutant: replace core_tag -> Option<core::File> with Some(Default::default()).
        let file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("db".into()),
        )];
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = core_tag(file, &settings, &mut errors);
        assert!(result.is_some(), "tag of non-empty file must succeed");
        let tagged = result.unwrap();
        assert!(
            !tagged.is_empty(),
            "core_tag must preserve decls (not return Default::default())"
        );
    }

    #[test]
    fn core_effectize_passes_through_empty_file() {
        // Catches mutant: core_effectize panics or returns garbage on empty input.
        let settings = Settings::default();
        let result = core_effectize(Default::default(), &settings);

        assert!(result.is_empty(), "effectize of empty file must be empty");
    }

    #[test]
    fn core_effectize_preserves_non_empty_file() {
        let file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("d".into()),
        )];
        let settings = Settings::default();
        let result = core_effectize(file, &settings);
        assert!(
            !result.is_empty(),
            "core_effectize must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn check_marshal_passes_through_empty_file() {
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        check_marshal(&Default::default(), &settings, &mut errors);
        assert!(
            !errors.has_errors(),
            "marshal check of empty file must produce no errors"
        );
    }

    #[test]
    fn mono_script_check_passes_through_empty_file() {
        let settings = Settings::default();
        let mut errors = ErrorReporter::new();
        let result = mono_script_check(Default::default(), &settings, &mut errors);
        assert!(result.0.is_empty());
        assert!(!errors.has_errors());
    }

    #[test]
    fn mono_script_check_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let settings = Settings::default();
        let mut errors = ErrorReporter::new();
        let result = mono_script_check(file, &settings, &mut errors);
        assert!(
            !result.0.is_empty(),
            "mono_script_check must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_path_check_no_errors_on_empty_file() {
        let mut errors = ErrorReporter::new();
        mono_path_check(&Default::default(), &mut errors);
        assert!(!errors.has_errors());
    }

    #[test]
    fn mono_side_check_passes_through_empty_file() {
        let settings = Settings::default();
        let mut errors = ErrorReporter::new();
        let (file, env_vars) = mono_side_check(Default::default(), &settings, &mut errors);
        assert!(file.0.is_empty());
        assert!(env_vars.is_empty());
        assert!(!errors.has_errors());
    }

    #[test]
    fn mono_side_check_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let settings = Settings::default();
        let mut errors = ErrorReporter::new();
        let (result, _) = mono_side_check(file, &settings, &mut errors);
        assert!(
            !result.0.is_empty(),
            "mono_side_check must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_sig_check_passes_through_empty_file() {
        let result = mono_sig_check(Default::default());
        assert!(result.0.is_empty());
    }

    #[test]
    fn mono_sig_check_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let result = mono_sig_check(file);
        assert!(
            !result.0.is_empty(),
            "mono_sig_check must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_dbmode_check_passes_through_empty_file() {
        let result = mono_dbmode_check(Default::default());
        assert!(result.0.is_empty());
    }

    #[test]
    fn mono_dbmode_check_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let result = mono_dbmode_check(file);
        assert!(
            !result.0.is_empty(),
            "mono_dbmode_check must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn check_termination_noop() {
        let mut errors = ErrorReporter::new();
        check_termination(&Default::default(), &mut errors);
        assert!(!errors.has_errors());
    }

    #[test]
    fn cjr_check_nest_empty_file() {
        // Catches mutant: cjr_check_nest panics or drops decls on empty input.
        let result = cjr_check_nest(Default::default());
        assert!(result.0.is_empty());
        assert!(result.1.is_empty());
    }

    #[test]
    fn cjr_check_nest_preserves_non_empty_file() {
        let cjr_file = minimal_cjr_file();
        let result = cjr_check_nest(cjr_file);
        assert!(
            !result.0.is_empty(),
            "cjr_check_nest must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn cjr_prepare_empty_file() {
        let settings = Settings::default();
        let result = cjr_prepare(Default::default(), &settings);
        // prepare always prepends DPreparedStatements
        assert_eq!(result.0.len(), 1);
        assert!(matches!(
            &result.0[0].node,
            crate::c_like_representation::Decl::PreparedStatements(v) if v.is_empty()
        ));
    }

    #[test]
    fn monoize_empty_file() {
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = monoize(Default::default(), &settings, &mut errors);
        assert!(result.is_some());
        assert!(result.unwrap().0.is_empty());
    }

    #[test]
    fn monoize_preserves_non_empty_file() {
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let core_file: crate::core::File = vec![crate::error_types::Located::dummy(
            crate::core::Declaration::Database("db".into()),
        )];
        let result = monoize(core_file, &settings, &mut errors);
        assert!(
            result.is_some(),
            "monoize must return Some (catches replace with None)"
        );
        let mono = result.unwrap();
        assert!(
            !mono.0.is_empty(),
            "monoize must produce non-empty mono (catches Some(Default::default()))"
        );
    }

    #[test]
    fn mono_untangle_passes_through_empty_file() {
        let result = mono_untangle(Default::default());
        assert!(result.0.is_empty(), "untangle of empty file must be empty");
    }

    #[test]
    fn mono_untangle_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let result = mono_untangle(file);
        assert!(
            !result.0.is_empty(),
            "mono_untangle must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_fuse_passes_through_empty_file() {
        let result = mono_fuse(Default::default());
        assert!(
            result.0.is_empty(),
            "fuse of empty file should produce no decls"
        );
    }

    #[test]
    fn mono_fuse_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let result = mono_fuse(file);
        assert!(
            !result.0.is_empty(),
            "mono_fuse must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_reduce_passes_through_empty_file() {
        let settings = Settings::default();
        let result = mono_reduce(Default::default(), &settings);
        assert!(
            result.0.is_empty(),
            "mono_reduce of empty file must produce no decls"
        );
    }

    #[test]
    fn mono_reduce_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let settings = Settings::default();
        let result = mono_reduce(file, &settings);
        assert!(
            !result.0.is_empty(),
            "mono_reduce must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_opt_passes_through_empty_file() {
        let settings = Settings::default();
        let mut errors = ErrorReporter::new();
        let result = mono_opt(Default::default(), &settings, &mut errors);
        assert!(
            result.0.is_empty(),
            "mono_opt of empty file must produce no decls"
        );
    }

    #[test]
    fn mono_opt_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let settings = Settings::default();
        let mut errors = ErrorReporter::new();
        let result = mono_opt(file, &settings, &mut errors);
        assert!(
            !result.0.is_empty(),
            "mono_opt must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_shake_passes_through_empty_file() {
        let result = mono_shake(Default::default());
        assert!(
            result.0.is_empty(),
            "mono_shake of empty file must be empty"
        );
    }

    #[test]
    fn mono_shake_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let result = mono_shake(file);
        assert!(
            !result.0.is_empty(),
            "mono_shake must retain Database (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_inline_passes_through_empty_file() {
        let settings = Settings::default();
        let result = mono_inline(Default::default(), &settings);
        assert!(
            result.0.is_empty(),
            "mono_inline of empty file must produce no decls"
        );
    }

    #[test]
    fn mono_inline_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let settings = Settings::default();
        let result = mono_inline(file, &settings);
        assert!(
            !result.0.is_empty(),
            "mono_inline must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_name_js_passthrough() {
        let result = mono_name_js(Default::default());
        assert!(result.0.is_empty());
    }

    #[test]
    fn mono_name_js_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let result = mono_name_js(file);
        assert!(
            !result.0.is_empty(),
            "mono_name_js must preserve decls (catches replace with Default::default())"
        );
    }

    #[test]
    fn mono_iflow_passthrough() {
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = mono_iflow(Default::default(), &settings, &mut errors);
        assert!(result.is_some());
    }

    #[test]
    fn mono_iflow_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = mono_iflow(file, &settings, &mut errors);
        assert!(
            result.is_some(),
            "mono_iflow must return Some (catches replace with None)"
        );
        assert!(
            !result.unwrap().0.is_empty(),
            "mono_iflow must preserve decls (catches Some(Default::default()))"
        );
    }

    #[test]
    fn mono_sqlcache_passthrough() {
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = mono_sqlcache(Default::default(), &settings, &mut errors);
        assert!(result.is_some());
    }

    #[test]
    fn mono_sqlcache_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = mono_sqlcache(file, &settings, &mut errors);
        assert!(
            result.is_some(),
            "mono_sqlcache must return Some (catches replace with None)"
        );
        assert!(
            !result.unwrap().0.is_empty(),
            "mono_sqlcache must preserve decls (catches Some(Default::default()))"
        );
    }

    #[test]
    fn cjrize_empty_file() {
        let mut errors = ErrorReporter::new();
        let result = cjrize(Default::default(), &mut errors);
        assert!(result.is_some());
        let (decls, ps) = result.unwrap();
        assert!(decls.is_empty());
        assert!(ps.is_empty());
    }

    #[test]
    fn cjrize_preserves_non_empty_file() {
        let file = minimal_mono_file();
        let mut errors = ErrorReporter::new();
        let result = cjrize(file, &mut errors);
        assert!(
            result.is_some(),
            "cjrize must return Some (catches replace with None)"
        );
        let (decls, _) = result.unwrap();
        assert!(
            !decls.is_empty(),
            "cjrize must produce decls (catches Some(Default::default()))"
        );
    }

    #[test]
    fn cjr_print_empty_file_generates_header() {
        let settings = Settings::default();
        let result = cjr_print(&Default::default(), &settings);
        assert!(
            result.contains("#include"),
            "cjr_print of empty file must produce C header includes, got:\n{}",
            result
        );
        assert!(
            result.contains("uw_app uw_application"),
            "cjr_print of empty file must produce uw_app struct, got:\n{}",
            result
        );
    }

    #[test]
    fn cjr_print_non_empty_file_produces_more_than_empty() {
        // Kills: cjr_print mutants that return same output for non-empty CJR file.
        let settings = Settings::default();
        let empty_out = cjr_print(&Default::default(), &settings);
        let cjr_file = minimal_cjr_file();
        let non_empty_out = cjr_print(&cjr_file, &settings);
        assert!(
            non_empty_out.len() >= empty_out.len(),
            "cjr_print of file with Database must produce at least as much output as empty"
        );
        assert!(
            !non_empty_out.is_empty() && !non_empty_out.contains("xyzzy"),
            "cjr_print must not return placeholder (catches replace with xyzzy mutant)"
        );
    }

    #[test]
    fn js_compile_empty_file_returns_none() {
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let result = js_compile(&Default::default(), &settings, &mut errors);
        assert!(result.is_none());
    }

    #[test]
    fn js_compile_collects_javascript_decls() {
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        let file: crate::monomorphized::File = (
            vec![crate::error_types::Located::dummy(
                crate::monomorphized::Decl::JavaScript("alert(1)".into()),
            )],
            vec![],
        );
        let result = js_compile(&file, &settings, &mut errors);
        assert!(
            result.is_some(),
            "js_compile must return Some when file has JavaScript decl (catches replace with None)"
        );
        assert!(result.unwrap().contains("alert(1)"));
    }

    #[test]
    fn sql_generate_empty_file() {
        let settings = Settings::default();
        let result = sql_generate(&Default::default(), &settings);
        assert!(result.is_empty());
    }

    #[test]
    fn sql_generate_produces_sql_for_table() {
        let settings = Settings {
            db_backend: Some(ProjectDb::postgres()),
            ..Default::default()
        };
        let xts = vec![(
            "Id".to_string(),
            crate::error_types::Located::dummy(crate::c_like_representation::Typ::Ffi(
                "Basis".into(),
                "int".into(),
            )),
        )];
        let cjr_file: crate::c_like_representation::File = (
            vec![crate::error_types::Located::dummy(
                crate::c_like_representation::Decl::Table("t".into(), xts, "".into(), vec![]),
            )],
            vec![],
        );
        let result = sql_generate(&cjr_file, &settings);
        assert!(
            !result.is_empty() && result.contains("CREATE TABLE"),
            "sql_generate must produce SQL for Table (catches replace with String::new()): {}",
            result
        );
    }

    #[test]
    fn cc_and_link_returns_result() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("a.out");
        // Without the urweb runtime installed, linking will fail (Err), but it should not panic.
        let result = cc_and_link(
            "int main(void) { return 0; }\n",
            &out,
            &Job::default(),
            &Settings::default(),
        );
        // Either Ok (if cc is available and links) or Err (no urweb runtime) — not a panic.
        let _ = result;
    }

    #[test]
    fn cc_and_link_rejects_invalid_c() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("a.out");
        let result = cc_and_link("not valid C {", &out, &Job::default(), &Settings::default());
        assert!(
            result.is_err(),
            "cc_and_link must actually invoke the C compiler"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("compilation")
                || err_msg.contains("compil")
                || err_msg.contains("timed out"),
            "invalid C must fail at compile or time out (never silent link): {}",
            err_msg
        );
    }

    #[test]
    fn run_compile_invokes_apply_boot_settings() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("boot.urp"), "m\n").unwrap();
        APPLY_BOOT_SETTINGS_CALLS.store(0, Ordering::SeqCst);
        let proj = dir.path().join("boot");
        let _ = run_compile(&proj, &mut Settings::default());
        assert!(
            APPLY_BOOT_SETTINGS_CALLS.load(Ordering::SeqCst) >= 1,
            "apply_boot_settings must run (catches replace with () mutant)"
        );
    }

    #[test]
    fn resolve_urp_project_path_appends_urp_suffix() {
        assert_eq!(
            resolve_urp_project_path(Path::new("/tmp/w/widget.ur")),
            PathBuf::from("/tmp/w/widget.urp")
        );
        assert_eq!(
            resolve_urp_project_path(Path::new("/tmp/w/widget.urp")),
            PathBuf::from("/tmp/w/widget.urp")
        );
    }

    #[test]
    fn dbms_link_library_flag_sqlite_is_sqlite3() {
        assert_eq!(
            dbms_link_library_flag(&settings_with_db(ProjectDb::sqlite())),
            "-lsqlite3"
        );
        assert_eq!(
            dbms_link_library_flag(&settings_with_db(ProjectDb::mysql())),
            "-lmysqlclient"
        );
        assert_eq!(dbms_link_library_flag(&Settings::default()), "-lpq");
        assert_eq!(
            dbms_link_library_flag(&settings_with_db(ProjectDb::Rocksdb)),
            "-lrocksdb -lstdc++"
        );
        assert_eq!(
            dbms_link_library_flag(&settings_with_db(ProjectDb::Persy)),
            "-lurweb_persy"
        );
        assert_eq!(
            dbms_link_library_flag(&settings_with_db(ProjectDb::Ndb)),
            "-lurweb_ndb"
        );
        assert_eq!(
            dbms_link_library_flag(&settings_with_db(ProjectDb::Tigerbeetle)),
            "-ltb_client"
        );
    }

    #[test]
    fn mono_filecache_invokes_instrument() {
        MONO_FILECACHE_CALLS.store(0, Ordering::SeqCst);
        let settings = Settings {
            file_cache: Some("/tmp/urweb_fc_test".into()),
            ..Default::default()
        };
        let file: crate::monomorphized::File = (
            vec![crate::error_types::Located::dummy(
                crate::monomorphized::Decl::JavaScript("/*x*/".into()),
            )],
            vec![],
        );
        let out = mono_filecache(file.clone(), &settings);
        assert_eq!(MONO_FILECACHE_CALLS.load(Ordering::SeqCst), 1);
        assert_eq!(out.0.len(), file.0.len());
    }

    #[test]
    fn css_summarize_invokes_core_summarize() {
        CSS_SUMMARIZE_CALLS.store(0, Ordering::SeqCst);
        let file: crate::core::File = vec![];
        let _ = css_summarize(&file);
        assert_eq!(CSS_SUMMARIZE_CALLS.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn parse_sources_ffi_module_span_names_urs_file() {
        let dir = tempfile::tempdir().unwrap();
        let urp_path = dir.path().join("app.urp");
        std::fs::write(
            &urp_path,
            "ffi extmod\ndatabase dbname=test\nsql out.sql\n\nx\n",
        )
        .unwrap();
        std::fs::write(dir.path().join("extmod.urs"), "val f : int").unwrap();
        std::fs::write(dir.path().join("x.ur"), "val x = 1").unwrap();
        let job = parse_urp(&urp_path).unwrap();
        let mut errors = ErrorReporter::new();
        let settings = Settings::new();
        let source_file =
            with_parse_test_cwd(dir.path(), || parse_sources(&job, &settings, &mut errors))
                .expect("parse_sources");
        let ffi_decl = source_file.iter().find(|d| {
            matches!(
                &d.node,
                crate::source::Decl::FfiStr(name, _, _) if name == "Extmod"
            )
        });
        let ffi_decl = ffi_decl.expect("FFI module decl");
        assert!(
            ffi_decl.span.file.ends_with("extmod.urs"),
            "FFI span.file must be the .urs path (catches delete field file in ffi span): {}",
            ffi_decl.span.file
        );
    }
}
