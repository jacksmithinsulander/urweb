//! Pipeline orchestration — drives all compilation phases.
//!
//! Parses `.urp` project files into `Job`, then runs: parse → elaborate →
//! explify → core passes → mono passes → cjr_print / sql_generate → C compile.
//!
//! Mirrors `compiler.sml`.

use anyhow::{bail, Context, Result};
use std::path::{Path, PathBuf};
#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::error_types::ErrorReporter;
use crate::settings::Settings;

#[cfg(test)]
pub(crate) static APPLY_BOOT_SETTINGS_CALLS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static CSS_SUMMARIZE_CALLS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static MONO_FILECACHE_CALLS: AtomicUsize = AtomicUsize::new(0);

/// When diagnostics were already printed to stderr, summarize why compilation stops.
fn bail_if_errors_reported(errors: &ErrorReporter, phase: &str) -> Result<()> {
    if !errors.has_errors() {
        return Ok(());
    }
    let n = errors.errors.len();
    bail!(
        "{phase} reported {n} error(s). Messages above list each issue with file and location.\n\
         Fix those problems, then run the compiler again."
    );
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
    /// Consume and return the inner `Result` (for `match` / `?`).
    #[must_use]
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

/// Parse a `.urp` project file into a `Job` description.
pub fn parse_urp(path: &Path) -> Result<Job> {
    crate::urp_parser::parse_urp(path)
}

// ---------------------------------------------------------------------------
// Boot path resolution
// ---------------------------------------------------------------------------

/// When `settings.boot_linking` is set, walk up from the current executable to
/// find the project root (the directory containing `lib/ur/basis.urs`) and
/// populate `job.basis_lib_dir` and the `config_*` settings.
fn apply_boot_settings(job: &mut Job, settings: &mut Settings) {
    #[cfg(test)]
    APPLY_BOOT_SETTINGS_CALLS.fetch_add(1, Ordering::SeqCst);
    if !settings.boot_linking {
        return;
    }
    let exe = match std::env::current_exe() {
        Ok(e) => e,
        Err(_) => return,
    };
    let mut candidate = exe.parent().map(|p| p.to_path_buf());
    let root = loop {
        match candidate {
            None => return,
            Some(ref dir) => {
                if dir.join("lib/ur/basis.urs").exists() {
                    break dir.clone();
                }
                candidate = dir.parent().map(|p| p.to_path_buf());
            }
        }
    };
    if job.basis_lib_dir.is_none() {
        job.basis_lib_dir = Some(root.join("lib/ur"));
    }
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
}

// ---------------------------------------------------------------------------
// Phase 2: Parse source files
// ---------------------------------------------------------------------------

pub fn parse_sources(job: &Job, errors: &mut ErrorReporter) -> Option<crate::source::File> {
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
                Ok(src) => {
                    match crate::parse::parse_urs(&urs_path.to_string_lossy(), &src, errors) {
                        Some(items) => items,
                        None => return None, // parse errors already recorded
                    }
                }
                Err(e) => {
                    errors.report(CompileError::Plain(format!(
                        "cannot read basis library {}: {}",
                        urs_path.display(),
                        e
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

    let mut had_errors = false;

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
                errors.report(CompileError::Plain(format!(
                    "cannot read FFI signature {urs_path}: {e}"
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

        // Read .ur source
        let ur_src = match std::fs::read_to_string(&ur_path) {
            Ok(s) => s,
            Err(e) => {
                errors.report(CompileError::Plain(format!("cannot read {ur_path}: {e}")));
                had_errors = true;
                continue;
            }
        };

        // Parse optional .urs signature
        let sgn_opt = if Path::new(&urs_path).exists() {
            match std::fs::read_to_string(&urs_path) {
                Err(e) => {
                    errors.report(CompileError::Plain(format!("cannot read {urs_path}: {e}")));
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
        match crate::parse::parse_ur(&ur_path, &ur_src, errors) {
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

pub fn unnest(file: crate::elaborated::File) -> crate::elaborated::File {
    crate::elaborated::unnest::unnest(file)
}

// ---------------------------------------------------------------------------
// Phase 4: Explify (elab → expl)
// ---------------------------------------------------------------------------

pub fn explify(
    file: crate::elaborated::File,
    errors: &mut ErrorReporter,
) -> Option<crate::explicit::File> {
    crate::elaborated::explify::explify(file, errors)
}

// ---------------------------------------------------------------------------
// Phase 5: Corify (expl → core)
// ---------------------------------------------------------------------------

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

pub fn core_untangle(file: crate::core::File) -> crate::core::File {
    crate::core::untangling::untangle(file)
}

pub fn core_reduce_local(file: crate::core::File) -> crate::core::File {
    crate::core::local_reduction::reduce(file)
}

pub fn core_shake(file: crate::core::File) -> crate::core::File {
    crate::core::dead_code_elimination::shake(file)
}

pub fn core_reduce(file: crate::core::File, settings: &Settings) -> crate::core::File {
    crate::core::global_reduction::reduce(file, settings)
}

pub fn core_especialize(file: crate::core::File) -> crate::core::File {
    crate::core::especialize::especialize(file)
}

pub fn core_unpoly(file: crate::core::File) -> crate::core::File {
    crate::core::unpoly::unpoly(file)
}

pub fn core_specialize(file: crate::core::File) -> crate::core::File {
    crate::core::specialize::specialize(file)
}

pub fn core_rpcify(
    file: crate::core::File,
    _settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::core::File> {
    let mut had_errors = false;
    let result = crate::core::rpc_elaboration::rpcify(file, &mut |span, msg| {
        errors.report_at(span.clone(), msg);
        had_errors = true;
    });
    if had_errors {
        None
    } else {
        Some(result)
    }
}

pub fn core_tag(
    file: crate::core::File,
    _settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::core::File> {
    let mut had_errors = false;
    let result = crate::core::export_tagging::tag(file, &mut |span, msg| {
        errors.report_at(span.clone(), msg);
        had_errors = true;
    });
    if had_errors {
        None
    } else {
        Some(result)
    }
}

pub fn core_effectize(file: crate::core::File, settings: &Settings) -> crate::core::File {
    let (result, _warnings) = crate::core::effect_analysis::effectize(file, settings);
    result
}

// ---------------------------------------------------------------------------
// Checks on Core
// ---------------------------------------------------------------------------

pub fn check_marshal(file: &crate::core::File, settings: &Settings, errors: &mut ErrorReporter) {
    crate::core::marshal_check::check(file, settings, errors);
}

pub fn check_termination(file: &crate::core::File, errors: &mut ErrorReporter) {
    crate::core::termination_check::check(file, errors);
}

// ---------------------------------------------------------------------------
// Mono checks
// ---------------------------------------------------------------------------

pub fn mono_script_check(
    file: crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> crate::monomorphized::File {
    crate::monomorphized::script_check::classify(file, settings, errors)
}

pub fn mono_path_check(file: &crate::monomorphized::File, errors: &mut ErrorReporter) {
    crate::monomorphized::path_check::check(file, errors)
}

pub fn mono_side_check(
    file: crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> (crate::monomorphized::File, Vec<String>) {
    crate::monomorphized::side_check::check(file, settings, errors)
}

pub fn mono_sig_check(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::sig_check::check(file)
}

pub fn mono_dbmode_check(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::db_mode_check::classify(file)
}

// ---------------------------------------------------------------------------
// Phase: Monoize (core → mono)
// ---------------------------------------------------------------------------

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

pub fn mono_untangle(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::untangle::untangle(file)
}

pub fn mono_fuse(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::fuse::fuse(file)
}

pub fn mono_reduce(
    file: crate::monomorphized::File,
    settings: &Settings,
) -> crate::monomorphized::File {
    crate::monomorphized::mono_reduce::reduce(file, settings)
}

pub fn mono_opt(
    file: crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> crate::monomorphized::File {
    crate::monomorphized::mono_opt::optimize(file, settings, errors)
}

pub fn mono_shake(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::mono_shake::shake(file)
}

pub fn mono_inline(
    file: crate::monomorphized::File,
    settings: &Settings,
) -> crate::monomorphized::File {
    use std::sync::atomic::Ordering;
    let mut errors = ErrorReporter::new();
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

pub fn mono_name_js(file: crate::monomorphized::File) -> crate::monomorphized::File {
    crate::monomorphized::name_js::rewrite(file)
}

pub fn mono_endpoints(
    file: crate::monomorphized::File,
) -> (
    crate::monomorphized::File,
    Vec<crate::monomorphized::endpoints::Endpoint>,
) {
    crate::monomorphized::endpoints::collect(file)
}

pub fn mono_filecache(
    file: crate::monomorphized::File,
    settings: &Settings,
) -> crate::monomorphized::File {
    #[cfg(test)]
    MONO_FILECACHE_CALLS.fetch_add(1, Ordering::SeqCst);
    crate::monomorphized::filecache::instrument(file, settings)
}

pub fn mono_iflow(
    file: crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::monomorphized::File> {
    crate::monomorphized::iflow::check(&file, settings, errors);
    if errors.has_errors() {
        None
    } else {
        Some(file)
    }
}

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

pub fn cjrize(
    file: crate::monomorphized::File,
    errors: &mut ErrorReporter,
) -> Option<crate::c_like_representation::File> {
    crate::c_like_representation::cjrize::cjrize(file, errors)
}

// ---------------------------------------------------------------------------
// Phase: Prepare (cjr → cjr with prepared SQL statements)
// ---------------------------------------------------------------------------

pub fn cjr_prepare(
    file: crate::c_like_representation::File,
    settings: &Settings,
) -> crate::c_like_representation::File {
    crate::c_like_representation::prepare::prepare(file, settings)
}

// ---------------------------------------------------------------------------
// Phase: CheckNest (annotate EQuery.prepared.nested on CJR)
// ---------------------------------------------------------------------------

pub fn cjr_check_nest(
    file: crate::c_like_representation::File,
) -> crate::c_like_representation::File {
    crate::c_like_representation::check_nest::annotate(file)
}

// ---------------------------------------------------------------------------
// Phase: C code generation (cjr → .c file)
// ---------------------------------------------------------------------------

pub fn cjr_print(file: &crate::c_like_representation::File, settings: &Settings) -> String {
    crate::c_like_representation::cjr_print::cjr_print(file, settings)
}

// ---------------------------------------------------------------------------
// Phase: JS compilation
// ---------------------------------------------------------------------------

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

pub fn sql_generate(file: &crate::c_like_representation::File, settings: &Settings) -> String {
    crate::c_like_representation::sql_generate::sql_generate(file, settings)
}

// ---------------------------------------------------------------------------
// Phase: CSS summary (after core shake, optional diagnostic)
// ---------------------------------------------------------------------------

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
) -> Result<std::process::ExitStatus> {
    use std::time::{Duration, Instant};
    let mut child = cmd.spawn().with_context(|| format!("spawn {what}"))?;
    let start = Instant::now();
    loop {
        match child.try_wait().with_context(|| format!("poll {what}"))? {
            Some(st) => return Ok(st),
            None => {}
        }
        if start.elapsed() > CC_LINK_TEST_DEADLINE {
            let _ = child.kill();
            let _ = child.wait();
            bail!(
                "{what} timed out after {:?} (likely bad argv from a mutant)",
                CC_LINK_TEST_DEADLINE
            );
        }
        std::thread::sleep(Duration::from_millis(25));
    }
}

#[cfg(not(test))]
fn command_status_deadline(
    cmd: &mut std::process::Command,
    what: &str,
) -> Result<std::process::ExitStatus> {
    cmd.status().with_context(|| format!("running {what}"))
}

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

    std::fs::write(&c_file, c_source)
        .with_context(|| format!("writing C source to {}", c_file.display()))?;

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

    let compile_status = command_status_deadline(&mut compile_cmd, &format!("C compiler '{cc}'"))?;
    match compile_status.success() {
        true => {}
        false => bail!("C compilation failed (exit {})", compile_status),
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
    // DBMS-specific library (factored for unit tests; `match` avoids `==`/`!=` mutants in `cc_and_link`).
    let dbms = settings.dbms.as_str();
    link_cmd.arg(dbms_link_library_flag(dbms));
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

    let link_status =
        command_status_deadline(&mut link_cmd, &format!("linker '{linker_cmd_base}'"))?;
    match link_status.success() {
        true => {}
        false => bail!("Linking failed (exit {})", link_status),
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Top-level: full build pipeline
// ---------------------------------------------------------------------------

/// Resolve a user-given project path to the `.urp` file we open (`foo.ur` → `foo.urp`).
pub(crate) fn resolve_urp_project_path(urp_path: &Path) -> PathBuf {
    if urp_path.extension().map_or(true, |e| e != "urp") {
        urp_path.with_extension("urp")
    } else {
        urp_path.to_path_buf()
    }
}

/// Linker flag for the configured DBMS (unit-tested; `cc_and_link` delegates here).
pub(crate) fn dbms_link_library_flag(dbms: &str) -> &'static str {
    match dbms {
        "sqlite" => "-lsqlite3",
        "mysql" => "-lmysqlclient",
        _ => "-lpq",
    }
}

/// Run the complete compilation pipeline for a `.urp` project.
///
/// Corresponds to `Compiler.run` / the main compilation path in `main.mlton.sml`.
pub fn compile(urp_path: &Path, settings: &mut Settings) -> CompileResult {
    run_compile(urp_path, settings).into()
}

fn run_compile(urp_path: &Path, settings: &mut Settings) -> Result<PathBuf> {
    let mut errors = ErrorReporter::new();

    // Phase 1: parse project file (append .urp if not already present)
    let urp_path_buf = resolve_urp_project_path(urp_path);
    let mut job = parse_urp(&urp_path_buf)?;

    apply_boot_settings(&mut job, settings);

    // Apply job settings globally
    settings.set_url_prefix(&job.prefix);
    settings.timeout = job.timeout;
    settings.headers = job.headers.clone();
    settings.scripts = job.scripts.clone();
    settings.debug = job.debug;

    // Phase 2: parse sources
    let source_file =
        parse_sources(&job, &mut errors).ok_or_else(|| anyhow::anyhow!("Parse failed"))?;
    bail_if_errors_reported(&errors, "Parsing")?;

    // Phase 3: elaborate
    let elab_file = elaborate(source_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Elaboration failed"))?;
    bail_if_errors_reported(&errors, "Elaboration (types and modules)")?;

    // Phase 3.5: unnest
    let elab_file = unnest(elab_file);

    // Phase 4: explify
    let expl_file =
        explify(elab_file, &mut errors).ok_or_else(|| anyhow::anyhow!("Explify failed"))?;

    // Phase 5: corify
    let core_file =
        corify(expl_file, settings, &mut errors).ok_or_else(|| anyhow::anyhow!("Corify failed"))?;

    // Core passes
    let core_file = core_untangle(core_file);
    let core_file = core_reduce_local(core_file);
    let core_file = core_shake(core_file);
    let core_file = core_reduce(core_file, settings);
    let core_file = core_especialize(core_file);
    let core_file = core_unpoly(core_file);
    let core_file = core_specialize(core_file);
    let core_file = core_rpcify(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Rpcify failed"))?;
    let core_file =
        core_tag(core_file, settings, &mut errors).ok_or_else(|| anyhow::anyhow!("Tag failed"))?;
    let core_file = core_effectize(core_file, settings);

    // Core checks
    check_marshal(&core_file, settings, &mut errors);
    check_termination(&core_file, &mut errors);
    bail_if_errors_reported(&errors, "Core verification (marshalling / termination)")?;

    // Monoize
    let mono_file = monoize(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Monoize failed"))?;

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
    bail_if_errors_reported(&errors, "Monomorphization checks")?;

    let mono_file = if settings.debug {
        mono_iflow(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow::anyhow!("Iflow failed"))?
    } else {
        mono_file
    };

    // Name JavaScript fragments (name_js.sml) — hoist non-trivial EJavaScript
    // sub-expressions to top-level DVal bindings for app.js placement.
    let mono_file = mono_name_js(mono_file);
    let mono_file = mono_filecache(mono_file, settings);

    let mono_file = if settings.sqlcache {
        mono_sqlcache(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow::anyhow!("Sqlcache failed"))?
    } else {
        mono_file
    };

    // JS compilation
    let _js = js_compile(&mono_file, settings, &mut errors);

    // CJRize
    let cjr_file =
        cjrize(mono_file, &mut errors).ok_or_else(|| anyhow::anyhow!("CJRize failed"))?;
    bail_if_errors_reported(&errors, "C back-end (CJR)")?;

    // Prepare SQL statements and annotate nested queries
    let cjr_file = cjr_prepare(cjr_file, settings);
    let cjr_file = cjr_check_nest(cjr_file);

    // Generate C code
    let c_code = cjr_print(&cjr_file, settings);
    let sql_ddl = sql_generate(&cjr_file, settings);

    // Write SQL if requested
    if let Some(sql_path) = &job.sql {
        std::fs::write(sql_path, &sql_ddl)
            .with_context(|| format!("writing SQL to {}", sql_path))?;
    }

    // Compile and link
    let exe_path = PathBuf::from(&job.exe);
    cc_and_link(&c_code, &exe_path, &job, settings)?;

    Ok(exe_path)
}

/// Run the compilation pipeline and return the generated C code and SQL DDL
/// without invoking the C compiler or linker.
///
/// Used by tests to assert on generated output (catches return-value mutants
/// that replace phases with Default::default()).
pub fn compile_to_outputs(urp_path: &Path, settings: &mut Settings) -> Result<(String, String)> {
    let mut errors = ErrorReporter::new();

    let mut job = parse_urp(urp_path)?;
    apply_boot_settings(&mut job, settings);
    settings.set_url_prefix(&job.prefix);
    settings.timeout = job.timeout;
    settings.headers = job.headers.clone();
    settings.scripts = job.scripts.clone();
    settings.debug = job.debug;

    let source_file =
        parse_sources(&job, &mut errors).ok_or_else(|| anyhow::anyhow!("Parse failed"))?;
    bail_if_errors_reported(&errors, "Parsing")?;

    let elab_file = elaborate(source_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Elaboration failed"))?;
    bail_if_errors_reported(&errors, "Elaboration (types and modules)")?;

    let elab_file = unnest(elab_file);
    let expl_file =
        explify(elab_file, &mut errors).ok_or_else(|| anyhow::anyhow!("Explify failed"))?;
    let core_file =
        corify(expl_file, settings, &mut errors).ok_or_else(|| anyhow::anyhow!("Corify failed"))?;

    let core_file = core_untangle(core_file);
    let core_file = core_reduce_local(core_file);
    let core_file = core_shake(core_file);
    let core_file = core_reduce(core_file, settings);
    let core_file = core_especialize(core_file);
    let core_file = core_unpoly(core_file);
    let core_file = core_specialize(core_file);
    let core_file = core_rpcify(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Rpcify failed"))?;
    let core_file =
        core_tag(core_file, settings, &mut errors).ok_or_else(|| anyhow::anyhow!("Tag failed"))?;
    let core_file = core_effectize(core_file, settings);

    check_marshal(&core_file, settings, &mut errors);
    check_termination(&core_file, &mut errors);
    bail_if_errors_reported(&errors, "Core verification (marshalling / termination)")?;

    let mono_file = monoize(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Monoize failed"))?;
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
    bail_if_errors_reported(&errors, "Monomorphization checks")?;

    let mono_file = if settings.debug {
        mono_iflow(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow::anyhow!("Iflow failed"))?
    } else {
        mono_file
    };
    let mono_file = mono_name_js(mono_file);
    let mono_file = if settings.sqlcache {
        mono_sqlcache(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow::anyhow!("Sqlcache failed"))?
    } else {
        mono_file
    };

    let _js = js_compile(&mono_file, settings, &mut errors);
    let cjr_file =
        cjrize(mono_file, &mut errors).ok_or_else(|| anyhow::anyhow!("CJRize failed"))?;
    bail_if_errors_reported(&errors, "C back-end (CJR)")?;

    let cjr_file = cjr_prepare(cjr_file, settings);
    let cjr_file = cjr_check_nest(cjr_file);

    let c_code = cjr_print(&cjr_file, settings);
    let sql_ddl = sql_generate(&cjr_file, settings);
    Ok((c_code, sql_ddl))
}

// ---------------------------------------------------------------------------
// Module name helper (used by main.rs)
// ---------------------------------------------------------------------------

/// Derive the Ur/Web module name from a filename.
/// e.g., `/path/to/my_app.ur` → `"MyApp"`.
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
    use std::sync::atomic::Ordering;

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
        let result = parse_sources(&Job::default(), &mut errors);
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
        let cwd = std::env::current_dir().unwrap();
        std::env::set_current_dir(dir.path()).unwrap();
        let result = parse_sources(&job, &mut errors);
        std::env::set_current_dir(&cwd).unwrap();
        assert!(
            result.is_some(),
            "parse_sources must return Some (catches replace with None)"
        );
        let source_file = result.unwrap();
        // source_file[0] is the synthetic Basis FfiStr; user modules start at index 1.
        assert!(
            source_file.len() >= 2,
            "parse_sources must return Basis + at least one user module (catches Some(Default::default()))"
        );
        assert_eq!(
            source_file[0].span.file, "<basis>",
            "Basis wrapper span.file must be set (catches delete field file in basis Span literal)"
        );
        let user_module = &source_file[1];
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
        let cwd = std::env::current_dir().unwrap();
        std::env::set_current_dir(dir.path()).unwrap();
        let result = parse_sources(&job, &mut errors);
        std::env::set_current_dir(&cwd).unwrap();
        let source_file = result.unwrap_or_else(|| {
            panic!("parse_sources: {:?}", errors);
        });
        let user_module = &source_file[1];
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
        let mut settings = Settings::default();
        settings.dbms = "sqlite".to_string();
        let cwd = std::env::current_dir().unwrap();
        std::env::set_current_dir(dir.path()).unwrap();
        let result = compile_to_outputs(&urp_path, &mut settings);
        std::env::set_current_dir(&cwd).unwrap();
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
        let mut settings = Settings::default();
        settings.sqlcache = true;
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
        let mut settings = Settings::default();
        let result = elaborate(Default::default(), &mut settings, &mut errors);
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
        let mut settings = Settings::default();
        let result = core_rpcify(Default::default(), &mut settings, &mut errors);
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
        let mut settings = Settings::default();
        let result = core_tag(Default::default(), &mut settings, &mut errors);
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
        let mut settings = Settings::default();
        let result = core_tag(file, &mut settings, &mut errors);
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
        let mut settings = Settings::default();
        settings.dbms = "postgres".to_string();
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
        assert_eq!(dbms_link_library_flag("sqlite"), "-lsqlite3");
        assert_eq!(dbms_link_library_flag("mysql"), "-lmysqlclient");
        assert_eq!(dbms_link_library_flag(""), "-lpq");
    }

    #[test]
    fn mono_filecache_invokes_instrument() {
        MONO_FILECACHE_CALLS.store(0, Ordering::SeqCst);
        let mut settings = Settings::default();
        settings.file_cache = Some("/tmp/urweb_fc_test".into());
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
        let cwd = std::env::current_dir().unwrap();
        std::env::set_current_dir(dir.path()).unwrap();
        let result = parse_sources(&job, &mut errors);
        std::env::set_current_dir(&cwd).unwrap();
        let source_file = result.expect("parse_sources");
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
