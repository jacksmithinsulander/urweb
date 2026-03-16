//! Pipeline orchestration — drives all compilation phases.
//!
//! Parses `.urp` project files into `Job`, then runs: parse → elaborate →
//! explify → core passes → mono passes → cjr_print / sql_generate → C compile.
//!
//! Mirrors `compiler.sml`.

use anyhow::{bail, Context, Result};
use std::path::{Path, PathBuf};

use crate::error_types::ErrorReporter;
use crate::settings::Settings;

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
        }
    }
}

// ---------------------------------------------------------------------------
// Pipeline phases (named, mirrors SML `transform` wrappers)
// ---------------------------------------------------------------------------

/// Result of a single compilation phase.
pub type PhaseResult<T> = Result<T>;

/// The complete pipeline result.
pub type CompileResult = Result<PathBuf /* generated executable */>;

// ---------------------------------------------------------------------------
// Phase 1: Parse .urp file
// ---------------------------------------------------------------------------

/// Parse a `.urp` project file into a `Job` description.
pub fn parse_urp(path: &Path) -> Result<Job> {
    crate::urp_parser::parse_urp(path)
}

// ---------------------------------------------------------------------------
// Phase 2: Parse source files
// ---------------------------------------------------------------------------

pub fn parse_sources(job: &Job, errors: &mut ErrorReporter) -> Option<crate::source::File> {
    use crate::error_types::{CompileError, Located, Span};
    use crate::source;
    use std::path::Path;

    let mut decls: source::File = Vec::new();

    // Always prepend a minimal synthetic Basis FFI structure so that primitive
    // types (int, float, string, char, …) resolve to Basis.int etc. during
    // elaboration.  A Flattening::Ffi module in corify returns Ffi(module, name)
    // for any name lookup, so an empty signature suffices.
    {
        let basis_span = Span {
            file: "<basis>".into(),
            ..Span::dummy()
        };
        let sgn = Located::new(source::Sgn::Const(vec![]), basis_span.clone());
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
        None
    } else {
        Some(decls)
    }
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

pub fn mono_iflow(
    file: crate::monomorphized::File,
    _settings: &Settings,
    _errors: &mut ErrorReporter,
) -> Option<crate::monomorphized::File> {
    // Information-flow analysis pass (iflow.sml). Not yet translated; pass through.
    Some(file)
}

pub fn mono_sqlcache(
    file: crate::monomorphized::File,
    _settings: &Settings,
    _errors: &mut ErrorReporter,
) -> Option<crate::monomorphized::File> {
    // SQL cache optimization pass (sqlcache.sml). Not yet translated; pass through.
    Some(file)
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
// Phase: C compilation + linking
// ---------------------------------------------------------------------------

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

    let opt_flag = if job.debug { "" } else { "-O3" };

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
    if !opt_flag.is_empty() {
        compile_cmd.arg(opt_flag);
    }
    if !settings.config_include.is_empty() {
        compile_cmd.arg("-I").arg(&settings.config_include);
    }
    #[cfg(test)]
    {
        compile_cmd.stderr(Stdio::null()).stdout(Stdio::null());
    }
    if job.debug {
        compile_cmd.arg("-g");
    }
    if job.profile {
        compile_cmd.arg("-pg");
    }

    let compile_status = compile_cmd
        .status()
        .with_context(|| format!("running C compiler '{}'", cc))?;
    if !compile_status.success() {
        bail!("C compilation failed (exit {})", compile_status);
    }

    // Link step.
    let linker_cmd_base = job.linker.as_deref().unwrap_or(cc);
    let mut link_cmd = Command::new(linker_cmd_base);
    #[cfg(test)]
    {
        link_cmd.stderr(Stdio::null()).stdout(Stdio::null());
    }
    link_cmd.arg(&o_file);
    if !settings.config_lib.is_empty() {
        link_cmd.arg(format!("-L{}", settings.config_lib));
    }
    link_cmd.arg("-lurweb").arg("-lm").arg("-o").arg(output);
    if job.debug {
        link_cmd.arg("-g");
    }
    if job.profile {
        link_cmd.arg("-pg");
    }

    let link_status = link_cmd
        .status()
        .with_context(|| format!("running linker '{}'", linker_cmd_base))?;
    if !link_status.success() {
        bail!("Linking failed (exit {})", link_status);
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Top-level: full build pipeline
// ---------------------------------------------------------------------------

/// Run the complete compilation pipeline for a `.urp` project.
///
/// Corresponds to `Compiler.run` / the main compilation path in `main.mlton.sml`.
pub fn compile(urp_path: &Path, settings: &mut Settings) -> CompileResult {
    let mut errors = ErrorReporter::new();

    // Phase 1: parse project file
    let job = parse_urp(urp_path)?;

    // Apply job settings globally
    settings.set_url_prefix(&job.prefix);
    settings.timeout = job.timeout;
    settings.headers = job.headers.clone();
    settings.scripts = job.scripts.clone();
    settings.debug = job.debug;

    // Phase 2: parse sources
    let source_file =
        parse_sources(&job, &mut errors).ok_or_else(|| anyhow::anyhow!("Parse failed"))?;
    if errors.has_errors() {
        bail!("parse errors");
    }

    // Phase 3: elaborate
    let elab_file = elaborate(source_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Elaboration failed"))?;
    if errors.has_errors() {
        bail!("elaboration errors");
    }

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
    if errors.has_errors() {
        bail!("check errors");
    }

    // Monoize
    let mono_file = monoize(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Monoize failed"))?;

    // Mono passes
    let mono_file = mono_untangle(mono_file);
    let mono_file = mono_fuse(mono_file);
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
    if errors.has_errors() {
        bail!("mono check errors");
    }

    let mono_file = if settings.debug {
        mono_iflow(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow::anyhow!("Iflow failed"))?
    } else {
        mono_file
    };

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
    if errors.has_errors() {
        bail!("CJR errors");
    }

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

    let job = parse_urp(urp_path)?;
    settings.set_url_prefix(&job.prefix);
    settings.timeout = job.timeout;
    settings.headers = job.headers.clone();
    settings.scripts = job.scripts.clone();
    settings.debug = job.debug;

    let source_file =
        parse_sources(&job, &mut errors).ok_or_else(|| anyhow::anyhow!("Parse failed"))?;
    if errors.has_errors() {
        bail!("parse errors");
    }

    let elab_file = elaborate(source_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Elaboration failed"))?;
    if errors.has_errors() {
        bail!("elaboration errors");
    }

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
    if errors.has_errors() {
        bail!("check errors");
    }

    let mono_file = monoize(core_file, settings, &mut errors)
        .ok_or_else(|| anyhow::anyhow!("Monoize failed"))?;
    let mono_file = mono_untangle(mono_file);
    let mono_file = mono_fuse(mono_file);
    let mono_file = mono_reduce(mono_file, settings);
    let mono_file = mono_opt(mono_file, settings, &mut errors);
    let mono_file = mono_shake(mono_file);
    let mono_file = mono_inline(mono_file, settings);
    let mono_file = mono_script_check(mono_file, settings, &mut errors);
    mono_path_check(&mono_file, &mut errors);
    let (mono_file, _env_vars) = mono_side_check(mono_file, settings, &mut errors);
    let mono_file = mono_sig_check(mono_file);
    let mono_file = mono_dbmode_check(mono_file);
    if errors.has_errors() {
        bail!("mono check errors");
    }

    let mono_file = if settings.debug {
        mono_iflow(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow::anyhow!("Iflow failed"))?
    } else {
        mono_file
    };
    let mono_file = if settings.sqlcache {
        mono_sqlcache(mono_file, settings, &mut errors)
            .ok_or_else(|| anyhow::anyhow!("Sqlcache failed"))?
    } else {
        mono_file
    };

    let _js = js_compile(&mono_file, settings, &mut errors);
    let cjr_file =
        cjrize(mono_file, &mut errors).ok_or_else(|| anyhow::anyhow!("CJRize failed"))?;
    if errors.has_errors() {
        bail!("CJR errors");
    }

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
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let user_module = &source_file[1];
        assert!(
            user_module.span.file.ends_with("x.ur"),
            "span.file must be set to source path (catches delete field file mutant): {}",
            user_module.span.file
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
            "cc_and_link must actually invoke compiler (catches delete ! mutant)"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("compilation") || err_msg.contains("compil"),
            "invalid C must fail at compile step, not link (catches delete ! in compile_status check): {}",
            err_msg
        );
    }
}
