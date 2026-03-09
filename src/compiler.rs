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
    let _source = crate::file_io::open_text(path)
        .with_context(|| format!("reading project file {}", path.display()))?;
    todo!("parse_urp: .urp parser not yet implemented")
}

// ---------------------------------------------------------------------------
// Phase 2: Parse source files
// ---------------------------------------------------------------------------

pub fn parse_sources(_job: &Job, _errors: &mut ErrorReporter) -> Option<crate::source::File> {
    todo!("parse_sources: source parser not yet implemented")
}

// ---------------------------------------------------------------------------
// Phase 3: Elaborate
// ---------------------------------------------------------------------------

pub fn elaborate(
    _file: crate::source::File,
    _settings: &Settings,
    _errors: &mut ErrorReporter,
) -> Option<crate::elaborated::File> {
    todo!("elaborate: type checker not yet implemented")
}

// ---------------------------------------------------------------------------
// Phase 4: Explify (elab → expl)
// ---------------------------------------------------------------------------

pub fn explify(
    _file: crate::elaborated::File,
    _errors: &mut ErrorReporter,
) -> Option<crate::explicit::File> {
    todo!("explify: not yet implemented")
}

// ---------------------------------------------------------------------------
// Phase 5: Corify (expl → core)
// ---------------------------------------------------------------------------

pub fn corify(
    _file: crate::explicit::File,
    _errors: &mut ErrorReporter,
) -> Option<crate::core::File> {
    todo!("corify: not yet implemented")
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

pub fn check_script(_file: &crate::core::File, _errors: &mut ErrorReporter) {
    todo!("check_script")
}

pub fn check_path(_file: &crate::core::File, _settings: &Settings, _errors: &mut ErrorReporter) {
    todo!("check_path")
}

pub fn check_side(_file: &crate::core::File, _errors: &mut ErrorReporter) {
    todo!("check_side")
}

pub fn check_sig(_file: &crate::core::File, _errors: &mut ErrorReporter) {
    todo!("check_sig")
}

pub fn check_dbmode(_file: &crate::core::File, _errors: &mut ErrorReporter) {
    todo!("check_dbmode")
}

pub fn check_termination(_file: &crate::core::File, _errors: &mut ErrorReporter) {
    todo!("check_termination")
}

pub fn check_nest(_file: &crate::core::File, _errors: &mut ErrorReporter) {
    todo!("check_nest")
}

// ---------------------------------------------------------------------------
// Phase: Monoize (core → mono)
// ---------------------------------------------------------------------------

pub fn monoize(
    _file: crate::core::File,
    _settings: &Settings,
    _errors: &mut ErrorReporter,
) -> Option<crate::monomorphized::File> {
    todo!("monoize: not yet implemented")
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
    _file: crate::monomorphized::File,
    _settings: &Settings,
    _errors: &mut ErrorReporter,
) -> Option<crate::monomorphized::File> {
    todo!("mono_iflow: information-flow analysis")
}

pub fn mono_sqlcache(
    _file: crate::monomorphized::File,
    _settings: &Settings,
    _errors: &mut ErrorReporter,
) -> Option<crate::monomorphized::File> {
    todo!("mono_sqlcache")
}

// ---------------------------------------------------------------------------
// Phase: CJRize (mono → cjr)
// ---------------------------------------------------------------------------

pub fn cjrize(
    _file: crate::monomorphized::File,
    _errors: &mut ErrorReporter,
) -> Option<crate::c_like_representation::File> {
    todo!("cjrize: not yet implemented")
}

// ---------------------------------------------------------------------------
// Phase: C code generation (cjr → .c file)
// ---------------------------------------------------------------------------

pub fn cjr_print(_file: &crate::c_like_representation::File, _settings: &Settings) -> String {
    todo!("cjr_print: C code generator not yet implemented")
}

// ---------------------------------------------------------------------------
// Phase: JS compilation
// ---------------------------------------------------------------------------

pub fn js_compile(
    _file: &crate::monomorphized::File,
    _settings: &Settings,
    _errors: &mut ErrorReporter,
) -> Option<String> {
    todo!("js_compile: JavaScript compiler not yet implemented")
}

// ---------------------------------------------------------------------------
// Phase: SQL DDL generation
// ---------------------------------------------------------------------------

pub fn sql_generate(_file: &crate::c_like_representation::File, _settings: &Settings) -> String {
    todo!("sql_generate: SQL DDL generator not yet implemented")
}

// ---------------------------------------------------------------------------
// Phase: C compilation + linking
// ---------------------------------------------------------------------------

pub fn cc_and_link(
    _c_source: &str,
    _output: &Path,
    _job: &Job,
    _settings: &Settings,
) -> Result<()> {
    todo!("cc_and_link: C compilation not yet implemented")
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
        corify(expl_file, &mut errors).ok_or_else(|| anyhow::anyhow!("Corify failed"))?;

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
    check_script(&core_file, &mut errors);
    check_path(&core_file, settings, &mut errors);
    check_side(&core_file, &mut errors);
    check_sig(&core_file, &mut errors);
    check_dbmode(&core_file, &mut errors);
    check_termination(&core_file, &mut errors);
    check_nest(&core_file, &mut errors);
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
    #[should_panic(expected = "parse_urp")]
    fn parse_urp_panics_until_implemented() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("x.urp");
        std::fs::write(&p, "x.ur").unwrap();
        let _ = parse_urp(&p);
    }

    #[test]
    #[should_panic(expected = "parse_sources")]
    fn parse_sources_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let _ = parse_sources(&Job::default(), &mut errors);
    }

    #[test]
    #[should_panic(expected = "elaborate")]
    fn elaborate_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let mut settings = Settings::default();
        let _ = elaborate(Default::default(), &mut settings, &mut errors);
    }

    #[test]
    #[should_panic(expected = "explify")]
    fn explify_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let _ = explify(Default::default(), &mut errors);
    }

    #[test]
    #[should_panic(expected = "corify")]
    fn corify_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let _ = corify(Default::default(), &mut errors);
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
    fn core_especialize_passes_through_empty_file() {
        let result = core_especialize(Default::default());
        assert!(result.is_empty(), "especialize of empty file must be empty");
    }

    #[test]
    fn core_unpoly_passes_through_empty_file() {
        let result = core_unpoly(Default::default());
        assert!(result.is_empty(), "unpoly of empty file must be empty");
    }

    #[test]
    fn core_specialize_passes_through_empty_file() {
        let result = core_specialize(Default::default());
        assert!(result.is_empty(), "specialize of empty file must be empty");
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
    fn core_effectize_passes_through_empty_file() {
        // Catches mutant: core_effectize panics or returns garbage on empty input.
        let settings = Settings::default();
        let result = core_effectize(Default::default(), &settings);

        assert!(result.is_empty(), "effectize of empty file must be empty");
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
    #[should_panic(expected = "check_script")]
    fn check_script_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        check_script(&Default::default(), &mut errors);
    }

    #[test]
    #[should_panic(expected = "check_path")]
    fn check_path_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let mut settings = Settings::default();
        check_path(&Default::default(), &mut settings, &mut errors);
    }

    #[test]
    #[should_panic(expected = "check_side")]
    fn check_side_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        check_side(&Default::default(), &mut errors);
    }

    #[test]
    #[should_panic(expected = "check_sig")]
    fn check_sig_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        check_sig(&Default::default(), &mut errors);
    }

    #[test]
    #[should_panic(expected = "check_dbmode")]
    fn check_dbmode_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        check_dbmode(&Default::default(), &mut errors);
    }

    #[test]
    #[should_panic(expected = "check_termination")]
    fn check_termination_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        check_termination(&Default::default(), &mut errors);
    }

    #[test]
    #[should_panic(expected = "check_nest")]
    fn check_nest_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        check_nest(&Default::default(), &mut errors);
    }

    #[test]
    #[should_panic(expected = "monoize")]
    fn monoize_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let mut settings = Settings::default();
        let _ = monoize(Default::default(), &mut settings, &mut errors);
    }

    #[test]
    fn mono_untangle_passes_through_empty_file() {
        let result = mono_untangle(Default::default());
        assert!(result.0.is_empty(), "untangle of empty file must be empty");
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
    fn mono_reduce_passes_through_empty_file() {
        let settings = Settings::default();
        let result = mono_reduce(Default::default(), &settings);
        assert!(
            result.0.is_empty(),
            "mono_reduce of empty file must produce no decls"
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
    fn mono_shake_passes_through_empty_file() {
        let result = mono_shake(Default::default());
        assert!(
            result.0.is_empty(),
            "mono_shake of empty file must be empty"
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
    #[should_panic(expected = "mono_iflow")]
    fn mono_iflow_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let mut settings = Settings::default();
        let _ = mono_iflow(Default::default(), &mut settings, &mut errors);
    }

    #[test]
    #[should_panic(expected = "mono_sqlcache")]
    fn mono_sqlcache_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let mut settings = Settings::default();
        let _ = mono_sqlcache(Default::default(), &mut settings, &mut errors);
    }

    #[test]
    #[should_panic(expected = "cjrize")]
    fn cjrize_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let _ = cjrize(Default::default(), &mut errors);
    }

    #[test]
    #[should_panic(expected = "cjr_print")]
    fn cjr_print_panics_until_implemented() {
        let mut settings = Settings::default();
        let _ = cjr_print(&Default::default(), &mut settings);
    }

    #[test]
    #[should_panic(expected = "js_compile")]
    fn js_compile_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let mut settings = Settings::default();
        let _ = js_compile(&Default::default(), &mut settings, &mut errors);
    }

    #[test]
    #[should_panic(expected = "sql_generate")]
    fn sql_generate_panics_until_implemented() {
        let mut settings = Settings::default();
        let _ = sql_generate(&Default::default(), &mut settings);
    }

    #[test]
    #[should_panic(expected = "cc_and_link")]
    fn cc_and_link_panics_until_implemented() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("a.out");
        let _ = cc_and_link("int main() {}", &out, &Job::default(), &Settings::default());
    }
}
