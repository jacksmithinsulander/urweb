//! Shared command-line helpers and templates for the `ur` orchestrator and `ur-*` helper binaries.
//!
//! New and edited code follows [README.md](../README.md) (naming, line comments on logic, `///` on functions; see Exceptions there).
//!
//! ## Conventions for small binaries
//!
//! - Help: `ur` and `ur-compile` print overviews to standard output; `ur-debugger` prints usage to standard error.
//! - Unknown flags: `ur-compile` fails on unknown `-` flags; `ur-fmt` may log a warning and continue.
//! - Exit codes: `0` means success; `1` usually means failure unless documented (for example `ur-lsp` exits `0` on a clean
//!   disconnect when [`crate::lsp_support::disconnect_error_exits_clean`] matches).
//! - `main` style: long-running tools (`ur-lsp`, `ur-debugger`) use [`anyhow::Result`] in `run()`; thin wrappers often return `i32` and use `eprintln!`.

use serde::Deserialize;

/// Relative path to the project manifest (strict Tom’s Obvious, Minimal Language).
pub const UR_MANIFEST_FILE: &str = "ur.toml";

const UR_MANIFEST_MISSING_ORCHESTRATOR: &str = "ur.toml not found in current directory\n\
Run 'ur new <name>' to create a project, then 'cd <name> && ur build'";

const UR_MANIFEST_MISSING_FMT: &str =
    "error: ur.toml not found; run from project directory or specify files";

/// Lines printed under `usage:` for the `ur` orchestrator (`ur new`, `ur build`, …).
pub const UR_ORCHESTRATOR_USAGE_LINES: &[&str] = &[
    "  ur new <project-name>",
    "  ur new --lib <project-name>",
    "  ur build",
    "  ur fmt [options] [files...]",
    "  ur install author/repo",
    "  ur daemon [stop|start]",
    "  ur lsp",
    "  ur debugger [ur-debugger-args...]",
    "  ur [flag ...] project-name",
];

/// Load and strictly parse [`UR_MANIFEST_FILE`] (`ur.toml`) from the current working directory.
///
/// Unknown keys are rejected (`deny_unknown_fields`) as the configuration trust boundary.
///
/// # Returns
///
/// [`UrTomlStrict`] on success.
///
/// # Errors
///
/// Missing manifest (orchestrator message), read failure, or invalid Tom's Obvious, Minimal Language (prefixed human-readable `String`).
pub fn load_ur_manifest_cwd() -> Result<UrTomlStrict, String> {
    load_ur_manifest_cwd_inner(UR_MANIFEST_MISSING_ORCHESTRATOR)
}

/// Like [`load_ur_manifest_cwd`], used when `ur-fmt` discovers files and needs a different missing-file message.
///
/// # Returns
///
/// [`UrTomlStrict`] on success.
///
/// # Errors
///
/// Same as [`load_ur_manifest_cwd`] but with the formatter-oriented missing-manifest text.
pub fn load_ur_manifest_cwd_for_fmt_discovery() -> Result<UrTomlStrict, String> {
    load_ur_manifest_cwd_inner(UR_MANIFEST_MISSING_FMT)
}

/// Read `ur.toml` if present; otherwise return `missing_msg` as `Err`.
///
/// # Arguments
///
/// * `missing_msg` — Error string when [`UR_MANIFEST_FILE`] is absent.
///
/// # Returns
///
/// Parsed manifest or error string.
///
/// # Errors
///
/// Missing file (`missing_msg`), I/O while reading, or TOML/serde rejection.
fn load_ur_manifest_cwd_inner(missing_msg: &str) -> Result<UrTomlStrict, String> {
    if !file_exists(UR_MANIFEST_FILE) {
        return Err(missing_msg.to_string());
    }
    let toml_content = std::fs::read_to_string(UR_MANIFEST_FILE)
        .map_err(|e| format!("error reading ur.toml: {}", e))?;
    parse_ur_toml_strict(&toml_content).map_err(|e| format!("error: ur.toml: {}", e))
}

/// Require a non-empty `[build] entry` (used by `ur build` and default `ur-fmt` project discovery).
///
/// # Arguments
///
/// * `cfg` — Strict manifest already parsed from disk.
///
/// # Returns
///
/// `Ok(())` when `cfg.build.entry` is non-empty.
///
/// # Errors
///
/// Fixed error string when `entry` is empty.
pub fn require_manifest_entry(cfg: &UrTomlStrict) -> Result<(), String> {
    if cfg.build.entry.is_empty() {
        Err("error: ur.toml: [build] entry is required".into())
    } else {
        Ok(())
    }
}

/// For `ur-install`: require `ur.toml` in the current working directory (existence only, no parse).
///
/// # Returns
///
/// `Ok(())` when [`UR_MANIFEST_FILE`] exists.
///
/// # Errors
///
/// User-facing string when the file is missing.
pub fn ensure_ur_toml_present_for_install() -> Result<(), String> {
    if !file_exists(UR_MANIFEST_FILE) {
        Err("error: ur.toml not found; run from project directory".into())
    } else {
        Ok(())
    }
}

/// Run `exe` as found on the user’s `PATH` with `args`, returning the child exit status.
///
/// Uses [`std::process::Command`] and only searches `PATH` (not the current directory).
///
/// # Arguments
///
/// * `exe` — Program name on the path (for example `"ur-compile"`).
/// * `args` — Argument vector after `exe` (no implicit `argv[0]` insertion).
///
/// # Returns
///
/// Child exit code, `0` on success; `1` if the executable could not be started; otherwise the child’s non-zero status.
pub fn exec_peer_bin(exe: &str, args: &[String]) -> i32 {
    match std::process::Command::new(exe).args(args).status() {
        Ok(s) => {
            if s.success() {
                0
            } else {
                s.code().unwrap_or(1)
            }
        }
        Err(_) => {
            eprintln!("error: {} not found in PATH", exe);
            1
        }
    }
}

// ---------------------------------------------------------------------------
// Project scaffolding templates
// ---------------------------------------------------------------------------

/// `cursor.md` for new projects (`ur-new`); body lives in `templates/project_ai_shared.md`.
pub const CURSOR_MD: &str = concat!(
    "# Ur/Web — Cursor context (this project)\n\n",
    "Reference this file in chat as **`@cursor.md`** when editing Ur/Web sources here.\n\n",
    include_str!("../templates/project_ai_shared.md"),
);

/// `claude.md` for new projects (`ur-new`); body lives in `templates/project_ai_shared.md`.
pub const CLAUDE_MD: &str = concat!(
    "# Ur/Web — Claude context (this project)\n\n",
    "Attach **`claude.md`** (e.g. `@claude.md`) when editing this Ur/Web project so answers follow Ur/Web semantics, not other languages.\n\n",
    include_str!("../templates/project_ai_shared.md"),
);

pub const GITIGNORE: &str = "# Compiled executables\n\
*.exe\n\
\n\
# SQLite databases and generated SQL schemas\n\
*.db\n\
*.sql\n\
\n\
# ur daemon socket\n\
.ur_daemon\n";

pub const GITIGNORE_APP_SUFFIX: &str = "\n\
# Compiled CSS (regenerated by 'ur build' from style/scss/)\n\
style/css/*.css\n";

pub const URP_DIRECTIVE_KEYWORDS: &[&str] = &[
    "database",
    "sql",
    "prefix",
    "rewrite",
    "file",
    "library",
    "link",
    "ffi",
    "effectful",
    "benignEffectful",
    "clientOnly",
    "serverOnly",
    "jsFunc",
    "timeout",
    "sigfile",
    "debug",
];

// ---------------------------------------------------------------------------
// Project kind and validation
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProjectKind {
    App,
    Library,
}

/// Validate `ur new` / scaffold names: non-empty, starts with letter, alphanumeric + `_` only.
///
/// # Arguments
///
/// * `name` — Proposed directory / module stem.
///
/// # Returns
///
/// `Ok(())` when rules pass.
///
/// # Errors
///
/// Descriptive `String` when validation fails.
pub fn validate_project_name(name: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err("project name cannot be empty".into());
    }
    if !name.chars().next().is_some_and(|c| c.is_alphabetic()) {
        return Err(format!("project name must start with a letter: '{}'", name));
    }
    if !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return Err(format!(
            "project name must contain only letters, digits, or underscores: '{}'",
            name
        ));
    }
    Ok(())
}

/// Uppercase the first Unicode scalar (used for generated Ur module names).
///
/// # Arguments
///
/// * `s` — Input string (may be empty).
///
/// # Returns
///
/// New string with the first character uppercased; empty if `s` is empty.
pub fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => {
            let mut out = c.to_uppercase().collect::<String>();
            out.push_str(chars.as_str());
            out
        }
    }
}

/// Paths printed by `ur new` that depend on app vs library layout.
///
/// # Arguments
///
/// * `kind` — Application or library scaffold.
/// * `name` — Project directory name.
///
/// # Returns
///
/// Relative paths (as strings) to mention in the success message (may be empty).
pub fn kind_specific_created_files(kind: ProjectKind, name: &str) -> Vec<String> {
    let mut out = vec![];
    if kind == ProjectKind::Library {
        out.push(format!("{name}/{name}.urs"));
    }
    if kind == ProjectKind::App {
        out.push(format!("{name}/style/scss/main.scss"));
        out.push(format!("{name}/style/css/main.css"));
    }
    out
}

// ---------------------------------------------------------------------------
// TOML
// ---------------------------------------------------------------------------

/// Project manifest with **closed** tables: extra keys are rejected (LangSec-style trust boundary).
#[derive(Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UrTomlStrict {
    pub package: UrTomlPackageStrict,
    pub build: UrTomlBuildStrict,
    #[serde(default)]
    pub style: Option<UrTomlStyleStrict>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UrTomlPackageStrict {
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default = "default_pkg_kind")]
    pub kind: String,
    /// `en`, `sv`, or `es` (see [`crate::diagnostics::DiagnosticLocale::parse_manifest_token`]).
    #[serde(default)]
    pub language: String,
}

/// `[package].kind` default when omitted in `ur.toml`.
fn default_pkg_kind() -> String {
    "app".into()
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UrTomlBuildStrict {
    pub entry: String,
    /// Database **engine** for `ur build` → passed as `-dbms` (same names as `.urp` `dbms`: sqlite, mysql, postgres, …).
    /// Validated by [`crate::db::validate_manifest_db_engine`] in the orchestrator. Not the SQL connection string (`-db` / `.urp` `database`).
    #[serde(default = "default_build_db")]
    pub db: String,
    #[serde(default)]
    pub ccompiler: String,
    #[serde(default)]
    pub boot: bool,
}

/// `[build].db` default engine when omitted.
fn default_build_db() -> String {
    "sqlite".into()
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UrTomlStyleStrict {
    #[serde(default)]
    pub scss: Option<String>,
    #[serde(default)]
    pub css: Option<String>,
}

impl Default for UrTomlPackageStrict {
    fn default() -> Self {
        Self {
            name: None,
            kind: default_pkg_kind(),
            language: String::new(),
        }
    }
}

impl Default for UrTomlBuildStrict {
    fn default() -> Self {
        Self {
            entry: String::new(),
            db: default_build_db(),
            ccompiler: String::new(),
            boot: false,
        }
    }
}

/// Deserialize closed `ur.toml` tables; unknown keys are rejected by serde.
///
/// # Arguments
///
/// * `content` — Full manifest file text.
///
/// # Returns
///
/// [`UrTomlStrict`] on success.
///
/// # Errors
///
/// TOML syntax or schema errors as display string.
pub fn parse_ur_toml_strict(content: &str) -> Result<UrTomlStrict, String> {
    toml::from_str(content).map_err(|e| format!("{e}"))
}

/// Loose line-based TOML-ish parse for legacy `ur-install` patching (not strict `UrTomlStrict`).
///
/// # Arguments
///
/// * `content` — Whole file body.
///
/// # Returns
///
/// Flattened `section.key` → value pairs best-effort (no serde validation).
pub fn parse_toml(content: &str) -> Vec<(String, String)> {
    let mut section = String::new();
    let mut entries = vec![];
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            section = line[1..line.len() - 1].trim().to_string();
            continue;
        }
        if let Some(eq) = line.find('=') {
            let key = line[..eq].trim();
            let raw_val = line[eq + 1..].trim();
            let val = if raw_val.starts_with('"') && raw_val.ends_with('"') && raw_val.len() >= 2 {
                raw_val[1..raw_val.len() - 1].to_string()
            } else {
                raw_val.to_string()
            };
            let full_key = if section.is_empty() {
                key.to_string()
            } else {
                format!("{}.{}", section, key)
            };
            entries.push((full_key, val));
        }
    }
    entries
}

/// Look up `section.key` style flattened entries from [`parse_toml`].
///
/// # Arguments
///
/// * `entries` — Output of [`parse_toml`].
/// * `key` — Full flattened key to match exactly.
///
/// # Returns
///
/// Value reference when the key exists.
pub fn toml_get<'a>(entries: &'a [(String, String)], key: &str) -> Option<&'a str> {
    entries
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.as_str())
}

// ---------------------------------------------------------------------------
// File and flag helpers
// ---------------------------------------------------------------------------

/// True if `path` exists on disk (symlink follows OS rules).
///
/// # Arguments
///
/// * `path` — Filesystem path string.
///
/// # Returns
///
/// Whether [`std::path::Path::exists`] is true.
pub fn file_exists(path: &str) -> bool {
    std::path::Path::new(path).exists()
}

/// Last path segment of an `author/repo` install spec, ignoring empty `//` segments.
///
/// # Arguments
///
/// * `spec` — Package specifier string.
///
/// # Returns
///
/// Repository leaf name slice into `spec`.
pub fn package_spec_repo_leaf(spec: &str) -> &str {
    spec.split('/').rfind(|s| !s.is_empty()).unwrap_or(spec)
}

/// Heuristic: argv token is a file/project name, not a `-flag`.
///
/// # Arguments
///
/// * `arg` — One command-line token.
///
/// # Returns
///
/// `true` when `arg` does not start with `-`.
pub fn is_file_arg(arg: &str) -> bool {
    !arg.starts_with('-')
}

/// Blank or `#` comment lines in `.urp` source parsing.
///
/// # Arguments
///
/// * `line` — Single line (may include leading whitespace depending on caller).
///
/// # Returns
///
/// Whether the line should be ignored as blank or comment.
pub fn should_skip_urp_line(line: &str) -> bool {
    line.is_empty() || line.starts_with('#')
}

/// Merge one Foundry-style verbosity flag body (text after the leading `-`, only `v` characters) into [`crate::settings::Settings::verbosity`].
///
/// A lone `v` increments by one; `vv` or longer sets verbosity to at least that length. Capped at [`crate::compiler_tracing::MAX_COMPILER_VERBOSITY`].
pub fn apply_verbosity_v_flag(settings: &mut crate::settings::Settings, flag_body: &str) {
    if flag_body.is_empty() || flag_body.len() > 5 || !flag_body.chars().all(|c| c == 'v') {
        return;
    }
    let level = flag_body.len() as u8;
    settings.verbosity = match level == 1 {
        true => (settings.verbosity + 1).min(crate::compiler_tracing::MAX_COMPILER_VERBOSITY),
        false => settings
            .verbosity
            .max(level)
            .min(crate::compiler_tracing::MAX_COMPILER_VERBOSITY),
    };
}

/// Collect leading `-v` / `-vv` / `-verbose` tokens from `ur build …` argv so they can be forwarded to `ur-compile`.
pub fn leading_build_verbosity_flags(build_args: &[String]) -> Vec<String> {
    let mut forwarded = Vec::new();
    for token in build_args {
        let raw = token.trim_start_matches('-');
        let repeats_v_only = token.starts_with('-')
            && !raw.is_empty()
            && raw.len() <= 5
            && raw.chars().all(|c| c == 'v');
        if repeats_v_only {
            forwarded.push(token.clone());
            continue;
        }
        if token.starts_with('-') && raw == "verbose" {
            forwarded.push("-verbose".to_string());
            continue;
        }
        break;
    }
    forwarded
}

/// Used by formatter lenient flag handling: empty flag or argv looks like another flag.
///
/// # Arguments
///
/// * `flag` — Current flag token being parsed (may be empty).
/// * `arg` — Next argv token.
///
/// # Returns
///
/// `true` when the formatter should treat this as an unknown or ambiguous flag boundary.
pub fn is_unknown_compiler_flag(flag: &str, arg: &str) -> bool {
    flag.is_empty() || arg.starts_with('-')
}

/// Resource limit class values must be non-negative.
///
/// # Arguments
///
/// * `n` — Candidate limit value.
///
/// # Returns
///
/// `true` when `n >= 0`.
pub fn is_valid_limit(n: i32) -> bool {
    n >= 0
}

/// True when `status` is `Ok` and the child exited successfully.
///
/// # Arguments
///
/// * `status` — Result from [`std::process::Command::status`] or similar.
///
/// # Returns
///
/// Whether spawning worked and [`std::process::ExitStatus::success`] is true.
pub fn command_succeeded(status: &std::io::Result<std::process::ExitStatus>) -> bool {
    status.as_ref().is_ok_and(|s| s.success())
}

// ---------------------------------------------------------------------------
// Build config helpers
// ---------------------------------------------------------------------------

/// `ur.toml` `kind == "lib"` selects type-check-only `ur build` path.
///
/// # Arguments
///
/// * `kind` — `[package].kind` string.
///
/// # Returns
///
/// `true` for `"lib"`.
pub fn is_lib_project(kind: &str) -> bool {
    kind == "lib"
}

/// Parse `[build].boot` string to bool for templates.
///
/// # Arguments
///
/// * `value` — Raw table value text.
///
/// # Returns
///
/// `true` only when `value == "true"`.
pub fn parse_boot(value: &str) -> bool {
    value == "true"
}

/// Forward `-ccompiler` only when the manifest field is non-empty.
///
/// # Arguments
///
/// * `cc` — `[build].ccompiler` field.
///
/// # Returns
///
/// `true` when `cc` is not empty.
pub fn should_add_ccompiler(cc: &str) -> bool {
    !cc.is_empty()
}

/// True if either Dart Sass or `sassc` is installed per `which` probes.
///
/// # Arguments
///
/// * `has_sass` — Whether `which sass` succeeded for the caller’s probe.
/// * `has_sassc` — Whether `which sassc` succeeded.
///
/// # Returns
///
/// Logical OR of the two flags.
pub fn sass_tool_available(has_sass: bool, has_sassc: bool) -> bool {
    has_sass || has_sassc
}

/// Probe `PATH` for `sass` and `sassc` to decide whether SCSS precompilation can run.
///
/// # Returns
///
/// `true` if either executable is found (non-interactive `which` checks).
pub fn has_sass_or_sassc() -> bool {
    let has_sass = std::process::Command::new("which")
        .arg("sass")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok_and(|s| s.success());
    let has_sassc = std::process::Command::new("which")
        .arg("sassc")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok_and(|s| s.success());
    sass_tool_available(has_sass, has_sassc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler_diagnostics::{lock_for_compile, TEST_CWD_LOCK};

    #[test]
    fn validate_name_empty() {
        assert!(validate_project_name("").is_err());
    }

    #[test]
    fn validate_name_starts_with_digit() {
        assert!(validate_project_name("1foo").is_err());
    }

    #[test]
    fn validate_name_valid() {
        assert!(validate_project_name("my_app").is_ok());
        assert!(validate_project_name("Foo123").is_ok());
    }

    #[test]
    fn validate_name_hyphen_invalid() {
        assert!(validate_project_name("my-app").is_err());
    }

    #[test]
    fn ur_toml_strict_accepts_new_project_shape() {
        let content = r#"[package]
name = "demo"
kind = "app"

[build]
entry = "demo"
db = "sqlite"
ccompiler = "gcc"
boot = false

[style]
scss = "style/scss/main.scss"
css = "style/css/main.css"
"#;
        let cfg = parse_ur_toml_strict(content).expect("valid ur.toml");
        assert_eq!(cfg.package.kind, "app");
        assert_eq!(cfg.build.entry, "demo");
        assert!(cfg.style.is_some());
    }

    /// Omitted `[package].kind` must deserialize to `"app"` via [`default_pkg_kind`] (mutants on that default break orchestration).
    #[test]
    fn ur_toml_package_kind_defaults_to_app() {
        let content = r#"[package]
name = "nokind"

[build]
entry = "Main"
db = "sqlite"
"#;
        let cfg = parse_ur_toml_strict(content).expect("parse");
        assert_eq!(cfg.package.kind, "app");
    }

    /// Omitted `[build].db` uses [`default_build_db`] (`sqlite`).
    #[test]
    fn ur_toml_build_db_defaults_to_sqlite() {
        let content = r#"[package]
name = "x"
kind = "app"

[build]
entry = "Main"
"#;
        let cfg = parse_ur_toml_strict(content).expect("parse");
        assert_eq!(cfg.build.db, "sqlite");
    }

    #[test]
    fn ur_toml_strict_accepts_library_template_shape() {
        let content = r#"[package]
name = "mylib"
kind = "lib"

[build]
entry = "mylib"
boot = false
"#;
        assert!(parse_ur_toml_strict(content).is_ok());
    }

    #[test]
    fn ur_toml_strict_rejects_unknown_table_fields() {
        let content = r#"[package]
name = "x"
kind = "app"
wat = true

[build]
entry = "m"
"#;
        assert!(parse_ur_toml_strict(content).is_err());
    }

    #[test]
    fn toml_parse_basic() {
        let content = "[build]\nentry = \"myapp\"\ndb = \"sqlite\"\n";
        let entries = parse_toml(content);
        assert_eq!(
            entries
                .iter()
                .find(|(k, _)| k == "build.entry")
                .map(|(_, v)| v.as_str()),
            Some("myapp")
        );
    }

    #[test]
    fn toml_parse_section_and_key() {
        let content = "[build]\nentry = \"x\"\n";
        let entries = parse_toml(content);
        assert_eq!(toml_get(&entries, "build.entry"), Some("x"));
    }

    #[test]
    fn toml_get_missing_returns_none() {
        let entries = parse_toml("[build]\nentry = \"x\"\n");
        assert_eq!(toml_get(&entries, "build.other"), None);
        assert_eq!(toml_get(&entries, "missing"), None);
    }

    #[test]
    fn toml_parse_empty_line_skipped() {
        let content = "[a]\n\nkey = \"v\"\n";
        let entries = parse_toml(content);
        assert_eq!(toml_get(&entries, "a.key"), Some("v"));
    }

    #[test]
    fn toml_parse_quoted_value() {
        let content = r#"[x]
k = "hello""#;
        let entries = parse_toml(content);
        assert_eq!(toml_get(&entries, "x.k"), Some("hello"));
    }

    #[test]
    fn toml_comment_ignored() {
        let content = "# comment\n[build]\nentry = \"x\"\n";
        let entries = parse_toml(content);
        assert_eq!(entries.len(), 1);
    }

    #[test]
    fn toml_line_looks_like_comment_not_parsed_as_key() {
        let content = "#key = value\n[build]\nentry = \"x\"\n";
        let entries = parse_toml(content);
        assert!(!entries.iter().any(|(k, _)| k.starts_with('#')));
        assert_eq!(toml_get(&entries, "build.entry"), Some("x"));
    }

    #[test]
    fn toml_section_bracket_requires_both() {
        let content = "[build\nentry = \"x\"\n";
        let entries = parse_toml(content);
        assert_eq!(toml_get(&entries, "entry"), Some("x"));
    }

    #[test]
    fn is_lib_project_detects_lib() {
        assert!(is_lib_project("lib"));
        assert!(!is_lib_project("app"));
        assert!(!is_lib_project(""));
    }

    #[test]
    fn parse_boot_detects_true() {
        assert!(parse_boot("true"));
        assert!(!parse_boot("false"));
        assert!(!parse_boot(""));
    }

    #[test]
    fn should_add_ccompiler_when_non_empty() {
        assert!(should_add_ccompiler("gcc"));
        assert!(!should_add_ccompiler(""));
    }

    #[test]
    fn is_file_arg_accepts_ur_without_dash() {
        assert!(is_file_arg("m.ur"));
        assert!(!is_file_arg("-check"));
    }

    #[test]
    fn should_skip_urp_line_empty_and_comments() {
        assert!(should_skip_urp_line(""));
        assert!(should_skip_urp_line("# comment"));
        assert!(!should_skip_urp_line("mymod"));
    }

    #[test]
    fn is_unknown_compiler_flag_detects_flags() {
        assert!(is_unknown_compiler_flag("", "-"));
        assert!(is_unknown_compiler_flag("bad", "-bad"));
        assert!(!is_unknown_compiler_flag("myproj", "myproj"));
    }

    #[test]
    fn apply_verbosity_v_flag_increments_and_caps() {
        let mut s = crate::settings::Settings::new();
        apply_verbosity_v_flag(&mut s, "v");
        assert_eq!(s.verbosity, 1);
        apply_verbosity_v_flag(&mut s, "v");
        assert_eq!(s.verbosity, 2);
        apply_verbosity_v_flag(&mut s, "vvvvv");
        assert_eq!(s.verbosity, crate::compiler_tracing::MAX_COMPILER_VERBOSITY);
        apply_verbosity_v_flag(&mut s, "v");
        assert_eq!(s.verbosity, crate::compiler_tracing::MAX_COMPILER_VERBOSITY);
    }

    #[test]
    fn leading_build_verbosity_collects_prefix_only() {
        let args = vec![
            "-vv".to_string(),
            "-verbose".to_string(),
            "rest".to_string(),
        ];
        let v = leading_build_verbosity_flags(&args);
        assert_eq!(v.len(), 2);
        assert_eq!(v[0], "-vv");
    }

    #[test]
    fn is_valid_limit_non_negative() {
        assert!(is_valid_limit(0));
        assert!(is_valid_limit(1));
        assert!(!is_valid_limit(-1));
    }

    #[test]
    fn command_succeeded_ok_and_success() {
        let s = std::process::Command::new("true").status();
        assert!(command_succeeded(&s));
    }

    #[test]
    fn sass_tool_available_either_or() {
        assert!(sass_tool_available(true, false));
        assert!(sass_tool_available(false, true));
        assert!(sass_tool_available(true, true));
        assert!(!sass_tool_available(false, false));
    }

    #[test]
    fn file_exists_detects_present_and_absent() {
        let _guard = lock_for_compile(&TEST_CWD_LOCK, "cli_common file_exists test");
        let dir = tempfile::tempdir().unwrap();
        let cwd = std::env::current_dir().unwrap();
        std::env::set_current_dir(dir.path()).unwrap();
        std::fs::write("exists.txt", "").unwrap();
        assert!(file_exists("exists.txt"));
        assert!(!file_exists("nonexistent.txt"));
        std::env::set_current_dir(&cwd).unwrap();
    }

    #[test]
    fn command_succeeded_err_fails() {
        let s = std::process::Command::new("/nonexistent").status();
        assert!(!command_succeeded(&s));
    }

    #[test]
    fn toml_unclosed_quote_preserves_raw() {
        let content = "[x]\nk = \"hello\n";
        let entries = parse_toml(content);
        let v = toml_get(&entries, "x.k").unwrap();
        assert!(v.contains("hello"), "unclosed quote should not strip");
    }

    #[test]
    fn capitalize_helper() {
        assert_eq!(capitalize("hello"), "Hello");
        assert_eq!(capitalize(""), "");
        assert_eq!(capitalize("A"), "A");
    }

    #[test]
    fn kind_specific_created_files_app() {
        let files = kind_specific_created_files(ProjectKind::App, "foo");
        assert!(files.iter().any(|s| s.contains("style/scss")));
        assert!(!files.iter().any(|s| s.ends_with(".urs")));
    }

    #[test]
    fn kind_specific_created_files_library() {
        let files = kind_specific_created_files(ProjectKind::Library, "mylib");
        assert!(files.iter().any(|s| s.ends_with(".urs")));
        assert!(!files.iter().any(|s| s.contains("style/")));
    }

    #[test]
    fn package_spec_repo_leaf_skips_empty_segments() {
        assert_eq!(package_spec_repo_leaf("org/repo"), "repo");
        assert_eq!(package_spec_repo_leaf("org//repo"), "repo");
    }

    #[test]
    fn load_ur_manifest_cwd_ok_and_entry() {
        let _guard = lock_for_compile(&TEST_CWD_LOCK, "cli_common manifest load");
        let dir = tempfile::tempdir().unwrap();
        let cwd = std::env::current_dir().unwrap();
        std::env::set_current_dir(dir.path()).unwrap();
        std::fs::write(
            UR_MANIFEST_FILE,
            r#"[package]
kind = "app"
[build]
entry = "demo"
"#,
        )
        .unwrap();
        let cfg = load_ur_manifest_cwd().unwrap();
        assert_eq!(cfg.build.entry, "demo");
        assert!(require_manifest_entry(&cfg).is_ok());
        std::fs::write(
            UR_MANIFEST_FILE,
            r#"[package]
kind = "app"
[build]
entry = ""
"#,
        )
        .unwrap();
        let cfg_empty = load_ur_manifest_cwd().unwrap();
        assert!(require_manifest_entry(&cfg_empty).is_err());
        std::env::set_current_dir(&cwd).unwrap();
    }

    #[test]
    fn ensure_ur_toml_present_for_install_checks_file() {
        let _guard = lock_for_compile(&TEST_CWD_LOCK, "cli_common install manifest");
        let dir = tempfile::tempdir().unwrap();
        let cwd = std::env::current_dir().unwrap();
        std::env::set_current_dir(dir.path()).unwrap();
        assert!(super::ensure_ur_toml_present_for_install().is_err());
        std::fs::write(
            UR_MANIFEST_FILE,
            "[package]\nkind=\"app\"\n[build]\nentry=\"x\"\n",
        )
        .unwrap();
        assert!(super::ensure_ur_toml_present_for_install().is_ok());
        std::env::set_current_dir(&cwd).unwrap();
    }

    #[test]
    fn exec_peer_bin_missing_prints_path_error() {
        let code = exec_peer_bin("/nonexistent-peer-binary-ur-test", &[]);
        assert_eq!(code, 1);
    }
}
