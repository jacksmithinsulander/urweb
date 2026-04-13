//! Compilation settings parsed from Ur/Web `.urp` project files.
//!
//! [`crate::compiler::Job`] and [`Settings`] hold uniform resource locator prefixes, database options,
//! foreign function interface maps, and effect annotations. Rewrite rules filter by path or request shape.
//! Structured Query Language identifier mangling, protocol hooks, timeouts, and resolved `db_backend` live here too.
//!
//! Non-trivial methods document `# Arguments`, `# Returns`, and `# Errors` (or `# Panics`) where helpful;
//! one-field predicates usually omit headings.
//!
//! **Style:** new/edited Rust here follows [README.md](../README.md) Rust code style (exceptions documented there).

use std::collections::{BTreeMap, BTreeSet};

use uuid::Uuid;

use crate::db::{ProjectDb, ProjectDbCtx};
use crate::diagnostics::DiagnosticLocale;

/// An FFI function identifier: `(module_name, function_name)`.
pub type Ffi = (String, String);

/// Selects how much of the historical Ur/Web pipeline applies (surface syntax, glue, and backends).
///
/// `UrWeb` is the default full-stack profile. `UrCore` is an experimental stricter surface aimed at
/// separating the functional language from HTTP/SQL/JS codegen paths; full batch codegen still
/// aborts until a dedicated ur-core backend exists, but `ur-compile -tc` may run through core verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LanguageCompilationProfile {
    /// Full Ur/Web: XML literals, project export glue, RPC rewrite, JS client bundle, C/SQL output.
    #[default]
    UrWeb,
    /// Ur language focus: no XML markup lexing in user modules, no auto-export, no project DB injection.
    UrCore,
}

impl LanguageCompilationProfile {
    /// Returns true when the lexer may enter XML modes for `<tag>...</tag>` inside user `.ur` files.
    pub fn allows_xml_surface_markup(self) -> bool {
        matches!(self, Self::UrWeb)
    }

    /// Returns true when [`crate::compiler::parse_sources_inner`] should append `export` for the last module.
    pub fn injects_last_module_export(self) -> bool {
        matches!(self, Self::UrWeb)
    }

    /// Returns true when a `database` line from the job file becomes a top-level `Decl::Database`.
    pub fn injects_project_database_declaration(self) -> bool {
        matches!(self, Self::UrWeb)
    }

    /// Returns true when the native-surface FFI shim is prepended for selected backends.
    pub fn injects_urweb_native_prelude(self) -> bool {
        matches!(self, Self::UrWeb)
    }

    /// Returns true when `core_rpcify` should rewrite `Basis.rpc` applications.
    pub fn runs_rpc_elaboration_pass(self) -> bool {
        matches!(self, Self::UrWeb)
    }

    /// Returns true when `js_compile` should walk the mono file for client code.
    pub fn runs_javascript_compilation(self) -> bool {
        matches!(self, Self::UrWeb)
    }

    /// Returns true when `compile` / `compile_to_outputs` must refuse to run the full codegen pipeline.
    pub fn blocks_batch_codegen_pipeline(self) -> bool {
        matches!(self, Self::UrCore)
    }
}

impl std::str::FromStr for LanguageCompilationProfile {
    type Err = ();

    /// Parses case-insensitive `ur-web` / `urweb` and `ur-core` / `urcore`.
    fn from_str(raw: &str) -> Result<Self, Self::Err> {
        let normalized = raw.trim().to_ascii_lowercase();
        match normalized.as_str() {
            "ur-web" | "urweb" => Ok(Self::UrWeb),
            "ur-core" | "urcore" => Ok(Self::UrCore),
            _ => Err(()),
        }
    }
}

// ---------------------------------------------------------------------------
// Pattern matching helpers
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternKind {
    Exact,
    Prefix,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Action {
    Allow,
    Deny,
}

#[derive(Debug, Clone)]
pub struct Rule {
    pub action: Action,
    pub kind: PatternKind,
    pub pattern: String,
}

impl Rule {
    pub fn matches(&self, s: &str) -> bool {
        match self.kind {
            PatternKind::Exact => self.pattern == s,
            PatternKind::Prefix => s.starts_with(&*self.pattern),
        }
    }
}

// ---------------------------------------------------------------------------
// Path-kind rewriting
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathKind {
    Any,
    Url,
    Table,
    Sequence,
    View,
    Relation,
    Cookie,
    Style,
}

#[derive(Debug, Clone)]
pub struct Rewrite {
    pub pkind: PathKind,
    pub kind: PatternKind,
    pub from: String,
    pub to: String,
    pub hyphenate: bool,
}

pub(crate) fn subsumes(pk1: &PathKind, pk2: &PathKind) -> bool {
    pk1 == pk2
        || *pk2 == PathKind::Any
        || (*pk2 == PathKind::Relation
            && (*pk1 == PathKind::Table || *pk1 == PathKind::Sequence || *pk1 == PathKind::View))
}

// ---------------------------------------------------------------------------
// SQL types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SqlType {
    Int,
    Float,
    String,
    Char,
    Bool,
    Time,
    Clocktime,
    Calendardate,
    Blob,
    Channel,
    Client,
    Nullable(Box<SqlType>),
}

impl SqlType {
    pub fn c_type(&self) -> std::string::String {
        match self {
            SqlType::Int => "uw_Basis_int".into(),
            SqlType::Float => "uw_Basis_float".into(),
            SqlType::String => "uw_Basis_string".into(),
            SqlType::Char => "uw_Basis_char".into(),
            SqlType::Bool => "uw_Basis_bool".into(),
            SqlType::Time => "uw_Basis_time".into(),
            SqlType::Clocktime => "uw_Basis_clocktime".into(),
            SqlType::Calendardate => "uw_Basis_calendardate".into(),
            SqlType::Blob => "uw_Basis_blob".into(),
            SqlType::Channel => "uw_Basis_channel".into(),
            SqlType::Client => "uw_Basis_client".into(),
            SqlType::Nullable(t) => match t.as_ref() {
                SqlType::String => "uw_Basis_string".into(),
                inner => format!("{}*", inner.c_type()),
            },
        }
    }

    pub fn is_blob(&self) -> bool {
        match self {
            SqlType::Blob => true,
            SqlType::Nullable(t) => t.is_blob(),
            _ => false,
        }
    }

    pub fn is_not_null(&self) -> bool {
        !matches!(self, SqlType::Nullable(_))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FailureMode {
    Error,
    None,
}

// ---------------------------------------------------------------------------
// Main Settings struct
// ---------------------------------------------------------------------------

/// Compiler-wide settings (replaces global `ref` cells in settings.sml).
#[derive(Debug, Clone)]
pub struct Settings {
    // Paths
    pub config_bin: String,
    pub config_lib: String,
    pub config_src_lib: String,
    pub config_include: String,
    pub config_sitelisp: String,
    pub config_libunistring_includes: String,
    pub config_libunistring_libs: String,
    pub config_bearssl_ldflags: String,
    pub config_bearssl_libs: String,
    pub config_c_compiler: String,

    // URL
    pub url_prefix_full: String,
    pub url_prefix: String,
    pub url_pre_prefix: String,

    // Runtime
    pub timeout: u32,
    pub disable_sql_structure_check: bool,
    pub headers: Vec<String>,
    pub scripts: Vec<String>,

    // FFI sets
    pub client_to_server: BTreeSet<Ffi>,
    pub effectful: BTreeSet<Ffi>,
    pub benign: BTreeSet<Ffi>,
    pub client_only: BTreeSet<Ffi>,
    pub server_only: BTreeSet<Ffi>,

    // JavaScript function map
    pub js_funcs: BTreeMap<Ffi, String>,
    pub js_module: Option<String>,

    // Path rules
    pub rewrites: Vec<Rewrite>,
    pub url_rules: Vec<Rule>,
    pub mime_rules: Vec<Rule>,
    pub request_rules: Vec<Rule>,
    pub response_rules: Vec<Rule>,
    pub env_rules: Vec<Rule>,
    pub meta_rules: Vec<Rule>,

    // Current protocol / database backend (`None` = legacy unset → Postgres family at resolve)
    pub protocol: String,
    pub db_backend: Option<ProjectDb>,

    // Output targets
    pub dbstring: Option<String>,
    pub exe: Option<String>,
    pub sql: Option<String>,
    pub endpoints: Option<String>,

    // Optimisation levels
    pub core_inline: u32,
    pub mono_inline: u32,

    // Linking
    pub static_linking: bool,
    pub boot_linking: bool,

    // Deadlines
    pub deadlines: bool,
    pub sig_file: Option<String>,
    pub file_cache: Option<String>,

    // Safe-GET whitelist
    pub safe_get_default: bool,
    pub safe_gets: BTreeSet<String>,

    // On-error handler
    pub on_error: Option<(String, Vec<String>, String)>,

    // Resource limits: (name, value)
    pub limits: Vec<(String, i32)>,
    pub min_heap: u32,

    // Inlining overrides
    pub always_inline: BTreeSet<String>,
    pub never_inline: BTreeSet<String>,

    // XSRF
    pub no_xsrf_protection: BTreeSet<String>,

    // Time formatting
    pub time_format: String,

    // SQL name mangling
    pub mangle: bool,

    // HTML5
    pub html5: bool,

    // Less-safe FFI
    pub less_safe_ffi: bool,

    // SQL cache
    pub sqlcache: bool,

    // MIME types path
    pub mime_file_path: String,

    // Debug
    pub debug: bool,

    /// Foundry-style `-v` … `-vvvvv` (capped at [`crate::compiler_tracing::MAX_COMPILER_VERBOSITY`]); `0` keeps default tracing quiet unless `RUST_LOG` is set.
    pub verbosity: u8,

    /// Legacy `-timing`: print coarse phase wall times on stderr; also enabled when `verbosity >= 4`.
    pub emit_phase_timing: bool,

    /// User-facing diagnostic language from `ur.toml` `[package].language` (`en` / `sv` / `es`).
    pub diagnostic_locale: DiagnosticLocale,

    /// Ur vs Ur/Web pipeline selection (`-languageProfile` on `ur-compile`; default `ur-web`).
    pub language_compilation_profile: LanguageCompilationProfile,

    /// When true, batch `compile` / `compile_to_outputs` stop after core verification (`-tc` on `ur-compile`).
    pub typecheck_only: bool,

    /// UUID v4 minted by [`Self::begin_compilation_job`] at the start of each batch pipeline or LSP analysis snapshot.
    ///
    /// Empty string before [`Self::begin_compilation_job`] runs; language server work clones settings,
    /// mints a fresh id per snapshot, and passes it through [`crate::error_types::ErrorReporter`]
    /// without putting it in editor-facing diagnostic text.
    pub compilation_id: String,

    // Static files
    pub file_path: String,
    pub js_output: Option<String>,
}

fn basis_ffi_set(names: &[&str]) -> BTreeSet<Ffi> {
    names
        .iter()
        .map(|s| ("Basis".into(), s.to_string()))
        .collect()
}

fn basis_js_map(pairs: &[(&str, &str)]) -> BTreeMap<Ffi, String> {
    pairs
        .iter()
        .map(|(k, v)| (("Basis".into(), k.to_string()), v.to_string()))
        .collect()
}

impl Settings {
    /// Default compilation settings (built-in Foreign Function Interface sets, rules, limits, paths).
    ///
    /// # Returns
    ///
    /// Fresh [`Settings`] as if no `.urp` overrides were applied yet.
    pub fn new() -> Self {
        let client_to_server_base = basis_ffi_set(&[
            "int",
            "float",
            "string",
            "char",
            "time",
            "clocktime",
            "calendardate",
            "file",
            "unit",
            "option",
            "list",
            "bool",
            "variant",
        ]);
        let effectful_base = basis_ffi_set(&[
            "dml",
            "nextval",
            "setval",
            "set_cookie",
            "clear_cookie",
            "new_channel",
            "send",
            "htmlifyInt_w",
            "htmlifyFloat_w",
            "htmlifyString_w",
            "htmlifyBool_w",
            "htmlifyTime_w",
            "attrifyInt_w",
            "attrifyFloat_w",
            "attrifyString_w",
            "attrifyChar_w",
            "urlifyInt_w",
            "urlifyFloat_w",
            "urlifyString_w",
            "urlifyBool_w",
            "urlifyChannel_w",
        ]);
        let benign_base = basis_ffi_set(&[
            "get_cookie",
            "getenv",
            "new_client_source",
            "get_client_source",
            "set_client_source",
            "current",
            "alert",
            "confirm",
            "onError",
            "onFail",
            "onConnectFail",
            "onDisconnect",
            "onServerError",
            "mouseEvent",
            "keyEvent",
            "debug",
            "rand",
            "now",
            "getCurrentLocalCalendardate",
            "getCurrentLocalClocktime",
            "getCurrentUTCCalendardate",
            "getCurrentUTCClocktime",
            "getHeader",
            "setHeader",
            "spawn",
            "onClick",
            "onDblclick",
            "onContextmenu",
            "onKeydown",
            "onKeypress",
            "onKeyup",
            "onMousedown",
            "onMouseenter",
            "onMouseleave",
            "onMousemove",
            "onMouseout",
            "onMouseover",
            "onMouseup",
            "preventDefault",
            "stopPropagation",
            "fresh",
            "giveFocus",
            "currentUrlHasPost",
            "currentUrlHasQueryString",
            "currentUrl",
        ]);
        let client_base = basis_ffi_set(&[
            "get_client_source",
            "current",
            "alert",
            "confirm",
            "recv",
            "sleep",
            "spawn",
            "onError",
            "onFail",
            "onConnectFail",
            "onDisconnect",
            "onServerError",
            "mouseEvent",
            "keyEvent",
            "onClick",
            "onContextmenu",
            "onDblclick",
            "onKeydown",
            "onKeypress",
            "onKeyup",
            "onMousedown",
            "onMouseenter",
            "onMouseleave",
            "onMousemove",
            "onMouseout",
            "onMouseover",
            "onMouseup",
            "preventDefault",
            "stopPropagation",
            "giveFocus",
        ]);
        let server_base = basis_ffi_set(&[
            "requestHeader",
            "query",
            "dml",
            "nextval",
            "setval",
            "channel",
            "send",
            "fieldName",
            "fieldValue",
            "remainingFields",
            "firstFormField",
        ]);
        let js_funcs_base = basis_js_map(&[
            ("alert", "alert"),
            ("stringToTime", "stringToTime"),
            ("stringToTime_error", "stringToTime_error"),
            ("timef", "strftime"),
            ("confirm", "confrm"),
            ("get_client_source", "sg"),
            ("current", "scur"),
            ("htmlifyBool", "bs"),
            ("htmlifyFloat", "ts"),
            ("htmlifyInt", "ts"),
            ("htmlifyString", "eh"),
            ("new_client_source", "sc"),
            ("set_client_source", "sv"),
            ("stringToFloat", "pflo"),
            ("stringToInt", "pio"),
            ("stringToFloat_error", "pfl"),
            ("stringToInt_error", "pi"),
            ("urlifyInt", "ts"),
            ("urlifyFloat", "ts"),
            ("urlifyTime", "ts"),
            ("urlifyClocktime", "urlifyClocktime"),
            ("urlifyCalendardate", "urlifyCalendardate"),
            ("getCurrentLocalClocktime", "getCurrentLocalClocktime"),
            ("getCurrentUTCClocktime", "getCurrentUTCClocktime"),
            ("getMinuteFromClocktime", "getMinuteFromClocktime"),
            ("getHourFromClocktime", "getHourFromClocktime"),
            ("makeClocktime", "makeClocktime"),
            ("addSecondsToClocktime", "addSecondsToClocktime"),
            ("getCurrentLocalCalendardate", "getCurrentLocalCalendardate"),
            ("getCurrentUTCCalendardate", "getCurrentUTCCalendardate"),
            ("getYearFromCalendardate", "getYearFromCalendardate"),
            ("getMonthFromCalendardate", "getMonthFromCalendardate"),
            ("getDayFromCalendardate", "getDayFromCalendardate"),
            ("makeCalendardate", "makeCalendardate"),
            ("addDaysToCalendardate", "addDaysToCalendardate"),
            ("urlifyString", "uf"),
            ("urlifyChar", "uf"),
            ("urlifyBool", "ub"),
            ("recv", "rv"),
            ("strcat", "cat"),
            ("intToString", "ts"),
            ("floatToString", "ts"),
            ("charToString", "ts"),
            ("onError", "onError"),
            ("onFail", "onFail"),
            ("onConnectFail", "onConnectFail"),
            ("onDisconnect", "onDisconnect"),
            ("onServerError", "onServerError"),
            ("attrifyString", "atr"),
            ("attrifyInt", "ts"),
            ("attrifyFloat", "ts"),
            ("attrifyBool", "bs"),
            ("boolToString", "bs"),
            ("str1", "id"),
            ("strsub", "sub"),
            ("strsubUtf8", "subUtf8"),
            ("strsuffixUtf8", "sufUtf8"),
            ("strsuffix", "suf"),
            ("strlenUtf8", "slenUtf8"),
            ("strlen", "slen"),
            ("strindex", "sidx"),
            ("strsindex", "ssidx"),
            ("strchr", "schr"),
            ("substring", "ssub"),
            ("strcspn", "sspn"),
            ("strlenGe", "strlenGe"),
            ("mouseEvent", "uw_mouseEvent"),
            ("keyEvent", "uw_keyEvent"),
            ("minTime", "0"),
            ("stringToBool_error", "s2be"),
            ("stringToBool", "s2b"),
            ("islower", "isLower"),
            ("isupper", "isUpper"),
            ("isalpha", "isAlpha"),
            ("isdigit", "isDigit"),
            ("isalnum", "isAlnum"),
            ("isblank", "isBlank"),
            ("isspace", "isSpace"),
            ("isxdigit", "isXdigit"),
            ("isprint", "isPrint"),
            ("tolower", "toLower"),
            ("toupper", "toUpper"),
            ("ord", "ord"),
            ("checkUrl", "checkUrl"),
            ("anchorUrl", "anchorUrl"),
            ("bless", "bless"),
            ("blessData", "blessData"),
            ("currentUrl", "currentUrl"),
            ("eq_time", "eq"),
            ("lt_time", "lt"),
            ("le_time", "le"),
            ("eq_calendardate", "eqCalendardate"),
            ("lt_calendardate", "ltCalendardate"),
            ("le_calendardate", "leCalendardate"),
            ("eq_clocktime", "eqClocktime"),
            ("lt_clocktime", "ltClocktime"),
            ("le_clocktime", "leClocktime"),
            ("debug", "uw_debug"),
            ("naughtyDebug", "uw_debug"),
            ("floatFromInt", "float"),
            ("ceil", "ceil"),
            ("trunc", "trunc"),
            ("round", "round"),
            ("floor", "floor"),
            ("pow", "pow"),
            ("sqrt", "sqrt"),
            ("sin", "sin"),
            ("cos", "cos"),
            ("log", "log"),
            ("exp", "exp"),
            ("asin", "asin"),
            ("acos", "acos"),
            ("atan", "atan"),
            ("atan2", "atan2"),
            ("abs", "abs"),
            ("now", "now"),
            ("timeToString", "showTime"),
            ("htmlifyTime", "showTimeHtml"),
            ("toSeconds", "toSeconds"),
            ("addSeconds", "addSeconds"),
            ("diffInSeconds", "diffInSeconds"),
            ("toMilliseconds", "toMilliseconds"),
            ("fromMilliseconds", "fromMilliseconds"),
            ("diffInMilliseconds", "diffInMilliseconds"),
            ("fromDatetime", "fromDatetime"),
            ("datetimeYear", "datetimeYear"),
            ("datetimeMonth", "datetimeMonth"),
            ("datetimeDay", "datetimeDay"),
            ("datetimeHour", "datetimeHour"),
            ("datetimeMinute", "datetimeMinute"),
            ("datetimeSecond", "datetimeSecond"),
            ("datetimeDayOfWeek", "datetimeDayOfWeek"),
            ("onClick", "uw_onClick"),
            ("onContextmenu", "uw_onContextmenu"),
            ("onDblclick", "uw_onDblclick"),
            ("onKeydown", "uw_onKeydown"),
            ("onKeypress", "uw_onKeypress"),
            ("onKeyup", "uw_onKeyup"),
            ("onMousedown", "uw_onMousedown"),
            ("onMouseenter", "uw_onMouseenter"),
            ("onMouseleave", "uw_onMouseleave"),
            ("onMousemove", "uw_onMousemove"),
            ("onMouseout", "uw_onMouseout"),
            ("onMouseover", "uw_onMouseover"),
            ("onMouseup", "uw_onMouseup"),
            ("preventDefault", "uw_preventDefault"),
            ("stopPropagation", "uw_stopPropagation"),
            ("fresh", "fresh"),
            ("atom", "atom"),
            ("css_url", "css_url"),
            ("property", "property"),
            ("giveFocus", "giveFocus"),
            ("htmlifySpecialChar", "htmlifySpecialChar"),
            ("chr", "chr"),
        ]);

        Settings {
            config_bin: String::new(),
            config_lib: String::new(),
            config_src_lib: String::new(),
            config_include: String::new(),
            config_sitelisp: String::new(),
            config_libunistring_includes: String::new(),
            config_libunistring_libs: String::new(),
            config_bearssl_ldflags: String::new(),
            config_bearssl_libs: String::new(),
            config_c_compiler: "cc".into(),
            url_prefix_full: "/".into(),
            url_prefix: "/".into(),
            url_pre_prefix: String::new(),
            timeout: 0,
            disable_sql_structure_check: false,
            headers: vec![],
            scripts: vec![],
            client_to_server: client_to_server_base,
            effectful: effectful_base,
            benign: benign_base,
            client_only: client_base,
            server_only: server_base,
            js_funcs: js_funcs_base,
            js_module: None,
            rewrites: vec![],
            url_rules: vec![],
            mime_rules: vec![],
            request_rules: vec![],
            response_rules: vec![],
            env_rules: vec![],
            meta_rules: vec![],
            protocol: String::new(),
            db_backend: None,
            dbstring: None,
            exe: None,
            sql: None,
            endpoints: None,
            core_inline: 5,
            mono_inline: 5,
            static_linking: true,
            boot_linking: false,
            deadlines: false,
            sig_file: None,
            file_cache: None,
            safe_get_default: false,
            safe_gets: BTreeSet::new(),
            on_error: None,
            limits: vec![],
            min_heap: 0,
            always_inline: BTreeSet::new(),
            never_inline: BTreeSet::new(),
            no_xsrf_protection: BTreeSet::new(),
            time_format: "%c".into(),
            mangle: true,
            html5: true,
            less_safe_ffi: false,
            sqlcache: false,
            mime_file_path: "/etc/mime.types".into(),
            debug: false,
            verbosity: 0,
            emit_phase_timing: false,
            diagnostic_locale: DiagnosticLocale::default(),
            language_compilation_profile: LanguageCompilationProfile::default(),
            typecheck_only: false,
            compilation_id: String::new(), // Filled by [`Self::begin_compilation_job`] when a pipeline starts.
            file_path: ".".into(),
            js_output: None,
        }
    }

    /// Mint a new RFC 4122 UUID v4 and assign it to [`Self::compilation_id`].
    ///
    /// Call once at the start of each batch compile pipeline or analysis snapshot so diagnostics and
    /// [`tracing`] events can be correlated for that job.
    pub fn begin_compilation_job(&mut self) {
        self.compilation_id = Uuid::new_v4().to_string(); // Fresh random id for this compile or analysis pass.
    }

    // -----------------------------------------------------------------------
    // URL prefix
    // -----------------------------------------------------------------------

    /// Normalize `p` into `url_prefix`, `url_pre_prefix`, and `url_prefix_full` (adds trailing `/`, splits `http(s)://`).
    ///
    /// # Arguments
    ///
    /// * `p` — User-supplied prefix string (may be empty or include a scheme).
    pub fn set_url_prefix(&mut self, p: &str) {
        let prefix = if p.is_empty() {
            "/".to_string()
        } else if !p.ends_with('/') {
            format!("{}/", p)
        } else {
            p.to_string()
        };

        let (prepre, prefix) = if prefix.starts_with("http://") {
            Self::split_prefix(&prefix, 7)
        } else if prefix.starts_with("https://") {
            Self::split_prefix(&prefix, 8)
        } else {
            (String::new(), prefix)
        };

        self.url_prefix_full = p.to_string();
        self.url_pre_prefix = prepre;
        self.url_prefix = prefix;
    }

    fn split_prefix(prefix: &str, skip: usize) -> (String, String) {
        let after_scheme = &prefix[skip..];
        if let Some(slash) = after_scheme.find('/') {
            let prepre = prefix[..skip + slash].to_string();
            let rest = prefix[skip + slash..].to_string();
            (prepre, rest)
        } else {
            (String::new(), prefix.to_string())
        }
    }

    // -----------------------------------------------------------------------
    // SQL name mangling
    // -----------------------------------------------------------------------

    /// Effective database backend after resolving `None` (legacy empty `dbms`) to Postgres-style.
    ///
    /// # Returns
    ///
    /// [`ProjectDb`] chosen from [`Settings::db_backend`] and project defaults.
    pub fn resolved_db_backend(&self) -> ProjectDb {
        ProjectDbCtx::new(&self.db_backend).resolved()
    }

    pub fn mangle_sql_table(&self, s: &str) -> String {
        ProjectDbCtx::new(&self.db_backend).mangle_sql_table(self.mangle, s)
    }

    pub fn mangle_sql(&self, s: &str) -> String {
        ProjectDbCtx::new(&self.db_backend).mangle_sql_ident(self.mangle, s)
    }

    // -----------------------------------------------------------------------
    // Effectfulness queries
    // -----------------------------------------------------------------------

    pub fn is_effectful(&self, ffi: &Ffi) -> bool {
        ffi.0 == "Sqlcache" || self.effectful.contains(ffi)
    }

    pub fn may_client_to_server(&self, ffi: &Ffi) -> bool {
        self.client_to_server.contains(ffi)
    }

    pub fn is_benign_effectful(&self, ffi: &Ffi) -> bool {
        self.benign.contains(ffi)
    }

    pub fn is_client_only(&self, ffi: &Ffi) -> bool {
        self.client_only.contains(ffi)
    }

    pub fn is_server_only(&self, ffi: &Ffi) -> bool {
        self.server_only.contains(ffi)
    }

    pub fn js_func(&self, ffi: &Ffi) -> Option<&str> {
        self.js_funcs.get(ffi).map(|s| s.as_str())
    }

    // -----------------------------------------------------------------------
    // URL / MIME checking
    // -----------------------------------------------------------------------

    fn check_rules(rules: &[Rule], s: &str) -> bool {
        rules
            .iter()
            .find(|r| r.matches(s))
            .is_some_and(|r| r.action == Action::Allow)
    }

    pub fn check_url(&self, s: &str) -> bool {
        Self::check_rules(&self.url_rules, s)
    }

    pub fn check_mime(&self, s: &str) -> bool {
        Self::is_valid_mime(s) && Self::check_rules(&self.mime_rules, s)
    }

    pub fn check_request_header(&self, s: &str) -> bool {
        Self::is_valid_mime(s) && Self::check_rules(&self.request_rules, s)
    }

    pub fn check_response_header(&self, s: &str) -> bool {
        Self::is_valid_mime(s) && Self::check_rules(&self.response_rules, s)
    }

    pub fn check_env_var(&self, s: &str) -> bool {
        Self::is_valid_env(s) && Self::check_rules(&self.env_rules, s)
    }

    pub fn check_meta(&self, s: &str) -> bool {
        Self::is_valid_meta(s) && Self::check_rules(&self.meta_rules, s)
    }

    /// Return true if the current protocol uses persistent connections (fastcgi, http).
    /// Persistent protocols use `PQexecPrepared`; non-persistent use `PQexecParams`.
    pub fn persistent(&self) -> bool {
        matches!(self.protocol.as_str(), "fastcgi" | "http")
    }

    pub(crate) fn is_valid_mime(s: &str) -> bool {
        s.chars()
            .all(|c| c.is_alphanumeric() || matches!(c, '/' | '-' | '.' | '+'))
    }

    pub(crate) fn is_valid_env(s: &str) -> bool {
        s.chars()
            .all(|c| c.is_alphanumeric() || matches!(c, '_' | '.'))
    }

    pub(crate) fn is_valid_meta(s: &str) -> bool {
        s.chars().all(|c| c.is_alphabetic() || c == '-')
    }

    // -----------------------------------------------------------------------
    // Path rewriting
    // -----------------------------------------------------------------------

    /// Apply the first matching rewrite in [`Settings::rewrites`] for `pk`, or return `s` unchanged.
    ///
    /// # Arguments
    ///
    /// * `pk` — Kind of path (URL, table, style, etc.).
    /// * `s` — Input string before rewriting.
    ///
    /// # Returns
    ///
    /// Rewritten string, optionally with underscores replaced by hyphens per rule.
    pub fn rewrite(&self, pk: &PathKind, s: &str) -> String {
        for rewr in &self.rewrites {
            if subsumes(pk, &rewr.pkind) {
                let matched_len = match rewr.kind {
                    PatternKind::Exact => {
                        if rewr.from == s {
                            Some(s.len())
                        } else {
                            None
                        }
                    }
                    PatternKind::Prefix => {
                        if s.starts_with(&*rewr.from) {
                            Some(rewr.from.len())
                        } else {
                            None
                        }
                    }
                };
                if let Some(suffix_start) = matched_len {
                    let result = format!("{}{}", rewr.to, &s[suffix_start..]);
                    return if rewr.hyphenate {
                        result.replace('_', "-")
                    } else {
                        result
                    };
                }
            }
        }
        s.to_string()
    }

    // -----------------------------------------------------------------------
    // Limits
    // -----------------------------------------------------------------------

    pub const VALID_LIMITS: &'static [&'static str] = &[
        "messages",
        "clients",
        "headers",
        "page",
        "heap",
        "script",
        "inputs",
        "subinputs",
        "cleanup",
        "deltas",
        "transactionals",
        "globals",
        "database",
        "time",
    ];

    /// Append a resource limit if `name` is in [`Settings::VALID_LIMITS`].
    ///
    /// # Arguments
    ///
    /// * `name` — Limit category (e.g. `messages`, `heap`).
    /// * `value` — Numeric bound for that category.
    ///
    /// # Errors
    ///
    /// Returns an error string when `name` is not a known limit.
    ///
    /// # Returns
    ///
    /// `Ok(())` after pushing `(name, value)`; enables deadlines when `name` is `time`.
    pub fn add_limit(&mut self, name: &str, value: i32) -> Result<(), String> {
        if Self::VALID_LIMITS.contains(&name) {
            self.limits.push((name.to_string(), value));
            if name == "time" {
                self.deadlines = true;
            }
            Ok(())
        } else {
            Err(format!("Unknown limit category '{}'", name))
        }
    }

    pub fn is_safe_get(&self, path: &str) -> bool {
        self.safe_get_default || self.safe_gets.contains(path)
    }
}

impl Default for Settings {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subsumes_same_kind() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(subsumes(&PathKind::Table, &PathKind::Table));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn subsumes_any_accepts_all() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(subsumes(&PathKind::Url, &PathKind::Any));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn subsumes_relation_accepts_table() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(subsumes(&PathKind::Table, &PathKind::Relation));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn subsumes_relation_rejects_url() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(!subsumes(&PathKind::Url, &PathKind::Relation));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn persistent_true_for_fastcgi() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.protocol = "fastcgi".into();
        assert!(s.persistent(), "fastcgi must be persistent");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn persistent_true_for_http() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.protocol = "http".into();
        assert!(s.persistent());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn persistent_false_for_cgi() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.protocol = "cgi".into();
        assert!(!s.persistent());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn subsumes_relation_accepts_sequence_and_view() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(subsumes(&PathKind::Sequence, &PathKind::Relation));
        assert!(subsumes(&PathKind::View, &PathKind::Relation));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn url_prefix_slash() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.set_url_prefix("/app");
        assert_eq!(s.url_prefix, "/app/");
        assert_eq!(s.url_pre_prefix, "");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn url_prefix_http() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.set_url_prefix("http://example.com/app");
        assert_eq!(s.url_pre_prefix, "http://example.com");
        assert_eq!(s.url_prefix, "/app/");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mangle_sql_table_postgres() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.db_backend = Some(ProjectDb::postgres());
        assert_eq!(s.mangle_sql_table("users"), "uw_Users");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mangle_sql_table_mysql() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.db_backend = Some(ProjectDb::mysql());
        assert_eq!(s.mangle_sql_table("Users"), "uw_users");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mangle_no_mangle() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.db_backend = Some(ProjectDb::postgres());
        s.mangle = false;
        assert_eq!(s.mangle_sql_table("FooBar"), "fooBar");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mangle_sql_mysql_vs_postgres() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s_mysql = Settings::new();
        s_mysql.db_backend = Some(ProjectDb::mysql());
        s_mysql.mangle = true;
        let mut s_pg = Settings::new();
        s_pg.db_backend = Some(ProjectDb::postgres());
        s_pg.mangle = true;
        assert_eq!(s_mysql.mangle_sql("Foo"), "uw_foo");
        assert_eq!(s_pg.mangle_sql("Foo"), "uw_Foo");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_effectful_false_when_not_in_set() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(!s.is_effectful(&("Other".into(), "fn".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_benign_effectful_false_when_empty() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(!s.is_benign_effectful(&("X".into(), "y".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_client_only_false_when_empty() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(!s.is_client_only(&("X".into(), "y".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_server_only_false_when_empty() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(!s.is_server_only(&("X".into(), "y".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_url_with_rules() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.url_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "/api".into(),
        });
        assert!(s.check_url("/api"));
        assert!(!s.check_url("/other"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_mime_valid_and_rules() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.mime_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "text/plain".into(),
        });
        assert!(s.check_mime("text/plain"));
        assert!(!s.check_mime("text/x"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_mime_requires_valid_chars() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.mime_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "text/plain!".into(),
        });
        assert!(
            !s.check_mime("text/plain!"),
            "invalid mime char ! must fail"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_valid_env_rejects_hyphen() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(!Settings::is_valid_env("FOO-BAR"));
        assert!(Settings::is_valid_env("FOO_BAR"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_valid_meta_allows_hyphen_rejects_digit() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(Settings::is_valid_meta("content-type"));
        assert!(!Settings::is_valid_meta("meta2"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_request_header_valid() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.request_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "X-Foo".into(),
        });
        assert!(s.check_request_header("X-Foo"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_request_header_invalid_mime_fails() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.request_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "X-Foo!".into(),
        });
        assert!(!s.check_request_header("X-Foo!"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_response_header_invalid_mime_fails() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.response_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "X-Bad!".into(),
        });
        assert!(!s.check_response_header("X-Bad!"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_env_var_invalid_chars_fails() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.env_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "FOO-BAR".into(),
        });
        assert!(!s.check_env_var("FOO-BAR"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_meta_invalid_chars_fails() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.meta_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "meta2".into(),
        });
        assert!(!s.check_meta("meta2"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_response_header_valid() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.response_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "Content-Type".into(),
        });
        assert!(s.check_response_header("Content-Type"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_env_var_valid() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.env_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "FOO_BAR".into(),
        });
        assert!(s.check_env_var("FOO_BAR"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_meta_valid() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.meta_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "description".into(),
        });
        assert!(s.check_meta("description"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn rewrite_exact_match() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.rewrites.push(Rewrite {
            pkind: PathKind::Any,
            kind: PatternKind::Exact,
            from: "foo".into(),
            to: "bar".into(),
            hyphenate: false,
        });
        assert_eq!(s.rewrite(&PathKind::Url, "foo"), "bar");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn effectful_sqlcache() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(s.is_effectful(&("Sqlcache".into(), "anything".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn effectful_basis_dml() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(s.is_effectful(&("Basis".into(), "dml".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn client_only_recv() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(s.is_client_only(&("Basis".into(), "recv".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn add_limit_valid() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.add_limit("page", 1024).map_err(anyhow::Error::msg)?;
        assert_eq!(s.limits.len(), 1);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn add_limit_invalid() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        assert!(s.add_limit("bogus", 0).is_err());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn add_limit_time_sets_deadlines() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.add_limit("time", 30).map_err(anyhow::Error::msg)?;
        assert!(s.deadlines);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn rewrite_prefix() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.rewrites.push(Rewrite {
            pkind: PathKind::Any,
            kind: PatternKind::Prefix,
            from: "foo".into(),
            to: "bar".into(),
            hyphenate: false,
        });
        assert_eq!(s.rewrite(&PathKind::Url, "foobar"), "barbar");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn rewrite_hyphenate() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.rewrites.push(Rewrite {
            pkind: PathKind::Any,
            kind: PatternKind::Prefix,
            from: String::new(),
            to: String::new(),
            hyphenate: true,
        });
        assert_eq!(s.rewrite(&PathKind::Url, "foo_bar"), "foo-bar");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn rule_matches_exact() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let r = Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "foo".into(),
        };
        assert!(r.matches("foo"));
        assert!(!r.matches("foobar"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn rule_matches_prefix() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let r = Rule {
            action: Action::Allow,
            kind: PatternKind::Prefix,
            pattern: "foo".into(),
        };
        assert!(r.matches("foobar"));
        assert!(!r.matches("bar"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sql_type_is_blob() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(SqlType::Blob.is_blob());
        assert!(!SqlType::Int.is_blob());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sql_type_nullable_blob_is_blob() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(SqlType::Nullable(Box::new(SqlType::Blob)).is_blob());
        assert!(!SqlType::Nullable(Box::new(SqlType::Int)).is_blob());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sql_type_is_not_null() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(SqlType::Int.is_not_null());
        assert!(!SqlType::Nullable(Box::new(SqlType::Int)).is_not_null());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn may_client_to_server() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.client_to_server.insert(("M".into(), "f".into()));
        assert!(s.may_client_to_server(&("M".into(), "f".into())));
        assert!(!s.may_client_to_server(&("M".into(), "g".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_benign_effectful() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(s.is_benign_effectful(&("Basis".into(), "get_cookie".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_client_only() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(s.is_client_only(&("Basis".into(), "recv".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_server_only() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert!(s.is_server_only(&("Basis".into(), "dml".into())));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn js_func() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::new();
        assert_eq!(s.js_func(&("Basis".into(), "alert".into())), Some("alert"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_url_with_rule() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.url_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "foo".into(),
        });
        assert!(s.check_url("foo"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mangle_sql_mysql() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        s.db_backend = Some(ProjectDb::mysql());
        s.mangle = true;
        assert!(s.mangle_sql("Foo").contains("uw_"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_safe_get() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::new();
        assert!(!s.is_safe_get("/x"));
        s.safe_gets.insert("/x".into());
        assert!(s.is_safe_get("/x"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sql_type_c_type() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(SqlType::Int.c_type(), "uw_Basis_int");
        assert_eq!(
            SqlType::Nullable(Box::new(SqlType::Int)).c_type(),
            "uw_Basis_int*"
        );
        assert_eq!(
            SqlType::Nullable(Box::new(SqlType::String)).c_type(),
            "uw_Basis_string"
        );
        Ok(()) // return success to the test harness
    }

    /// [`Settings::begin_compilation_job`] must populate [`Settings::compilation_id`] with a random UUID v4 string.
    #[test]
    fn begin_compilation_job_mints_uuid_v4() {
        let mut settings = Settings::new();
        assert!(settings.compilation_id.is_empty()); // Default remains empty until a pipeline starts.
        settings.begin_compilation_job(); // Mint one id for a compile or analysis snapshot.
        let parsed =
            Uuid::parse_str(&settings.compilation_id).expect("compilation_id must parse as UUID");
        assert_eq!(parsed.get_version(), Some(uuid::Version::Random)); // v4 random UUID per RFC 4122.
    }
}
