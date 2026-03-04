//! Compilation settings parsed from `.urp` project files.
//!
//! - **Job** / **Settings**: URL prefix, database, FFI mappings, effectful annotations
//! - **Rewrite**, **Rule**: URL/mime/request filters
//! - SQL mangling, timeouts, protocol, dbms, etc.

use std::collections::{BTreeMap, BTreeSet};

/// An FFI function identifier: `(module_name, function_name)`.
pub type Ffi = (String, String);

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

#[derive(Debug, Clone, PartialEq, Eq)]
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

    // Current protocol / DBMS names
    pub protocol: String,
    pub dbms: String,

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
            dbms: String::new(),
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
            file_path: ".".into(),
            js_output: None,
        }
    }

    // -----------------------------------------------------------------------
    // URL prefix
    // -----------------------------------------------------------------------

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

    pub fn mangle_sql_table(&self, s: &str) -> String {
        if self.dbms == "mysql" {
            if self.mangle {
                format!("uw_{}", s.to_lowercase())
            } else {
                s.to_lowercase()
            }
        } else if self.mangle {
            let capitalized = Self::capitalize(s);
            format!("uw_{}", capitalized)
        } else {
            Self::lowercase(s)
        }
    }

    pub fn mangle_sql(&self, s: &str) -> String {
        if self.dbms == "mysql" {
            if self.mangle {
                format!("uw_{}", s.to_lowercase())
            } else {
                s.to_lowercase()
            }
        } else if self.mangle {
            format!("uw_{}", s)
        } else {
            Self::lowercase(s)
        }
    }

    fn capitalize(s: &str) -> String {
        let mut chars = s.chars();
        match chars.next() {
            None => String::new(),
            Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
        }
    }

    fn lowercase(s: &str) -> String {
        let mut chars = s.chars();
        match chars.next() {
            None => String::new(),
            Some(c) => c.to_lowercase().collect::<String>() + chars.as_str(),
        }
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
            .map_or(false, |r| r.action == Action::Allow)
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
    fn subsumes_same_kind() {
        assert!(subsumes(&PathKind::Table, &PathKind::Table));
    }

    #[test]
    fn subsumes_any_accepts_all() {
        assert!(subsumes(&PathKind::Url, &PathKind::Any));
    }

    #[test]
    fn subsumes_relation_accepts_table() {
        assert!(subsumes(&PathKind::Table, &PathKind::Relation));
    }

    #[test]
    fn subsumes_relation_rejects_url() {
        assert!(!subsumes(&PathKind::Url, &PathKind::Relation));
    }

    #[test]
    fn subsumes_relation_accepts_sequence_and_view() {
        assert!(subsumes(&PathKind::Sequence, &PathKind::Relation));
        assert!(subsumes(&PathKind::View, &PathKind::Relation));
    }

    #[test]
    fn url_prefix_slash() {
        let mut s = Settings::new();
        s.set_url_prefix("/app");
        assert_eq!(s.url_prefix, "/app/");
        assert_eq!(s.url_pre_prefix, "");
    }

    #[test]
    fn url_prefix_http() {
        let mut s = Settings::new();
        s.set_url_prefix("http://example.com/app");
        assert_eq!(s.url_pre_prefix, "http://example.com");
        assert_eq!(s.url_prefix, "/app/");
    }

    #[test]
    fn mangle_sql_table_postgres() {
        let mut s = Settings::new();
        s.dbms = "postgres".into();
        assert_eq!(s.mangle_sql_table("users"), "uw_Users");
    }

    #[test]
    fn mangle_sql_table_mysql() {
        let mut s = Settings::new();
        s.dbms = "mysql".into();
        assert_eq!(s.mangle_sql_table("Users"), "uw_users");
    }

    #[test]
    fn mangle_no_mangle() {
        let mut s = Settings::new();
        s.dbms = "postgres".into();
        s.mangle = false;
        assert_eq!(s.mangle_sql_table("FooBar"), "fooBar");
    }

    #[test]
    fn mangle_sql_mysql_vs_postgres() {
        let mut s_mysql = Settings::new();
        s_mysql.dbms = "mysql".into();
        s_mysql.mangle = true;
        let mut s_pg = Settings::new();
        s_pg.dbms = "postgres".into();
        s_pg.mangle = true;
        assert_eq!(s_mysql.mangle_sql("Foo"), "uw_foo");
        assert_eq!(s_pg.mangle_sql("Foo"), "uw_Foo");
    }

    #[test]
    fn is_effectful_false_when_not_in_set() {
        let s = Settings::new();
        assert!(!s.is_effectful(&("Other".into(), "fn".into())));
    }

    #[test]
    fn is_benign_effectful_false_when_empty() {
        let s = Settings::new();
        assert!(!s.is_benign_effectful(&("X".into(), "y".into())));
    }

    #[test]
    fn is_client_only_false_when_empty() {
        let s = Settings::new();
        assert!(!s.is_client_only(&("X".into(), "y".into())));
    }

    #[test]
    fn is_server_only_false_when_empty() {
        let s = Settings::new();
        assert!(!s.is_server_only(&("X".into(), "y".into())));
    }

    #[test]
    fn check_url_with_rules() {
        let mut s = Settings::new();
        s.url_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "/api".into(),
        });
        assert!(s.check_url("/api"));
        assert!(!s.check_url("/other"));
    }

    #[test]
    fn check_mime_valid_and_rules() {
        let mut s = Settings::new();
        s.mime_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "text/plain".into(),
        });
        assert!(s.check_mime("text/plain"));
        assert!(!s.check_mime("text/x"));
    }

    #[test]
    fn check_mime_requires_valid_chars() {
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
    }

    #[test]
    fn is_valid_env_rejects_hyphen() {
        assert!(!Settings::is_valid_env("FOO-BAR"));
        assert!(Settings::is_valid_env("FOO_BAR"));
    }

    #[test]
    fn is_valid_meta_allows_hyphen_rejects_digit() {
        assert!(Settings::is_valid_meta("content-type"));
        assert!(!Settings::is_valid_meta("meta2"));
    }

    #[test]
    fn check_request_header_valid() {
        let mut s = Settings::new();
        s.request_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "X-Foo".into(),
        });
        assert!(s.check_request_header("X-Foo"));
    }

    #[test]
    fn check_request_header_invalid_mime_fails() {
        let mut s = Settings::new();
        s.request_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "X-Foo!".into(),
        });
        assert!(!s.check_request_header("X-Foo!"));
    }

    #[test]
    fn check_response_header_invalid_mime_fails() {
        let mut s = Settings::new();
        s.response_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "X-Bad!".into(),
        });
        assert!(!s.check_response_header("X-Bad!"));
    }

    #[test]
    fn check_env_var_invalid_chars_fails() {
        let mut s = Settings::new();
        s.env_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "FOO-BAR".into(),
        });
        assert!(!s.check_env_var("FOO-BAR"));
    }

    #[test]
    fn check_meta_invalid_chars_fails() {
        let mut s = Settings::new();
        s.meta_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "meta2".into(),
        });
        assert!(!s.check_meta("meta2"));
    }

    #[test]
    fn check_response_header_valid() {
        let mut s = Settings::new();
        s.response_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "Content-Type".into(),
        });
        assert!(s.check_response_header("Content-Type"));
    }

    #[test]
    fn check_env_var_valid() {
        let mut s = Settings::new();
        s.env_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "FOO_BAR".into(),
        });
        assert!(s.check_env_var("FOO_BAR"));
    }

    #[test]
    fn check_meta_valid() {
        let mut s = Settings::new();
        s.meta_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "description".into(),
        });
        assert!(s.check_meta("description"));
    }

    #[test]
    fn rewrite_exact_match() {
        let mut s = Settings::new();
        s.rewrites.push(Rewrite {
            pkind: PathKind::Any,
            kind: PatternKind::Exact,
            from: "foo".into(),
            to: "bar".into(),
            hyphenate: false,
        });
        assert_eq!(s.rewrite(&PathKind::Url, "foo"), "bar");
    }

    #[test]
    fn effectful_sqlcache() {
        let s = Settings::new();
        assert!(s.is_effectful(&("Sqlcache".into(), "anything".into())));
    }

    #[test]
    fn effectful_basis_dml() {
        let s = Settings::new();
        assert!(s.is_effectful(&("Basis".into(), "dml".into())));
    }

    #[test]
    fn client_only_recv() {
        let s = Settings::new();
        assert!(s.is_client_only(&("Basis".into(), "recv".into())));
    }

    #[test]
    fn add_limit_valid() {
        let mut s = Settings::new();
        s.add_limit("page", 1024).unwrap();
        assert_eq!(s.limits.len(), 1);
    }

    #[test]
    fn add_limit_invalid() {
        let mut s = Settings::new();
        assert!(s.add_limit("bogus", 0).is_err());
    }

    #[test]
    fn add_limit_time_sets_deadlines() {
        let mut s = Settings::new();
        s.add_limit("time", 30).unwrap();
        assert!(s.deadlines);
    }

    #[test]
    fn rewrite_prefix() {
        let mut s = Settings::new();
        s.rewrites.push(Rewrite {
            pkind: PathKind::Any,
            kind: PatternKind::Prefix,
            from: "foo".into(),
            to: "bar".into(),
            hyphenate: false,
        });
        assert_eq!(s.rewrite(&PathKind::Url, "foobar"), "barbar");
    }

    #[test]
    fn rewrite_hyphenate() {
        let mut s = Settings::new();
        s.rewrites.push(Rewrite {
            pkind: PathKind::Any,
            kind: PatternKind::Prefix,
            from: String::new(),
            to: String::new(),
            hyphenate: true,
        });
        assert_eq!(s.rewrite(&PathKind::Url, "foo_bar"), "foo-bar");
    }

    #[test]
    fn rule_matches_exact() {
        let r = Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "foo".into(),
        };
        assert!(r.matches("foo"));
        assert!(!r.matches("foobar"));
    }

    #[test]
    fn rule_matches_prefix() {
        let r = Rule {
            action: Action::Allow,
            kind: PatternKind::Prefix,
            pattern: "foo".into(),
        };
        assert!(r.matches("foobar"));
        assert!(!r.matches("bar"));
    }

    #[test]
    fn sql_type_is_blob() {
        assert!(SqlType::Blob.is_blob());
        assert!(!SqlType::Int.is_blob());
    }

    #[test]
    fn sql_type_nullable_blob_is_blob() {
        assert!(SqlType::Nullable(Box::new(SqlType::Blob)).is_blob());
        assert!(!SqlType::Nullable(Box::new(SqlType::Int)).is_blob());
    }

    #[test]
    fn sql_type_is_not_null() {
        assert!(SqlType::Int.is_not_null());
        assert!(!SqlType::Nullable(Box::new(SqlType::Int)).is_not_null());
    }

    #[test]
    fn may_client_to_server() {
        let mut s = Settings::new();
        s.client_to_server.insert(("M".into(), "f".into()));
        assert!(s.may_client_to_server(&("M".into(), "f".into())));
        assert!(!s.may_client_to_server(&("M".into(), "g".into())));
    }

    #[test]
    fn is_benign_effectful() {
        let s = Settings::new();
        assert!(s.is_benign_effectful(&("Basis".into(), "get_cookie".into())));
    }

    #[test]
    fn is_client_only() {
        let s = Settings::new();
        assert!(s.is_client_only(&("Basis".into(), "recv".into())));
    }

    #[test]
    fn is_server_only() {
        let s = Settings::new();
        assert!(s.is_server_only(&("Basis".into(), "dml".into())));
    }

    #[test]
    fn js_func() {
        let s = Settings::new();
        assert_eq!(s.js_func(&("Basis".into(), "alert".into())), Some("alert"));
    }

    #[test]
    fn check_url_with_rule() {
        let mut s = Settings::new();
        s.url_rules.push(Rule {
            action: Action::Allow,
            kind: PatternKind::Exact,
            pattern: "foo".into(),
        });
        assert!(s.check_url("foo"));
    }

    #[test]
    fn mangle_sql_mysql() {
        let mut s = Settings::new();
        s.dbms = "mysql".into();
        s.mangle = true;
        assert!(s.mangle_sql("Foo").contains("uw_"));
    }

    #[test]
    fn is_safe_get() {
        let mut s = Settings::new();
        assert!(!s.is_safe_get("/x"));
        s.safe_gets.insert("/x".into());
        assert!(s.is_safe_get("/x"));
    }

    #[test]
    fn sql_type_c_type() {
        assert_eq!(SqlType::Int.c_type(), "uw_Basis_int");
        assert_eq!(
            SqlType::Nullable(Box::new(SqlType::Int)).c_type(),
            "uw_Basis_int*"
        );
        assert_eq!(
            SqlType::Nullable(Box::new(SqlType::String)).c_type(),
            "uw_Basis_string"
        );
    }
}
