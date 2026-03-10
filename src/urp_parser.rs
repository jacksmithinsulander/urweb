//! Parser for `.urp` (Ur/Web project) files.
//!
//! A `.urp` file has two sections separated by a blank line:
//!   1. **Directive section**: `key [value]` lines (e.g., `database mydb`, `debug`).
//!   2. **Source section**: one Ur/Web module filename per line (without extension).
//!
//! Lines starting with `#` (or where only whitespace precedes `#`) are comments.
//! If no blank line exists, the whole file is treated as source filenames.
//!
//! Mirrors the `parseUrp'` function in `compiler.sml`.

use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};

use crate::compiler::Job;
use crate::settings::{Action, PathKind, PatternKind, Rewrite, Rule};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Parse a `.urp` project file and return a `Job` description.
pub fn parse_urp(path: &Path) -> Result<Job> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("reading project file {}", path.display()))?;

    let abs_path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let dir = abs_path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();

    let stem = path
        .file_stem()
        .unwrap_or_default()
        .to_string_lossy()
        .into_owned();

    let mut job = Job::default();
    // Default exe is <stem>.exe next to the .urp file
    job.exe = dir
        .join(format!("{stem}.exe"))
        .to_string_lossy()
        .into_owned();

    let mut sources: Vec<String> = Vec::new();
    let mut in_sources = false;
    let mut found_blank = false;

    for raw in content.lines() {
        // Strip comment: if '#' is at a position where only whitespace precedes it,
        // the whole line is a comment.
        let effective = match raw.find('#') {
            Some(pos) if raw[..pos].chars().all(|c| c.is_whitespace()) => {
                // Pure comment — skip line
                continue;
            }
            Some(pos) => raw[..pos].trim_end(),
            None => raw.trim_end(),
        };

        // Trim leading whitespace too
        let line = effective.trim();

        if in_sources {
            if !line.is_empty() {
                sources.push(resolve_source(&dir, line));
            }
        } else if line.is_empty() {
            // Blank line separates directive section from source section
            in_sources = true;
            found_blank = true;
        } else if looks_like_directive(line) {
            // Parse directive
            parse_directive(&mut job, line, &dir)
                .with_context(|| format!("in directive: {line}"))?;
        } else {
            // No directives yet and line looks like a source filename
            // This handles .urp files that are just a list of filenames with no blank line.
            sources.push(resolve_source(&dir, line));
            // Stay in source mode
            in_sources = true;
        }
    }

    // If we never saw a blank line and never entered source mode, the whole file
    // was directives only (no sources).  That's unusual but valid.
    let _ = found_blank;

    job.sources = sources;
    Ok(job)
}

// ---------------------------------------------------------------------------
// Heuristic: is a line a directive rather than a source filename?
// ---------------------------------------------------------------------------

/// Returns true when a line looks like a directive (has spaces, or is a known
/// 0-argument keyword).
fn looks_like_directive(line: &str) -> bool {
    line.contains(' ')
        || line.contains('\t')
        || matches!(
            line,
            "debug"
                | "profile"
                | "html5"
                | "xhtml"
                | "noMangleSql"
                | "lessSafeFfi"
                | "safeGetDefault"
        )
}

// ---------------------------------------------------------------------------
// Source path resolution
// ---------------------------------------------------------------------------

fn resolve_source(dir: &Path, name: &str) -> String {
    // Source names may contain $VARIABLE prefixes; we do a best-effort join.
    let p = if name.starts_with('/') {
        PathBuf::from(name)
    } else {
        dir.join(name)
    };
    p.to_string_lossy().into_owned()
}

fn resolve_path(dir: &Path, s: &str) -> String {
    if s.starts_with('/') || s.starts_with('-') {
        s.to_string()
    } else {
        dir.join(s).to_string_lossy().into_owned()
    }
}

fn resolve_path_abs(dir: &Path, s: &str) -> String {
    if s.starts_with('/') {
        s.to_string()
    } else {
        dir.join(s)
            .canonicalize()
            .unwrap_or_else(|_| dir.join(s))
            .to_string_lossy()
            .into_owned()
    }
}

// ---------------------------------------------------------------------------
// FFI helpers
// ---------------------------------------------------------------------------

/// Parse `Module.func` into `("Module", "func")`.
fn parse_ffi(cmd: &str, arg: &str) -> Result<(String, String)> {
    let parts: Vec<&str> = arg.splitn(2, '.').collect();
    if parts.len() != 2 || parts[0].is_empty() || parts[1].is_empty() {
        bail!("{cmd} argument must be of the form Module.func, got: {arg}");
    }
    Ok((parts[0].to_string(), parts[1].to_string()))
}

/// Parse `Module.func=jsname` into `(("Module","func"), "jsname")`.
fn parse_ffi_map(cmd: &str, arg: &str) -> Result<((String, String), String)> {
    let eq_parts: Vec<&str> = arg.splitn(2, '=').collect();
    if eq_parts.len() != 2 {
        bail!("{cmd} argument must be Module.func=func', got: {arg}");
    }
    let f = eq_parts[0].trim();
    let s = eq_parts[1].trim();
    let ffi = parse_ffi(cmd, f)?;
    Ok((ffi, s.to_string()))
}

// ---------------------------------------------------------------------------
// Pattern helpers
// ---------------------------------------------------------------------------

fn parse_pattern(s: &str) -> (PatternKind, String) {
    if s.ends_with('*') {
        (PatternKind::Prefix, s[..s.len() - 1].to_string())
    } else {
        (PatternKind::Exact, s.to_string())
    }
}

fn parse_path_kind(s: &str) -> Result<PathKind> {
    Ok(match s {
        "all" => PathKind::Any,
        "url" => PathKind::Url,
        "table" => PathKind::Table,
        "sequence" => PathKind::Sequence,
        "view" => PathKind::View,
        "relation" => PathKind::Relation,
        "cookie" => PathKind::Cookie,
        "style" => PathKind::Style,
        _ => bail!("unknown path kind: {s}"),
    })
}

// ---------------------------------------------------------------------------
// Directive parser
// ---------------------------------------------------------------------------

fn parse_directive(job: &mut Job, line: &str, dir: &Path) -> Result<()> {
    // Split into command and (optional) argument
    let (cmd, arg) = match line.find(|c: char| c.is_whitespace()) {
        None => (line, ""),
        Some(pos) => (line[..pos].trim(), line[pos..].trim()),
    };

    match cmd {
        "prefix" => job.prefix = arg.to_string(),

        "database" => {
            if job.database.is_none() {
                job.database = Some(arg.to_string());
            }
        }

        "dbms" => {
            if job.dbms.is_none() {
                job.dbms = Some(arg.to_string());
            }
        }

        "exe" => job.exe = resolve_path(dir, arg),

        "sql" => {
            if job.sql.is_none() {
                job.sql = Some(resolve_path(dir, arg));
            }
        }

        "endpoints" => {
            if job.endpoints.is_none() {
                job.endpoints = Some(resolve_path(dir, arg));
            }
        }

        "debug" => job.debug = true,
        "profile" => job.profile = true,

        "timeout" => {
            job.timeout = arg
                .parse::<u32>()
                .with_context(|| format!("invalid timeout: {arg}"))?;
        }

        "ffi" => job.ffi.push(resolve_path(dir, arg)),

        "link" => job.link.push(resolve_path(dir, arg)),

        "linker" => job.linker = Some(arg.to_string()),

        "include" => job.headers.push(resolve_path_abs(dir, arg)),

        "script" => job.scripts.push(arg.to_string()),

        "clientToServer" => job.client_to_server.push(parse_ffi(cmd, arg)?),
        "effectful" => job.effectful.push(parse_ffi(cmd, arg)?),
        "benignEffectful" => job.benign_effectful.push(parse_ffi(cmd, arg)?),
        "clientOnly" => job.client_only.push(parse_ffi(cmd, arg)?),
        "serverOnly" => job.server_only.push(parse_ffi(cmd, arg)?),

        "jsModule" => {
            if job.js_module.is_none() {
                job.js_module = Some(arg.to_string());
            }
        }

        "jsFunc" => job.js_funcs.push(parse_ffi_map(cmd, arg)?),

        "safeGetDefault" => job.safe_get_default = true,
        "safeGet" => job.safe_gets.push(arg.to_string()),

        "sigfile" => {
            if job.sig_file.is_none() {
                job.sig_file = Some(arg.to_string());
            }
        }

        "filecache" => {
            if job.file_cache.is_none() {
                job.file_cache = Some(arg.to_string());
            }
        }

        "minHeap" => {
            job.min_heap = arg
                .parse::<u32>()
                .with_context(|| format!("invalid minHeap: {arg}"))?;
        }

        "mimeTypes" => {
            job.mime_types = Some(resolve_path(dir, arg));
        }

        "onError" => {
            let parts: Vec<&str> = arg.split('.').collect();
            if parts.len() < 2 {
                bail!("invalid onError argument: {arg}");
            }
            let m1 = parts[0].to_string();
            let last = parts[parts.len() - 1].to_string();
            let middle: Vec<String> = parts[1..parts.len() - 1]
                .iter()
                .map(|s| s.to_string())
                .collect();
            job.on_error = Some((m1, middle, last));
        }

        "rewrite" => {
            let tokens: Vec<&str> = arg.split_whitespace().collect();
            let (pkind, from, to, hyph) = match tokens.as_slice() {
                [pkind, from, to, "[-]"] => (pkind, from, to.to_string(), true),
                [pkind, from, "[-]"] => (pkind, from, String::new(), true),
                [pkind, from, to] => (pkind, from, to.to_string(), false),
                [pkind, from] => (pkind, from, String::new(), false),
                _ => bail!("bad 'rewrite' syntax: {arg}"),
            };
            let pkind = parse_path_kind(pkind)?;
            let (kind, from) = parse_pattern(from);
            job.rewrites.push(Rewrite {
                pkind,
                kind,
                from,
                to,
                hyphenate: hyph,
            });
        }

        "allow" => {
            let tokens: Vec<&str> = arg.split_whitespace().collect();
            if tokens.len() != 2 {
                bail!("bad 'allow' syntax: {arg}");
            }
            let (kind, pattern) = parse_pattern(tokens[1]);
            let rule = Rule {
                action: Action::Allow,
                kind,
                pattern,
            };
            push_filter_rule(job, tokens[0], rule)?;
        }

        "deny" => {
            let tokens: Vec<&str> = arg.split_whitespace().collect();
            if tokens.len() != 2 {
                bail!("bad 'deny' syntax: {arg}");
            }
            let (kind, pattern) = parse_pattern(tokens[1]);
            let rule = Rule {
                action: Action::Deny,
                kind,
                pattern,
            };
            push_filter_rule(job, tokens[0], rule)?;
        }

        "library" => {
            // Recursively parse the library .urp and merge its sources/settings.
            // We do a simplified merge: just add its sources to our sources.
            let lib_path = resolve_library_path(dir, arg);
            if let Ok(lib_path) = lib_path {
                match parse_urp(&lib_path) {
                    Ok(lib_job) => merge_library(job, lib_job),
                    Err(e) => {
                        eprintln!("warning: failed to parse library {arg}: {e}");
                    }
                }
            }
        }

        "path" => {
            // path NAME=VALUE — sets a path variable for $NAME substitution.
            // We don't implement variable substitution fully; just ignore.
        }

        // Settings-only directives (update Settings not Job)
        "html5" | "xhtml" | "noMangleSql" | "lessSafeFfi" | "noXsrfProtection" | "timeFormat"
        | "alwaysInline" | "neverInline" | "coreInline" | "monoInline" | "file" | "jsFile"
        | "limit" => {
            // These affect global Settings rather than the Job; skip for now.
        }

        _ => {
            eprintln!("warning: unrecognized .urp directive: {cmd}");
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Filter rule routing
// ---------------------------------------------------------------------------

fn push_filter_rule(job: &mut Job, kind: &str, rule: Rule) -> Result<()> {
    match kind {
        "url" => job.filter_url.push(rule),
        "mime" => job.filter_mime.push(rule),
        "requestHeader" => job.filter_request.push(rule),
        "responseHeader" => job.filter_response.push(rule),
        "env" => job.filter_env.push(rule),
        "meta" => job.filter_meta.push(rule),
        _ => bail!("unknown filter kind: {kind}"),
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Library resolution & merge
// ---------------------------------------------------------------------------

fn resolve_library_path(dir: &Path, arg: &str) -> Result<PathBuf> {
    let base = dir.join(arg);
    // Try base.urp, then base/lib.urp
    let with_urp = base.with_extension("urp");
    if with_urp.exists() {
        return Ok(with_urp);
    }
    let lib_urp = base.join("lib.urp");
    if lib_urp.exists() {
        return Ok(lib_urp);
    }
    bail!("library not found: {arg}")
}

fn merge_library(job: &mut Job, lib: Job) {
    // Prepend library sources (library sources come first)
    // Use HashSet for O(n) dedup instead of O(n²) with Vec::contains
    let mut combined = lib.sources;
    let mut seen: std::collections::HashSet<String> = combined.iter().cloned().collect();
    for s in &job.sources {
        if seen.insert(s.clone()) {
            combined.push(s.clone());
        }
    }
    job.sources = combined;

    // Merge other fields
    if job.database.is_none() {
        job.database = lib.database;
    }
    job.ffi.extend(lib.ffi);
    job.link.extend(lib.link);
    job.headers.extend(lib.headers);
    job.scripts.extend(lib.scripts);
    job.effectful.extend(lib.effectful);
    job.benign_effectful.extend(lib.benign_effectful);
    job.client_to_server.extend(lib.client_to_server);
    job.client_only.extend(lib.client_only);
    job.server_only.extend(lib.server_only);
    job.rewrites.extend(lib.rewrites);
    job.filter_url.extend(lib.filter_url);
    job.filter_mime.extend(lib.filter_mime);
    job.filter_request.extend(lib.filter_request);
    job.filter_response.extend(lib.filter_response);
    job.filter_env.extend(lib.filter_env);
    job.filter_meta.extend(lib.filter_meta);
    if job.protocol.is_none() {
        job.protocol = lib.protocol;
    }
    if job.dbms.is_none() {
        job.dbms = lib.dbms;
    }
    job.debug = job.debug || lib.debug;
    job.profile = job.profile || lib.profile;
    job.min_heap = job.min_heap.max(lib.min_heap);
    if job.sig_file.is_none() {
        job.sig_file = lib.sig_file;
    }
    if job.file_cache.is_none() {
        job.file_cache = lib.file_cache;
    }
    job.safe_get_default = job.safe_get_default || lib.safe_get_default;
    job.safe_gets.extend(lib.safe_gets);
    if job.on_error.is_none() {
        job.on_error = lib.on_error;
    }
    if job.js_module.is_none() {
        job.js_module = lib.js_module;
    }
    job.js_funcs.extend(lib.js_funcs);
    if job.mime_types.is_none() {
        job.mime_types = lib.mime_types;
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::settings::PathKind;
    use std::fs;
    use tempfile::tempdir;

    fn write_urp(dir: &Path, name: &str, contents: &str) -> PathBuf {
        let path = dir.join(name);
        fs::write(&path, contents).unwrap();
        path
    }

    #[test]
    fn parse_simple_sources_only() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "foo\nbar\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.sources.len(), 2);
        assert!(job.sources[0].ends_with("foo"));
        assert!(job.sources[1].ends_with("bar"));
        assert_eq!(job.prefix, "/");
    }

    #[test]
    fn parse_directives_then_sources() {
        let dir = tempdir().unwrap();
        let urp = write_urp(
            dir.path(),
            "app.urp",
            "database postgres://localhost/mydb\ndebug\n\nmod1\nmod2\n",
        );
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.database.as_deref(), Some("postgres://localhost/mydb"));
        assert!(job.debug);
        assert_eq!(job.sources.len(), 2);
        assert!(job.sources[0].ends_with("mod1"));
        assert!(job.sources[1].ends_with("mod2"));
    }

    #[test]
    fn parse_comments_stripped() {
        let dir = tempdir().unwrap();
        let urp = write_urp(
            dir.path(),
            "app.urp",
            "# this is a comment\n\n# another\nmod1\n",
        );
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.sources.len(), 1);
    }

    #[test]
    fn parse_prefix_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "prefix /myapp\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.prefix, "/myapp");
    }

    #[test]
    fn parse_timeout() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "timeout 30\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.timeout, 30);
    }

    #[test]
    fn parse_rewrite_three_tokens() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "rewrite all * /\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.rewrites.len(), 1);
        assert_eq!(job.rewrites[0].pkind, PathKind::Any);
        assert_eq!(job.rewrites[0].kind, PatternKind::Prefix);
        assert_eq!(job.rewrites[0].from, "");
        assert_eq!(job.rewrites[0].to, "/");
    }

    #[test]
    fn parse_allow_deny() {
        let dir = tempdir().unwrap();
        let urp = write_urp(
            dir.path(),
            "app.urp",
            "allow url /public*\ndeny url /admin*\n\nmod1\n",
        );
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.filter_url.len(), 2);
        assert_eq!(job.filter_url[0].action, Action::Allow);
        assert_eq!(job.filter_url[0].kind, PatternKind::Prefix);
        assert_eq!(job.filter_url[0].pattern, "/public");
        assert_eq!(job.filter_url[1].action, Action::Deny);
    }

    #[test]
    fn parse_ffi_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(
            dir.path(),
            "app.urp",
            "effectful Mod.func\nclientOnly Mod.render\n\nmod1\n",
        );
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.effectful, vec![("Mod".into(), "func".into())]);
        assert_eq!(job.client_only, vec![("Mod".into(), "render".into())]);
    }

    #[test]
    fn parse_on_error() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "onError Mod.Sub.handler\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        let (m1, ms, x) = job.on_error.unwrap();
        assert_eq!(m1, "Mod");
        assert_eq!(ms, vec!["Sub".to_string()]);
        assert_eq!(x, "handler");
    }

    #[test]
    fn parse_exe_resolves_path() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "exe myapp\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert!(
            job.exe.ends_with("myapp"),
            "exe must be resolved via resolve_path, got: {}",
            job.exe
        );
    }

    #[test]
    fn parse_jsfunc_uses_parse_ffi_map() {
        let dir = tempdir().unwrap();
        let urp = write_urp(
            dir.path(),
            "app.urp",
            "jsFunc Mod.render=renderJs\n\nmod1\n",
        );
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.js_funcs.len(), 1);
        assert_eq!(job.js_funcs[0].0 .0, "Mod");
        assert_eq!(job.js_funcs[0].0 .1, "render");
        assert_eq!(job.js_funcs[0].1, "renderJs");
    }

    #[test]
    fn parse_rewrite_path_kinds() {
        let dir = tempdir().unwrap();
        for (pkind_str, expected) in [
            ("url", PathKind::Url),
            ("table", PathKind::Table),
            ("sequence", PathKind::Sequence),
            ("view", PathKind::View),
            ("relation", PathKind::Relation),
            ("cookie", PathKind::Cookie),
            ("style", PathKind::Style),
        ] {
            let content = format!("rewrite {} * /\n\nmod1\n", pkind_str);
            let urp = write_urp(dir.path(), "app.urp", &content);
            let job = parse_urp(&urp).unwrap();
            assert_eq!(
                job.rewrites[0].pkind, expected,
                "path kind {} must parse to {:?}",
                pkind_str, expected
            );
        }
    }

    #[test]
    fn parse_dbms_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "dbms postgres\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.dbms.as_deref(), Some("postgres"));
    }

    #[test]
    fn parse_sql_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "sql schema.sql\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert!(job.sql.as_ref().unwrap().ends_with("schema.sql"));
    }

    #[test]
    fn parse_endpoints_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "endpoints eps.txt\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert!(job.endpoints.as_ref().unwrap().ends_with("eps.txt"));
    }

    #[test]
    fn parse_ffi_rejects_bad_format() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "effectful BadFormat\n\nmod1\n");
        let res = parse_urp(&urp);
        assert!(res.is_err(), "effectful BadFormat must fail parse_ffi");
    }

    #[test]
    fn parse_comment_line_requires_whitespace_before_hash() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "prefix /x\n# comment\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.prefix, "/x");
        assert_eq!(job.sources.len(), 1);
    }

    #[test]
    fn parse_profile_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "profile\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert!(job.profile);
    }

    #[test]
    fn parse_link_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "link libfoo\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.link.len(), 1);
        assert!(job.link[0].contains("libfoo"));
    }

    #[test]
    fn parse_linker_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "linker ld\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.linker.as_deref(), Some("ld"));
    }

    #[test]
    fn parse_include_directive() {
        let dir = tempdir().unwrap();
        let subdir = dir.path().join("inc");
        std::fs::create_dir_all(&subdir).unwrap();
        let urp = write_urp(dir.path(), "app.urp", &format!("include inc\n\nmod1\n"));
        let job = parse_urp(&urp).unwrap();
        assert!(!job.headers.is_empty(), "include must use resolve_path_abs");
        assert!(
            job.headers[0].contains("inc"),
            "header path must contain inc, got: {}",
            job.headers[0]
        );
    }

    #[test]
    fn parse_script_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "script foo.js\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.scripts, vec!["foo.js"]);
    }

    #[test]
    fn parse_client_to_server_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "clientToServer Mod.fn\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.client_to_server.len(), 1);
        assert_eq!(job.client_to_server[0].0, "Mod");
        assert_eq!(job.client_to_server[0].1, "fn");
    }

    #[test]
    fn parse_benign_effectful_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "benignEffectful Mod.fn\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.benign_effectful.len(), 1);
        assert_eq!(job.benign_effectful[0].0, "Mod");
        assert_eq!(job.benign_effectful[0].1, "fn");
    }

    #[test]
    fn parse_server_only_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "serverOnly Mod.fn\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.server_only.len(), 1);
        assert_eq!(job.server_only[0].0, "Mod");
        assert_eq!(job.server_only[0].1, "fn");
    }

    #[test]
    fn parse_js_module_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "jsModule m\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.js_module.as_deref(), Some("m"));
    }

    #[test]
    fn parse_safe_get_default_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "safeGetDefault\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert!(job.safe_get_default);
    }

    #[test]
    fn parse_safe_get_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "safeGet path\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.safe_gets, vec!["path"]);
    }

    #[test]
    fn parse_sigfile_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "sigfile s.urs\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.sig_file.as_deref(), Some("s.urs"));
    }

    #[test]
    fn parse_filecache_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "filecache c\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.file_cache.as_deref(), Some("c"));
    }

    #[test]
    fn parse_min_heap_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "minHeap 64\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.min_heap, 64);
    }

    #[test]
    fn parse_mime_types_directive() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "mimeTypes mime.types\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert!(job.mime_types.is_some());
        assert!(job.mime_types.as_ref().unwrap().contains("mime.types"));
    }

    #[test]
    fn parse_filter_mime() {
        let dir = tempdir().unwrap();
        let urp = write_urp(
            dir.path(),
            "app.urp",
            "allow mime text/plain\ndeny mime application/json\n\nmod1\n",
        );
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.filter_mime.len(), 2);
        assert_eq!(job.filter_mime[0].pattern, "text/plain");
        assert_eq!(job.filter_mime[1].pattern, "application/json");
    }

    #[test]
    fn parse_filter_request_header() {
        let dir = tempdir().unwrap();
        let urp = write_urp(
            dir.path(),
            "app.urp",
            "allow requestHeader X-Custom\n\nmod1\n",
        );
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.filter_request.len(), 1);
        assert_eq!(job.filter_request[0].pattern, "X-Custom");
    }

    #[test]
    fn parse_filter_response_header() {
        let dir = tempdir().unwrap();
        let urp = write_urp(
            dir.path(),
            "app.urp",
            "allow responseHeader Content-Type\n\nmod1\n",
        );
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.filter_response.len(), 1);
        assert_eq!(job.filter_response[0].pattern, "Content-Type");
    }

    #[test]
    fn parse_filter_env() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "allow env VAR_NAME\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.filter_env.len(), 1);
        assert_eq!(job.filter_env[0].pattern, "VAR_NAME");
    }

    #[test]
    fn parse_filter_meta() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "allow meta name\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.filter_meta.len(), 1);
        assert_eq!(job.filter_meta[0].pattern, "name");
    }

    #[test]
    fn parse_path_directive_no_error() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "path FOO=/some/path\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.sources.len(), 1);
    }

    #[test]
    fn parse_comment_whitespace_only_before_hash_strips_line() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "   # comment\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.sources.len(), 1);
    }

    #[test]
    fn parse_comment_non_whitespace_before_hash_keeps_prefix() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "x # inline\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.sources.len(), 2);
        assert!(job.sources[0].ends_with('x') || job.sources[1].ends_with('x'));
    }

    #[test]
    fn parse_rewrite_four_tokens_with_hyphen() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "rewrite url /old /new [-]\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.rewrites.len(), 1);
        assert_eq!(job.rewrites[0].to, "/new");
        assert!(job.rewrites[0].hyphenate);
    }

    #[test]
    fn parse_rewrite_three_tokens_no_hyphen() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "rewrite url /old /new\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.rewrites.len(), 1);
        assert_eq!(job.rewrites[0].to, "/new");
        assert!(!job.rewrites[0].hyphenate);
    }

    #[test]
    fn parse_rewrite_two_tokens() {
        let dir = tempdir().unwrap();
        let urp = write_urp(dir.path(), "app.urp", "rewrite url /prefix\n\nmod1\n");
        let job = parse_urp(&urp).unwrap();
        assert_eq!(job.rewrites.len(), 1);
        assert_eq!(job.rewrites[0].from, "/prefix");
        assert_eq!(job.rewrites[0].to, "");
    }

    #[test]
    fn parse_library_merge() {
        let dir = tempdir().unwrap();
        let lib_urp = dir.path().join("lib.urp");
        std::fs::write(&lib_urp, "profile\n\nlibmod\n").unwrap();
        let app_urp = write_urp(dir.path(), "app.urp", "library lib.urp\n\nappmod\n");
        let job = parse_urp(&app_urp).unwrap();
        assert!(
            job.profile,
            "library directive must be processed and profile merged from lib.urp"
        );
    }
}
