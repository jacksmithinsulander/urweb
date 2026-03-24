//! Demo mode: build a combined demo application from a demo directory.
//!
//! Translates `demo.sml` from the ML compiler.  Given a prefix (e.g. `/Demo`)
//! and a dirname (e.g. `demo/`), this module reads the `prose` file, generates
//! HTML frameset files in `demo/out/`, synthesises `demo/demo.ur[ps]` and
//! `demo/demo.urp`, then compiles the combined project.

use std::fs;
use std::io::Write as IoWrite;
use std::path::{Path, PathBuf};

use anyhow::{bail, Result};

use crate::settings::Settings;
use crate::urp_parser::parse_urp;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => {
            let mut out = c.to_uppercase().to_string();
            out.push_str(chars.as_str());
            out
        }
    }
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

/// Build the demo application.
///
/// * `prefix`  — URL prefix (e.g. `/Demo`)
/// * `dirname` — path to the demo source directory
/// * `settings` — compiler settings (dbms, db, etc.)
/// * `guided`  — if true, use guided-demo frameset proportions
///
/// Returns `true` on success, `false` on failure.
pub fn make(prefix: &str, dirname: &str, settings: &mut Settings, guided: bool) -> Result<bool> {
    let dir = PathBuf::from(dirname)
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from(dirname));

    // Create out/ dir
    let out_dir = dir.join("out");
    if !out_dir.exists() {
        fs::create_dir_all(&out_dir)?;
    }

    // Write out/index.html (frameset)
    {
        let mut f = fs::File::create(out_dir.join("index.html"))?;
        writeln!(f, "<frameset cols=\"15%,85%\">")?;
        writeln!(f, "<frame src=\"demos.html\">")?;
        writeln!(f, "<frame src=\"intro.html\" name=\"staging\">")?;
        writeln!(f, "</frameset>")?;
    }

    // Open demos.html (navigation list)
    let demos_path = out_dir.join("demos.html");
    let mut demos_content = String::new();
    demos_content.push_str("<html><body>\n\n");
    demos_content.push_str("<li> <a target=\"staging\" href=\"intro.html\">Intro</a></li>\n\n");

    // demo.urs
    {
        let mut f = fs::File::create(dir.join("demo.urs"))?;
        writeln!(f, "val main : unit -> transaction page")?;
    }

    // demo.ur — will be extended as we process each sub-project
    let mut demo_ur_body = String::new();
    demo_ur_body.push_str("fun main () = return <xml><body>\n");

    // Read prose file
    let prose_path = dir.join("prose");
    let prose = fs::read_to_string(&prose_path)
        .map_err(|e| anyhow::anyhow!("Cannot read {}: {}", prose_path.display(), e))?;

    // Combined job state (mirrors combiner in demo.sml)
    let mut combined_database: Option<String> = None;
    let mut combined_sources: Vec<String> = Vec::new();
    let mut combined_rewrites: Vec<crate::settings::Rewrite> = Vec::new();
    let mut combined_filter_url: Vec<crate::settings::Rule> = Vec::new();
    let mut combined_filter_mime: Vec<crate::settings::Rule> = Vec::new();
    let mut combined_safe_gets: Vec<String> = Vec::new();
    let mut combined_timeout: u32 = 0;
    let mut found_first_urp = false;

    // intro.html writer — written until the first .urp line
    let intro_path = out_dir.join("intro.html");
    let mut intro_content = String::new();
    intro_content.push_str("<html><head>\n<title>Ur/Web Demo</title>\n</head><body>\n\n");

    // desc.html writer for the current sub-project (none until first .urp)
    let mut current_desc: Option<(String, String)> = None; // (name, content)

    for line in prose.lines() {
        if line.ends_with(".urp") {
            // This line names a sub-project
            let urp = line.trim();
            let base = urp.strip_suffix(".urp").unwrap_or(urp);
            let name = capitalize(base);

            // Flush previous desc
            if let Some((prev_name, prev_content)) = current_desc.take() {
                let _ = prev_name; // already written
                                   // content is flushed below — we actually write at end of section
                let desc_path = out_dir.join(format!("{}.desc.html", uncapitalize(&prev_name)));
                let mut full = prev_content;
                full.push_str("\n</body></html>\n");
                fs::write(&desc_path, full)?;
            }

            // Flush intro if this is the first .urp
            if !found_first_urp {
                intro_content.push_str("\n</body></html>\n");
                fs::write(&intro_path, &intro_content)?;
                found_first_urp = true;
            }

            // Navigation entry
            demos_content.push_str(&format!(
                "<li> <a target=\"staging\" href=\"{base}.html\">{name}</a></li>\n"
            ));

            // demo.ur entry
            demo_ur_body.push_str(&format!(
                "  <li> <a link={{{name}.main ()}}>{name}</a></li>\n"
            ));

            // Generate out/{base}.html (frameset for this demo)
            {
                let rows = if guided { "*,100" } else { "50%,*" };
                let mut f = fs::File::create(out_dir.join(format!("{base}.html")))?;
                writeln!(f, "<frameset rows=\"{rows}\">")?;
                writeln!(f, "<frame src=\"{prefix}/{name}/main\" name=\"showcase\">")?;
                writeln!(f, "<frame src=\"{base}.desc.html\">")?;
                writeln!(f, "</frameset>")?;
            }

            // Parse the sub-project .urp to collect its sources/rewrites
            let urp_file = dir.join(urp);
            match parse_urp(&urp_file) {
                Ok(job) => {
                    // Merge database
                    if let Some(db) = &job.database {
                        if let Some(existing) = &combined_database {
                            if existing != db {
                                bail!(
                                    "Different demos want to use different database strings: {} vs {}",
                                    existing,
                                    db
                                );
                            }
                        } else {
                            combined_database = Some(db.clone());
                        }
                    }
                    // Merge sources (deduplicate)
                    for src in &job.sources {
                        if !combined_sources.contains(src) {
                            combined_sources.push(src.clone());
                        }
                    }
                    // Merge rewrites/filters
                    combined_rewrites.extend(job.rewrites.clone());
                    combined_filter_url.extend(job.filter_url.clone());
                    combined_filter_mime.extend(job.filter_mime.clone());
                    combined_safe_gets.extend(job.safe_gets.clone());
                    if job.timeout > combined_timeout {
                        combined_timeout = job.timeout;
                    }

                    // Start desc content
                    let mut desc = String::new();
                    desc.push_str(&format!(
                        "<html><head>\n<title>{name}</title>\n</head><body>\n\n<h1>{name}</h1>\n\n"
                    ));
                    desc.push_str(&format!(
                        "<center>[ <a target=\"showcase\" href=\"{prefix}/{name}/main\">Application</a>"
                    ));
                    desc.push_str(&format!(
                        " | <a target=\"showcase\" href=\"{urp}.html\"><tt>{urp}</tt></a>"
                    ));
                    // Link to .urs and .ur source files if they exist
                    for src in &job.sources {
                        let src_path = Path::new(src);
                        let src_stem = src_path.file_stem().unwrap_or_default().to_string_lossy();
                        let dir_str = dir.to_string_lossy();
                        for ext in &["urs", "ur"] {
                            let candidate = format!("{}/{src_stem}.{ext}", dir_str);
                            let candidate_path = Path::new(&candidate);
                            // `match` avoids `delete !` mutants inverting `starts_with` / `exists`.
                            match candidate_path.starts_with(&dir) {
                                true => {}
                                false => continue,
                            }
                            match candidate_path.exists() {
                                true => {}
                                false => continue,
                            }
                            let display = format!("{src_stem}.{ext}");
                            desc.push_str(&format!(
                                " | <a target=\"showcase\" href=\"{display}.html\"><tt>{display}</tt></a>"
                            ));
                        }
                    }
                    desc.push_str(" ]</center>\n\n");
                    current_desc = Some((name, desc));
                }
                Err(e) => {
                    bail!("Can't parse {}: {}", urp_file.display(), e);
                }
            }
        } else {
            // Regular HTML line
            if found_first_urp {
                if let Some((_, ref mut desc)) = current_desc {
                    desc.push_str(line);
                    desc.push('\n');
                }
            } else {
                intro_content.push_str(line);
                intro_content.push('\n');
            }
        }
    }

    // Flush last desc
    if let Some((name, content)) = current_desc.take() {
        let base = uncapitalize(&name);
        let desc_path = out_dir.join(format!("{base}.desc.html"));
        let mut full = content;
        full.push_str("\n</body></html>\n");
        fs::write(&desc_path, full)?;
    }

    // If we never found a .urp, that's an error
    if !found_first_urp {
        // Still need to close intro
        intro_content.push_str("\n</body></html>\n");
        fs::write(&intro_path, &intro_content)?;
        bail!("No demo applications!");
    }

    // Close demos.html
    demos_content.push_str("\n</body></html>\n");
    fs::write(&demos_path, &demos_content)?;

    // Close demo.ur
    demo_ur_body.push_str("</body></xml>\n");
    fs::write(dir.join("demo.ur"), &demo_ur_body)?;

    // Write demo.urp
    let demo_urp_path = dir.join("demo.urp");
    {
        let mut f = fs::File::create(&demo_urp_path)?;
        if let Some(db) = &combined_database {
            writeln!(f, "database {db}")?;
        }
        // Use settings db string if provided
        if let Some(db) = &settings.dbstring {
            if combined_database.is_none() {
                writeln!(f, "database {db}")?;
            }
        }

        if combined_timeout > 0 {
            writeln!(f, "timeout {combined_timeout}")?;
        }

        let sql_path = settings
            .sql
            .clone()
            .unwrap_or_else(|| dir.join("demo.sql").to_string_lossy().into_owned());
        writeln!(f, "sql {sql_path}")?;
        writeln!(f, "prefix {prefix}")?;

        // Rewrites
        for rw in &combined_rewrites {
            let pkind = match rw.pkind {
                crate::settings::PathKind::Any => "all",
                crate::settings::PathKind::Url => "url",
                crate::settings::PathKind::Table => "table",
                crate::settings::PathKind::Sequence => "sequence",
                crate::settings::PathKind::View => "view",
                crate::settings::PathKind::Relation => "relation",
                crate::settings::PathKind::Cookie => "cookie",
                crate::settings::PathKind::Style => "style",
            };
            let suffix = if rw.kind == crate::settings::PatternKind::Prefix {
                "*"
            } else {
                ""
            };
            let hyphen = if rw.hyphenate { " [-]" } else { "" };
            writeln!(f, "rewrite {pkind} {}{suffix} {}{hyphen}", rw.from, rw.to)?;
        }

        // URL filters
        for rule in &combined_filter_url {
            // Skip fragment patterns (contain '#') — they clash with comment syntax
            if rule.pattern.contains('#') {
                continue;
            }
            let action = match rule.action {
                crate::settings::Action::Allow => "allow",
                crate::settings::Action::Deny => "deny",
            };
            let suffix = if rule.kind == crate::settings::PatternKind::Prefix {
                "*"
            } else {
                ""
            };
            writeln!(f, "{action} url {}{suffix}", rule.pattern)?;
        }

        // MIME filters
        for rule in &combined_filter_mime {
            if rule.pattern.contains('#') {
                continue;
            }
            let action = match rule.action {
                crate::settings::Action::Allow => "allow",
                crate::settings::Action::Deny => "deny",
            };
            let suffix = if rule.kind == crate::settings::PatternKind::Prefix {
                "*"
            } else {
                ""
            };
            writeln!(f, "{action} mime {}{suffix}", rule.pattern)?;
        }

        // Safe gets
        for sg in &combined_safe_gets {
            writeln!(f, "safeGet {sg}")?;
        }

        writeln!(f)?;

        // Sources (absolute paths)
        for src in &combined_sources {
            let src_abs = if Path::new(src).is_absolute() {
                src.clone()
            } else {
                std::env::current_dir()
                    .ok()
                    .map(|cwd| cwd.join(src).to_string_lossy().into_owned())
                    .unwrap_or_else(|| src.clone())
            };
            writeln!(f, "{src_abs}")?;
        }

        writeln!(f)?;
        writeln!(f, "demo")?;
    }

    // Now compile demo.urp
    let demo_urp_base = dir.join("demo");
    match crate::compiler::compile(&demo_urp_base, settings).into_result() {
        Ok(_) => {
            // Pretty-print source files (no-op when noEmacs is set — handled by caller)
            Ok(true)
        }
        Err(e) => {
            eprintln!("{}", e);
            Ok(false)
        }
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn uncapitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => {
            let mut out = c.to_lowercase().to_string();
            out.push_str(chars.as_str());
            out
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn capitalize_title_cases_first_rune() {
        assert_eq!(capitalize("hello"), "Hello");
        assert_eq!(capitalize("x"), "X");
        assert_eq!(capitalize(""), "");
    }

    fn write_minimal_demo_files(root: &Path) {
        fs::write(root.join("prose"), "<p>intro</p>\nwidget.urp\n").unwrap();
        fs::write(root.join("widget.urp"), "m\n").unwrap();
    }

    #[test]
    fn make_emits_capitalized_demo_name_in_nav() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        write_minimal_demo_files(root);
        let mut settings = Settings::default();
        let _ = make("/Demo", root.to_str().unwrap(), &mut settings, false);
        let demos = fs::read_to_string(root.join("out/demos.html")).expect("demos.html");
        assert!(
            demos.contains(">Widget</a>"),
            "expected capitalized demo title in nav, got {demos:?}"
        );
    }

    #[test]
    fn make_errors_when_prose_has_no_urp() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("prose"), "nothing here\n").unwrap();
        let mut settings = Settings::default();
        let err = make("/Demo", root.to_str().unwrap(), &mut settings, false).unwrap_err();
        assert!(err.to_string().contains("No demo applications"), "{err:?}");
    }

    #[test]
    fn make_rejects_conflicting_subproject_databases() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("prose"), "x\na.urp\nb.urp\n").unwrap();
        fs::write(root.join("a.urp"), "database db1\n\nm\n").unwrap();
        fs::write(root.join("b.urp"), "database db2\n\nm\n").unwrap();
        let mut settings = Settings::default();
        let err = make("/Demo", root.to_str().unwrap(), &mut settings, false).unwrap_err();
        assert!(err.to_string().contains("different database"), "{err:?}");
    }

    #[test]
    fn make_accepts_same_database_across_subprojects() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("prose"), "x\na.urp\nb.urp\n").unwrap();
        fs::write(root.join("a.urp"), "database same\n\nm\n").unwrap();
        fs::write(root.join("b.urp"), "database same\n\nm\n").unwrap();
        let mut settings = Settings::default();
        assert!(
            make("/Demo", root.to_str().unwrap(), &mut settings, false).is_ok(),
            "duplicate identical database strings should not error"
        );
    }

    #[test]
    fn make_dedupes_identical_source_entries() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("prose"), "x\none.urp\n").unwrap();
        fs::write(root.join("one.urp"), "x\n\nuniq\nuniq\n").unwrap();
        let mut settings = Settings::default();
        let _ = make("/Demo", root.to_str().unwrap(), &mut settings, false);
        let urp = fs::read_to_string(root.join("demo.urp")).expect("demo.urp");
        assert_eq!(
            urp.lines().filter(|l| l.ends_with("/uniq")).count(),
            1,
            "combined sources should list each module once, got {urp:?}"
        );
    }

    #[test]
    fn make_links_existing_ur_sources_in_desc() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("prose"), "x\napp.urp\n").unwrap();
        fs::write(root.join("app.urp"), "m\n").unwrap();
        fs::write(root.join("m.ur"), "fun main () = return <xml/>").unwrap();
        let mut settings = Settings::default();
        let _ = make("/Demo", root.to_str().unwrap(), &mut settings, false);
        let desc = fs::read_to_string(root.join("out/app.desc.html")).expect("desc");
        assert!(
            desc.contains("m.ur"),
            "desc should link to existing .ur file, got {desc:?}"
        );
    }

    #[test]
    fn make_emits_prefix_star_for_prefix_rewrite() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("prose"), "x\nr.urp\n").unwrap();
        fs::write(root.join("r.urp"), "rewrite all * /\n\nm\n").unwrap();
        let mut settings = Settings::default();
        let _ = make("/Demo", root.to_str().unwrap(), &mut settings, false);
        let urp = fs::read_to_string(root.join("demo.urp")).expect("demo.urp");
        assert!(
            urp.lines()
                .any(|l| l.starts_with("rewrite ") && l.contains('*')),
            "prefix rewrite should keep `*` marker, got {urp:?}"
        );
    }

    #[test]
    fn make_emits_prefix_star_for_allow_url_rule() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("prose"), "x\nf.urp\n").unwrap();
        fs::write(root.join("f.urp"), "allow url /pub*\n\nm\n").unwrap();
        let mut settings = Settings::default();
        let _ = make("/Demo", root.to_str().unwrap(), &mut settings, false);
        let urp = fs::read_to_string(root.join("demo.urp")).expect("demo.urp");
        assert!(
            urp.lines()
                .any(|l| l.starts_with("allow url ") && l.contains('*')),
            "prefix url allow should emit trailing `*`, got {urp:?}"
        );
    }

    #[test]
    fn make_emits_prefix_star_for_allow_mime_rule() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("prose"), "x\nf.urp\n").unwrap();
        fs::write(root.join("f.urp"), "allow mime text/plain*\n\nm\n").unwrap();
        let mut settings = Settings::default();
        let _ = make("/Demo", root.to_str().unwrap(), &mut settings, false);
        let urp = fs::read_to_string(root.join("demo.urp")).expect("demo.urp");
        assert!(
            urp.lines()
                .any(|l| l.starts_with("allow mime ") && l.contains('*')),
            "prefix mime allow should emit trailing `*`, got {urp:?}"
        );
    }

    #[test]
    fn make_writes_max_subproject_timeout() {
        let dir = tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("prose"), "x\na.urp\nb.urp\n").unwrap();
        fs::write(root.join("a.urp"), "timeout 5\n\nm\n").unwrap();
        fs::write(root.join("b.urp"), "timeout 99\n\nm\n").unwrap();
        let mut settings = Settings::default();
        let _ = make("/Demo", root.to_str().unwrap(), &mut settings, false);
        let urp = fs::read_to_string(root.join("demo.urp")).expect("demo.urp");
        assert!(
            urp.contains("timeout 99"),
            "merged demo should record max timeout, got {urp:?}"
        );
        assert!(
            !urp.contains("timeout 5"),
            "lower timeout should not win, got {urp:?}"
        );
    }
}
