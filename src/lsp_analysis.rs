//! Full-project parse and elaboration for the language server, with an in-memory overlay for one `.ur` buffer.

use std::path::{Path, PathBuf};

use crate::cli_common::cli_diagnostic_text;
use crate::compiler::{self, elaborate, parse_sources_with_overlay, Job};
use crate::diagnostics::{DiagnosticId, DiagnosticLocale};
use crate::elaborated::File as ElabFile;
use crate::error_types::ErrorReporter;
use crate::settings::Settings;

/// Opened Ur/Web project: workspace directory, resolved `.urp` path, job graph, and compiler settings.
#[derive(Debug, Clone)]
pub struct ProjectState {
    pub root: PathBuf,
    pub urp_path: PathBuf,
    pub job: Job,
    pub settings: Settings,
}

impl ProjectState {
    /// Load the single `.urp` under `workspace_root` and resolve [`Job`] plus [`Settings`] like batch compile.
    ///
    /// # Arguments
    ///
    /// * `workspace_root` — Folder the editor opened (must contain exactly one `.urp`).
    /// * `locale` — Diagnostic language for discovery and resolution error text (`ur.toml` / environment).
    ///
    /// # Returns
    ///
    /// [`ProjectState`] on success.
    ///
    /// # Errors
    ///
    /// Localized project discovery or resolver failures as `String`.
    pub fn open(workspace_root: &Path, locale: DiagnosticLocale) -> Result<Self, String> {
        let urp_path = crate::lsp_workspace::discover_unique_urp(workspace_root)
            .map_err(|discovery_error| discovery_error.to_diagnostic_text(locale))?;
        let (job, settings) =
            compiler::resolve_project_job_and_settings(&urp_path).map_err(|resolver_error| {
                cli_diagnostic_text(
                    DiagnosticId::CliLspProjectResolveFailed,
                    vec![
                        urp_path.display().to_string(),
                        format!("{resolver_error:#}"),
                    ],
                    locale,
                )
            })?;
        Ok(ProjectState {
            root: workspace_root.to_path_buf(),
            urp_path,
            job,
            settings,
        })
    }

    /// Parse the whole project from disk, substituting `buffer_text` for `disk_ur_path`, then run elaboration.
    ///
    /// # Arguments
    ///
    /// * `disk_ur_path` — On-disk `.ur` path whose module should use `buffer_text` instead of file contents.
    /// * `buffer_text` — Editor buffer text for that module.
    ///
    /// # Returns
    ///
    /// [`AnalysisSnapshot`] with diagnostics and optional elaborated [`crate::elaborated::File`].
    pub fn analyze_buffer(&self, disk_ur_path: &Path, buffer_text: &str) -> AnalysisSnapshot {
        let mut snapshot_settings = self.settings.clone(); // Per-snapshot settings so we can mint a job id.
        snapshot_settings.begin_compilation_job(); // Fresh UUID for this LSP analysis pass (tracing correlation only).
        let mut errors = ErrorReporter::from_settings_silent(&snapshot_settings); // Carries `compilation_id` without stderr echo.
        let Some(src_file) = parse_sources_with_overlay(
            &self.job,
            disk_ur_path,
            buffer_text,
            &snapshot_settings,
            &mut errors,
        ) else {
            return AnalysisSnapshot {
                errors,
                elaborated: None,
            };
        };
        let elab = elaborate(src_file, &snapshot_settings, &mut errors);
        if let Some(ref file) = elab {
            let open_key = crate::lsp_unused::open_key_for_buffer(&self.root, disk_ur_path);
            crate::lsp_unused::report_unused_top_level_values(file, &open_key, &mut errors);
        }
        AnalysisSnapshot {
            errors,
            elaborated: elab,
        }
    }
}

/// Diagnostics plus optional elaborated file after one analysis pass.
#[derive(Debug)]
pub struct AnalysisSnapshot {
    pub errors: ErrorReporter,
    pub elaborated: Option<ElabFile>,
}

impl Default for ProjectState {
    fn default() -> Self {
        Self {
            root: PathBuf::new(),
            urp_path: PathBuf::new(),
            job: Job::default(),
            settings: Settings::new(),
        }
    }
}

impl Default for AnalysisSnapshot {
    fn default() -> Self {
        Self {
            errors: ErrorReporter::new_silent(),
            elaborated: None,
        }
    }
}
