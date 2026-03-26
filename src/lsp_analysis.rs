//! Full-project parse + elaborate for LSP, with optional in-memory `.ur` overlay.

use std::path::{Path, PathBuf};

use crate::compiler::{self, elaborate, parse_sources_with_overlay, Job};
use crate::elaborated::File as ElabFile;
use crate::error_types::ErrorReporter;
use crate::settings::Settings;

#[derive(Debug, Clone)]
pub struct ProjectState {
    pub root: PathBuf,
    pub urp_path: PathBuf,
    pub job: Job,
    pub settings: Settings,
}

impl ProjectState {
    pub fn open(workspace_root: &Path) -> Result<Self, String> {
        let urp_path = crate::lsp_workspace::discover_unique_urp(workspace_root)?;
        let (job, settings) = compiler::resolve_project_job_and_settings(&urp_path)
            .map_err(|e| format!("{}: {e}", urp_path.display()))?;
        Ok(ProjectState {
            root: workspace_root.to_path_buf(),
            urp_path,
            job,
            settings,
        })
    }

    /// Parse all modules from disk plus one overlay buffer, then elaborate.
    pub fn analyze_buffer(&self, disk_ur_path: &Path, buffer_text: &str) -> AnalysisSnapshot {
        let mut errors = ErrorReporter::new_silent();
        let Some(src_file) = parse_sources_with_overlay(
            &self.job,
            disk_ur_path,
            buffer_text,
            &self.settings,
            &mut errors,
        ) else {
            return AnalysisSnapshot {
                errors,
                elaborated: None,
            };
        };
        let elab = elaborate(src_file, &self.settings, &mut errors);
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

#[derive(Debug)]
pub struct AnalysisSnapshot {
    pub errors: ErrorReporter,
    pub elaborated: Option<ElabFile>,
}
