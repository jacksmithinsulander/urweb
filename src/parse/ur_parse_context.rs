use crate::db::ProjectDb;
use crate::settings::LanguageCompilationProfile;

/// Carries per-parse inputs beyond raw source: database/LangSec profile and language surface profile.
#[derive(Debug, Clone)]
pub struct UrParseContext {
    /// Effective project database choice merged from manifest, `.urp`, and CLI.
    pub project_db: ProjectDb,
    /// Whether user `.ur` modules keep Ur/Web XML lexing or use the Ur core subset.
    pub language_profile: LanguageCompilationProfile,
}

impl UrParseContext {
    /// Full Ur/Web defaults: XML allowed, `project_db` drives LangSec tiers.
    pub fn for_project_db(project_db: ProjectDb) -> Self {
        Self {
            project_db,
            language_profile: LanguageCompilationProfile::UrWeb,
        }
    }

    /// Context for boot `top.ur` / `basis` reads: always use Ur/Web surface rules inside the library.
    pub fn boot_library(project_db: ProjectDb) -> Self {
        Self::for_project_db(project_db)
    }
}

impl Default for UrParseContext {
    /// Defaults to SQLite-class LangSec profile and full Ur/Web surface.
    fn default() -> Self {
        Self::for_project_db(ProjectDb::default())
    }
}
