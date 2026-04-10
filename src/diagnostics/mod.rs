//! Stable [`DiagnosticId`] values, localized templates (English / Swedish / Spanish), and [`DiagnosticPayload`] trees.

mod ids;
pub mod locale;
pub mod payload;
pub mod render;
mod template_tables;

pub use ids::DiagnosticId;
pub use locale::DiagnosticLocale;
pub use payload::{DiagnosticHint, DiagnosticPayload, DiagnosticSeverity};
pub use render::{
    diagnostic_id_as_u32, format_diagnostic_payload_for_user, render_diagnostic_body,
    HINT_TRAILER_PREFIX,
};
pub use template_tables::diagnostic_template;
