//! Effect and export kind annotations.
//!
//! - **Effect**: ReadOnly, ReadCookieWrite, ReadWrite — what an exported fn can do
//! - **ExportKind**: Link, Action, Rpc, Extern — how it's exposed

/// Effect annotation on an exported function (mirrors `Export.effect`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Effect {
    ReadOnly,
    ReadCookieWrite,
    ReadWrite,
}

impl Effect {
    pub fn as_str(self) -> &'static str {
        match self {
            Effect::ReadOnly => "r",
            Effect::ReadCookieWrite => "rcw",
            Effect::ReadWrite => "rw",
        }
    }
}

impl std::fmt::Display for Effect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Kind of an exported page/action (mirrors `Export.export_kind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExportKind {
    Link(Effect),
    Action(Effect),
    Rpc(Effect),
    Extern(Effect),
}

impl std::fmt::Display for ExportKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExportKind::Link(effect) => write!(f, "link({})", effect),
            ExportKind::Action(effect) => write!(f, "action({})", effect),
            ExportKind::Rpc(effect) => write!(f, "rpc({})", effect),
            ExportKind::Extern(effect) => write!(f, "extern({})", effect),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn effect_as_str() {
        assert_eq!(Effect::ReadOnly.as_str(), "r");
        assert_eq!(Effect::ReadCookieWrite.as_str(), "rcw");
        assert_eq!(Effect::ReadWrite.as_str(), "rw");
    }

    #[test]
    fn effect_display_non_empty() {
        assert!(!format!("{}", Effect::ReadOnly).is_empty());
    }

    #[test]
    fn export_kind_display() {
        assert!(format!("{}", ExportKind::Link(Effect::ReadOnly)).contains("link"));
    }
}
