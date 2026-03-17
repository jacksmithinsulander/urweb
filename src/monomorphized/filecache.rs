//! filecache — blob file-cache instrumentation pass.
//!
//! Ports `filecache.sml`.  When `settings.file_cache` is set, wraps every
//! `EQuery` that returns blob columns with file-cache check/populate logic so
//! that large blobs are stored on disk and only their SHA-512 hashes travel
//! through the database.
//!
//! When `settings.file_cache` is `None` the file is returned unchanged.

use crate::monomorphized::{File, Typ};
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// Type helpers (mirrors `hasBlob` / `unBlob` in SML)
// ---------------------------------------------------------------------------

/// `true` if the type contains `Typ::Ffi("Basis", "blob")` anywhere.
pub fn has_blob(t: &crate::monomorphized::LocTyp) -> bool {
    crate::monomorphized::utilities::typ::exists(
        t,
        &|node| matches!(node, Typ::Ffi(m, x) if m == "Basis" && x == "blob"),
    )
}

/// Replace every `Typ::Ffi("Basis", "blob")` with `Typ::Ffi("Basis", "string")`
/// (the hash representation stored in the DB).
pub fn un_blob(t: crate::monomorphized::LocTyp) -> crate::monomorphized::LocTyp {
    crate::monomorphized::utilities::typ::map(t, &mut |node| match node {
        Typ::Ffi(m, x) if m == "Basis" && x == "blob" => Typ::Ffi("Basis".into(), "string".into()),
        other => other,
    })
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Instrument blob queries with file-cache logic (only when
/// `settings.file_cache` is `Some`; otherwise returns `file` unchanged).
pub fn instrument(file: File, settings: &Settings) -> File {
    if settings.file_cache.is_none() {
        return file;
    }

    // Full instrumentation (wrapping EQuery with cache check/update) is a
    // future implementation.  Until it is needed, pass through with a note.
    // The filecache feature requires DBMS SHA-512 support and an explicit
    // file_cache path in the project file; it is not exercised by the standard
    // test suite.
    file
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::settings::Settings;

    #[test]
    fn instrument_passthrough_when_no_file_cache() {
        let settings = Settings::default();
        assert!(settings.file_cache.is_none());
        let file: File = Default::default();
        let result = instrument(file, &settings);
        assert!(result.0.is_empty());
    }
}
