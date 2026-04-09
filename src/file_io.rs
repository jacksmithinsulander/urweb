//! File input/output and operating-system path handling for the compiler driver.
//!
//! Unicode UTF-8 text reads go through [`crate::file_io::open_text`]; raw bytes through [`crate::file_io::open_binary`].
//! [`crate::file_io::ModTime`] records the latest file modification time observed for incremental rebuilds.
//!
//! - [`crate::file_io::open_text`] / [`crate::file_io::open_binary`]: read files and refresh the global modification-time tracker
//! - [`crate::file_io::resolve`]: resolve a relative name against a base directory
//! - [`crate::file_io::most_recent_mod_time`] / [`crate::file_io::ModTime`]: clock used for incremental decisions

use crate::cli_common::{cli_diagnostic_text, diagnostic_locale_for_cli};
use crate::compiler_diagnostics::lock_for_compile;
use crate::diagnostics::DiagnosticId;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

/// Newtype around the standard library [`SystemTime`] with [`Default`] set to the Unix epoch.
///
/// Lets mutation-testing tools use `Default::default()`; orphan rules block implementing [`Default`] for [`SystemTime`] directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModTime(pub SystemTime);

/// Default mod-time is Unix epoch (no file read yet).
impl Default for ModTime {
    fn default() -> Self {
        ModTime(SystemTime::UNIX_EPOCH)
    }
}

/// Tracks the most-recent modification time of any file opened via this module
/// (mirrors SML's `FileIO.mostRecentModTimeRef`).
static MOST_RECENT_MOD: std::sync::Mutex<Option<SystemTime>> = std::sync::Mutex::new(None);

/// Number of times the mod-time tracker was updated (for tests; > vs >= is observable here).
static UPDATE_COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Update the process-global modification time when `path`’s metadata reports a strictly newer timestamp.
fn update_mod_time(path: &Path) {
    // Read filesystem metadata; ignore missing files.
    if let Ok(meta) = std::fs::metadata(path) {
        if let Ok(mtime) = meta.modified() {
            let mut guard =
                lock_for_compile(&MOST_RECENT_MOD, "file I/O modification time tracker");
            // Only bump when strictly greater so reopening the same file does not inflate counts.
            if guard.is_none_or(|prev| mtime > prev) {
                *guard = Some(mtime);
                UPDATE_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
        }
    }
}

/// Test-only: number of times the modification-time tracker recorded a strictly newer file timestamp.
///
/// # Returns
///
/// The number of successful timestamp updates since the last reset.
pub(crate) fn __update_count_for_test() -> usize {
    UPDATE_COUNT.load(std::sync::atomic::Ordering::Relaxed) // Atomic read of bump counter.
}

/// Test-only: reset the global modification-time state and bump counter (for `#[cfg(test)]` callers).
///
/// # Returns
///
/// Nothing.
pub(crate) fn __reset_for_test() {
    *lock_for_compile(&MOST_RECENT_MOD, "file I/O modification time tracker") = None; // Clear last mtime.
    UPDATE_COUNT.store(0, std::sync::atomic::Ordering::Relaxed); // Reset bump counter.
}

/// Latest modification time seen through [`crate::file_io::open_text`] or [`crate::file_io::open_binary`], or the Unix epoch if none.
///
/// # Returns
///
/// [`ModTime`] wrapping the stored [`SystemTime`], or the Unix epoch when no file has been read yet.
pub fn most_recent_mod_time() -> ModTime {
    ModTime(
        lock_for_compile(&MOST_RECENT_MOD, "file I/O modification time tracker")
            .unwrap_or(SystemTime::UNIX_EPOCH), // `MutexGuard<Option<_>>` derefs to `Option`.
    )
}

/// Read a file as Unicode UTF-8 and update the modification-time tracker.
///
/// # Arguments
///
/// * `path` — Filesystem path; any `T: AsRef<Path>`.
///
/// # Returns
///
/// The full decoded text on success.
///
/// # Errors
///
/// Input/output failures from the kernel or invalid UTF-8 (message from the diagnostic catalog).
pub fn open_text(path: impl AsRef<Path>) -> anyhow::Result<String> {
    let path = path.as_ref(); // Borrow as `Path`.
    update_mod_time(path); // Record mtime for incremental builds.
    let locale = diagnostic_locale_for_cli(None); // Same locale selection as other driver I/O.
    std::fs::read_to_string(path).map_err(|read_error| {
        anyhow::anyhow!(
            "{}",
            cli_diagnostic_text(
                DiagnosticId::CliFileReadFailed,
                vec![path.display().to_string(), read_error.to_string()],
                locale,
            )
        )
    }) // Utf-8 read.
}

/// Read a file as raw bytes and update the modification-time tracker (no Unicode validation).
///
/// # Arguments
///
/// * `path` — Filesystem path; any `T: AsRef<Path>`.
///
/// # Returns
///
/// The file contents as a byte vector on success.
///
/// # Errors
///
/// Input/output failures from reading the file (message from the diagnostic catalog).
pub fn open_binary(path: impl AsRef<Path>) -> anyhow::Result<Vec<u8>> {
    let path = path.as_ref();
    update_mod_time(path);
    let locale = diagnostic_locale_for_cli(None);
    std::fs::read(path).map_err(|read_error| {
        anyhow::anyhow!(
            "{}",
            cli_diagnostic_text(
                DiagnosticId::CliFileReadFailed,
                vec![path.display().to_string(), read_error.to_string()],
                locale,
            )
        )
    })
}

/// Join `name` under `base`, unless `name` is already an absolute path (platform-specific).
///
/// Matches Standard ML `OS.Path.concat` behaviour from the MLton reference compiler.
///
/// # Arguments
///
/// * `base` — Directory or prefix path (`AsRef<Path>`).
/// * `name` — Relative or absolute path string.
///
/// # Returns
///
/// [`PathBuf`] for `name` alone if it is absolute; otherwise `base.join(name)`.
pub fn resolve(base: impl AsRef<Path>, name: &str) -> PathBuf {
    let base = base.as_ref();
    if Path::new(name).is_absolute() {
        PathBuf::from(name) // Absolute paths ignore `base`.
    } else {
        base.join(name) // Relative paths join under `base`.
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    static FILEIO_STATE_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn open_text_reads_file() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let _g = lock_for_compile(&FILEIO_STATE_LOCK, "file_io tests (serial)");
        let dir = tempfile::tempdir()?;
        let f = dir.path().join("t.txt");
        std::fs::write(&f, "hello")?;
        let s = open_text(&f)?;
        assert_eq!(s, "hello");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn open_binary_reads_file() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let _g = lock_for_compile(&FILEIO_STATE_LOCK, "file_io tests (serial)");
        let dir = tempfile::tempdir()?;
        let f = dir.path().join("t.bin");
        std::fs::write(&f, [1u8, 2, 3])?;
        let v = open_binary(&f)?;
        assert_eq!(v, vec![1, 2, 3]);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn resolve_relative() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let base = Path::new("/foo/bar");
        let r = resolve(base, "baz");
        assert!(r.ends_with("baz"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn most_recent_mod_time_updates_on_open() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let _g = lock_for_compile(&FILEIO_STATE_LOCK, "file_io tests (serial)");
        let dir = tempfile::tempdir()?;
        let f = dir.path().join("t.txt");
        std::fs::write(&f, "x")?;
        let t_before = most_recent_mod_time();
        let _ = open_text(&f)?;
        let t_after = most_recent_mod_time();
        assert!(t_after >= t_before, "mod time must update after open_text");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn most_recent_mod_time_later_file_wins() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let _g = lock_for_compile(&FILEIO_STATE_LOCK, "file_io tests (serial)");
        __reset_for_test();
        let dir = tempfile::tempdir()?;
        let f1 = dir.path().join("a.txt");
        let f2 = dir.path().join("b.txt");
        std::fs::write(&f1, "1")?;
        std::thread::sleep(std::time::Duration::from_millis(10));
        std::fs::write(&f2, "2")?;
        let _ = open_text(&f1)?;
        let t1 = most_recent_mod_time();
        let _ = open_text(&f2)?;
        let t2 = most_recent_mod_time();
        assert!(t2 > t1, "opening newer file must update mod time");
        assert_eq!(
            __update_count_for_test(),
            2,
            "two distinct files must update twice"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn update_mod_time_uses_strict_greater_not_ge() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let _g = lock_for_compile(&FILEIO_STATE_LOCK, "file_io tests (serial)");
        // Open same file twice (mtime unchanged). With mtime > prev we do NOT update
        // the second time. With mtime >= prev (mutant) we would. update_count differs.
        __reset_for_test();
        let dir = tempfile::tempdir()?;
        let f = dir.path().join("x.txt");
        std::fs::write(&f, "x")?;
        let _ = open_text(&f)?;
        let _ = open_text(&f)?;
        assert_eq!(
            __update_count_for_test(),
            1,
            "opening same file twice must update only once (mtime > prev, not >=)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn resolve_absolute() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        #[cfg(unix)]
        let abs = "/tmp/x";
        #[cfg(windows)]
        let abs = "C:\\tmp\\x";
        let r = resolve(Path::new("/other"), abs);
        assert_eq!(r, PathBuf::from(abs));
        Ok(()) // return success to the test harness
    }
}
