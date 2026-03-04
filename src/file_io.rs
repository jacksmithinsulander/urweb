//! File I/O and path resolution.
//!
//! - **open_text** / **open_binary**: read files, update most_recent_mod_time
//! - **resolve**: resolve path relative to base
//! - **most_recent_mod_time**: for incremental builds

use anyhow::Context;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

/// Tracks the most-recent modification time of any file opened via this module
/// (mirrors SML's `FileIO.mostRecentModTimeRef`).
static MOST_RECENT_MOD: std::sync::Mutex<Option<SystemTime>> = std::sync::Mutex::new(None);

/// Number of times the mod-time tracker was updated (for tests; > vs >= is observable here).
static UPDATE_COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn update_mod_time(path: &Path) {
    if let Ok(meta) = std::fs::metadata(path) {
        if let Ok(mtime) = meta.modified() {
            let mut guard = MOST_RECENT_MOD.lock().unwrap();
            if guard.map_or(true, |prev| mtime > prev) {
                *guard = Some(mtime);
                UPDATE_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
        }
    }
}

/// Returns how many times the mod-time tracker was updated (tests only).
pub(crate) fn __update_count_for_test() -> usize {
    UPDATE_COUNT.load(std::sync::atomic::Ordering::Relaxed)
}

/// Resets mod-time state for tests.
pub(crate) fn __reset_for_test() {
    *MOST_RECENT_MOD.lock().unwrap() = None;
    UPDATE_COUNT.store(0, std::sync::atomic::Ordering::Relaxed);
}

/// Returns the most recent modification time seen, or `SystemTime::UNIX_EPOCH` if none.
pub fn most_recent_mod_time() -> SystemTime {
    MOST_RECENT_MOD
        .lock()
        .unwrap()
        .unwrap_or(SystemTime::UNIX_EPOCH)
}

/// Open a text file for reading, updating the mod-time tracker.
pub fn open_text(path: impl AsRef<Path>) -> anyhow::Result<String> {
    let path = path.as_ref();
    update_mod_time(path);
    std::fs::read_to_string(path).with_context(|| format!("opening {}", path.display()))
}

/// Open a binary file for reading, updating the mod-time tracker.
pub fn open_binary(path: impl AsRef<Path>) -> anyhow::Result<Vec<u8>> {
    let path = path.as_ref();
    update_mod_time(path);
    std::fs::read(path).with_context(|| format!("opening {}", path.display()))
}

/// Resolve a filename relative to a base directory, with fallback to the
/// filename itself (mirrors `OS.Path.concat` with `handle Path`).
pub fn resolve(base: impl AsRef<Path>, name: &str) -> PathBuf {
    let base = base.as_ref();
    if Path::new(name).is_absolute() {
        PathBuf::from(name)
    } else {
        base.join(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    static FILEIO_STATE_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn open_text_reads_file() {
        let _g = FILEIO_STATE_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("t.txt");
        std::fs::write(&f, "hello").unwrap();
        let s = open_text(&f).unwrap();
        assert_eq!(s, "hello");
    }

    #[test]
    fn open_binary_reads_file() {
        let _g = FILEIO_STATE_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("t.bin");
        std::fs::write(&f, [1u8, 2, 3]).unwrap();
        let v = open_binary(&f).unwrap();
        assert_eq!(v, vec![1, 2, 3]);
    }

    #[test]
    fn resolve_relative() {
        let base = Path::new("/foo/bar");
        let r = resolve(base, "baz");
        assert!(r.ends_with("baz"));
    }

    #[test]
    fn most_recent_mod_time_updates_on_open() {
        let _g = FILEIO_STATE_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("t.txt");
        std::fs::write(&f, "x").unwrap();
        let t_before = most_recent_mod_time();
        let _ = open_text(&f).unwrap();
        let t_after = most_recent_mod_time();
        assert!(t_after >= t_before, "mod time must update after open_text");
    }

    #[test]
    fn most_recent_mod_time_later_file_wins() {
        let _g = FILEIO_STATE_LOCK.lock().unwrap();
        __reset_for_test();
        let dir = tempfile::tempdir().unwrap();
        let f1 = dir.path().join("a.txt");
        let f2 = dir.path().join("b.txt");
        std::fs::write(&f1, "1").unwrap();
        std::thread::sleep(std::time::Duration::from_millis(10));
        std::fs::write(&f2, "2").unwrap();
        let _ = open_text(&f1).unwrap();
        let t1 = most_recent_mod_time();
        let _ = open_text(&f2).unwrap();
        let t2 = most_recent_mod_time();
        assert!(t2 > t1, "opening newer file must update mod time");
        assert_eq!(
            __update_count_for_test(),
            2,
            "two distinct files must update twice"
        );
    }

    #[test]
    fn update_mod_time_uses_strict_greater_not_ge() {
        let _g = FILEIO_STATE_LOCK.lock().unwrap();
        // Open same file twice (mtime unchanged). With mtime > prev we do NOT update
        // the second time. With mtime >= prev (mutant) we would. update_count differs.
        __reset_for_test();
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("x.txt");
        std::fs::write(&f, "x").unwrap();
        let _ = open_text(&f).unwrap();
        let _ = open_text(&f).unwrap();
        assert_eq!(
            __update_count_for_test(),
            1,
            "opening same file twice must update only once (mtime > prev, not >=)"
        );
    }

    #[test]
    fn resolve_absolute() {
        #[cfg(unix)]
        let abs = "/tmp/x";
        #[cfg(windows)]
        let abs = "C:\\tmp\\x";
        let r = resolve(Path::new("/other"), abs);
        assert_eq!(r, PathBuf::from(abs));
    }
}
