//! Line-oriented `UrK=` / `UrV=` records — same surface convention as the old plan9port
//! emitter, implemented in Rust and exposed as a normal **staticlib** for ISO C11 builds.

use std::ffi::{c_char, c_void};
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

const PREFIX_K: &str = "UrK=";
const MID_V: &str = " UrV=";

struct Handle {
    path: PathBuf,
    lock: Mutex<()>,
}

fn valid_field(bytes: &[u8]) -> bool {
    !bytes.is_empty()
        && !bytes.contains(&b'=')
        && !bytes.contains(&b'\n')
        && !bytes.contains(&b'\r')
}

fn resolve_path(path: &str) -> Option<PathBuf> {
    if path.is_empty() {
        return None;
    }
    if path == ":memory:" {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .ok()?
            .as_nanos();
        let mut p = std::env::temp_dir();
        p.push(format!("urweb_ndb_{}_{}.txt", std::process::id(), nanos));
        return Some(p);
    }
    Some(PathBuf::from(path))
}

fn open_create_append(path: &Path) -> std::io::Result<()> {
    OpenOptions::new()
        .create(true)
        .append(true)
        .read(true)
        .open(path)
        .map(|_| ())
}

/// Open or create an NDB-backed line file. Returns an opaque handle or null on error.
///
/// # Safety
///
/// `path` must be a valid, null-terminated C string pointer, or null.
#[no_mangle]
pub unsafe extern "C" fn urweb_ndb_open(path: *const c_char) -> *mut c_void {
    if path.is_null() {
        return std::ptr::null_mut();
    }
    let s = match std::ffi::CStr::from_ptr(path).to_str() {
        Ok(x) => x,
        Err(_) => return std::ptr::null_mut(),
    };
    let Some(pb) = resolve_path(s) else {
        return std::ptr::null_mut();
    };
    if open_create_append(&pb).is_err() {
        return std::ptr::null_mut();
    }
    Box::into_raw(Box::new(Handle {
        path: pb,
        lock: Mutex::new(()),
    })) as *mut c_void
}

/// Release a handle returned by [`urweb_ndb_open`].
///
/// # Safety
///
/// `h` must be null or a pointer previously returned by `urweb_ndb_open` and not yet closed.
#[no_mangle]
pub unsafe extern "C" fn urweb_ndb_close(h: *mut c_void) {
    if h.is_null() {
        return;
    }
    drop(Box::from_raw(h as *mut Handle));
}

/// Append one `UrK=... UrV=...` line for `key`/`val`. Returns 0 on success.
///
/// # Safety
///
/// `h` must be a live handle from `urweb_ndb_open`. `key`/`val` must be valid for `key_len`/`val_len`
/// bytes and not alias if the contract requires disjoint buffers (callers must ensure validity).
#[no_mangle]
pub unsafe extern "C" fn urweb_ndb_put(
    h: *mut c_void,
    key: *const u8,
    key_len: usize,
    val: *const u8,
    val_len: usize,
) -> i32 {
    if h.is_null() || key.is_null() || val.is_null() {
        return -1;
    }
    let k = std::slice::from_raw_parts(key, key_len);
    let v = std::slice::from_raw_parts(val, val_len);
    if !valid_field(k) || !valid_field(v) {
        return -1;
    }
    let (Ok(_ks), Ok(_vs)) = (std::str::from_utf8(k), std::str::from_utf8(v)) else {
        return -1;
    };
    let handle = &*(h as *const Handle);
    let _g = match handle.lock.lock() {
        Ok(g) => g,
        Err(_) => return -1,
    };
    let mut f = match OpenOptions::new()
        .create(true)
        .append(true)
        .open(&handle.path)
    {
        Ok(f) => f,
        Err(_) => return -1,
    };
    let line = format!("{PREFIX_K}{}{MID_V}{}\n", _ks, _vs);
    if f.write_all(line.as_bytes()).is_err() {
        return -1;
    }
    if f.flush().is_err() {
        return -1;
    }
    0
}

/// Look up the last value for `key`. On success sets `*out` and `*out_len` to a `malloc`ed buffer.
///
/// # Safety
///
/// `h` must be a live handle. `key` must be valid for `key_len` bytes. `out` and `out_len` must be
/// valid for writes. If this returns 0, the caller must `free` `*out` when done.
#[no_mangle]
pub unsafe extern "C" fn urweb_ndb_get(
    h: *mut c_void,
    key: *const u8,
    key_len: usize,
    out: *mut *mut u8,
    out_len: *mut usize,
) -> i32 {
    if h.is_null() || key.is_null() || out.is_null() || out_len.is_null() {
        return -1;
    }
    *out = std::ptr::null_mut();
    *out_len = 0;

    let k = std::slice::from_raw_parts(key, key_len);
    let Ok(ks) = std::str::from_utf8(k) else {
        return -1;
    };
    let handle = &*(h as *const Handle);
    let _g = match handle.lock.lock() {
        Ok(g) => g,
        Err(_) => return -1,
    };
    let mut buf = String::new();
    let mut f = match std::fs::File::open(&handle.path) {
        Ok(f) => f,
        Err(_) => return -1,
    };
    if f.read_to_string(&mut buf).is_err() {
        return -1;
    }

    let mut found: Option<Vec<u8>> = None;
    for raw_line in buf.lines() {
        let line = raw_line.trim_end_matches('\r');
        let Some(rest) = line.strip_prefix(PREFIX_K) else {
            continue;
        };
        let Some((kpart, vpart)) = rest.split_once(MID_V) else {
            continue;
        };
        if kpart == ks {
            found = Some(vpart.as_bytes().to_vec());
        }
    }

    let Some(bytes) = found else {
        return 1;
    };
    let n = bytes.len();
    let p = unsafe {
        extern "C" {
            fn malloc(size: usize) -> *mut c_void;
        }
        malloc(n) as *mut u8
    };
    if p.is_null() {
        return -1;
    }
    unsafe {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), p, n);
        *out = p;
        *out_len = n;
    }
    0
}
