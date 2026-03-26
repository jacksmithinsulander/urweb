//! Static library: Persy embedded store for `dbms persy` Ur/Web builds.
//!
//! Build: `cargo build -p urweb-persy --release`
//! Link: `-L path/to/target/release -lurweb_persy` and `-I path/to/crates/urweb-persy/include`.
//! See `URWEB_NATIVE_LIB_DIR` in the main compiler (`cc_and_link`).

use std::ffi::{c_char, c_void};
use std::path::Path;

use persy::{ByteVec, Persy, ValueMode};

/// Persy index name (byte keys/values).
const IX: &str = "urweb_kv";

#[no_mangle]
pub unsafe extern "C" fn urweb_persy_open(path: *const c_char) -> *mut c_void {
    if path.is_null() {
        return std::ptr::null_mut();
    }
    let s = match std::ffi::CStr::from_ptr(path).to_str() {
        Ok(x) => x,
        Err(_) => return std::ptr::null_mut(),
    };
    let p: Persy = match Persy::open_or_create_with(Path::new(s), persy::Config::new(), |db| {
        if db.exists_index(IX)? {
            return Ok(());
        }
        let mut tx = db.begin()?;
        tx.create_index::<ByteVec, ByteVec>(IX, ValueMode::Replace)?;
        tx.prepare()?.commit()?;
        Ok(())
    }) {
        Ok(p) => p,
        Err(_) => return std::ptr::null_mut(),
    };
    Box::into_raw(Box::new(p)) as *mut c_void
}

#[no_mangle]
pub unsafe extern "C" fn urweb_persy_close(h: *mut c_void) {
    if h.is_null() {
        return;
    }
    drop(Box::from_raw(h as *mut Persy));
}

#[no_mangle]
pub unsafe extern "C" fn urweb_persy_put(
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
    let p = &*(h as *const Persy);

    let mut tx = match p.begin() {
        Ok(t) => t,
        Err(_) => return -1,
    };
    let index_ok = match tx.exists_index(IX) {
        Ok(b) => b,
        Err(_) => return -1,
    };
    if !index_ok {
        if tx
            .create_index::<ByteVec, ByteVec>(IX, ValueMode::Replace)
            .is_err()
        {
            return -1;
        }
    }
    if tx
        .put(IX, ByteVec::from(k.to_vec()), ByteVec::from(v.to_vec()))
        .is_err()
    {
        return -1;
    }
    let prep = match tx.prepare() {
        Ok(x) => x,
        Err(_) => return -1,
    };
    if prep.commit().is_err() {
        return -1;
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn urweb_persy_get(
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
    let p = &*(h as *const Persy);

    let key_bv = ByteVec::from(k.to_vec());
    let got = match p.one::<ByteVec, ByteVec>(IX, &key_bv) {
        Ok(x) => x,
        Err(_) => return -1,
    };
    let Some(bytes) = got else {
        return 1;
    };
    let v: Vec<u8> = bytes.into();
    let n = v.len();
    let buf = unsafe {
        extern "C" {
            fn malloc(size: usize) -> *mut c_void;
        }
        malloc(n) as *mut u8
    };
    if buf.is_null() {
        return -1;
    }
    std::ptr::copy_nonoverlapping(v.as_ptr(), buf, n);
    *out = buf;
    *out_len = n;
    0
}
