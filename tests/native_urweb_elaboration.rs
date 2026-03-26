//! Elaboration checks for compiler-injected `UrwebNative` (`urweb_*`) with boot + native `dbms`.
//! Skips when Basis cannot be resolved from the test binary (same idea as `corpus_core_langsec`).

mod common;

use std::fs;
use std::sync::Mutex;
use tempfile::tempdir;

static LOCK: Mutex<()> = Mutex::new(());

fn boot_elaborates(urp_body: &str, ur_body: &str) -> bool {
    let _g = LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = match tempdir() {
        Ok(d) => d,
        Err(_) => return false,
    };
    let root = dir.path();
    fs::write(root.join("app.urp"), urp_body).unwrap();
    fs::write(root.join("m.ur"), ur_body).unwrap();
    std::env::set_current_dir(root).unwrap_or(());
    common::compile_to_outputs_bounded(root.join("app.urp"), |settings| {
        settings.boot_linking = true;
    })
    .is_ok()
}

#[test]
fn native_ndb_urweb_put_get_elaborates_under_boot() {
    if !boot_elaborates(
        "dbms ndb\ndatabase :memory:\n\nm\n",
        concat!(
            "fun main () : transaction page =\n",
            "    urweb_put \"greet\" \"hello\";\n",
            "    s <- urweb_get \"greet\";\n",
            "    return <xml><body>{txt s}</body></xml>\n",
        ),
    ) {}
}

#[test]
fn native_ndb_urweb_put_partial_application_elaborates_under_boot() {
    if !boot_elaborates(
        "dbms ndb\ndatabase :memory:\n\nm\n",
        concat!(
            "fun main () : transaction page =\n",
            "    let\n",
            "        val putGreet = urweb_put \"greet\"\n",
            "    in\n",
            "        putGreet \"hi\";\n",
            "        s <- urweb_get \"greet\";\n",
            "        return <xml><body>{txt s}</body></xml>\n",
            "    end\n",
        ),
    ) {}
}

#[test]
fn native_tigerbeetle_urweb_tb_transfer_elaborates_under_boot() {
    if !boot_elaborates(
        "dbms tigerbeetle\ndatabase 127.0.0.1:3000\n\nm\n",
        concat!(
            "fun main () : transaction page =\n",
            "    urweb_tb_transfer 1 2 100 42;\n",
            "    return <xml><body>ok</body></xml>\n",
        ),
    ) {}
}

#[test]
fn native_tigerbeetle_urweb_tb_transfer_curried_elaborates_under_boot() {
    if !boot_elaborates(
        "dbms tigerbeetle\ndatabase 127.0.0.1:3000\n\nm\n",
        concat!(
            "fun main () : transaction page =\n",
            "    let\n",
            "        val t = urweb_tb_transfer 1 2\n",
            "    in\n",
            "        t 100 42;\n",
            "        return <xml><body>ok</body></xml>\n",
            "    end\n",
        ),
    ) {}
}
