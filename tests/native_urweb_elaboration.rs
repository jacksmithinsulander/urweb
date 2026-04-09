//! Elaboration checks for compiler-injected `UrwebNative` (`urweb_*`) with boot + native `dbms`.
//! Skips when Basis cannot be resolved from the test binary (same idea as `corpus_core_langsec`).

mod common;

fn boot_elaborates(urp_body: &str, ur_body: &str) -> bool {
    let dir = common::tempdir("native_urweb_elaboration tempdir");
    let root = dir.path();
    common::write_file(
        &root.join("app.urp"),
        urp_body,
        "write app.urp for native elaboration test",
    );
    common::write_file(
        &root.join("m.ur"),
        ur_body,
        "write m.ur for native elaboration test",
    );
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
