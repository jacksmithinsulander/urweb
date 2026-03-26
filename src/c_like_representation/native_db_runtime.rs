//! Native DB runtimes (KV / ledger): C `uw_*` contract with vendor headers.
//!
//! Relational SQL (`query` / `dml` / prepared slots) is not executed here; use a
//! [`crate::db::ProjectDb::Sql`] backend for relational IR until native lowering exists.

use crate::c_like_representation::LocTyp;
use crate::db::{ProjectDb, ProjectDbCtx};
use crate::settings::Settings;

fn uw_client_init_sqlite_flavored() -> &'static str {
    concat!(
        "static void uw_client_init(void) {\n",
        "uw_sqlfmtInt = \"%lld%n\";\n",
        "uw_sqlfmtFloat = \"%.16g%n\";\n",
        "uw_Estrings = 0;\n",
        "uw_sql_type_annotations = 0;\n",
        "uw_sqlsuffixString = \"\";\n",
        "uw_sqlsuffixChar = \"\";\n",
        "uw_sqlsuffixBlob = \"\";\n",
        "uw_sqlfmtUint4 = \"%u%n\";\n",
        "}\n\n",
    )
}

fn relational_guard_fn(suffix: &str, backend: &str) -> String {
    format!(
        "static void uw_db_require_relational_disabled_{suffix}(uw_context ctx) {{\n\
         uw_error(ctx, FATAL, \"{backend}: relational SQL is not supported on this native runtime.\");\n\
         }}\n\n",
    )
}

fn needs_relational_guard(
    tables: &[(String, Vec<(String, LocTyp)>)],
    prepared: &[(String, usize)],
) -> bool {
    !tables.is_empty() || !prepared.is_empty()
}

/// RocksDB: `rocksdb_open` / `rocksdb_close`; no SQL prepare/exec.
pub(crate) fn emit_rocksdb_c_code(
    dbpath: &str,
    tables: &[(String, Vec<(String, LocTyp)>)],
    prepared: &[(String, usize)],
) -> String {
    let mut out = String::new();
    out.push_str("#include <rocksdb/c.h>\n");
    out.push_str("#include <stdlib.h>\n");
    out.push_str("#include <string.h>\n");
    out.push_str("#include <stdio.h>\n\n");

    let guard = needs_relational_guard(tables, prepared);
    if guard {
        out.push_str(&relational_guard_fn("rocks", "rocksdb"));
    }

    out.push_str("typedef struct {\nrocksdb_t *db;\nrocksdb_options_t *opts;\n");
    for i in 0..prepared.len() {
        out.push_str(&format!(
            "void *p{i}; /* reserved; SQL IR not supported */\n"
        ));
    }
    out.push_str("} uw_conn;\n\n");

    out.push_str(uw_client_init_sqlite_flavored());

    if guard {
        out.push_str(
            "static void uw_db_validate(uw_context ctx) {\n\
             uw_db_require_relational_disabled_rocks(ctx);\n\
             }\n\n",
        );
    } else {
        out.push_str("static void uw_db_validate(uw_context ctx) { }\n\n");
    }

    if guard || !prepared.is_empty() {
        out.push_str(
            "static void uw_db_prepare(uw_context ctx) {\n\
             uw_db_require_relational_disabled_rocks(ctx);\n\
             }\n\n",
        );
    } else {
        out.push_str("static void uw_db_prepare(uw_context ctx) { }\n\n");
    }

    let path = dbpath.replace('\\', "\\\\").replace('"', "\\\"");
    out.push_str("static void uw_db_init(uw_context ctx) {\n");
    out.push_str("char *err = NULL;\n");
    out.push_str("rocksdb_options_t *opts = rocksdb_options_create();\n");
    out.push_str("rocksdb_options_set_create_if_missing(opts, 1);\n");
    out.push_str(&format!(
        "rocksdb_t *db = rocksdb_open(opts, \"{path}\", &err);\n"
    ));
    out.push_str(
        "if (err != NULL) {\n\
         char buf[2048];\n\
         strncpy(buf, err, sizeof(buf) - 1);\n\
         buf[sizeof(buf)-1] = 0;\n\
         rocksdb_free(err);\n\
         rocksdb_options_destroy(opts);\n\
         uw_error(ctx, FATAL, \"RocksDB open failed: %s\", buf);\n\
         }\n",
    );
    out.push_str("uw_conn *conn = calloc(1, sizeof(uw_conn));\n");
    out.push_str("if (!conn) uw_error(ctx, FATAL, \"out of memory (uw_conn)\");\n");
    out.push_str("conn->db = db;\n");
    out.push_str("conn->opts = opts;\n");
    out.push_str("uw_set_db(ctx, conn);\n");
    out.push_str("uw_db_validate(ctx);\n");
    out.push_str("uw_db_prepare(ctx);\n");
    out.push_str("}\n\n");

    out.push_str("static void uw_db_close(uw_context ctx) {\n");
    out.push_str("uw_conn *conn = uw_get_db(ctx);\n");
    out.push_str("if (!conn) return;\n");
    out.push_str("if (conn->db) rocksdb_close(conn->db);\n");
    out.push_str("if (conn->opts) rocksdb_options_destroy(conn->opts);\n");
    out.push_str("free(conn);\n");
    out.push_str("}\n\n");

    out.push_str(concat!(
        "static int uw_db_begin(uw_context ctx, int could_write) { (void)ctx; (void)could_write; return 0; }\n",
        "static int uw_db_commit(uw_context ctx) { (void)ctx; return 0; }\n",
        "static int uw_db_rollback(uw_context ctx) { (void)ctx; return 0; }\n",
    ));

    out
}

pub(crate) fn emit_persy_c_code(
    dbpath: &str,
    tables: &[(String, Vec<(String, LocTyp)>)],
    prepared: &[(String, usize)],
) -> String {
    let mut out = String::new();
    out.push_str("#include <urweb_persy.h>\n");
    out.push_str("#include <stdlib.h>\n");
    out.push_str("#include <string.h>\n");
    out.push_str("#include <stdio.h>\n\n");

    let guard = needs_relational_guard(tables, prepared);
    if guard {
        out.push_str(&relational_guard_fn("persy", "persy"));
    }

    out.push_str("typedef struct {\nvoid *persy_handle;\n");
    for i in 0..prepared.len() {
        out.push_str(&format!(
            "void *p{i}; /* reserved; SQL IR not supported */\n"
        ));
    }
    out.push_str("} uw_conn;\n\n");

    out.push_str(uw_client_init_sqlite_flavored());

    if guard {
        out.push_str(
            "static void uw_db_validate(uw_context ctx) {\n\
             uw_db_require_relational_disabled_persy(ctx);\n\
             }\n\n",
        );
    } else {
        out.push_str("static void uw_db_validate(uw_context ctx) { }\n\n");
    }

    if guard || !prepared.is_empty() {
        out.push_str(
            "static void uw_db_prepare(uw_context ctx) {\n\
             uw_db_require_relational_disabled_persy(ctx);\n\
             }\n\n",
        );
    } else {
        out.push_str("static void uw_db_prepare(uw_context ctx) { }\n\n");
    }

    let path = dbpath.replace('\\', "\\\\").replace('"', "\\\"");
    out.push_str("static void uw_db_init(uw_context ctx) {\n");
    out.push_str("uw_conn *conn = calloc(1, sizeof(uw_conn));\n");
    out.push_str("if (!conn) uw_error(ctx, FATAL, \"out of memory (uw_conn)\");\n");
    out.push_str(&format!("void *ph = urweb_persy_open(\"{path}\");\n"));
    out.push_str(
        "if (!ph) {\n\
         free(conn);\n\
         uw_error(ctx, FATAL, \"Persy open failed\");\n\
         }\n",
    );
    out.push_str("conn->persy_handle = ph;\n");
    out.push_str("uw_set_db(ctx, conn);\n");
    out.push_str("uw_db_validate(ctx);\n");
    out.push_str("uw_db_prepare(ctx);\n");
    out.push_str("}\n\n");

    out.push_str("static void uw_db_close(uw_context ctx) {\n");
    out.push_str("uw_conn *conn = uw_get_db(ctx);\n");
    out.push_str("if (!conn) return;\n");
    out.push_str("if (conn->persy_handle) urweb_persy_close(conn->persy_handle);\n");
    out.push_str("free(conn);\n");
    out.push_str("}\n\n");

    out.push_str(concat!(
        "static int uw_db_begin(uw_context ctx, int could_write) { (void)ctx; (void)could_write; return 0; }\n",
        "static int uw_db_commit(uw_context ctx) { (void)ctx; return 0; }\n",
        "static int uw_db_rollback(uw_context ctx) { (void)ctx; return 0; }\n",
    ));

    out
}

/// NDB-style line file ([`urweb_ndb`](../../crates/urweb-ndb)): **`UrK=` / `UrV=`** records via the
/// `urweb_ndb_*` Rust staticlib — **ISO C11**, same link/include pattern as Persy (`-lurweb_ndb`,
/// `URWEB_NATIVE_LIB_DIR` or workspace `target/{debug,release}` from boot root).
pub(crate) fn emit_ndb_c_code(
    dbpath: &str,
    tables: &[(String, Vec<(String, LocTyp)>)],
    prepared: &[(String, usize)],
) -> String {
    let mut out = String::new();
    out.push_str("#include <urweb_ndb.h>\n");
    out.push_str("#include <stdlib.h>\n");
    out.push_str("#include <string.h>\n");
    out.push_str("#include <stdio.h>\n\n");

    let guard = needs_relational_guard(tables, prepared);
    if guard {
        out.push_str(&relational_guard_fn("ndb", "ndb"));
    }

    out.push_str("typedef struct {\nvoid *ndb_handle;\n");
    for i in 0..prepared.len() {
        out.push_str(&format!(
            "void *p{i}; /* reserved; SQL IR not supported */\n"
        ));
    }
    out.push_str("} uw_conn;\n\n");

    out.push_str(uw_client_init_sqlite_flavored());

    if guard {
        out.push_str(
            "static void uw_db_validate(uw_context ctx) {\n\
             uw_db_require_relational_disabled_ndb(ctx);\n\
             }\n\n",
        );
    } else {
        out.push_str("static void uw_db_validate(uw_context ctx) { }\n\n");
    }

    if guard || !prepared.is_empty() {
        out.push_str(
            "static void uw_db_prepare(uw_context ctx) {\n\
             uw_db_require_relational_disabled_ndb(ctx);\n\
             }\n\n",
        );
    } else {
        out.push_str("static void uw_db_prepare(uw_context ctx) { }\n\n");
    }

    let path_esc = dbpath.replace('\\', "\\\\").replace('"', "\\\"");
    out.push_str("static void uw_db_init(uw_context ctx) {\n");
    out.push_str("uw_conn *conn = calloc(1, sizeof(uw_conn));\n");
    out.push_str("if (!conn) uw_error(ctx, FATAL, \"out of memory (uw_conn)\");\n");
    if dbpath.is_empty() {
        out.push_str("void *nh = urweb_ndb_open(\":memory:\");\n");
    } else {
        out.push_str(&format!("void *nh = urweb_ndb_open(\"{path_esc}\");\n"));
    }
    out.push_str(
        "if (!nh) {\n\
         free(conn);\n\
         uw_error(ctx, FATAL, \"urweb_ndb_open failed\");\n\
         }\n",
    );
    out.push_str("conn->ndb_handle = nh;\n");
    out.push_str("uw_set_db(ctx, conn);\n");
    out.push_str("uw_db_validate(ctx);\n");
    out.push_str("uw_db_prepare(ctx);\n");
    out.push_str("}\n\n");

    out.push_str("static void uw_db_close(uw_context ctx) {\n");
    out.push_str("uw_conn *conn = uw_get_db(ctx);\n");
    out.push_str("if (!conn) return;\n");
    out.push_str("if (conn->ndb_handle) urweb_ndb_close(conn->ndb_handle);\n");
    out.push_str("free(conn);\n");
    out.push_str("}\n\n");

    out.push_str(concat!(
        "static int uw_db_begin(uw_context ctx, int could_write) { (void)ctx; (void)could_write; return 0; }\n",
        "static int uw_db_commit(uw_context ctx) { (void)ctx; return 0; }\n",
        "static int uw_db_rollback(uw_context ctx) { (void)ctx; return 0; }\n",
    ));

    out
}

pub(crate) fn emit_tigerbeetle_c_code(
    dbpath: &str,
    tables: &[(String, Vec<(String, LocTyp)>)],
    prepared: &[(String, usize)],
) -> String {
    let mut out = String::new();
    out.push_str("#include <tb_client.h>\n");
    out.push_str("#include <stdint.h>\n");
    out.push_str("#include <stdlib.h>\n");
    out.push_str("#include <stdio.h>\n");
    out.push_str("#include <string.h>\n");
    out.push_str("#include <pthread.h>\n\n");

    let guard = needs_relational_guard(tables, prepared);
    if guard {
        out.push_str(&relational_guard_fn("tigerbeetle", "tigerbeetle"));
    }

    out.push_str("typedef struct {\ntb_client_t tb_client;\n");
    for i in 0..prepared.len() {
        out.push_str(&format!(
            "void *p{i}; /* reserved; SQL IR not supported */\n"
        ));
    }
    out.push_str("} uw_conn;\n\n");

    out.push_str(
        "typedef struct {\n\
         pthread_mutex_t mu;\n\
         pthread_cond_t cv;\n\
         int done;\n\
         uint8_t pkt_status;\n\
         uint32_t xfer_status;\n\
         } urweb_tb_submit_sync;\n\n",
    );

    out.push_str(uw_client_init_sqlite_flavored());

    if guard {
        out.push_str(
            "static void uw_db_validate(uw_context ctx) {\n\
             uw_db_require_relational_disabled_tigerbeetle(ctx);\n\
             }\n\n",
        );
    } else {
        out.push_str("static void uw_db_validate(uw_context ctx) { }\n\n");
    }

    if guard || !prepared.is_empty() {
        out.push_str(
            "static void uw_db_prepare(uw_context ctx) {\n\
             uw_db_require_relational_disabled_tigerbeetle(ctx);\n\
             }\n\n",
        );
    } else {
        out.push_str("static void uw_db_prepare(uw_context ctx) { }\n\n");
    }

    let path = dbpath.replace('\\', "\\\\").replace('"', "\\\"");
    out.push_str(
        "static void urweb_tb_on_complete(uintptr_t userdata, tb_packet_t *packet, uint64_t timestamp, const uint8_t *result, uint32_t result_size) {\n\
         (void)userdata;\n\
         (void)timestamp;\n\
         if (!packet || !packet->user_data) return;\n\
         urweb_tb_submit_sync *sync = (urweb_tb_submit_sync *)packet->user_data;\n\
         pthread_mutex_lock(&sync->mu);\n\
         sync->pkt_status = packet->status;\n\
         sync->xfer_status = 0;\n\
         if (packet->status == TB_PACKET_OK && result != NULL && result_size >= sizeof(tb_create_transfer_result_t)) {\n\
         sync->xfer_status = ((const tb_create_transfer_result_t *)result)->status;\n\
         }\n\
         sync->done = 1;\n\
         pthread_cond_signal(&sync->cv);\n\
         pthread_mutex_unlock(&sync->mu);\n\
         }\n\n",
    );

    out.push_str("static void uw_db_init(uw_context ctx) {\n");
    out.push_str("uw_conn *conn = calloc(1, sizeof(uw_conn));\n");
    out.push_str("if (!conn) uw_error(ctx, FATAL, \"out of memory (uw_conn)\");\n");
    out.push_str("static const uint8_t urweb_tb_cluster_zero[16] = {0};\n");
    out.push_str(&format!("const char *tb_addr = \"{path}\";\n"));
    out.push_str(
        "uint32_t tb_alen = (uint32_t)strlen(tb_addr);\n\
         TB_INIT_STATUS tbs = tb_client_init(&conn->tb_client, urweb_tb_cluster_zero, tb_addr, tb_alen, 0, urweb_tb_on_complete);\n\
         if (tbs != TB_INIT_SUCCESS) {\n\
         free(conn);\n\
         uw_error(ctx, FATAL, \"TigerBeetle tb_client_init failed (status %d)\", (int)tbs);\n\
         }\n",
    );
    out.push_str("uw_set_db(ctx, conn);\n");
    out.push_str("uw_db_validate(ctx);\n");
    out.push_str("uw_db_prepare(ctx);\n");
    out.push_str("}\n\n");

    out.push_str("static void uw_db_close(uw_context ctx) {\n");
    out.push_str("uw_conn *conn = uw_get_db(ctx);\n");
    out.push_str("if (!conn) return;\n");
    out.push_str("(void)tb_client_deinit(&conn->tb_client);\n");
    out.push_str("free(conn);\n");
    out.push_str("}\n\n");

    out.push_str(concat!(
        "static int uw_db_begin(uw_context ctx, int could_write) { (void)ctx; (void)could_write; return 0; }\n",
        "static int uw_db_commit(uw_context ctx) { (void)ctx; return 0; }\n",
        "static int uw_db_rollback(uw_context ctx) { (void)ctx; return 0; }\n",
    ));

    out
}

/// C implementations for [`crate::compiler`] synthetic `UrwebNative` FFI (`uw_UrwebNative_*`).
pub(crate) fn emit_urweb_native_ffi_bundle(settings: &Settings) -> String {
    let db = ProjectDbCtx::new(&settings.db_backend).resolved();
    if !db.exposes_urweb_native_surface() {
        return String::new();
    }
    let mut s = String::from(
        "\n/* ---- UrwebNative FFI (compiler-injected; native db backends only) ---- */\n",
    );
    s.push_str("#include <stdint.h>\n#include <string.h>\n#include <stdlib.h>\n");
    match db {
        ProjectDb::Rocksdb => s.push_str("#include <rocksdb/c.h>\n"),
        ProjectDb::Persy => s.push_str("#include <urweb_persy.h>\n"),
        ProjectDb::Ndb => s.push_str("#include <urweb_ndb.h>\n"),
        ProjectDb::Tigerbeetle => s.push_str("#include <tb_client.h>\n"),
        _ => {}
    }

    s.push_str(
        "static uw_unit uw_UrwebNative_urweb_put(uw_context ctx, uw_Basis_string k, uw_Basis_string v) {\n\
         uw_ensure_transaction(ctx);\n\
         uw_conn *c = uw_get_db(ctx);\n\
         if (!c) uw_error(ctx, FATAL, \"urweb_put: no DB connection\");\n\
         if (!k || !v) uw_error(ctx, FATAL, \"urweb_put: null string\");\n",
    );
    match db {
        ProjectDb::Rocksdb => {
            s.push_str(
                "size_t kn = strlen(k);\n\
                 size_t vn = strlen(v);\n\
                 char *err = NULL;\n\
                 rocksdb_writeoptions_t *wo = rocksdb_writeoptions_create();\n\
                 if (!wo) uw_error(ctx, FATAL, \"urweb_put: rocksdb_writeoptions_create\");\n\
                 rocksdb_put(c->db, wo, k, kn, v, vn, &err);\n\
                 rocksdb_writeoptions_destroy(wo);\n\
                 if (err != NULL) { uw_error(ctx, FATAL, \"urweb_put: %s\", err); }\n",
            );
        }
        ProjectDb::Persy => {
            s.push_str(
                "if (!c->persy_handle) uw_error(ctx, FATAL, \"urweb_put: no Persy handle\");\n\
                 size_t kn = strlen(k);\n\
                 size_t vn = strlen(v);\n\
                 if (urweb_persy_put(c->persy_handle, (const uint8_t *)k, kn, (const uint8_t *)v, vn) != 0)\n\
                 uw_error(ctx, FATAL, \"urweb_put: persy put failed\");\n",
            );
        }
        ProjectDb::Tigerbeetle => {
            s.push_str(
                "(void)k;\n\
                 (void)v;\n\
                 uw_error(ctx, FATAL, \"urweb_put: TigerBeetle is a ledger (not a KV store). Use dbms persy, ndb, or rocksdb for urweb_put/urweb_get, or urweb_tb_transfer on tigerbeetle.\");\n",
            );
        }
        ProjectDb::Ndb => {
            s.push_str(
                "if (!c->ndb_handle) uw_error(ctx, FATAL, \"urweb_put: no ndb handle\");\n\
                 size_t kn = strlen(k);\n\
                 size_t vn = strlen(v);\n\
                 if (urweb_ndb_put(c->ndb_handle, (const uint8_t *)k, kn, (const uint8_t *)v, vn) != 0)\n\
                 uw_error(ctx, FATAL, \"urweb_put: ndb put failed (invalid UTF-8 or '='/newline in key or value)\");\n",
            );
        }
        _ => {}
    }
    s.push_str("return 0;\n}\n\n");

    s.push_str(
        "static uw_Basis_string uw_UrwebNative_urweb_get(uw_context ctx, uw_Basis_string k) {\n\
         uw_ensure_transaction(ctx);\n\
         uw_conn *c = uw_get_db(ctx);\n\
         if (!c) uw_error(ctx, FATAL, \"urweb_get: no DB connection\");\n\
         if (!k) uw_error(ctx, FATAL, \"urweb_get: null key\");\n",
    );
    match db {
        ProjectDb::Rocksdb => {
            s.push_str(
                "size_t kn = strlen(k);\n\
                 char *err = NULL;\n\
                 size_t vlen = 0;\n\
                 rocksdb_readoptions_t *ro = rocksdb_readoptions_create();\n\
                 if (!ro) uw_error(ctx, FATAL, \"urweb_get: rocksdb_readoptions_create\");\n\
                 char *raw = rocksdb_get(c->db, ro, k, kn, &vlen, &err);\n\
                 rocksdb_readoptions_destroy(ro);\n\
                 if (err != NULL) uw_error(ctx, FATAL, \"urweb_get: %s\", err);\n\
                 if (raw == NULL) return uw_strdup(ctx, \"\");\n\
                 uw_Basis_string r = uw_strdup(ctx, raw);\n\
                 rocksdb_free(raw);\n\
                 return r;\n",
            );
        }
        ProjectDb::Persy => {
            s.push_str(
                "if (!c->persy_handle) uw_error(ctx, FATAL, \"urweb_get: no Persy handle\");\n\
                 size_t kn = strlen(k);\n\
                 uint8_t *buf = NULL;\n\
                 size_t n = 0;\n\
                 int gr = urweb_persy_get(c->persy_handle, (const uint8_t *)k, kn, &buf, &n);\n\
                 if (gr < 0) uw_error(ctx, FATAL, \"urweb_get: persy read failed\");\n\
                 if (gr != 0) return uw_strdup(ctx, \"\");\n\
                 char *tmp = (char *)malloc(n + 1);\n\
                 if (!tmp) uw_error(ctx, FATAL, \"urweb_get: malloc\");\n\
                 memcpy(tmp, buf, n);\n\
                 tmp[n] = 0;\n\
                 free(buf);\n\
                 uw_Basis_string r = uw_strdup(ctx, tmp);\n\
                 free(tmp);\n\
                 return r;\n",
            );
        }
        ProjectDb::Tigerbeetle => {
            s.push_str(
                "(void)k;\n\
                 uw_error(ctx, FATAL, \"urweb_get: TigerBeetle is a ledger (not a KV store). Use dbms persy, ndb, or rocksdb for urweb_put/urweb_get, or urweb_tb_transfer on tigerbeetle.\");\n\
                 return NULL;\n",
            );
        }
        ProjectDb::Ndb => {
            s.push_str(
                "if (!c->ndb_handle) uw_error(ctx, FATAL, \"urweb_get: no ndb handle\");\n\
                 size_t kn = strlen(k);\n\
                 uint8_t *buf = NULL;\n\
                 size_t n = 0;\n\
                 int gr = urweb_ndb_get(c->ndb_handle, (const uint8_t *)k, kn, &buf, &n);\n\
                 if (gr < 0) uw_error(ctx, FATAL, \"urweb_get: ndb read failed\");\n\
                 if (gr != 0) return uw_strdup(ctx, \"\");\n\
                 char *tmp = (char *)malloc(n + 1);\n\
                 if (!tmp) uw_error(ctx, FATAL, \"urweb_get: malloc\");\n\
                 memcpy(tmp, buf, n);\n\
                 tmp[n] = 0;\n\
                 free(buf);\n\
                 uw_Basis_string r = uw_strdup(ctx, tmp);\n\
                 free(tmp);\n\
                 return r;\n",
            );
        }
        _ => {}
    }
    s.push_str("}\n\n");

    s.push_str(
        "static uw_unit uw_UrwebNative_urweb_tb_transfer(\n\
             uw_context ctx,\n\
             uw_Basis_int debit_id,\n\
             uw_Basis_int credit_id,\n\
             uw_Basis_int amount,\n\
             uw_Basis_int xfer_id) {\n\
         uw_ensure_transaction(ctx);\n",
    );
    match db {
        ProjectDb::Tigerbeetle => {
            s.push_str(
                "uw_conn *c = uw_get_db(ctx);\n\
                 if (!c) uw_error(ctx, FATAL, \"urweb_tb_transfer: no DB connection\");\n\
                 if (debit_id < 1 || credit_id < 1 || xfer_id < 1)\n\
                 uw_error(ctx, FATAL, \"urweb_tb_transfer: debit_id, credit_id, and xfer_id must be >= 1 (TigerBeetle 128-bit ids use the lower 64 bits from Basis.int; zero is invalid)\");\n\
                 if (amount < 0) uw_error(ctx, FATAL, \"urweb_tb_transfer: amount must be non-negative\");\n\
                 tb_transfer_t tb_tr;\n\
                 memset(&tb_tr, 0, sizeof(tb_tr));\n\
                 tb_tr.id = (tb_uint128_t)(uint64_t)xfer_id;\n\
                 tb_tr.debit_account_id = (tb_uint128_t)(uint64_t)debit_id;\n\
                 tb_tr.credit_account_id = (tb_uint128_t)(uint64_t)credit_id;\n\
                 tb_tr.amount = (tb_uint128_t)(uint64_t)amount;\n\
                 tb_tr.ledger = 1;\n\
                 tb_tr.code = 1;\n\
                 tb_packet_t pkt;\n\
                 memset(&pkt, 0, sizeof(pkt));\n\
                 urweb_tb_submit_sync sync;\n\
                 memset(&sync, 0, sizeof(sync));\n\
                 if (pthread_mutex_init(&sync.mu, NULL) != 0)\n\
                 uw_error(ctx, FATAL, \"urweb_tb_transfer: pthread_mutex_init failed\");\n\
                 if (pthread_cond_init(&sync.cv, NULL) != 0) {\n\
                 pthread_mutex_destroy(&sync.mu);\n\
                 uw_error(ctx, FATAL, \"urweb_tb_transfer: pthread_cond_init failed\");\n\
                 }\n\
                 pkt.user_data = &sync;\n\
                 pkt.data = &tb_tr;\n\
                 pkt.data_size = sizeof(tb_tr);\n\
                 pkt.operation = TB_OPERATION_CREATE_TRANSFERS;\n\
                 if (tb_client_submit(&c->tb_client, &pkt) != TB_CLIENT_OK) {\n\
                 pthread_mutex_destroy(&sync.mu);\n\
                 pthread_cond_destroy(&sync.cv);\n\
                 uw_error(ctx, FATAL, \"urweb_tb_transfer: tb_client_submit failed\");\n\
                 }\n\
                 pthread_mutex_lock(&sync.mu);\n\
                 while (!sync.done) pthread_cond_wait(&sync.cv, &sync.mu);\n\
                 uint8_t ps = sync.pkt_status;\n\
                 uint32_t xs = sync.xfer_status;\n\
                 pthread_mutex_unlock(&sync.mu);\n\
                 pthread_mutex_destroy(&sync.mu);\n\
                 pthread_cond_destroy(&sync.cv);\n\
                 if (ps != TB_PACKET_OK)\n\
                 uw_error(ctx, FATAL, \"urweb_tb_transfer: packet status %u (see TB_PACKET_STATUS in tb_client.h)\", (unsigned)ps);\n\
                 if (xs != (uint32_t)TB_CREATE_TRANSFER_CREATED)\n\
                 uw_error(ctx, FATAL, \"urweb_tb_transfer: transfer rejected with status %u (see TB_CREATE_TRANSFER_* in tb_client.h)\", xs);\n",
            );
        }
        _ => {
            s.push_str(
                "(void)debit_id;\n\
                 (void)credit_id;\n\
                 (void)amount;\n\
                 (void)xfer_id;\n\
                 uw_error(ctx, FATAL, \"urweb_tb_transfer: use dbms tigerbeetle\");\n",
            );
        }
    }
    s.push_str("return 0;\n}\n");

    s
}
