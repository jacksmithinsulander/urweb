//! Database **driver** routing for C emission.
//!
//! # SQL track: `uw_*` / `uw_conn` contract
//!
//! [`crate::c_like_representation::relational_sql_runtime`] implements the client for
//! `sqlite`, `mysql`, and `postgres` (`ProjectDb::Sql`).
//!
//! # Native track: KV / ledger
//!
//! [`crate::c_like_representation::native_db_runtime`] emits vendor-oriented `uw_*` shims:
//! RocksDB opens a real `rocksdb_t*`; Persy uses `urweb_persy_*`; TigerBeetle uses `tb_client_*`;
//! **ndb** uses the in-repo **`urweb_ndb`** Rust staticlib (line file `UrK=`/`UrV=`, ISO C, `-lurweb_ndb`).
//!
//! ## Compiler-injected `UrwebNative` (`urweb_*`)
//!
//! When the project uses a native `dbms`, the compiler opens [`UrwebNative`](crate::compiler) with:
//!
//! - **`urweb_put` / `urweb_get`** — string KV for **Persy, RocksDB, and ndb (`urweb_ndb`)** only.
//!   TigerBeetle is a **ledger**, not a KV store; those calls fail at runtime with an explanatory error.
//!   Use **`urweb_tb_transfer`** on `dbms tigerbeetle` instead.
//! - **`urweb_tb_transfer debit credit amount xfer_id`** — curried `int → … → transaction unit`.
//!   Emitted C submits one [`TB_OPERATION_CREATE_TRANSFERS`](https://github.com/tigerbeetle/tigerbeetle)
//!   via `tb_client_submit`, blocks on pthread condition variables until the async completion runs,
//!   then checks `TB_CREATE_TRANSFER_CREATED`. **Account and transfer ids** are taken from `Basis.int`
//!   and zero-extended to 128-bit (only the lower **64** bits are set today). TigerBeetle rejects zero
//!   ids; generated C requires `debit_id`, `credit_id`, and `xfer_id` ≥ 1.
//!   **`ledger`** and **`code`** on the wire are fixed at **1** until manifest-level knobs exist.
//! - **Cluster id** — `uw_db_init` passes an all-zero 16-byte cluster id to `tb_client_init`.
//!   Production TigerBeetle deployments must use the real cluster id (future: env or `.urp` field).
//!
//! Layouts match the expected headers for linking. **Relational** `table` / SQL IR is rejected in generated C
//! when the project would emit non-empty schema validation or prepared SQL against these backends,
//! until lowering to native operations is implemented.
//!
//! The generated translation unit defines symbols consumed by `urweb.c` and the mono/CJR layer:
//!
//! | Symbol | Role |
//! |--------|------|
//! | `uw_client_init` | One-time init: sets `uw_sqlfmtInt`, `uw_sqlfmtFloat`, `uw_Estrings`, typed SQL suffixes, etc. |
//! | `uw_conn` | Opaque struct holding the vendor connection plus **`p0`…`p{n-1}`** prepared-statement handles (order matches CJR `PreparedStatements` after `cjr_prepare`) on SQL backends; native backends use placeholder fields until the IR is ledger/KV-native. |
//! | `uw_db_validate` | Optional schema existence checks (SQL backends); native backends error if relational tables are declared. |
//! | `uw_db_prepare` | Populates each `p{i}` from the `i`th SQL string on SQL backends; native backends error if any prepared slot is required. |
//! | `uw_db_init` | Open connection from project `database` / CLI `-db`, `uw_set_db`, then validate + prepare. |
//! | `uw_db_close` | Finalize prepared handles and tear down the connection. |
//! | `uw_db_begin` / `uw_db_commit` / `uw_db_rollback` | Serializable transactions (`BEGIN`…`COMMIT` / driver equivalents). |
