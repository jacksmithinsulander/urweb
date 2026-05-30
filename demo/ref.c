#include "urweb.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#include <sqlite3.h>

static void uw_client_init(void) {
uw_sqlfmtInt = "%lld%n";
uw_sqlfmtFloat = "%.16g%n";
uw_Estrings = 0;
uw_sql_type_annotations = 0;
uw_sqlsuffixString = "";
uw_sqlsuffixChar = "";
uw_sqlsuffixBlob = "";
uw_sqlfmtUint4 = "%u%n";
}

typedef struct {
sqlite3 *conn;
} uw_conn;

static void uw_db_validate(uw_context ctx) {
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
int res;
{ int _prepare_rc;
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_IR_t'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_IR_t'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_IR_t'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_IR_t'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_IR_t'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_Ref_IR_t' does not exist.");
}
sqlite3_finalize(stmt);
{ int _prepare_rc;
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_SR_t'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_SR_t'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_SR_t'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_SR_t'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Ref_SR_t'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_Ref_SR_t' does not exist.");
}
sqlite3_finalize(stmt);
}

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/tmp/urweb-ref.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

if (sqlite3_exec(sqlite, "PRAGMA foreign_keys = ON", NULL, NULL, NULL) != SQLITE_OK)
uw_error(ctx, FATAL, "Can't enable foreign_keys for SQLite database");

if (uw_database_max < SIZE_MAX) {
char buf[100];

sprintf(buf, "PRAGMA max_page_count = %llu", (unsigned long long)(uw_database_max / 1024));

if (sqlite3_prepare_v2(sqlite, buf, -1, &stmt, NULL) != SQLITE_OK) {
sqlite3_close(sqlite);
uw_error(ctx, FATAL, "Can't prepare max_page_count query for SQLite database");
}

if (sqlite3_step(stmt) != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(sqlite);
uw_error(ctx, FATAL, "Can't set max_page_count parameter for SQLite database");
}

sqlite3_finalize(stmt);
}

conn = calloc(1, sizeof(uw_conn));
conn->conn = sqlite;
uw_set_db(ctx, conn);
uw_db_validate(ctx);
uw_db_prepare(ctx);
}

static void uw_db_close(uw_context ctx) {
uw_conn *conn = uw_get_db(ctx);
sqlite3_close(conn->conn);
}

static int uw_db_begin(uw_context ctx, int could_write) {
uw_conn *conn = uw_get_db(ctx);

if (sqlite3_exec(conn->conn, "BEGIN", NULL, NULL, NULL) == SQLITE_OK)
return 0;
else {
fprintf(stderr, "Begin error: %s<br />", sqlite3_errmsg(conn->conn));
return 1;
}
}
static int uw_db_commit(uw_context ctx) {
uw_conn *conn = uw_get_db(ctx);
if (sqlite3_exec(conn->conn, "COMMIT", NULL, NULL, NULL) == SQLITE_OK)
return 0;
else {
fprintf(stderr, "Commit error: %s<br />", sqlite3_errmsg(conn->conn));
return 1;
}
}

static int uw_db_rollback(uw_context ctx) {
uw_conn *conn = uw_get_db(ctx);
if (sqlite3_exec(conn->conn, "ROLLBACK", NULL, NULL, NULL) == SQLITE_OK)
return 0;
else {
fprintf(stderr, "Rollback error: %s<br />", sqlite3_errmsg(conn->conn));
return 1;
}
}

static int uw_input_num(const char *name) { return -1; }

extern void uw_sign(const char *in, char *out);
extern int uw_hash_blocksize;
static uw_Basis_string uw_cookie_sig(uw_context ctx) {
    uw_Basis_string r = uw_malloc(ctx, uw_hash_blocksize);
    uw_sign("", r);
    return uw_Basis_makeSigString(ctx, r);
}

static inline uw_Basis_string uw_Basis_attrOptional(
    struct uw_context *ctx, uw_Basis_string name, uw_Basis_string val) {
    if (val == NULL || val[0] == '\0') return "";
    return uw_Basis_mstrcat(ctx, " ", name, "=\"", val, "\"", NULL);
}

struct __uws_1 {
uw_Basis_string __uwf_Data;
};

struct __uws_2 {
uw_Basis_int __uwf_Data;
};

struct __uws_3 {
struct __uws_2 __uwf_T;
};

struct __uws_4 {
struct __uws_1 __uwf_T;
};

/* Function prototypes */
static uw_unit __uwn_lam_1783_1783(uw_context, uw_Basis_client);
static uw_unit __uwn_expunger_1781(uw_context, uw_Basis_client);
static uw_unit __uwn_initializer_1782(uw_context, uw_unit);
static uw_unit __uwn_lam_1784_1784(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_wrap_mutate_1780(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_wrap_main_1779(uw_context, uw_unit, uw_unit);

static char jslib[] = "";

static uw_unit __uwn_lam_1783_1783(uw_context ctx, uw_Basis_client __uwr_cli_0) {
return(0);
}

static uw_unit __uwn_expunger_1781(uw_context ctx, uw_Basis_client __uwr_x_0) {
return(__uwn_lam_1783_1783(ctx, __uwr_x_0));
}

static uw_unit __uwn_initializer_1782(uw_context ctx, uw_unit __uwr___0) {
return(0);
}

#line 8 "/Users/jacksmith/prog/urweb/demo/refFun.ur"
/* SQL sequence uw_Ref_IR_s */

#line 9 "/Users/jacksmith/prog/urweb/demo/refFun.ur"
/* SQL table uw_Ref_IR_t uw_Id constraints  */

#line 8 "/Users/jacksmith/prog/urweb/demo/refFun.ur"
/* SQL sequence uw_Ref_SR_s */

#line 9 "/Users/jacksmith/prog/urweb/demo/refFun.ur"
/* SQL table uw_Ref_SR_t uw_Id constraints  */

#line 28 "/Users/jacksmith/prog/urweb/demo/ref.ur"
static uw_unit __uwn_lam_1784_1784(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(({
uw_Basis_int __uwr_r_2 = ({
uw_Basis_int n;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
char *insert = uw_Basis_strcat(ctx, "INSERT INTO ", uw_Basis_strcat(ctx, "uw_Ref_IR_s", " VALUES (NULL)"));
char *delete = uw_Basis_strcat(ctx, "DELETE FROM ", "uw_Ref_IR_s");
if (sqlite3_exec(conn->conn, insert, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' INSERT failed: %s", sqlite3_errmsg(conn->conn));
n = sqlite3_last_insert_rowid(conn->conn);
if (sqlite3_exec(conn->conn, delete, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' DELETE failed: %s", sqlite3_errmsg(conn->conn));
n;
});
({
uw_unit __uwr_r_3 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "INSERT INTO uw_Ref_IR_t (uw_Data, uw_Id) VALUES (3::int8, ", uw_Basis_sqlifyInt(ctx, __uwr_r_2), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_3 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_3;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, dml, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
if ((r = sqlite3_step(stmt)) == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "dml: DML step failed: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
uw_end_region(ctx);
0;
}));
}) : ({
uw_unit tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
uw_Basis_int __uwr_r_4 = ({
uw_Basis_int n;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
char *insert = uw_Basis_strcat(ctx, "INSERT INTO ", uw_Basis_strcat(ctx, "uw_Ref_IR_s", " VALUES (NULL)"));
char *delete = uw_Basis_strcat(ctx, "DELETE FROM ", "uw_Ref_IR_s");
if (sqlite3_exec(conn->conn, insert, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' INSERT failed: %s", sqlite3_errmsg(conn->conn));
n = sqlite3_last_insert_rowid(conn->conn);
if (sqlite3_exec(conn->conn, delete, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' DELETE failed: %s", sqlite3_errmsg(conn->conn));
n;
});
({
uw_unit __uwr_r_5 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "INSERT INTO uw_Ref_IR_t (uw_Data, uw_Id) VALUES (7::int8, ", uw_Basis_sqlifyInt(ctx, __uwr_r_4), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_5 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_5;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, dml, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
if ((r = sqlite3_step(stmt)) == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "dml: DML step failed: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
uw_end_region(ctx);
0;
}));
}) : ({
uw_unit tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
uw_Basis_int __uwr_r_6 = ({
uw_Basis_int n;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
char *insert = uw_Basis_strcat(ctx, "INSERT INTO ", uw_Basis_strcat(ctx, "uw_Ref_SR_s", " VALUES (NULL)"));
char *delete = uw_Basis_strcat(ctx, "DELETE FROM ", "uw_Ref_SR_s");
if (sqlite3_exec(conn->conn, insert, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' INSERT failed: %s", sqlite3_errmsg(conn->conn));
n = sqlite3_last_insert_rowid(conn->conn);
if (sqlite3_exec(conn->conn, delete, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' DELETE failed: %s", sqlite3_errmsg(conn->conn));
n;
});
({
uw_unit __uwr_r_7 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "INSERT INTO uw_Ref_SR_t (uw_Data, uw_Id) VALUES (\'hi\', ", uw_Basis_sqlifyInt(ctx, __uwr_r_6), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_7 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_7;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, dml, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
if ((r = sqlite3_step(stmt)) == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "dml: DML step failed: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
uw_end_region(ctx);
0;
}));
}) : ({
uw_unit tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
uw_Basis_string __uwr_arg0_8 = uw_Basis_mstrcat(ctx, "UPDATE ", ({ struct __uws_1 tmp = {"10::int8"}; tmp; }), " SET uw_Data = ", uw_Basis_unAs(ctx, 0.__uwf_Data), " WHERE uw_Ref_IR_t", NULL)(ctx, uw_Basis_mstrcat(ctx, "(T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_4), ")", NULL));
({
uw_unit __uwr_r_9 = ({
uw_Basis_string disc = __uwr_arg0_8;

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_9 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_9;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, dml, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
if ((r = sqlite3_step(stmt)) == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "dml: DML step failed: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
uw_end_region(ctx);
0;
}));
}) : ({
uw_unit tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
struct __uws_3* __uwr_r_10 = (({
struct __uws_3* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_data FROM uw_Ref_IR_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_2), ") HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_10 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_10);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), NULL);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_3 __uwr_r_10;
struct __uws_3* __uwr_acc_11 = acc;

__uwr_r_10.__uwf_T.__uwf_Data = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : sqlite3_column_int64(stmt, 0));

acc = ({
struct __uws_3 *tmp = uw_malloc(ctx, sizeof(struct __uws_3));
*tmp = __uwr_r_10;
tmp;
});
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
}));
({
uw_Basis_int __uwr_r_11 = ({
struct __uws_3* disc = __uwr_r_10;

(disc == NULL) ? ({
uw_Basis_int (*tmp)(uw_context, uw_unit);
uw_error(ctx, FATAL, "%s", "You already deleted that ref!");
tmp;
})(ctx, 0) : (disc != NULL) && 1 ? ({
struct __uws_3 __uwr_r_11 = (*disc);
__uwr_r_11.__uwf_T.__uwf_Data;
}) : ({
uw_Basis_int tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
struct __uws_3* __uwr_r_12 = (({
struct __uws_3* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_data FROM uw_Ref_IR_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_4), ") HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_12 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_12);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), NULL);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_3 __uwr_r_12;
struct __uws_3* __uwr_acc_13 = acc;

__uwr_r_12.__uwf_T.__uwf_Data = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : sqlite3_column_int64(stmt, 0));

acc = ({
struct __uws_3 *tmp = uw_malloc(ctx, sizeof(struct __uws_3));
*tmp = __uwr_r_12;
tmp;
});
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
}));
({
uw_Basis_int __uwr_r_13 = ({
struct __uws_3* disc = __uwr_r_12;

(disc == NULL) ? ({
uw_Basis_int (*tmp)(uw_context, uw_unit);
uw_error(ctx, FATAL, "%s", "You already deleted that ref!");
tmp;
})(ctx, 0) : (disc != NULL) && 1 ? ({
struct __uws_3 __uwr_r_13 = (*disc);
__uwr_r_13.__uwf_T.__uwf_Data;
}) : ({
uw_Basis_int tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
struct __uws_4* __uwr_r_14 = (({
struct __uws_4* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_data FROM uw_Ref_SR_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_6), ") HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_14 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_14);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), NULL);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_4 __uwr_r_14;
struct __uws_4* __uwr_acc_15 = acc;

__uwr_r_14.__uwf_T.__uwf_Data = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : uw_strdup(ctx, (uw_Basis_string)sqlite3_column_text(stmt, 0)));

acc = ({
struct __uws_4 *tmp = uw_malloc(ctx, sizeof(struct __uws_4));
*tmp = __uwr_r_14;
tmp;
});
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
}));
({
uw_Basis_string __uwr_r_15 = ({
struct __uws_4* disc = __uwr_r_14;

(disc == NULL) ? ({
uw_Basis_string (*tmp)(uw_context, uw_unit);
uw_error(ctx, FATAL, "%s", "You already deleted that ref!");
tmp;
})(ctx, 0) : (disc != NULL) && 1 ? ({
struct __uws_4 __uwr_r_15 = (*disc);
__uwr_r_15.__uwf_T.__uwf_Data;
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
uw_unit __uwr_r_16 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "DELETE FROM uw_Ref_IR_t WHERE (uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_2), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_16 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_16;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, dml, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
if ((r = sqlite3_step(stmt)) == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "dml: DML step failed: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
uw_end_region(ctx);
0;
}));
}) : ({
uw_unit tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
uw_unit __uwr_r_17 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "DELETE FROM uw_Ref_IR_t WHERE (uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_4), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_17 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_17;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, dml, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
if ((r = sqlite3_step(stmt)) == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "dml: DML step failed: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
uw_end_region(ctx);
0;
}));
}) : ({
uw_unit tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
uw_unit __uwr_r_18 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "DELETE FROM uw_Ref_SR_t WHERE (uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_6), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_18 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_18;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, dml, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
if ((r = sqlite3_step(stmt)) == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "dml: DML step failed: %s<br />%s", dml, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
uw_end_region(ctx);
0;
}));
}) : ({
uw_unit tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n"), 0), (uw_Basis_htmlifyInt_w(ctx, __uwr_r_11), ((uw_write(ctx, ", "), 0), (uw_Basis_htmlifyInt_w(ctx, __uwr_r_13), ((uw_write(ctx, ", "), 0), (uw_Basis_htmlifyString_w(ctx, __uwr_r_15), (uw_write(ctx, "\n</body>"), 0))))))))));
});
});
});
});
});
});
});
});
});
});
});
});
});
});
});
});
}));
}

#line 28 "/Users/jacksmith/prog/urweb/demo/ref.ur"
static uw_unit __uwn_wrap_mutate_1780(uw_context ctx, uw_unit __uwr_x_0, uw_unit __uwr_x_1) {
return(({
uw_unit arg0 = __uwr_x_0;
uw_unit arg1 = __uwr_x_1;
__uwn_lam_1784_1784(ctx, arg0, arg1);
}));
}

static uw_unit __uwn_wrap_main_1779(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<form method=\"post\" action=\"/Ref/mutate\"><input type=\"submit\""), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, " action=\"/Ref/mutate\" value=\"Do some pointless stuff\" /></form>\n</body>"), 0))))))));
}

static void uw_setup_limits(void) {
}

void uw_global_custom(void) {
uw_setup_limits();
}

static void uw_initializer(uw_context ctx) {
uw_begin_initializing(ctx);
uw_end_initializing(ctx);
__uwn_initializer_1782(ctx, 0);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
__uwn_expunger_1781(ctx, cli);
}

static uw_periodic my_periodics[] = {
  { NULL, 0 }
};

static int uw_check_url(const char *url) {
  return 1;
}

static int uw_check_mime(const char *mime) {
  return 1;
}

static int uw_check_requestHeader(const char *h) {
  return 1;
}

static int uw_check_responseHeader(const char *h) {
  return 1;
}

static int uw_check_envVar(const char *v) {
  return 1;
}

static int uw_check_meta(const char *m) {
  return 1;
}

static void uw_handle(uw_context ctx, char *request) {
if (!strncmp(request, "/Ref/mutate", 11) && (request[11] == 0 || request[11] == '/')) {
request += 11;
if (*request == '/') ++request;
uw_write_header(ctx, "Content-type: text/html; charset=utf-8\r\n");
uw_write(ctx, uw_begin_html5);
uw_mayReturnIndirectly(ctx);
uw_set_could_write_db(ctx, 1);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
__uwn_wrap_mutate_1780(ctx, arg0, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/Ref/main", 9) && (request[9] == 0 || request[9] == '/')) {
request += 9;
if (*request == '/') ++request;
uw_write_header(ctx, "Content-type: text/html; charset=utf-8\r\n");
uw_write(ctx, uw_begin_html5);
uw_mayReturnIndirectly(ctx);
uw_set_could_write_db(ctx, 0);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
__uwn_wrap_main_1779(ctx, arg0, 0);
uw_write(ctx, "</html>");
return;
}
}
uw_clear_headers(ctx);
uw_write_header(ctx, uw_supports_direct_status ? "HTTP/1.1 404 Not Found\r\n" : "Status: 404 Not Found\r\n");
uw_write_header(ctx, "Content-type: text/plain\r\n");
uw_write(ctx, "Not Found");
}

uw_app uw_application = {
1,
120,
"/",
uw_client_init,
uw_initializer,
uw_expunger,
uw_db_init, uw_db_begin, uw_db_commit, uw_db_rollback, uw_db_close,
uw_handle,
uw_input_num,
uw_cookie_sig,
uw_check_url, uw_check_mime, uw_check_requestHeader, uw_check_responseHeader,
uw_check_envVar, uw_check_meta,
NULL,
my_periodics,
"%c",
1,
NULL
};
