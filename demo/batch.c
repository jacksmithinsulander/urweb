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
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Batch_t'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Batch_t'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Batch_t'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Batch_t'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Batch_t'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_Batch_t' does not exist.");
}
sqlite3_finalize(stmt);
}

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/tmp/urweb-batch.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

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

struct __uws_2 {
struct __uws_1 __uwf_T;
};

struct __uws_3 {
uw_Basis_int __uwf_1;
uw_Basis_string __uwf_2;
};

struct __uws_4 {
uw_Basis_string __uwf_A;
uw_Basis_string __uwf_Id;
};

static uw_unit __uwn_expunger_1779(uw_context ctx, uw_Basis_client __uwr_cli_0) {
return(0);
}

/* Function prototypes */
static uw_unit __uwn_expunger_1779(uw_context, uw_Basis_client);
static uw_unit __uwn_initializer_1780(uw_context, uw_unit);
static uw_unit __uwn_allRows_1770(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_doBatch_1771(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_del_1772(uw_context, uw_Basis_int, uw_unit);
static uw_unit __uwn_show_1783(uw_context, uw_Basis_bool, uw_Basis_source);
static uw_unit __uwn_wrap_main_1778(uw_context, uw_unit, uw_unit);

struct __uws_1 {
uw_Basis_int __uwf_Id;
uw_Basis_string __uwf_A;
};

static uw_unit __uwn_initializer_1780(uw_context ctx, uw_unit __uwr___0) {
return(0);
}

#line 3 "/Users/jacksmith/prog/urweb/demo/batch.ur"
/* SQL table uw_Batch_t uw_Id constraints  */

#line 6 "/Users/jacksmith/prog/urweb/demo/batch.ur"
static uw_unit __uwn_allRows_1770(uw_context ctx, uw_unit __uwr__arg_0, uw_unit __uwr___1) {
return((({
uw_unit acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT * FROM ", __uwr___1, ({
uw_Basis_string disc = __uwr___1;
uw_Basis_string
(!strcmp(disc, "1")) ? "" : 1 ? ({
uw_Basis_string __uwr_w_2 = disc;
uw_Basis_strcat(ctx, " WHERE ", __uwr___1);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
uw_Basis_string disc = __uwr___1;
uw_Basis_string
(!strcmp(disc, "1")) ? "" : 1 ? ({
uw_Basis_string __uwr_h_2 = disc;
uw_Basis_strcat(ctx, " HAVING ", __uwr___1);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
uw_Basis_string disc = "";
uw_Basis_string
(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_2 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr___1);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), NULL);

PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexecParams(conn, query, 0, NULL, NULL, NULL, NULL, 0);

int n, i;
if (res == NULL) {
uw_try_reconnecting_and_restarting(ctx);
uw_error(ctx, FATAL, "Ur/Web / SQL: could not allocate memory for query result (database may be unreachable).");
}
if (PQresultStatus(res) != PGRES_TUPLES_OK) {
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40001")) {
PQclear(res);
uw_error(ctx, UNLIMITED_RETRY, "Ur/Web / SQL: serialization conflict — retrying this transaction.");
}
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40P01")) {
PQclear(res);
uw_error(ctx, UNLIMITED_RETRY, "Ur/Web / SQL: deadlock detected — retrying this transaction.");
}
PQclear(res);
uw_error(ctx, FATAL, "query: Ur/Web / SQL: query failed.\nSQL: %s\nServer: %s", query, PQerrorMessage(conn));
}
if (PQnfields(res) != 2) {
int nf = PQnfields(res);
PQclear(res);
uw_error(ctx, FATAL, "query: Ur/Web / SQL: each result row should have 2 column(s), but the database returned %d.\nSQL: %s\nServer: %s", nf, query, PQerrorMessage(conn));
}
uw_end_region(ctx);
uw_push_cleanup(ctx, (void (*)(void *))PQclear, res);
n = PQntuples(res);
for (i = 0; i < n; ++i) {
struct __uws_2 __uwr_r_2;
/* state */ __uwr_acc_3 = acc;

__uwr_r_2.__uwf_T.__uwf_A = (PQgetisnull(res, i, 0) ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Ur/Web / SQL: the database returned NULL for column 0, but this type does not allow missing values."); tmp; }) : uw_strdup(ctx, PQgetvalue(res, i, 0)));
__uwr_r_2.__uwf_T.__uwf_Id = (PQgetisnull(res, i, 1) ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Ur/Web / SQL: the database returned NULL for column 1, but this type does not allow missing values."); tmp; }) : uw_Basis_stringToInt_error(ctx, PQgetvalue(res, i, 1)));

acc = __uwr_acc_3;
}
uw_pop_cleanup(ctx);
acc;
})));
}

#line 11 "/Users/jacksmith/prog/urweb/demo/batch.ur"
static uw_unit __uwn_doBatch_1771(uw_context, uw_unit, uw_unit);

static uw_unit __uwn_doBatch_1771(uw_context ctx, uw_unit __uwr_ls_0, uw_unit __uwr_y_1) {
restart:
return(({
uw_unit disc = __uwr_ls_0;
uw_unit
(disc == NULL) ? 0 : (disc != NULL) && 1 && 1 && 1 ? ({
uw_Basis_int __uwr_id_2 = (*disc).__uwf_1.__uwf_1;
uw_Basis_string __uwr_a_3 = (*disc).__uwf_1.__uwf_2;
uw_unit __uwr_lsPRIME_4 = (*disc).__uwf_2;
({
uw_Basis_string __uwr_arg0_5 = uw_Basis_insert(ctx, "uw_Batch_t", ({ struct __uws_4 tmp = {__uwr_a_3, __uwr_id_2}; tmp; }));
({
uw_unit __uwr_r_6 = ({
uw_Basis_string disc = __uwr_arg0_5;
uw_unit
(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_6 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_6;
PGconn *conn = uw_get_db(ctx);
PGresult *res;
res = PQexecParams(conn, dml, 0, NULL, NULL, NULL, NULL, 0);

uw_ensure_transaction(ctx);

if (res == NULL) {
uw_try_reconnecting_and_restarting(ctx);
uw_error(ctx, FATAL, "Ur/Web / SQL: could not allocate memory for DML result (database may be unreachable).");
}
if (PQresultStatus(res) != PGRES_COMMAND_OK) {
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40001")) { PQclear(res); uw_error(ctx, UNLIMITED_RETRY, "Ur/Web / SQL: serialization conflict — retrying this transaction."); }
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40P01")) { PQclear(res); uw_error(ctx, UNLIMITED_RETRY, "Ur/Web / SQL: deadlock detected — retrying this transaction."); }
PQclear(res);
uw_error(ctx, FATAL, "dml: Ur/Web / SQL: insert/update/delete failed.\nSQL: %s\nServer: %s", dml, PQerrorMessage(conn));
}PQclear(res);

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
uw_unit arg0 = __uwr_lsPRIME_4;
uw_unit arg1 = 0;
__uwn_doBatch_1771(ctx, arg0, arg1);
});
});
});
}) : ({
uw_unit tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}


#line 18 "/Users/jacksmith/prog/urweb/demo/batch.ur"
static uw_unit __uwn_del_1772(uw_context ctx, uw_Basis_int __uwr_id_0, uw_unit __uwr_x_1) {
return(({
uw_Basis_string __uwr_arg0_2 = uw_Basis_delete(ctx, "uw_Batch_t", uw_Basis_mstrcat(ctx, "(T_T.uw_id = ", __uwr_id_0, ")", NULL));
({
uw_Basis_string disc = __uwr_x_1;
uw_unit
(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_3 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_x_1;
PGconn *conn = uw_get_db(ctx);
PGresult *res;
res = PQexecParams(conn, dml, 0, NULL, NULL, NULL, NULL, 0);

uw_ensure_transaction(ctx);

if (res == NULL) {
uw_try_reconnecting_and_restarting(ctx);
uw_error(ctx, FATAL, "Ur/Web / SQL: could not allocate memory for DML result (database may be unreachable).");
}
if (PQresultStatus(res) != PGRES_COMMAND_OK) {
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40001")) { PQclear(res); uw_error(ctx, UNLIMITED_RETRY, "Ur/Web / SQL: serialization conflict — retrying this transaction."); }
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40P01")) { PQclear(res); uw_error(ctx, UNLIMITED_RETRY, "Ur/Web / SQL: deadlock detected — retrying this transaction."); }
PQclear(res);
uw_error(ctx, FATAL, "dml: Ur/Web / SQL: insert/update/delete failed.\nSQL: %s\nServer: %s", dml, PQerrorMessage(conn));
}PQclear(res);

uw_end_region(ctx);
0;
}));
}) : ({
uw_unit tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
}));
}

#line 21 "/Users/jacksmith/prog/urweb/demo/batch.ur"
static uw_unit __uwn_show_1783(uw_context ctx, uw_Basis_bool __uwr_withDel_0, uw_Basis_source __uwr_lss_1) {
return(((uw_write(ctx, "<dyn"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, "></dyn>"), 0)))));
}

static uw_unit __uwn_wrap_main_1778(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(({
uw_Basis_source __uwr_r_2 = uw_Basis_source(ctx, NULL, 0);
({
uw_Basis_source __uwr_r_3 = uw_Basis_source(ctx, NULL, 0);
({
uw_Basis_source __uwr_r_4 = uw_Basis_source(ctx, "", 0);
({
uw_Basis_source __uwr_r_5 = uw_Basis_source(ctx, "", 0);
((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<h2"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Rows</h2>\n"), 0), (({
uw_Basis_bool arg0 = uw_Basis_bool_True;
uw_Basis_source arg1 = __uwr_r_2;
__uwn_show_1783(ctx, arg0, arg1);
}), ((uw_write(ctx, "\n<button"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></button><br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<h2"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Batch new rows to add</h2>\n<tabl"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<tr"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> <th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Id:</th> <td"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "><ctextbox"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></ctextbox></td> </tr>\n<tr"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> <th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">A:</th> <td"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "><ctextbox"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></ctextbox></td> </tr>\n<tr"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> <th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></th> <td"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "><button"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></button></td> </tr>\n</tabl>\n<h2"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Already batched:</h2>\n"), 0), (({
uw_Basis_bool arg0 = uw_Basis_bool_False;
uw_Basis_source arg1 = __uwr_r_3;
__uwn_show_1783(ctx, arg0, arg1);
}), ((uw_write(ctx, "\n<button"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, "></button>\n</body>"), 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
});
});
});
}));
}

static void uw_setup_limits(void) {
}

void uw_global_custom(void) {
uw_setup_limits();
}

static void uw_initializer(uw_context ctx) {
uw_begin_initializing(ctx);
uw_end_initializing(ctx);
__uwn_initializer_1780(ctx, 0);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
__uwn_expunger_1779(ctx, cli);
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
if (!strncmp(request, "/Batch/del", 10) && (request[10] == 0 || request[10] == '/')) {
request += 10;
if (*request == '/') ++request;
if (uw_hasPostBody(ctx)) {
uw_Basis_postBody pb = uw_getPostBody(ctx);
if (pb.data[0])
request = uw_Basis_strcat(ctx, request, pb.data);
}
{
uw_Basis_string sig = uw_Basis_requestHeader(ctx, "UrWeb-Sig");
if (sig == NULL) uw_error(ctx, FATAL, "Ur/Web security: missing UrWeb-Sig header (CSRF token). Resubmit the form from this app, or open a fresh page.");
if (!uw_streq(sig, uw_cookie_sig(ctx)))
uw_error(ctx, FATAL, "Ur/Web security: UrWeb-Sig does not match this session (possible CSRF, stale tab, or outdated form).");
}
uw_write_header(ctx, "Content-type: text/plain\r\n");
uw_set_could_write_db(ctx, 1);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_Basis_int arg0 = uw_Basis_unurlifyInt(ctx, &request);
uw_unit it0 = __uwn_del_1772(ctx, arg0, 0);
uw_write(ctx, uw_get_real_script(ctx));
uw_write(ctx, "\n");
uw_Basis_urlifyString_w(ctx, "");
return;
}
}
if (!strncmp(request, "/Batch/doBatch", 14) && (request[14] == 0 || request[14] == '/')) {
request += 14;
if (*request == '/') ++request;
if (uw_hasPostBody(ctx)) {
uw_Basis_postBody pb = uw_getPostBody(ctx);
if (pb.data[0])
request = uw_Basis_strcat(ctx, request, pb.data);
}
{
uw_Basis_string sig = uw_Basis_requestHeader(ctx, "UrWeb-Sig");
if (sig == NULL) uw_error(ctx, FATAL, "Ur/Web security: missing UrWeb-Sig header (CSRF token). Resubmit the form from this app, or open a fresh page.");
if (!uw_streq(sig, uw_cookie_sig(ctx)))
uw_error(ctx, FATAL, "Ur/Web security: UrWeb-Sig does not match this session (possible CSRF, stale tab, or outdated form).");
}
uw_write_header(ctx, "Content-type: text/plain\r\n");
uw_set_could_write_db(ctx, 1);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
uw_unit it0 = __uwn_doBatch_1771(ctx, arg0, 0);
uw_write(ctx, uw_get_real_script(ctx));
uw_write(ctx, "\n");
uw_Basis_urlifyString_w(ctx, "");
return;
}
}
if (!strncmp(request, "/Batch/allRows", 14) && (request[14] == 0 || request[14] == '/')) {
request += 14;
if (*request == '/') ++request;
if (uw_hasPostBody(ctx)) {
uw_Basis_postBody pb = uw_getPostBody(ctx);
if (pb.data[0])
request = uw_Basis_strcat(ctx, request, pb.data);
}
{
uw_Basis_string sig = uw_Basis_requestHeader(ctx, "UrWeb-Sig");
if (sig == NULL) uw_error(ctx, FATAL, "Ur/Web security: missing UrWeb-Sig header (CSRF token). Resubmit the form from this app, or open a fresh page.");
if (!uw_streq(sig, uw_cookie_sig(ctx)))
uw_error(ctx, FATAL, "Ur/Web security: UrWeb-Sig does not match this session (possible CSRF, stale tab, or outdated form).");
}
uw_write_header(ctx, "Content-type: text/plain\r\n");
uw_set_could_write_db(ctx, 1);
uw_set_at_most_one_query(ctx, 1);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
uw_unit it0 = __uwn_allRows_1770(ctx, arg0, 0);
uw_write(ctx, uw_get_real_script(ctx));
uw_write(ctx, "\n");
uw_Basis_urlifyString_w(ctx, "");
return;
}
}
if (!strncmp(request, "/Batch/main", 11) && (request[11] == 0 || request[11] == '/')) {
request += 11;
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
__uwn_wrap_main_1778(ctx, arg0, 0);
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
