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
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Crud1_t1'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Crud1_t1'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Crud1_t1'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Crud1_t1'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Crud1_t1'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_Crud1_t1' does not exist.");
}
sqlite3_finalize(stmt);
}

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/tmp/urweb-mono-name.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

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
uw_Basis_string __uwf_A;
uw_Basis_string __uwf_B;
uw_Basis_string __uwf_C;
uw_Basis_bool __uwf_D;
};

struct __uws_2 {
uw_Basis_string __uwf_A;
uw_Basis_string __uwf_B;
uw_Basis_string __uwf_C;
uw_Basis_string __uwf_D;
};

struct __uws_3 {
uw_Basis_int __uwf_A;
uw_Basis_string __uwf_B;
uw_Basis_float __uwf_C;
uw_Basis_bool __uwf_D;
uw_Basis_int __uwf_Id;
};

struct __uws_4 {
struct __uws_3 __uwf_T;
};

/* Function prototypes */
static uw_unit __uwn_lam_1798_1798(uw_context, uw_Basis_client);
static uw_unit __uwn_expunger_1796(uw_context, uw_Basis_client);
static uw_unit __uwn_initializer_1797(uw_context, uw_unit);
static uw_unit __uwn_lam_1799_1799(uw_context, uw_Basis_int, uw_unit, uw_unit);
static uw_unit __uwn_wrap__delete_1795(uw_context, uw_Basis_int, uw_unit, uw_unit);
static uw_unit __uwn_lam_1800_1800(uw_context, uw_Basis_int, struct __uws_1, uw_unit);
static uw_unit __uwn_wrap__save_1794(uw_context, uw_Basis_int, struct __uws_1, uw_unit);
static uw_Basis_string __uwn_list_1779(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_wrap_main_1790(uw_context, uw_unit, uw_unit);

static char jslib[] = "";

static uw_unit __uwn_lam_1798_1798(uw_context ctx, uw_Basis_client __uwr_cli_0) {
return(0);
}

static uw_unit __uwn_expunger_1796(uw_context ctx, uw_Basis_client __uwr_x_0) {
return(__uwn_lam_1798_1798(ctx, __uwr_x_0));
}

static uw_unit __uwn_initializer_1797(uw_context ctx, uw_unit __uwr___0) {
return(0);
}

#line 1 "/Users/jacksmith/prog/urweb/demo/crud1.ur"
/* SQL table uw_Crud1_t1 uw_Id constraints  */

#line 46 "/Users/jacksmith/prog/urweb/demo/crud.ur"
/* SQL sequence uw_Crud1_seq */

#line 48 "/Users/jacksmith/prog/urweb/demo/crud.ur"
static uw_unit __uwn_lam_1799_1799(uw_context ctx, uw_Basis_int __uwr_x1_0, uw_unit __uwr_x0_1, uw_unit __uwr___2) {
return(({
uw_unit __uwr_r_3 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "DELETE FROM uw_Crud1_t1 WHERE (uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_x1_0), ")", NULL);

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
uw_Basis_string __uwr_r_4 = ({
uw_unit arg0 = 0;
uw_unit arg1 = 0;
__uwn_list_1779(ctx, arg0, arg1);
});
((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<p"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">The deed is done.</p>\n"), 0), ((uw_write(ctx, __uwr_r_4), 0), (uw_write(ctx, "\n</body>"), 0)))))))));
});
}));
}

#line 48 "/Users/jacksmith/prog/urweb/demo/crud.ur"
static uw_unit __uwn_wrap__delete_1795(uw_context ctx, uw_Basis_int __uwr_x_0, uw_unit __uwr_x_1, uw_unit __uwr_x_2) {
return(({
uw_Basis_int arg0 = __uwr_x_0;
uw_unit arg1 = __uwr_x_1;
uw_unit arg2 = __uwr_x_2;
__uwn_lam_1799_1799(ctx, arg0, arg1, arg2);
}));
}

#line 48 "/Users/jacksmith/prog/urweb/demo/crud.ur"
static uw_unit __uwn_lam_1800_1800(uw_context ctx, uw_Basis_int __uwr_x1_0, struct __uws_1 __uwr_x0_1, uw_unit __uwr___2) {
return(({
uw_Basis_string __uwr_arg0_3 = uw_Basis_mstrcat(ctx, "UPDATE ", ({ struct __uws_2 tmp = {uw_Basis_sqlifyInt(ctx, uw_Basis_stringToInt_error(ctx, __uwr_x0_1.__uwf_A)), uw_Basis_sqlifyString(ctx, __uwr_x0_1.__uwf_B), uw_Basis_sqlifyFloat(ctx, uw_Basis_stringToFloat_error(ctx, __uwr_x0_1.__uwf_C)), ({
uw_Basis_bool disc = __uwr_x0_1.__uwf_D;

(disc == uw_Basis_True) ? "TRUE" : (disc == uw_Basis_False) ? "FALSE" : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})}; tmp; }), " SET uw_A = ", uw_Basis_unAs(ctx, 0LL.__uwf_A), ", uw_B = ", uw_Basis_unAs(ctx, 0LL.__uwf_B), ", uw_C = ", uw_Basis_unAs(ctx, 0LL.__uwf_C), ", uw_D = ", uw_Basis_unAs(ctx, 0LL.__uwf_D), " WHERE uw_Crud1_t1", NULL)(ctx, uw_Basis_mstrcat(ctx, "(T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_x1_0), ")", NULL));
({
uw_unit __uwr_r_4 = ({
uw_Basis_string disc = __uwr_arg0_3;

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_4 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_4;
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
uw_Basis_string __uwr_r_5 = ({
uw_unit arg0 = 0;
uw_unit arg1 = 0;
__uwn_list_1779(ctx, arg0, arg1);
});
((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<p"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Saved!</p>\n"), 0), ((uw_write(ctx, __uwr_r_5), 0), (uw_write(ctx, "\n</body>"), 0)))))))));
});
});
}));
}

#line 48 "/Users/jacksmith/prog/urweb/demo/crud.ur"
static uw_unit __uwn_wrap__save_1794(uw_context ctx, uw_Basis_int __uwr_x_0, struct __uws_1 __uwr_x_1, uw_unit __uwr_x_2) {
return(({
uw_Basis_int arg0 = __uwr_x_0;
struct __uws_1 arg1 = __uwr_x_1;
uw_unit arg2 = __uwr_x_2;
__uwn_lam_1800_1800(ctx, arg0, arg1, arg2);
}));
}

#line 48 "/Users/jacksmith/prog/urweb/demo/crud.ur"
static uw_Basis_string __uwn_list_1779(uw_context ctx, uw_unit __uwr__arg_0, uw_unit __uwr___1) {
return(({
uw_Basis_string __uwr_r_2 = (({
uw_Basis_string acc = "";
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_strcat(ctx, "SELECT T_T.uw_a, T_T.uw_b, T_T.uw_c, T_T.uw_d, T_T.uw_id FROM uw_Crud1_t1 AS T_T WHERE TRUE HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_2 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_2);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_4 __uwr_r_2;
uw_Basis_string __uwr_acc_3 = acc;

__uwr_r_2.__uwf_T.__uwf_A = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : sqlite3_column_int64(stmt, 0));
__uwr_r_2.__uwf_T.__uwf_B = (sqlite3_column_type(stmt, 1) == SQLITE_NULL ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #1"); tmp; }) : uw_strdup(ctx, (uw_Basis_string)sqlite3_column_text(stmt, 1)));
__uwr_r_2.__uwf_T.__uwf_C = (sqlite3_column_type(stmt, 2) == SQLITE_NULL ? ({ uw_Basis_float tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #2"); tmp; }) : sqlite3_column_double(stmt, 2));
__uwr_r_2.__uwf_T.__uwf_D = (sqlite3_column_type(stmt, 3) == SQLITE_NULL ? ({ uw_Basis_bool tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #3"); tmp; }) : (uw_Basis_bool)sqlite3_column_int(stmt, 3));
__uwr_r_2.__uwf_T.__uwf_Id = (sqlite3_column_type(stmt, 4) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #4"); tmp; }) : sqlite3_column_int64(stmt, 4));

acc = uw_Basis_mstrcat(ctx, __uwr_acc_3, "\n<tr", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_Id), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_A), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_A), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_A), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_A), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n<a", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">[Update]</a>\n<a", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">[Delete]</a>\n</td>\n</tr>\n", NULL);
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
}));
uw_Basis_mstrcat(ctx, "\n<table", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " border=\"1\">\n<tr", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n<th", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">ID</th>\n<th", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">A</th>\n<th", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">A</th>\n<th", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">A</th>\n<th", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">A</th>\n</tr>\n", __uwr_r_2, "\n</table>\n<br", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></br><hr", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></hr><br", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></br>\n<form method=\"post\">\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "> A: <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div></li>\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "> A: <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div></li>\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "> A: <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div></li>\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "> A: <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div></li>\n<input type=\"submit\"", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " />\n</form>\n", NULL);
}));
}

static uw_unit __uwn_wrap_main_1790(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(({
uw_Basis_string __uwr_r_2 = (({
uw_Basis_string acc = "";
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_strcat(ctx, "SELECT T_T.uw_a, T_T.uw_b, T_T.uw_c, T_T.uw_d, T_T.uw_id FROM uw_Crud1_t1 AS T_T WHERE TRUE HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_2 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_2);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_4 __uwr_r_2;
uw_Basis_string __uwr_acc_3 = acc;

__uwr_r_2.__uwf_T.__uwf_A = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : sqlite3_column_int64(stmt, 0));
__uwr_r_2.__uwf_T.__uwf_B = (sqlite3_column_type(stmt, 1) == SQLITE_NULL ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #1"); tmp; }) : uw_strdup(ctx, (uw_Basis_string)sqlite3_column_text(stmt, 1)));
__uwr_r_2.__uwf_T.__uwf_C = (sqlite3_column_type(stmt, 2) == SQLITE_NULL ? ({ uw_Basis_float tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #2"); tmp; }) : sqlite3_column_double(stmt, 2));
__uwr_r_2.__uwf_T.__uwf_D = (sqlite3_column_type(stmt, 3) == SQLITE_NULL ? ({ uw_Basis_bool tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #3"); tmp; }) : (uw_Basis_bool)sqlite3_column_int(stmt, 3));
__uwr_r_2.__uwf_T.__uwf_Id = (sqlite3_column_type(stmt, 4) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #4"); tmp; }) : sqlite3_column_int64(stmt, 4));

acc = uw_Basis_mstrcat(ctx, __uwr_acc_3, "\n<tr", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_Id), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_A), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_A), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_A), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_T.__uwf_A), "</td>\n<td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n<a", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">[Update]</a>\n<a", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">[Delete]</a>\n</td>\n</tr>\n", NULL);
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
}));
((uw_write(ctx, "<head"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<title"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Crud1</title>\n</head><body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<h1"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Crud1</h1>\n"), 0), (((uw_write(ctx, "\n<table"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, " border=\"1\">\n<tr"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">ID</th>\n<th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">A</th>\n<th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">A</th>\n<th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">A</th>\n<th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">A</th>\n</tr>\n"), 0), ((uw_write(ctx, __uwr_r_2), 0), ((uw_write(ctx, "\n</table>\n<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br><hr"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></hr><br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<form method=\"post\">\n<li"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> A: <div"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></div></li>\n<li"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> A: <div"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></div></li>\n<li"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> A: <div"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></div></li>\n<li"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> A: <div"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></div></li>\n<input type=\"submit\""), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, " />\n</form>\n"), 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (uw_write(ctx, "\n</body>"), 0)))))))))))))));
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
__uwn_initializer_1797(ctx, 0);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
__uwn_expunger_1796(ctx, cli);
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
if (!strncmp(request, "/Crud1/save", 11) && (request[11] == 0 || request[11] == '/')) {
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
uw_Basis_int arg0 = uw_Basis_unurlifyInt(ctx, &request);
struct __uws_1 arg1 = ({
uw_Basis_string uwr_A = uw_Basis_unurlifyString(ctx, &request);
uw_Basis_string uwr_B = uw_Basis_unurlifyString(ctx, &request);
uw_Basis_string uwr_C = uw_Basis_unurlifyString(ctx, &request);
uw_Basis_bool uwr_D = uw_Basis_unurlifyBool(ctx, &request);
struct __uws_1 tmp = { uwr_A, uwr_B, uwr_C, uwr_D };
tmp;
});
__uwn_wrap__save_1794(ctx, arg0, arg1, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/Crud1/delete", 13) && (request[13] == 0 || request[13] == '/')) {
request += 13;
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
uw_Basis_int arg0 = uw_Basis_unurlifyInt(ctx, &request);
uw_unit arg1 = uw_Basis_unurlifyUnit(ctx, &request);
__uwn_wrap__delete_1795(ctx, arg0, arg1, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/Crud1/main", 11) && (request[11] == 0 || request[11] == '/')) {
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
__uwn_wrap_main_1790(ctx, arg0, 0);
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
