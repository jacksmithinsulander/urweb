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
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_BatchG_t'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_BatchG_t'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_BatchG_t'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_BatchG_t'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_BatchG_t'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_BatchG_t' does not exist.");
}
sqlite3_finalize(stmt);
}

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/tmp/urweb-batchg.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

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
uw_Basis_float __uwf_B;
uw_Basis_int __uwf_Id;
};

struct __uws_2 {
struct __uws_1 __uwf_1;
struct __uws_2* __uwf_2;
};

struct __uws_3 {
struct __uws_1 __uwf_T;
};

struct __uws_4 {
uw_Basis_source __uwf_A;
uw_Basis_source __uwf_B;
};

/* Function prototypes */
static uw_unit __uwn_lam_1862_1862(uw_context, uw_Basis_client);
static uw_unit __uwn_expunger_1859(uw_context, uw_Basis_client);
static uw_unit __uwn_initializer_1860(uw_context, uw_unit);
static struct __uws_2* __uwn_allRows_1840(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_lam_1863_1863(uw_context, struct __uws_2*, uw_unit);
static uw_unit __uwn_doBatch_1843(uw_context, struct __uws_2*, uw_unit);
static uw_unit __uwn_doBatch_1844(uw_context, struct __uws_2*, uw_unit);
static uw_unit __uwn_lam_1864_1864(uw_context, uw_Basis_int, uw_unit);
static uw_unit __uwn_del_1846(uw_context, uw_Basis_int, uw_unit);
static uw_Basis_string __uwn_lam_1865_1865(uw_context, struct __uws_2*);
static uw_Basis_string __uwn_jsify_1861(uw_context, struct __uws_2*);
static uw_Basis_string __uwn_lam_1866_1866(uw_context, uw_unit, uw_unit);
static uw_Basis_string __uwn_lam_1867_1867(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_wrap_main_1858(uw_context, uw_unit, uw_unit);

/* URL handler prototypes */
static struct __uws_2 *unurlify_list_2(uw_context, char **);
static void urlifyl_2(uw_context, struct __uws_2 *);

static char jslib[] = "urlRules = null;\n\nurfuncs[1847] = {c:\"t\",f:'{c:\"l\",b:{c:\"l\",b:{c:\"m\",e:{c:\"v\",n:0},p:cons({p:{c:\"c\",v:null},b:{c:\"c\",v:\"\"}},cons({p:{c:\"s\",n:false,p:{c:\"r\",l:cons({n:\"1\",p:{/*hoho*/c:\"v\"}},cons({n:\"2\",p:{/*hoho*/c:\"v\"}},null))}},b:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\n\\\\\\\\074tr\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\\\\\\\\n\\\\\\\\074td\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ts,a:cons({c:\".\",r:{c:\"v\",n:1},f:\"Id\"},null)},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\074/td>\\\\\\\\n\"},cons({c:\"f\",f:cat,a:cons({c:\"a\",f:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\074td\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\"},cons({c:\"f\",f:cat,a:cons({c:\".\",r:{c:\".\",r:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\074td\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\"},cons({c:\"f\",f:cat,a:cons({c:\".\",r:{c:\".\",r:{c:\"l\",b:{c:\"c\",v:\"\"}},f:\"?\"},f:\"Show\"},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\074/td>\"},cons({c:\"c\",v:null},null)},null)},null)},null)},null)},null)},f:\"?\"},f:\"Show\"},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\074/td>\"},cons({c:\"c\",v:null},null)},null)},null)},null)},null)},null)},x:{c:\"r\",l:cons({n:\"A\",v:{c:\".\",r:{c:\"v\",n:1},f:\"A\"}},cons({n:\"B\",v:{c:\".\",r:{c:\"v\",n:1},f:\"B\"}},null))}},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\n\"},cons({c:\"f\",f:cat,a:cons({c:\"m\",e:{c:\"v\",n:3},p:cons({p:{c:\"c\",v:true},b:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\074td\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\\\\\\\\074button\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\" value=\\\\\\\\\"Delete\\\\\\\\\" onclick=\\\\\\\\\\\\\\'uw_event=event;exec(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1848},x:{c:\"v\",n:1}},x:{c:\"c\",v:null}}},cons({c:\"c\",v:\")\\\\\\\\\\\\\\'>\\\\\\\\074/button>\\\\\\\\074/td>\"},null)},null)},null)},null)},null)},null)},null)},null)}},cons({p:{c:\"c\",v:false},b:{c:\"c\",v:\"\"}},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\n\\\\\\\\074/tr>\\\\\\\\n\"},cons({c:\"f\",f:cat,a:cons({c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1847},x:{c:\"v\",n:3}},x:{c:\"v\",n:0}},cons({c:\"c\",v:\"\\\\\\\\n\"},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)}},null))}}}'};\nurfuncs[1848] = {c:\"t\",f:'{c:\"l\",b:{c:\"l\",b:{c:\"f\",f:rc,a:cons({c:\"c\",v:\"/\"},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"BatchG/del/\"},cons({c:\".\",r:{c:\"v\",n:1},f:\"Id\"},null)},cons({c:\"c\",v:function(s){var t=s.split(\"/\");var i=0;return (i++,null)}},cons({c:\"K\"},cons({c:\"c\",v:false},null)))))}}}'};\n\ntime_format = \"%c\";\n";

static uw_unit __uwn_lam_1862_1862(uw_context ctx, uw_Basis_client __uwr_cli_0) {
return(0);
}

static uw_unit __uwn_expunger_1859(uw_context ctx, uw_Basis_client __uwr_x_0) {
return(__uwn_lam_1862_1862(ctx, __uwr_x_0));
}

static uw_unit __uwn_initializer_1860(uw_context ctx, uw_unit __uwr___0) {
return(0);
}

#line 1 "/Users/jacksmith/prog/urweb/demo/batchG.ur"
/* SQL table uw_BatchG_t uw_Id constraints  */

#line 41 "/Users/jacksmith/prog/urweb/demo/batchFun.ur"
static struct __uws_2* __uwn_allRows_1840(uw_context ctx, uw_unit __uwr__arg_0, uw_unit __uwr___1) {
return((({
struct __uws_2* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_a, T_T.uw_b, T_T.uw_id FROM uw_BatchG_t AS T_T", ({
uw_Basis_string disc = "1";

(!strcmp(disc, "1")) ? "" : 1 ? ({
uw_Basis_string __uwr_frag_2 = disc;
uw_Basis_strcat(ctx, " WHERE ", __uwr_frag_2);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
uw_Basis_string disc = "1";

(!strcmp(disc, "1")) ? "" : 1 ? ({
uw_Basis_string __uwr_frag_2 = disc;
uw_Basis_strcat(ctx, " HAVING ", __uwr_frag_2);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_2 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_2);
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
struct __uws_3 __uwr_r_2;
struct __uws_2* __uwr_acc_3 = acc;

__uwr_r_2.__uwf_T.__uwf_A = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : uw_strdup(ctx, (uw_Basis_string)sqlite3_column_text(stmt, 0)));
__uwr_r_2.__uwf_T.__uwf_B = (sqlite3_column_type(stmt, 1) == SQLITE_NULL ? ({ uw_Basis_float tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #1"); tmp; }) : sqlite3_column_double(stmt, 1));
__uwr_r_2.__uwf_T.__uwf_Id = (sqlite3_column_type(stmt, 2) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #2"); tmp; }) : sqlite3_column_int64(stmt, 2));

acc = ({
struct __uws_2 *tmp = uw_malloc(ctx, sizeof(struct __uws_2));
*tmp = ({ struct __uws_2 tmp = {__uwr_r_2.__uwf_T, __uwr_acc_3}; tmp; });
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
})));
}

#line 55 "/Users/jacksmith/prog/urweb/demo/batchFun.ur"
static uw_unit __uwn_lam_1863_1863(uw_context ctx, struct __uws_2* __uwr_ls_0, uw_unit __uwr___1) {
return(({
struct __uws_2* disc = __uwr_ls_0;

(disc == NULL) ? 0 : (disc != NULL) && 1 && 1 ? ({
struct __uws_1 __uwr_r_2 = (*disc).__uwf_1;
struct __uws_2* __uwr_lsPRIME_3 = (*disc).__uwf_2;
({
uw_unit __uwr_r_4 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "INSERT INTO uw_BatchG_t (uw_A, uw_B, uw_Id) VALUES (", __uwr_r_2.__uwf_A, ", ", __uwr_r_2.__uwf_B, ", ", __uwr_r_2.__uwf_Id, ")", NULL);

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
struct __uws_2* arg0 = __uwr_lsPRIME_3;
uw_unit arg1 = 0;
__uwn_doBatch_1843(ctx, arg0, arg1);
});
});
}) : ({
uw_unit (*tmp)(uw_context, uw_unit);
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})(ctx, 0));
}

#line 55 "/Users/jacksmith/prog/urweb/demo/batchFun.ur"
static uw_unit __uwn_doBatch_1843(uw_context, struct __uws_2*, uw_unit);

static uw_unit __uwn_doBatch_1843(uw_context ctx, struct __uws_2* __uwr_x_0, uw_unit __uwr___1) {
restart:
return(({
struct __uws_2* arg0 = __uwr_x_0;
uw_unit arg1 = __uwr___1;
__uwn_lam_1863_1863(ctx, arg0, arg1);
}));
}


#line 55 "/Users/jacksmith/prog/urweb/demo/batchFun.ur"
static uw_unit __uwn_doBatch_1844(uw_context ctx, struct __uws_2* __uwr_x_0, uw_unit __uwr___1) {
return(({
struct __uws_2* arg0 = __uwr_x_0;
uw_unit arg1 = __uwr___1;
__uwn_doBatch_1843(ctx, arg0, arg1);
}));
}

#line 63 "/Users/jacksmith/prog/urweb/demo/batchFun.ur"
static uw_unit __uwn_lam_1864_1864(uw_context ctx, uw_Basis_int __uwr_id_0, uw_unit __uwr___1) {
return(({
uw_Basis_string disc = uw_Basis_strcat(ctx, "DELETE FROM uw_BatchG_t WHERE ", uw_Basis_unAs(ctx, uw_Basis_mstrcat(ctx, "(T_T.uw_id = ", __uwr_id_0, ")", NULL)));

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_2 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_2;
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
}));
}

#line 62 "/Users/jacksmith/prog/urweb/demo/batchFun.ur"
static uw_unit __uwn_del_1846(uw_context ctx, uw_Basis_int __uwr_x_0, uw_unit __uwr___1) {
return(({
uw_Basis_int arg0 = __uwr_x_0;
uw_unit arg1 = __uwr___1;
__uwn_lam_1864_1864(ctx, arg0, arg1);
}));
}

#line 98 "/Users/jacksmith/prog/urweb/demo/batchFun.ur"
static uw_Basis_string __uwn_lam_1865_1865(uw_context ctx, struct __uws_2* __uwr_x_0) {
return(({
struct __uws_2* disc = __uwr_x_0;

(disc == NULL) ? "null" : (disc != NULL) && 1 ? ({
struct __uws_2 __uwr_x_1 = (*disc);
uw_Basis_mstrcat(ctx, "{_1:{_A:", uw_Basis_jsifyString(ctx, __uwr_x_1.__uwf_1.__uwf_A), ",_B:", uw_Basis_htmlifyFloat(ctx, __uwr_x_1.__uwf_1.__uwf_B), ",_Id:", uw_Basis_htmlifyInt(ctx, __uwr_x_1.__uwf_1.__uwf_Id), "},_2:", __uwn_jsify_1861(ctx, __uwr_x_1.__uwf_2), "}", NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}

static uw_Basis_string __uwn_jsify_1861(uw_context, struct __uws_2*);

static uw_Basis_string __uwn_jsify_1861(uw_context ctx, struct __uws_2* __uwr_x_0) {
restart:
return(__uwn_lam_1865_1865(ctx, __uwr_x_0));
}


#line 156 "/Users/jacksmith/prog/urweb/lib/ur/top.ur"
static uw_Basis_string __uwn_lam_1866_1866(uw_context ctx, uw_unit __uwr___0, uw_unit __uwr___1) {
return("");
}

#line 156 "/Users/jacksmith/prog/urweb/lib/ur/top.ur"
static uw_Basis_string __uwn_lam_1867_1867(uw_context ctx, uw_unit __uwr___0, uw_unit __uwr___1) {
return("");
}

static uw_unit __uwn_wrap_main_1858(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(({
uw_Basis_source __uwr_r_2 = uw_Basis_new_client_source(ctx, uw_Basis_mstrcat(ctx, "{c:\"c\",v:", __uwn_jsify_1861(ctx, NULL), "}", NULL));
({
uw_Basis_source __uwr_r_3 = uw_Basis_new_client_source(ctx, uw_Basis_mstrcat(ctx, "{c:\"c\",v:", __uwn_jsify_1861(ctx, NULL), "}", NULL));
({
uw_Basis_source __uwr_r_4 = uw_Basis_new_client_source(ctx, uw_Basis_mstrcat(ctx, "{c:\"c\",v:", uw_Basis_jsifyString(ctx, ""), "}", NULL));
({
struct __uws_4 __uwr_r_5 = 0.__uwf__.__uwf_NewState(ctx, 0).__uwf_NewState;
((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<h2"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Rows</h2>\n"), 0), (((uw_write(ctx, "<script type=\"text/javascript\">dyn(\"span\", execD("), 0), (((uw_write(ctx, "{c:\"f\",f:sb,a:cons({c:\"f\",f:ss,a:cons({c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_2), (uw_write(ctx, "},null)},cons({c:\"l\",b:{c:\"f\",f:sr,a:cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074table\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\\n\\074tr\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\\n\\074th\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">Id\\074/th>\\n\"},cons({c:\"f\",f:cat,a:cons({c:\"a\",f:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074th\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:eh,a:cons({c:\".\",r:{c:\".\",r:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074th\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:eh,a:cons({c:\".\",r:{c:\".\",r:{c:\"l\",b:{c:\"c\",v:\"\"}},f:\"?\"},f:\"Nam\"},null)},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074/th>\"},cons({c:\"c\",v:null},null)},null)},null)},null)},null)},null)},f:\"?\"},f:\"Nam\"},null)},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074/th>\"},cons({c:\"c\",v:null},null)},null)},null)},null)},null)},null)},x:{c:\"r\",l:cons({n:\"A\",v:{c:\"r\",l:cons({n:\"Inject\",v:{c:\"l\",b:{c:\"v\",n:0}}},cons({n:\"Nam\",v:{c:\"c\",v:\"A\"}},cons({n:\"NewState\",v:{c:\"l\",b:{c:\"f\",f:sc,a:cons({c:\"c\",v:\"\"},null)}}},cons({n:\"ReadState\",v:{c:\"l\",b:{c:\"l\",b:{c:\"f\",f:sg,a:cons({c:\"v\",n:1},null)}}}},cons({n:\"Show\",v:{c:\"l\",b:{c:\"f\",f:eh,a:cons({c:\"v\",n:0},null)}}},cons({n:\"Widget\",v:{c:\"l\",b:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074script type=\\\"text/javascript\\\">inp(exec(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"v\",n:0}},cons({c:\"c\",v:\"))\\074/script>\"},null)},null)}}},null))))))}},cons({n:\"B\",v:{c:\"r\",l:cons({n:\"Inject\",v:{c:\"l\",b:{c:\"v\",n:0}}},cons({n:\"Nam\",v:{c:\"c\",v:\"B\"}},cons({n:\"NewState\",v:{c:\"l\",b:{c:\"f\",f:sc,a:cons({c:\"c\",v:\"\"},null)}}},cons({n:\"ReadState\",v:{c:\"l\",b:{c:\"l\",b:{c:\"a\",f:{c:\"c\",v:pfl},x:{c:\"f\",f:sg,a:cons({c:\"v\",n:1},null)}}}}},cons({n:\"Show\",v:{c:\"l\",b:{c:\"f\",f:ts,a:cons({c:\"v\",n:0},null)}}},cons({n:\"Widget\",v:{c:\"l\",b:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074script type=\\\"text/javascript\\\">inp(exec(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"v\",n:0}},cons({c:\"c\",v:\"))\\074/script>\"},null)},null)}}},null))))))}},null))}},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\n\\074/tr>\\n\"},cons({c:\"f\",f:cat,a:cons({c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1847},x:{c:\"c\",v:true}},x:{c:\"v\",n:0}},cons({c:\"c\",v:\"\\n\\074/table>\"},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)}},null)}"), 0))), (uw_write(ctx, "))</script>"), 0))), ((uw_write(ctx, "\n<button"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, " value=\"Update\" onclick=\'uw_event=event;exec("), 0), (((uw_write(ctx, "{c:\"=\",e1:{c:\"f\",f:rc,a:cons({c:\"c\",v:\"/\"},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"BatchG/allRows/\"},cons({c:\"c\",v:null},null)},cons({c:\"c\",v:function(s){var t=s.split(\"/\");var i=0;return uul(function(){return t[i++];},function(){return {_A:uu(t[i++]),_B:parseFloat(t[i++]),_Id:parseInt(t[i++])}})}},cons({c:\"K\"},cons({c:\"c\",v:false},null)))))},e2:{c:\"f\",f:sv,a:cons({c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_2), (uw_write(ctx, "},cons({c:\"v\",n:0},null))}}"), 0))), ((uw_write(ctx, ")\'></button><br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<h2"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Batch new rows to add</h2>\n<table"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<tr"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> <th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Id:</th> <td"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "><script type=\"text/javascript\">inp(exec("), 0), (((uw_write(ctx, "{c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_4), (uw_write(ctx, "}"), 0))), ((uw_write(ctx, "))</script></td> </tr>\n"), 0), ((uw_write(ctx, uw_Basis_mstrcat(ctx, "<tr", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "> <th", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyString(ctx, uw_Basis_mstrcat(ctx, "<tr", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "> <th", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyString(ctx, __uwn_lam_1866_1866.__uwf__.__uwf_Nam), ":</th> <td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", "".__uwf__.__uwf_Widget, "</td> </tr>", 0, NULL).__uwf__.__uwf_Nam), ":</th> <td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_mstrcat(ctx, "<tr", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "> <th", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyString(ctx, __uwn_lam_1867_1867.__uwf__.__uwf_Nam), ":</th> <td", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", "".__uwf__.__uwf_Widget, "</td> </tr>", 0, NULL).__uwf__.__uwf_Widget, "</td> </tr>", 0, NULL)(ctx, __uwr_r_5)), 0), ((uw_write(ctx, "\n<tr"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> <th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></th> <td"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "><button"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, " value=\"Batch it\" onclick=\'uw_event=event;exec("), 0), (((uw_write(ctx, "{c:\"=\",e1:{c:\"f\",f:sg,a:cons({c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_4), ((uw_write(ctx, "},null)},e2:{c:\"=\",e1:{c:\"a\",f:{c:\"r\",l:cons({n:\"?\",v:{c:\".\",r:{c:\".\",r:{c:\".\",r:{c:\"l\",b:{c:\"c\",v:null}},f:\"?\"},f:\"ReadState\"},f:\"ReadState\"}},null)},x:{c:\"c\",v:null}},e2:{c:\"=\",e1:{c:\"f\",f:sg,a:cons({c:\"c\",v:{_A:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_5.__uwf_A), ((uw_write(ctx, ",_B:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_5.__uwf_B), ((uw_write(ctx, "}},null)},e2:{c:\"f\",f:sv,a:cons({c:\"c\",v:{_A:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_5.__uwf_A), ((uw_write(ctx, ",_B:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_5.__uwf_B), (uw_write(ctx, "}},cons({c:\"r\",l:cons({n:\"1\",v:{c:\"r\",l:cons({n:\"A\",v:{c:\".\",r:{c:\"v\",n:1},f:\"A\"}},cons({n:\"B\",v:{c:\".\",r:{c:\"v\",n:1},f:\"B\"}},cons({n:\"Id\",v:{c:\"a\",f:{c:\"c\",v:pi},x:{c:\"v\",n:2}}},null)))}},cons({n:\"2\",v:{c:\"v\",n:0}},null))},null))}}}}"), 0))))))))))), ((uw_write(ctx, ")\'></button></td> </tr>\n</table>\n<h2"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Already batched:</h2>\n"), 0), (((uw_write(ctx, "<script type=\"text/javascript\">dyn(\"span\", execD("), 0), (((uw_write(ctx, "{c:\"f\",f:sb,a:cons({c:\"f\",f:ss,a:cons({c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_3), (uw_write(ctx, "},null)},cons({c:\"l\",b:{c:\"f\",f:sr,a:cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074table\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\\n\\074tr\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\\n\\074th\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">Id\\074/th>\\n\"},cons({c:\"f\",f:cat,a:cons({c:\"a\",f:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074th\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:eh,a:cons({c:\".\",r:{c:\".\",r:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074th\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:eh,a:cons({c:\".\",r:{c:\".\",r:{c:\"l\",b:{c:\"c\",v:\"\"}},f:\"?\"},f:\"Nam\"},null)},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074/th>\"},cons({c:\"c\",v:null},null)},null)},null)},null)},null)},null)},f:\"?\"},f:\"Nam\"},null)},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074/th>\"},cons({c:\"c\",v:null},null)},null)},null)},null)},null)},null)},x:{c:\"r\",l:cons({n:\"A\",v:{c:\"r\",l:cons({n:\"Inject\",v:{c:\"l\",b:{c:\"v\",n:0}}},cons({n:\"Nam\",v:{c:\"c\",v:\"A\"}},cons({n:\"NewState\",v:{c:\"l\",b:{c:\"f\",f:sc,a:cons({c:\"c\",v:\"\"},null)}}},cons({n:\"ReadState\",v:{c:\"l\",b:{c:\"l\",b:{c:\"f\",f:sg,a:cons({c:\"v\",n:1},null)}}}},cons({n:\"Show\",v:{c:\"l\",b:{c:\"f\",f:eh,a:cons({c:\"v\",n:0},null)}}},cons({n:\"Widget\",v:{c:\"l\",b:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074script type=\\\"text/javascript\\\">inp(exec(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"v\",n:0}},cons({c:\"c\",v:\"))\\074/script>\"},null)},null)}}},null))))))}},cons({n:\"B\",v:{c:\"r\",l:cons({n:\"Inject\",v:{c:\"l\",b:{c:\"v\",n:0}}},cons({n:\"Nam\",v:{c:\"c\",v:\"B\"}},cons({n:\"NewState\",v:{c:\"l\",b:{c:\"f\",f:sc,a:cons({c:\"c\",v:\"\"},null)}}},cons({n:\"ReadState\",v:{c:\"l\",b:{c:\"l\",b:{c:\"a\",f:{c:\"c\",v:pfl},x:{c:\"f\",f:sg,a:cons({c:\"v\",n:1},null)}}}}},cons({n:\"Show\",v:{c:\"l\",b:{c:\"f\",f:ts,a:cons({c:\"v\",n:0},null)}}},cons({n:\"Widget\",v:{c:\"l\",b:{c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\074script type=\\\"text/javascript\\\">inp(exec(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"v\",n:0}},cons({c:\"c\",v:\"))\\074/script>\"},null)},null)}}},null))))))}},null))}},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\n\\074/tr>\\n\"},cons({c:\"f\",f:cat,a:cons({c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1847},x:{c:\"c\",v:false}},x:{c:\"v\",n:0}},cons({c:\"c\",v:\"\\n\\074/table>\"},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)}},null)}"), 0))), (uw_write(ctx, "))</script>"), 0))), ((uw_write(ctx, "\n<button"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, " value=\"Execute\" onclick=\'uw_event=event;exec("), 0), (((uw_write(ctx, "{c:\"=\",e1:{c:\"f\",f:rc,a:cons({c:\"c\",v:\"/\"},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"BatchG/doBatch/\"},cons({c:\"f\",f:sg,a:cons({c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_3), ((uw_write(ctx, "},null)},null)},cons({c:\"c\",v:function(s){var t=s.split(\"/\");var i=0;return (i++,null)}},cons({c:\"K\"},cons({c:\"c\",v:false},null)))))},e2:{c:\"f\",f:sv,a:cons({c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_3), (uw_write(ctx, "},cons({c:\"c\",v:null},null))}}"), 0))))), (uw_write(ctx, ")\'></button>\n</body>"), 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
});
});
});
}));
}

/* URL handler helpers */
static struct __uws_2 *unurlify_list_2(uw_context ctx, char **request) {
return ((*request)[0] == '/' ? ++*request : *request,
((!strncmp(*request, "Nil", 3) && ((*request)[3] == 0 || (*request)[3] == '/')) ? (*request += 3, ((*request)[0] == '/' ? ((*request)[0] = 0, ++*request) : NULL), NULL) : ((!strncmp(*request, "Cons", 4) && ((*request)[4] == 0 || (*request)[4] == '/')) ? (*request += 4, ((*request)[0] == '/' ? ++*request : NULL),
({
struct __uws_2 *tmp = uw_malloc(ctx, sizeof(struct __uws_2));
*tmp = ({
struct __uws_1 uwr_1 = ({
uw_Basis_string uwr_A = uw_Basis_unurlifyString(ctx, request);
uw_Basis_float uwr_B = uw_Basis_unurlifyFloat(ctx, request);
uw_Basis_int uwr_Id = uw_Basis_unurlifyInt(ctx, request);
struct __uws_1 tmp = { uwr_A, uwr_B, uwr_Id };
tmp;
});
struct __uws_2* uwr_2 = unurlify_list_2(ctx, request);
struct __uws_2 tmp = { uwr_1, uwr_2 };
tmp;
});
tmp;
})) : (uw_error(ctx, FATAL, "Ur/Web: could not decode a list from the URL at this point in the path: %s", *request), NULL))));
}
static void urlifyl_2(uw_context ctx, struct __uws_2 *it0) {
if (it0) {
uw_write(ctx, "Cons/");
struct __uws_2 it1 = *it0;
{
struct __uws_1 it2 = it1.__uwf_1;
{
uw_Basis_string it3 = it2.__uwf_A;
uw_Basis_urlifyString_w(ctx, it3);
}
{
uw_Basis_float it3 = it2.__uwf_B;
uw_write(ctx, "/");
uw_Basis_urlifyFloat_w(ctx, it3);
}
{
uw_Basis_int it3 = it2.__uwf_Id;
uw_write(ctx, "/");
uw_Basis_urlifyInt_w(ctx, it3);
}
}
{
struct __uws_2* it2 = it1.__uwf_2;
uw_write(ctx, "/");
urlifyl_2(ctx, it2);
}
urlifyl_2(ctx, it0->next);
} else {
uw_write(ctx, "Nil");
}
}


static void uw_setup_limits(void) {
}

void uw_global_custom(void) {
uw_setup_limits();
}

static void uw_initializer(uw_context ctx) {
uw_begin_initializing(ctx);
uw_end_initializing(ctx);
__uwn_initializer_1860(ctx, 0);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
__uwn_expunger_1859(ctx, cli);
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
if (!strncmp(request, "/BatchG/del", 11) && (request[11] == 0 || request[11] == '/')) {
request += 11;
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
uw_unit it0 = __uwn_del_1846(ctx, arg0, 0);
uw_write(ctx, uw_get_real_script(ctx));
uw_write(ctx, "\n");
uw_Basis_urlifyString_w(ctx, "");
return;
}
}
if (!strncmp(request, "/BatchG/doBatch", 15) && (request[15] == 0 || request[15] == '/')) {
request += 15;
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
struct __uws_2* arg0 = unurlify_list_2(ctx, &request);
uw_unit it0 = __uwn_doBatch_1844(ctx, arg0, 0);
uw_write(ctx, uw_get_real_script(ctx));
uw_write(ctx, "\n");
uw_Basis_urlifyString_w(ctx, "");
return;
}
}
if (!strncmp(request, "/BatchG/allRows", 15) && (request[15] == 0 || request[15] == '/')) {
request += 15;
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
struct __uws_2* it0 = __uwn_allRows_1840(ctx, arg0, 0);
uw_write(ctx, uw_get_real_script(ctx));
uw_write(ctx, "\n");
urlifyl_2(ctx, it0);
return;
}
}
if (!strncmp(request, "/BatchG/main", 12) && (request[12] == 0 || request[12] == '/')) {
request += 12;
if (*request == '/') ++request;
uw_write_header(ctx, "Content-type: text/html; charset=utf-8\r\n");
uw_write_header(ctx, "Content-script-type: text/javascript\r\n");
uw_write(ctx, uw_begin_html5);
uw_mayReturnIndirectly(ctx);
uw_set_could_write_db(ctx, 0);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
__uwn_wrap_main_1858(ctx, arg0, 0);
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
