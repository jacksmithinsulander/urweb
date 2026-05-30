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
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_Chat_Room_t' does not exist.");
}
sqlite3_finalize(stmt);
{ int _prepare_rc;
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_Chat_t' does not exist.");
}
sqlite3_finalize(stmt);
}

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/private/tmp/chat.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

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
uw_Basis_string __uwf_1;
uw_Basis_source __uwf_2;
};

struct __uws_2 {
uw_Basis_int __uwf_Room;
};

struct __uws_3 {
struct __uws_2 __uwf_T;
};

struct __uws_4 {
uw_Basis_channel __uwf_Channel;
};

struct __uws_5 {
struct __uws_4 __uwf_T;
};

struct __uws_6 {
uw_Basis_source __uwf_Head;
uw_Basis_source __uwf_Tail;
};

struct __uws_7 {
uw_Basis_int __uwf_Room;
uw_Basis_string __uwf_Title;
};

struct __uws_8 {
struct __uws_7 __uwf_T;
};

struct __uws_9 {
uw_Basis_string __uwf_Title;
};

/* Function prototypes */
static uw_unit __uwn_lam_1816_1816(uw_context, uw_Basis_client);
static uw_unit __uwn_expunger_1801(uw_context, uw_Basis_client);
static uw_unit __uwn_initializer_1802(uw_context, uw_unit);
static uw_unit __uwn_lam_1817_1817(uw_context, uw_Basis_int, uw_Basis_string, uw_unit);
static uw_unit __uwn__speak_1762(uw_context, uw_Basis_int, uw_Basis_string, uw_unit);
static uw_Basis_string __uwn_lam_1818_1818(uw_context, uw_Basis_int, uw_unit, uw_unit);
static uw_Basis_string __uwn_lam_1819_1819(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_Basis_string __uwn_lam_1821_1821(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_lam_1822_1822(uw_context, uw_Basis_int, uw_unit, uw_unit);
static uw_unit __uwn_lam_1823_1823(uw_context, struct __uws_9, uw_unit);
static uw_unit __uwn_lam_1824_1824(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_unit __uwn_lam_1826_1826(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_lam_1827_1827(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_unit __uwn_lam_1829_1829(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_lam_1830_1830(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_unit __uwn_lam_1832_1832(uw_context, struct __uws_6, uw_unit);
static uw_Basis_string __uwn_list_1766(uw_context, uw_unit, uw_unit);
static uw_Basis_string __uwn_delete_1767(uw_context, uw_Basis_int, uw_unit, uw_unit);
static uw_Basis_string __uwn_main_1768(uw_context, uw_unit, uw_unit);
static uw_Basis_string __uwn_script1769_1769(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_Basis_string __uwn_script1770_1770(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_wrap_chat_1798(uw_context, uw_Basis_int, uw_unit, uw_unit);
static uw_unit __uwn_wrap__create_1800(uw_context, struct __uws_9, uw_unit);
static uw_unit __uwn_script1769_1808(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_unit __uwn_script1770_1809(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_script1769_1811(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_unit __uwn_script1770_1812(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_script1769_1814(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_unit __uwn_script1770_1815(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_wrap_main_1797(uw_context, uw_unit, uw_unit);

static char jslib[] = "urlRules = null;\n\nurfuncs[1770] = {c:\"t\",f:'{c:\"l\",b:{c:\"l\",b:{c:\"a\",f:{c:\"n\",n:1752},x:{c:\".\",r:{c:\"v\",n:1},f:\"Head\"}}}}'};\nurfuncs[1769] = {c:\"t\",f:'{c:\"l\",b:{c:\"l\",b:{c:\"l\",b:{c:\"=\",e1:{c:\"f\",f:sg,a:cons({c:\"v\",n:2},null)},e2:{c:\"=\",e1:{c:\"f\",f:sv,a:cons({c:\"v\",n:3},cons({c:\"c\",v:\"\"},null))},e2:{c:\"f\",f:rc,a:cons({c:\"c\",v:\"/\"},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"Chat/speak/\"},cons({c:\"f\",f:cat,a:cons({c:\"v\",n:3},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"/\"},cons({c:\"v\",n:1},null)},null)},null)},cons({c:\"c\",v:function(s){var t=s.split(\"/\");var i=0;return (i++,null)}},cons({c:\"K\"},cons({c:\"c\",v:false},null)))))}}}}}}'};\nurfuncs[1752] = {c:\"t\",f:'{c:\"l\",b:{c:\"f\",f:sb,a:cons({c:\"f\",f:ss,a:cons({c:\"v\",n:0},null)},cons({c:\"l\",b:{c:\"f\",f:sr,a:cons({c:\"a\",f:{c:\"n\",n:1751},x:{c:\"v\",n:0}},null)}},null)}}'};\nurfuncs[1751] = {c:\"t\",f:'{c:\"l\",b:{c:\"m\",e:{c:\"v\",n:0},p:cons({p:{c:\"c\",v:null},b:{c:\"c\",v:\"\"}},cons({p:{c:\"s\",n:false,p:{c:\"r\",l:cons({n:\"1\",p:{/*hoho*/c:\"v\"}},cons({n:\"2\",p:{/*hoho*/c:\"v\"}},null))}},b:{c:\"f\",f:cat,a:cons({c:\"f\",f:eh,a:cons({c:\"v\",n:1},null)},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\074br\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\\\\\\\\074/br>\\\\\\\\074script type=\\\\\\\\\"text/javascript\\\\\\\\\">dyn(\\\\\\\\\"span\\\\\\\\\", execD(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"a\",f:{c:\"n\",n:1752},x:{c:\"v\",n:0}}},cons({c:\"c\",v:\"))\\\\\\\\074/script>\"},null)},null)},null)},null)},null)},null)}},null))}}'};\n\ntime_format = \"%c\";\n";

static uw_unit __uwn_lam_1816_1816(uw_context ctx, uw_Basis_client __uwr_cli_0) {
return(0);
}

static uw_unit __uwn_expunger_1801(uw_context ctx, uw_Basis_client __uwr_x_0) {
return(__uwn_lam_1816_1816(ctx, __uwr_x_0));
}

static uw_unit __uwn_initializer_1802(uw_context ctx, uw_unit __uwr___0) {
return(0);
}

#line 2 "/Users/jacksmith/prog/urweb/demo/broadcast.ur"
/* SQL sequence uw_Chat_Room_s */

#line 3 "/Users/jacksmith/prog/urweb/demo/broadcast.ur"
/* SQL table uw_Chat_Room_t uw_Id, uw_Client constraints  */

#line 5 "/Users/jacksmith/prog/urweb/demo/chat.ur"
/* SQL sequence uw_Chat_s */

#line 6 "/Users/jacksmith/prog/urweb/demo/chat.ur"
/* SQL table uw_Chat_t uw_Id constraints  */

#line 31 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1817_1817(uw_context ctx, uw_Basis_int __uwr_id_0, uw_Basis_string __uwr_line_1, uw_unit __uwr___2) {
return(({
struct __uws_3* __uwr_r_3 = (({
struct __uws_3* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_room FROM uw_Chat_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_id_0), ") HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_3 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_3);
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
struct __uws_3 __uwr_r_3;
struct __uws_3* __uwr_acc_4 = acc;

__uwr_r_3.__uwf_T.__uwf_Room = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : sqlite3_column_int64(stmt, 0));

acc = ({
struct __uws_3 *tmp = uw_malloc(ctx, sizeof(struct __uws_3));
*tmp = __uwr_r_3;
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
struct __uws_3 __uwr_r_4 = ({
struct __uws_3* disc = __uwr_r_3;

(disc == NULL) ? ({
struct __uws_3 tmp;
uw_error(ctx, FATAL, "%s", "Query returned no rows");
tmp;
}) : (disc != NULL) && 1 ? ({
struct __uws_3 __uwr_r_4 = (*disc);
__uwr_r_4;
}) : ({
struct __uws_3 tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
(({
uw_unit acc = 0;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_channel FROM uw_Chat_Room_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_4.__uwf_T.__uwf_Room), ") HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_5 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_5);
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
struct __uws_5 __uwr_r_5;
uw_unit __uwr_acc_6 = acc;

__uwr_r_5.__uwf_T.__uwf_Channel = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_channel tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : ({
sqlite3_int64 n = sqlite3_column_int64(stmt, 0);
uw_Basis_channel ch = {n >> 32, n & 0xFFFFFFFF};
ch;
}));

acc = uw_Basis_send(ctx, __uwr_r_5.__uwf_T.__uwf_Channel, uw_Basis_urlifyString(ctx, __uwr_line_1));
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
}));
});
}));
}

#line 9 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn__speak_1762(uw_context ctx, uw_Basis_int __uwr_x_0, uw_Basis_string __uwr_x_1, uw_unit __uwr___2) {
return(({
uw_Basis_int arg0 = __uwr_x_0;
uw_Basis_string arg1 = __uwr_x_1;
uw_unit arg2 = __uwr___2;
__uwn_lam_1817_1817(ctx, arg0, arg1, arg2);
}));
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_Basis_string __uwn_lam_1818_1818(uw_context ctx, uw_Basis_int __uwr_id_0, uw_unit __uwr__arg_1, uw_unit __uwr___2) {
return(({
uw_unit __uwr_r_3 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "DELETE FROM uw_Chat_t WHERE (uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_id_0), ")", NULL);

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
uw_unit arg0 = 0;
uw_unit arg1 = 0;
__uwn_main_1768(ctx, arg0, arg1);
});
}));
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_Basis_string __uwn_lam_1819_1819(uw_context ctx, uw_Basis_int __uwr___0, uw_Basis_source __uwr___1, uw_unit __uwr___2) {
return(0);
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_Basis_string __uwn_lam_1821_1821(uw_context ctx, struct __uws_6 __uwr___0, uw_unit __uwr___1) {
return(0);
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1822_1822(uw_context ctx, uw_Basis_int __uwr_x1_0, uw_unit __uwr_x0_1, uw_unit __uwr___2) {
return(({
struct __uws_8* __uwr_r_3 = (({
struct __uws_8* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_room, T_T.uw_title FROM uw_Chat_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_x1_0), ") HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_3 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_3);
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
struct __uws_8 __uwr_r_3;
struct __uws_8* __uwr_acc_4 = acc;

__uwr_r_3.__uwf_T.__uwf_Room = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : sqlite3_column_int64(stmt, 0));
__uwr_r_3.__uwf_T.__uwf_Title = (sqlite3_column_type(stmt, 1) == SQLITE_NULL ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #1"); tmp; }) : uw_strdup(ctx, (uw_Basis_string)sqlite3_column_text(stmt, 1)));

acc = ({
struct __uws_8 *tmp = uw_malloc(ctx, sizeof(struct __uws_8));
*tmp = __uwr_r_3;
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
struct __uws_8 __uwr_r_4 = ({
struct __uws_8* disc = __uwr_r_3;

(disc == NULL) ? ({
struct __uws_8 tmp;
uw_error(ctx, FATAL, "%s", "Query returned no rows");
tmp;
}) : (disc != NULL) && 1 ? ({
struct __uws_8 __uwr_r_4 = (*disc);
__uwr_r_4;
}) : ({
struct __uws_8 tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
uw_Basis_client __uwr_r_5 = uw_Basis_self(ctx);
({
struct __uws_5* __uwr_r_6 = (({
struct __uws_5* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_channel FROM uw_Chat_Room_t AS T_T WHERE ((T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_4.__uwf_T.__uwf_Room), ") AND (T_T.uw_client = ", uw_Basis_sqlifyClient(ctx, __uwr_r_5), ")) HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_6 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_6);
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
struct __uws_5 __uwr_r_6;
struct __uws_5* __uwr_acc_7 = acc;

__uwr_r_6.__uwf_T.__uwf_Channel = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_channel tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : ({
sqlite3_int64 n = sqlite3_column_int64(stmt, 0);
uw_Basis_channel ch = {n >> 32, n & 0xFFFFFFFF};
ch;
}));

acc = ({
struct __uws_5 *tmp = uw_malloc(ctx, sizeof(struct __uws_5));
*tmp = __uwr_r_6;
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
uw_Basis_channel __uwr_r_7 = ({
struct __uws_5* disc = __uwr_r_6;

(disc == NULL) ? ({
uw_Basis_channel __uwr_r_7 = uw_Basis_new_channel(ctx, 0);
({
uw_unit __uwr_r_8 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "INSERT INTO uw_Chat_Room_t (uw_Channel, uw_Client, uw_Id) VALUES (", uw_Basis_sqlifyChannel(ctx, __uwr_r_7), ", ", uw_Basis_sqlifyClient(ctx, __uwr_r_5), ", ", uw_Basis_sqlifyInt(ctx, __uwr_r_4.__uwf_T.__uwf_Room), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_8 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_8;
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
__uwr_r_7;
});
}) : (disc != NULL) && 1 ? ({
struct __uws_5 __uwr_r_7 = (*disc);
__uwr_r_7.__uwf_T.__uwf_Channel;
}) : ({
uw_Basis_channel tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
uw_Basis_source __uwr_r_8 = uw_Basis_new_client_source(ctx, uw_Basis_mstrcat(ctx, "{c:\"c\",v:", uw_Basis_jsifyString(ctx, ""), "}", NULL));
({
uw_Basis_source __uwr_r_9 = uw_Basis_new_client_source(ctx, "{c:\"c\",v:null}");
({
struct __uws_6 __uwr_r_10 = ({ struct __uws_6 tmp = {__uwr_r_9, uw_Basis_new_client_source(ctx, uw_Basis_mstrcat(ctx, "{c:\"c\",v:", uw_Basis_htmlifySource(ctx, __uwr_r_9), "}", NULL))}; tmp; });
((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<h1"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">"), 0), (uw_Basis_htmlifyString_w(ctx, __uwr_r_4.__uwf_T.__uwf_Title), ((uw_write(ctx, "</h1>\n<button"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, " value=\"Send:\" onclick=\'uw_event=event;exec("), 0), (((uw_write(ctx, "{c:\"a\",f:{c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1769},x:{c:\"c\",v:"), 0), (uw_Basis_htmlifyInt_w(ctx, __uwr_x1_0), ((uw_write(ctx, "}},x:{c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_8), (uw_write(ctx, "}},x:{c:\"c\",v:null}}"), 0))))), ((uw_write(ctx, ")\'></button> <script type=\"text/javascript\">inp(exec("), 0), (((uw_write(ctx, "{c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_8), (uw_write(ctx, "}"), 0))), ((uw_write(ctx, "))</script>\n<h2"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Messages</h2>\n<script type=\"text/javascript\">dyn(\"span\", execD("), 0), (((uw_write(ctx, "{c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1770},x:{c:\"c\",v:{_Head:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_10.__uwf_Head), ((uw_write(ctx, ",_Tail:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_10.__uwf_Tail), (uw_write(ctx, "}}},x:{c:\"c\",v:null}}"), 0))))), (uw_write(ctx, "))</script>\n</body>"), 0)))))))))))))))))))));
});
});
});
});
});
});
});
}));
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1823_1823(uw_context ctx, struct __uws_9 __uwr_x0_0, uw_unit __uwr___1) {
return(({
uw_Basis_int __uwr_r_2 = ({
uw_Basis_int n;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
char *insert = uw_Basis_strcat(ctx, "INSERT INTO ", uw_Basis_strcat(ctx, "uw_Chat_s", " VALUES (NULL)"));
char *delete = uw_Basis_strcat(ctx, "DELETE FROM ", "uw_Chat_s");
if (sqlite3_exec(conn->conn, insert, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' INSERT failed: %s", sqlite3_errmsg(conn->conn));
n = sqlite3_last_insert_rowid(conn->conn);
if (sqlite3_exec(conn->conn, delete, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' DELETE failed: %s", sqlite3_errmsg(conn->conn));
n;
});
({
uw_Basis_int __uwr_r_3 = ({
uw_Basis_int n;
uw_ensure_transaction(ctx);
uw_conn *conn = uw_get_db(ctx);
char *insert = uw_Basis_strcat(ctx, "INSERT INTO ", uw_Basis_strcat(ctx, "uw_Chat_Room_s", " VALUES (NULL)"));
char *delete = uw_Basis_strcat(ctx, "DELETE FROM ", "uw_Chat_Room_s");
if (sqlite3_exec(conn->conn, insert, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' INSERT failed: %s", sqlite3_errmsg(conn->conn));
n = sqlite3_last_insert_rowid(conn->conn);
if (sqlite3_exec(conn->conn, delete, NULL, NULL, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "'nextval' DELETE failed: %s", sqlite3_errmsg(conn->conn));
n;
});
({
uw_unit __uwr_r_4 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "INSERT INTO uw_Chat_t (uw_Id, uw_Room, uw_Title) VALUES (", uw_Basis_sqlifyInt(ctx, __uwr_r_2), ", ", uw_Basis_sqlifyInt(ctx, __uwr_r_3), ", ", uw_Basis_sqlifyString(ctx, __uwr_x0_0.__uwf_Title), ")", NULL);

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
(uw_write(ctx, ({
uw_unit arg0 = 0;
uw_unit arg1 = 0;
__uwn_main_1768(ctx, arg0, arg1);
})), 0);
});
});
}));
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1824_1824(uw_context ctx, uw_Basis_int __uwr___0, uw_Basis_source __uwr___1, uw_unit __uwr___2) {
return(0);
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1826_1826(uw_context ctx, struct __uws_6 __uwr___0, uw_unit __uwr___1) {
return(0);
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1827_1827(uw_context ctx, uw_Basis_int __uwr___0, uw_Basis_source __uwr___1, uw_unit __uwr___2) {
return(0);
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1829_1829(uw_context ctx, struct __uws_6 __uwr___0, uw_unit __uwr___1) {
return(0);
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1830_1830(uw_context ctx, uw_Basis_int __uwr___0, uw_Basis_source __uwr___1, uw_unit __uwr___2) {
return(0);
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1832_1832(uw_context ctx, struct __uws_6 __uwr___0, uw_unit __uwr___1) {
return(0);
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_Basis_string __uwn_list_1766(uw_context, uw_unit, uw_unit);
static uw_Basis_string __uwn_delete_1767(uw_context, uw_Basis_int, uw_unit, uw_unit);
static uw_Basis_string __uwn_main_1768(uw_context, uw_unit, uw_unit);
static uw_Basis_string __uwn_script1769_1769(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_Basis_string __uwn_script1770_1770(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_wrap_chat_1798(uw_context, uw_Basis_int, uw_unit, uw_unit);
static uw_unit __uwn_wrap__create_1800(uw_context, struct __uws_9, uw_unit);
static uw_unit __uwn_script1769_1808(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_unit __uwn_script1770_1809(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_script1769_1811(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_unit __uwn_script1770_1812(uw_context, struct __uws_6, uw_unit);
static uw_unit __uwn_script1769_1814(uw_context, uw_Basis_int, uw_Basis_source, uw_unit);
static uw_unit __uwn_script1770_1815(uw_context, struct __uws_6, uw_unit);

static uw_Basis_string __uwn_list_1766(uw_context ctx, uw_unit __uwr___0, uw_unit __uwr___1) {
restart:
return(0);
}
static uw_Basis_string __uwn_delete_1767(uw_context ctx, uw_Basis_int __uwr___0, uw_unit __uwr___1, uw_unit __uwr___2) {
restart:
return(0);
}
static uw_Basis_string __uwn_main_1768(uw_context ctx, uw_unit __uwr___0, uw_unit __uwr___1) {
restart:
return(0);
}
static uw_Basis_string __uwn_script1769_1769(uw_context ctx, uw_Basis_int __uwr___0, uw_Basis_source __uwr___1, uw_unit __uwr___2) {
restart:
return(0);
}
static uw_Basis_string __uwn_script1770_1770(uw_context ctx, struct __uws_6 __uwr___0, uw_unit __uwr___1) {
restart:
return(0);
}
static uw_unit __uwn_wrap_chat_1798(uw_context ctx, uw_Basis_int __uwr___0, uw_unit __uwr___1, uw_unit __uwr___2) {
restart:
return(0);
}
static uw_unit __uwn_wrap__create_1800(uw_context ctx, struct __uws_9 __uwr___0, uw_unit __uwr___1) {
restart:
return(0);
}
static uw_unit __uwn_script1769_1808(uw_context ctx, uw_Basis_int __uwr___0, uw_Basis_source __uwr___1, uw_unit __uwr___2) {
restart:
return(0);
}
static uw_unit __uwn_script1770_1809(uw_context ctx, struct __uws_6 __uwr___0, uw_unit __uwr___1) {
restart:
return(0);
}
static uw_unit __uwn_script1769_1811(uw_context ctx, uw_Basis_int __uwr___0, uw_Basis_source __uwr___1, uw_unit __uwr___2) {
restart:
return(0);
}
static uw_unit __uwn_script1770_1812(uw_context ctx, struct __uws_6 __uwr___0, uw_unit __uwr___1) {
restart:
return(0);
}
static uw_unit __uwn_script1769_1814(uw_context ctx, uw_Basis_int __uwr___0, uw_Basis_source __uwr___1, uw_unit __uwr___2) {
restart:
return(0);
}
static uw_unit __uwn_script1770_1815(uw_context ctx, struct __uws_6 __uwr___0, uw_unit __uwr___1) {
restart:
return(0);
}


static uw_unit __uwn_wrap_main_1797(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return((uw_write(ctx, ({
uw_unit arg0 = __uwr_x0_0;
uw_unit arg1 = 0;
__uwn_main_1768(ctx, arg0, arg1);
})), 0));
}

static void uw_setup_limits(void) {
}

void uw_global_custom(void) {
uw_setup_limits();
}

static void uw_initializer(uw_context ctx) {
uw_begin_initializing(ctx);
uw_end_initializing(ctx);
__uwn_initializer_1802(ctx, 0);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
__uwn_expunger_1801(ctx, cli);
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
if (!strncmp(request, "/Chat/speak", 11) && (request[11] == 0 || request[11] == '/')) {
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
uw_Basis_string arg1 = uw_Basis_unurlifyString(ctx, &request);
uw_unit it0 = __uwn__speak_1762(ctx, arg0, arg1, 0);
uw_write(ctx, uw_get_real_script(ctx));
uw_write(ctx, "\n");
uw_Basis_urlifyString_w(ctx, "");
return;
}
}
if (!strncmp(request, "/Chat/chat", 10) && (request[10] == 0 || request[10] == '/')) {
request += 10;
if (*request == '/') ++request;
uw_write_header(ctx, "Content-type: text/html; charset=utf-8\r\n");
uw_write_header(ctx, "Content-script-type: text/javascript\r\n");
uw_write(ctx, uw_begin_html5);
uw_mayReturnIndirectly(ctx);
uw_set_could_write_db(ctx, 1);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 1);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_Basis_int arg0 = uw_Basis_unurlifyInt(ctx, &request);
uw_unit arg1 = uw_Basis_unurlifyUnit(ctx, &request);
__uwn_wrap_chat_1798(ctx, arg0, arg1, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/Chat/create", 12) && (request[12] == 0 || request[12] == '/')) {
request += 12;
if (*request == '/') ++request;
uw_write_header(ctx, "Content-type: text/html; charset=utf-8\r\n");
uw_write_header(ctx, "Content-script-type: text/javascript\r\n");
uw_write(ctx, uw_begin_html5);
uw_mayReturnIndirectly(ctx);
uw_set_could_write_db(ctx, 1);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 1);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
struct __uws_9 arg0 = ({
uw_Basis_string uwr_Title = uw_Basis_unurlifyString(ctx, &request);
struct __uws_9 tmp = { uwr_Title };
tmp;
});
__uwn_wrap__create_1800(ctx, arg0, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/Chat/main", 10) && (request[10] == 0 || request[10] == '/')) {
request += 10;
if (*request == '/') ++request;
uw_write_header(ctx, "Content-type: text/html; charset=utf-8\r\n");
uw_write_header(ctx, "Content-script-type: text/javascript\r\n");
uw_write(ctx, uw_begin_html5);
uw_mayReturnIndirectly(ctx);
uw_set_could_write_db(ctx, 1);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 1);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
__uwn_wrap_main_1797(ctx, arg0, 0);
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
