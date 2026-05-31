#include "urweb.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#include <libpq-fe.h>

static int strcmp_nullsafe(const char *a, const char *b) {
if (a == NULL || b == NULL) return 1;
return strcmp(a, b);
}

static void uw_client_init(void) {
uw_sqlfmtInt = "%lld::int8%n";
uw_sqlfmtFloat = "%.16g::float8%n";
uw_Estrings = 1;
uw_sql_type_annotations = 1;
uw_sqlsuffixString = "::text";
uw_sqlsuffixChar = "::char";
uw_sqlsuffixBlob = "::bytea";
uw_sqlfmtUint4 = "%u::int4%n";
}

static void uw_db_validate(uw_context ctx) { }

static void uw_db_prepare(uw_context ctx) {
PGconn *conn = uw_get_db(ctx);
PGresult *res;

res = PQprepare(conn, "uw0", "SELECT NEXTVAL('uw_Chat_s')", 0, NULL);
if (PQresultStatus(res) != PGRES_COMMAND_OK) {
char msg[1024];
strncpy(msg, PQerrorMessage(conn), 1024);
msg[1023] = 0;
PQclear(res);
PQfinish(conn);
uw_error(ctx, FATAL, "Unable to create prepared statement:\nSELECT NEXTVAL('uw_Chat_s')\n%s", msg);
}
PQclear(res);
res = PQprepare(conn, "uw1", "SELECT NEXTVAL('uw_Chat_Room_s')", 0, NULL);
if (PQresultStatus(res) != PGRES_COMMAND_OK) {
char msg[1024];
strncpy(msg, PQerrorMessage(conn), 1024);
msg[1023] = 0;
PQclear(res);
PQfinish(conn);
uw_error(ctx, FATAL, "Unable to create prepared statement:\nSELECT NEXTVAL('uw_Chat_Room_s')\n%s", msg);
}
PQclear(res);
}

static void uw_db_close(uw_context ctx) {
PQfinish(uw_get_db(ctx));
}

static int uw_db_begin(uw_context ctx, int could_write) {
PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexec(conn, could_write ? "BEGIN ISOLATION LEVEL SERIALIZABLE" : "BEGIN ISOLATION LEVEL SERIALIZABLE, READ ONLY");

if (res == NULL) return 1;

if (PQresultStatus(res) != PGRES_COMMAND_OK) {
PQclear(res);
return 1;
}
PQclear(res);
return 0;
}

static int uw_db_commit(uw_context ctx) {
PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexec(conn, "COMMIT");

if (res == NULL) return 1;

if (PQresultStatus(res) != PGRES_COMMAND_OK) {
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40001")) {
PQclear(res);
return -1;
}
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40P01")) {
PQclear(res);
return -1;
}
PQclear(res);
return 1;
}
PQclear(res);
return 0;
}

static int uw_db_rollback(uw_context ctx) {
PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexec(conn, "ROLLBACK");

if (res == NULL) return 1;

if (PQresultStatus(res) != PGRES_COMMAND_OK) {
PQclear(res);
return 1;
}
PQclear(res);
return 0;
}

static void uw_db_init(uw_context ctx) {
char *env_db_str = getenv("URWEB_PQ_CON");
PGconn *conn = PQconnectdb(env_db_str == NULL ? "dbname=test" : env_db_str);
if (conn == NULL) uw_error(ctx, FATAL, "libpq can't allocate a connection.");
if (PQstatus(conn) != CONNECTION_OK) {
char msg[1024];
strncpy(msg, PQerrorMessage(conn), 1024);
msg[1023] = 0;
PQfinish(conn);
uw_error(ctx, BOUNDED_RETRY, "Connection to Postgres server failed: %s", msg);
}
uw_set_db(ctx, conn);
uw_db_validate(ctx);
uw_db_prepare(ctx);
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
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_room FROM uw_Chat_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_id_0), ")", ({
uw_Basis_string disc = "TRUE";

(!strcmp(disc, "TRUE")) ? "" : 1 ? ({
uw_Basis_string __uwr_frag_3 = disc;
uw_Basis_strcat(ctx, " HAVING ", __uwr_frag_3);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
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
if (PQnfields(res) != 1) {
int nf = PQnfields(res);
PQclear(res);
uw_error(ctx, FATAL, "query: Ur/Web / SQL: each result row should have 1 column(s), but the database returned %d.\nSQL: %s\nServer: %s", nf, query, PQerrorMessage(conn));
}
uw_end_region(ctx);
uw_push_cleanup(ctx, (void (*)(void *))PQclear, res);
n = PQntuples(res);
for (i = 0; i < n; ++i) {
struct __uws_3 __uwr_r_3;
struct __uws_3* __uwr_acc_4 = acc;

__uwr_r_3.__uwf_T.__uwf_Room = (PQgetisnull(res, i, 0) ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Ur/Web / SQL: the database returned NULL for column 0, but this type does not allow missing values."); tmp; }) : uw_Basis_stringToInt_error(ctx, PQgetvalue(res, i, 0)));

acc = ({
struct __uws_3 *tmp = uw_malloc(ctx, sizeof(struct __uws_3));
*tmp = __uwr_r_3;
tmp;
});
}
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
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_channel FROM uw_Chat_Room_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_4.__uwf_T.__uwf_Room), ")", ({
uw_Basis_string disc = "TRUE";

(!strcmp(disc, "TRUE")) ? "" : 1 ? ({
uw_Basis_string __uwr_frag_5 = disc;
uw_Basis_strcat(ctx, " HAVING ", __uwr_frag_5);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
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
if (PQnfields(res) != 1) {
int nf = PQnfields(res);
PQclear(res);
uw_error(ctx, FATAL, "query: Ur/Web / SQL: each result row should have 1 column(s), but the database returned %d.\nSQL: %s\nServer: %s", nf, query, PQerrorMessage(conn));
}
uw_end_region(ctx);
uw_push_cleanup(ctx, (void (*)(void *))PQclear, res);
n = PQntuples(res);
for (i = 0; i < n; ++i) {
struct __uws_5 __uwr_r_5;
uw_unit __uwr_acc_6 = acc;

__uwr_r_5.__uwf_T.__uwf_Channel = (PQgetisnull(res, i, 0) ? ({ uw_Basis_channel tmp; uw_error(ctx, FATAL, "query: Ur/Web / SQL: the database returned NULL for column 0, but this type does not allow missing values."); tmp; }) : uw_Basis_stringToChannel_error(ctx, PQgetvalue(res, i, 0)));

acc = uw_Basis_send(ctx, __uwr_r_5.__uwf_T.__uwf_Channel, uw_Basis_urlifyString(ctx, __uwr_line_1));
}
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
uw_unit arg2 = 0;
__uwn_lam_1817_1817(ctx, arg0, arg1, arg2);
}));
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_Basis_string __uwn_lam_1818_1818(uw_context ctx, uw_Basis_int __uwr_id_0, uw_unit __uwr__arg_1, uw_unit __uwr___2) {
return(({
uw_unit __uwr_r_3 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "DELETE FROM uw_Chat_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_id_0), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_3 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_3;
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
uw_unit arg0 = 0;
uw_unit arg1 = 0;
__uwn_main_1768(ctx, arg0, arg1);
});
}));
}

#line 43 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_Basis_string __uwn_lam_1819_1819(uw_context ctx, uw_Basis_int __uwr___0, uw_Basis_source __uwr___1, uw_unit __uwr___2) {
return(0);
}

#line 47 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_Basis_string __uwn_lam_1821_1821(uw_context ctx, struct __uws_6 __uwr___0, uw_unit __uwr___1) {
return(0);
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1822_1822(uw_context ctx, uw_Basis_int __uwr_x1_0, uw_unit __uwr_x0_1, uw_unit __uwr___2) {
return((uw_write(ctx, ({
struct __uws_8* __uwr_r_3 = (({
struct __uws_8* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_room, T_T.uw_title FROM uw_Chat_t AS T_T WHERE (T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_x1_0), ")", ({
uw_Basis_string disc = "TRUE";

(!strcmp(disc, "TRUE")) ? "" : 1 ? ({
uw_Basis_string __uwr_frag_3 = disc;
uw_Basis_strcat(ctx, " HAVING ", __uwr_frag_3);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
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
struct __uws_8 __uwr_r_3;
struct __uws_8* __uwr_acc_4 = acc;

__uwr_r_3.__uwf_T.__uwf_Room = (PQgetisnull(res, i, 0) ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Ur/Web / SQL: the database returned NULL for column 0, but this type does not allow missing values."); tmp; }) : uw_Basis_stringToInt_error(ctx, PQgetvalue(res, i, 0)));
__uwr_r_3.__uwf_T.__uwf_Title = (PQgetisnull(res, i, 1) ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Ur/Web / SQL: the database returned NULL for column 1, but this type does not allow missing values."); tmp; }) : uw_strdup(ctx, PQgetvalue(res, i, 1)));

acc = ({
struct __uws_8 *tmp = uw_malloc(ctx, sizeof(struct __uws_8));
*tmp = __uwr_r_3;
tmp;
});
}
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
uw_Basis_channel __uwr_r_6 = ({
struct __uws_5* disc = (({
struct __uws_5* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_T.uw_channel FROM uw_Chat_Room_t AS T_T WHERE ((T_T.uw_id = ", uw_Basis_sqlifyInt(ctx, __uwr_r_4.__uwf_T.__uwf_Room), ") AND (T_T.uw_client = ", uw_Basis_sqlifyClient(ctx, __uwr_r_5), "))", ({
uw_Basis_string disc = "TRUE";

(!strcmp(disc, "TRUE")) ? "" : 1 ? ({
uw_Basis_string __uwr_frag_6 = disc;
uw_Basis_strcat(ctx, " HAVING ", __uwr_frag_6);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
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
if (PQnfields(res) != 1) {
int nf = PQnfields(res);
PQclear(res);
uw_error(ctx, FATAL, "query: Ur/Web / SQL: each result row should have 1 column(s), but the database returned %d.\nSQL: %s\nServer: %s", nf, query, PQerrorMessage(conn));
}
uw_end_region(ctx);
uw_push_cleanup(ctx, (void (*)(void *))PQclear, res);
n = PQntuples(res);
for (i = 0; i < n; ++i) {
struct __uws_5 __uwr_r_6;
struct __uws_5* __uwr_acc_7 = acc;

__uwr_r_6.__uwf_T.__uwf_Channel = (PQgetisnull(res, i, 0) ? ({ uw_Basis_channel tmp; uw_error(ctx, FATAL, "query: Ur/Web / SQL: the database returned NULL for column 0, but this type does not allow missing values."); tmp; }) : uw_Basis_stringToChannel_error(ctx, PQgetvalue(res, i, 0)));

acc = ({
struct __uws_5 *tmp = uw_malloc(ctx, sizeof(struct __uws_5));
*tmp = __uwr_r_6;
tmp;
});
}
uw_pop_cleanup(ctx);
acc;
}));

(disc == NULL) ? ({
uw_Basis_channel __uwr_r_6 = uw_Basis_new_channel(ctx, 0);
({
uw_unit __uwr_r_7 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "INSERT INTO uw_Chat_Room_t (uw_Channel, uw_Client, uw_Id) VALUES (", uw_Basis_sqlifyChannel(ctx, __uwr_r_6), ", ", uw_Basis_sqlifyClient(ctx, __uwr_r_5), ", ", uw_Basis_sqlifyInt(ctx, __uwr_r_4.__uwf_T.__uwf_Room), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_7 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_7;
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
__uwr_r_6;
});
}) : (disc != NULL) && 1 ? ({
struct __uws_5 __uwr_r_6 = (*disc);
__uwr_r_5.__uwf_T.__uwf_Channel;
}) : ({
uw_Basis_channel tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});
({
uw_Basis_source __uwr_r_7 = uw_Basis_new_client_source(ctx, uw_Basis_mstrcat(ctx, "{c:\"c\",v:", uw_Basis_jsifyString(ctx, ""), "}", NULL));
({
uw_Basis_source __uwr_r_8 = uw_Basis_new_client_source(ctx, "{c:\"c\",v:null}");
({
struct __uws_6 __uwr_r_9 = ({ struct __uws_6 tmp = {__uwr_r_8, uw_Basis_new_client_source(ctx, uw_Basis_mstrcat(ctx, "{c:\"c\",v:", uw_Basis_htmlifySource(ctx, __uwr_r_8), "}", NULL))}; tmp; });
uw_Basis_mstrcat(ctx, "<body", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n<h1", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyString(ctx, __uwr_r_4.__uwf_T.__uwf_Title), "</h1>\n<button", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " value=\"Send:\" onclick=\'uw_event=event;exec(", "{c:\"a\",f:{c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1769},x:{c:\"c\",v:", uw_Basis_htmlifyInt(ctx, __uwr_x1_0), "}},x:{c:\"c\",v:", uw_Basis_htmlifySource(ctx, __uwr_r_7), "}},x:{c:\"c\",v:null}})\'></button> <script type=\"text/javascript\">inp(exec({c:\"c\",v:", uw_Basis_htmlifySource(ctx, __uwr_r_7), "}))</script>\n<h2", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">Messages</h2>\n<script type=\"text/javascript\">dyn(\"span\", execD(", "{c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1770},x:{c:\"c\",v:{_Head:", uw_Basis_htmlifySource(ctx, __uwr_r_9.__uwf_Head), ",_Tail:", uw_Basis_htmlifySource(ctx, __uwr_r_9.__uwf_Tail), "}}},x:{c:\"c\",v:null}}))</script>\n</body>", NULL);
});
});
});
});
});
});
})), 0));
}

#line 52 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn_lam_1823_1823(uw_context ctx, struct __uws_9 __uwr_x0_0, uw_unit __uwr___1) {
return((uw_write(ctx, ({
uw_Basis_int __uwr_r_2 = ({
uw_Basis_int n;
uw_ensure_transaction(ctx);
PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexecPrepared(conn, "uw0", 0, NULL, NULL, NULL, 0);
if (res == NULL) {
uw_try_reconnecting_and_restarting(ctx);
uw_error(ctx, FATAL, "Ur/Web / SQL: could not run NEXTVAL (out of memory or database unreachable).");
}
if (PQresultStatus(res) != PGRES_TUPLES_OK) {
PQclear(res);
uw_error(ctx, FATAL, "Ur/Web / SQL: NEXTVAL failed.\nSQL: %s\nServer: %s", "SELECT NEXTVAL('uw_Chat_s')", PQerrorMessage(conn));
}
n = PQntuples(res);
if (n != 1) {
PQclear(res);
uw_error(ctx, FATAL, "Ur/Web / SQL: NEXTVAL returned the wrong row count (expected 1, got %d).\nSQL: %s\nServer: %s", n, "SELECT NEXTVAL('uw_Chat_s')", PQerrorMessage(conn));
}
n = uw_Basis_stringToInt_error(ctx, PQgetvalue(res, 0, 0));
PQclear(res);
n;
});
({
uw_Basis_int __uwr_r_3 = ({
uw_Basis_int n;
uw_ensure_transaction(ctx);
PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexecPrepared(conn, "uw1", 0, NULL, NULL, NULL, 0);
if (res == NULL) {
uw_try_reconnecting_and_restarting(ctx);
uw_error(ctx, FATAL, "Ur/Web / SQL: could not run NEXTVAL (out of memory or database unreachable).");
}
if (PQresultStatus(res) != PGRES_TUPLES_OK) {
PQclear(res);
uw_error(ctx, FATAL, "Ur/Web / SQL: NEXTVAL failed.\nSQL: %s\nServer: %s", "SELECT NEXTVAL('uw_Chat_Room_s')", PQerrorMessage(conn));
}
n = PQntuples(res);
if (n != 1) {
PQclear(res);
uw_error(ctx, FATAL, "Ur/Web / SQL: NEXTVAL returned the wrong row count (expected 1, got %d).\nSQL: %s\nServer: %s", n, "SELECT NEXTVAL('uw_Chat_Room_s')", PQerrorMessage(conn));
}
n = uw_Basis_stringToInt_error(ctx, PQgetvalue(res, 0, 0));
PQclear(res);
n;
});
({
uw_unit __uwr_r_4 = ({
uw_Basis_string disc = uw_Basis_mstrcat(ctx, "INSERT INTO uw_Chat_t (uw_Id, uw_Room, uw_Title) VALUES (", uw_Basis_sqlifyInt(ctx, __uwr_r_2), ", ", uw_Basis_sqlifyInt(ctx, __uwr_r_3), ", ", uw_Basis_sqlifyString(ctx, __uwr_x0_0.__uwf_Title), ")", NULL);

(!strcmp(disc, "")) ? 0 : 1 ? ({
uw_Basis_string __uwr_cmd_4 = disc;
(uw_begin_region(ctx), ({
char *dml = __uwr_cmd_4;
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
uw_unit arg0 = 0;
uw_unit arg1 = 0;
__uwn_main_1768(ctx, arg0, arg1);
});
});
});
})), 0));
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
