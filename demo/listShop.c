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
}

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/tmp/urweb-listshop.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

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
uw_Basis_int __uwf_1;
struct __uws_1* __uwf_2;
};

struct __uws_2 {
uw_Basis_string __uwf_X;
};

struct __uws_3 {
uw_Basis_string __uwf_1;
struct __uws_3* __uwf_2;
};

enum __uwe_list_s_1789 { __uwc_Nil_1790, __uwc_Cons_1791 };

struct __uwd_list_s_1789 {
enum __uwe_list_s_1789 tag;
union {
struct __uws_1 uw_Cons;
} data;
};

enum __uwe_list_s_1792 { __uwc_Nil_1793, __uwc_Cons_1794 };

struct __uwd_list_s_1792 {
enum __uwe_list_s_1792 tag;
union {
struct __uws_3 uw_Cons;
} data;
};

/* Function prototypes */
static uw_Basis_string __uwn_lam_1801_1801(uw_context, struct __uws_1*);
static uw_unit __uwn_lam_1802_1802(uw_context, struct __uws_1*);
static uw_Basis_string __uwn_toXml_1759(uw_context, struct __uws_1*);
static uw_unit __uwn_toXml_1799(uw_context, struct __uws_1*);
static struct __uws_1* __uwn_lam_1803_1803(uw_context, struct __uws_1*, struct __uws_1*);
static struct __uws_1* __uwn__revPRIME_unpoly_1785(uw_context, struct __uws_1*, struct __uws_1*);
static uw_Basis_int __uwn_lam_1804_1804(uw_context, struct __uws_1*, uw_Basis_int);
static uw_Basis_int __uwn__lengthPRIME_unpoly_1786(uw_context, struct __uws_1*, uw_Basis_int);
static uw_unit __uwn_lam_1805_1805(uw_context, struct __uws_1*, struct __uws_2, uw_unit);
static uw_unit __uwn_wrap__cons_1781(uw_context, struct __uws_1*, struct __uws_2, uw_unit);
static uw_Basis_string __uwn_lam_1806_1806(uw_context, struct __uws_3*);
static uw_unit __uwn_lam_1807_1807(uw_context, struct __uws_3*);
static uw_Basis_string __uwn_toXml_1772(uw_context, struct __uws_3*);
static uw_unit __uwn_toXml_1800(uw_context, struct __uws_3*);
static struct __uws_3* __uwn_lam_1808_1808(uw_context, struct __uws_3*, struct __uws_3*);
static struct __uws_3* __uwn__revPRIME_unpoly_1787(uw_context, struct __uws_3*, struct __uws_3*);
static uw_Basis_int __uwn_lam_1809_1809(uw_context, struct __uws_3*, uw_Basis_int);
static uw_Basis_int __uwn__lengthPRIME_unpoly_1788(uw_context, struct __uws_3*, uw_Basis_int);
static uw_unit __uwn_lam_1810_1810(uw_context, struct __uws_3*, struct __uws_2, uw_unit);
static uw_unit __uwn_wrap__cons_1782(uw_context, struct __uws_3*, struct __uws_2, uw_unit);
static uw_unit __uwn_lam_1811_1811(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_wrap_main_1783(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_lam_1812_1812(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_wrap_main_1784(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_wrap_main_1780(uw_context, uw_unit, uw_unit);

/* URL handler prototypes */
static struct __uws_1 *unurlify_list_1(uw_context, char **);
static struct __uws_3 *unurlify_list_3(uw_context, char **);

static char jslib[] = "";

#line 9 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_Basis_string __uwn_lam_1801_1801(uw_context ctx, struct __uws_1* __uwr_ls_0) {
return(({
struct __uws_1* disc = __uwr_ls_0;

(disc == NULL) ? "[]" : (disc != NULL) && 1 && 1 ? ({
uw_Basis_int __uwr_x_1 = (*disc).__uwf_1;
struct __uws_1* __uwr_lsPRIME_2 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, uw_Basis_htmlifyInt(ctx, __uwr_x_1), " :: ", __uwn_toXml_1759(ctx, __uwr_lsPRIME_2), NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}

#line 8 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_unit __uwn_lam_1802_1802(uw_context ctx, struct __uws_1* __uwr_ls_0) {
return((uw_write(ctx, ({
struct __uws_1* disc = __uwr_ls_0;

(disc == NULL) ? "[]" : (disc != NULL) && 1 && 1 ? ({
uw_Basis_int __uwr_x_1 = (*disc).__uwf_1;
struct __uws_1* __uwr_lsPRIME_2 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, uw_Basis_htmlifyInt(ctx, __uwr_x_1), " :: ", __uwn_toXml_1759(ctx, __uwr_lsPRIME_2), NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0));
}

#line 8 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_Basis_string __uwn_toXml_1759(uw_context, struct __uws_1*);
static uw_unit __uwn_toXml_1799(uw_context, struct __uws_1*);

static uw_Basis_string __uwn_toXml_1759(uw_context ctx, struct __uws_1* __uwr_x_0) {
restart:
return(__uwn_lam_1801_1801(ctx, __uwr_x_0));
}
static uw_unit __uwn_toXml_1799(uw_context ctx, struct __uws_1* __uwr_x_0) {
restart:
return(__uwn_lam_1802_1802(ctx, __uwr_x_0));
}


#line 16 "/Users/jacksmith/prog/urweb/demo/list.ur"
static struct __uws_1* __uwn_lam_1803_1803(uw_context ctx, struct __uws_1* __uwr_ls_0, struct __uws_1* __uwr_acc_1) {
return(({
struct __uws_1* disc = __uwr_ls_0;

(disc == NULL) ? __uwr_acc_1 : (disc != NULL) && 1 && 1 ? ({
uw_Basis_int __uwr_x_2 = (*disc).__uwf_1;
struct __uws_1* __uwr_lsPRIME_3 = (*disc).__uwf_2;
({
struct __uws_1* arg0 = __uwr_lsPRIME_3;
struct __uws_1* arg1 = ({
struct __uws_1 *tmp = uw_malloc(ctx, sizeof(struct __uws_1));
*tmp = ({ struct __uws_1 tmp = {__uwr_x_2, __uwr_acc_1}; tmp; });
tmp;
});
__uwn__revPRIME_unpoly_1785(ctx, arg0, arg1);
});
}) : ({
struct __uws_1* tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}

static struct __uws_1* __uwn__revPRIME_unpoly_1785(uw_context, struct __uws_1*, struct __uws_1*);

static struct __uws_1* __uwn__revPRIME_unpoly_1785(uw_context ctx, struct __uws_1* __uwr_x_0, struct __uws_1* __uwr_x_1) {
restart:
return(({
struct __uws_1* arg0 = __uwr_x_0;
struct __uws_1* arg1 = __uwr_x_1;
__uwn_lam_1803_1803(ctx, arg0, arg1);
}));
}


#line 6 "/Users/jacksmith/prog/urweb/demo/list.ur"
static uw_Basis_int __uwn_lam_1804_1804(uw_context ctx, struct __uws_1* __uwr_ls_0, uw_Basis_int __uwr_acc_1) {
return(({
struct __uws_1* disc = __uwr_ls_0;

(disc == NULL) ? __uwr_acc_1 : (disc != NULL) && 1 && 1 ? ({
uw_Basis_int __uwr___2 = (*disc).__uwf_1;
struct __uws_1* __uwr_lsPRIME_3 = (*disc).__uwf_2;
({
struct __uws_1* arg0 = __uwr_lsPRIME_3;
uw_Basis_int arg1 = (__uwr_acc_1 + 1LL);
__uwn__lengthPRIME_unpoly_1786(ctx, arg0, arg1);
});
}) : ({
uw_Basis_int tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}

static uw_Basis_int __uwn__lengthPRIME_unpoly_1786(uw_context, struct __uws_1*, uw_Basis_int);

static uw_Basis_int __uwn__lengthPRIME_unpoly_1786(uw_context ctx, struct __uws_1* __uwr_x_0, uw_Basis_int __uwr_x_1) {
restart:
return(({
struct __uws_1* arg0 = __uwr_x_0;
uw_Basis_int arg1 = __uwr_x_1;
__uwn_lam_1804_1804(ctx, arg0, arg1);
}));
}


#line 13 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_unit __uwn_lam_1805_1805(uw_context ctx, struct __uws_1* __uwr_x1_0, struct __uws_2 __uwr_x0_1, uw_unit __uwr___2) {
return((uw_write(ctx, ({
uw_Basis_int* disc = uw_Basis_stringToInt(ctx, __uwr_x0_1.__uwf_X);

(disc == NULL) ? uw_Basis_mstrcat(ctx, "<body", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">Invalid string!</body>", NULL) : (disc != NULL) && 1 ? ({
uw_Basis_int __uwr_v_3 = (*disc);
uw_Basis_mstrcat(ctx, "<body", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\nCurrent list: ", __uwn_toXml_1759(ctx, ({
struct __uws_1 *tmp = uw_malloc(ctx, sizeof(struct __uws_1));
*tmp = ({ struct __uws_1 tmp = {__uwr_v_3, __uwr_x1_0}; tmp; });
tmp;
})), "<br", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></br>\nReversed list: ", __uwn_toXml_1759(ctx, ({
struct __uws_1* arg0 = ({
struct __uws_1 *tmp = uw_malloc(ctx, sizeof(struct __uws_1));
*tmp = ({ struct __uws_1 tmp = {__uwr_v_3, __uwr_x1_0}; tmp; });
tmp;
});
struct __uws_1* arg1 = NULL;
__uwn__revPRIME_unpoly_1785(ctx, arg0, arg1);
})), "<br", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></br>\nLength: ", uw_Basis_htmlifyInt(ctx, ({
struct __uws_1* arg0 = ({
struct __uws_1 *tmp = uw_malloc(ctx, sizeof(struct __uws_1));
*tmp = ({ struct __uws_1 tmp = {__uwr_v_3, __uwr_x1_0}; tmp; });
tmp;
});
uw_Basis_int arg1 = 0LL;
__uwn__lengthPRIME_unpoly_1786(ctx, arg0, arg1);
})), "<br", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></br>\n<br", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></br>\n<form method=\"post\">\nAdd element: <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div> <input type=\"submit\"", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " />\n</form>\n</body>", NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0));
}

#line 13 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_unit __uwn_wrap__cons_1781(uw_context ctx, struct __uws_1* __uwr_x_0, struct __uws_2 __uwr_x_1, uw_unit __uwr_x_2) {
return(({
struct __uws_1* arg0 = __uwr_x_0;
struct __uws_2 arg1 = __uwr_x_1;
uw_unit arg2 = __uwr_x_2;
__uwn_lam_1805_1805(ctx, arg0, arg1, arg2);
}));
}

#line 9 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_Basis_string __uwn_lam_1806_1806(uw_context ctx, struct __uws_3* __uwr_ls_0) {
return(({
struct __uws_3* disc = __uwr_ls_0;

(disc == NULL) ? "[]" : (disc != NULL) && 1 && 1 ? ({
uw_Basis_string __uwr_x_1 = (*disc).__uwf_1;
struct __uws_3* __uwr_lsPRIME_2 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, uw_Basis_htmlifyString(ctx, __uwr_x_1), " :: ", __uwn_toXml_1772(ctx, __uwr_lsPRIME_2), NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}

#line 8 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_unit __uwn_lam_1807_1807(uw_context ctx, struct __uws_3* __uwr_ls_0) {
return((uw_write(ctx, ({
struct __uws_3* disc = __uwr_ls_0;

(disc == NULL) ? "[]" : (disc != NULL) && 1 && 1 ? ({
uw_Basis_string __uwr_x_1 = (*disc).__uwf_1;
struct __uws_3* __uwr_lsPRIME_2 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, uw_Basis_htmlifyString(ctx, __uwr_x_1), " :: ", __uwn_toXml_1772(ctx, __uwr_lsPRIME_2), NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0));
}

#line 8 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_Basis_string __uwn_toXml_1772(uw_context, struct __uws_3*);
static uw_unit __uwn_toXml_1800(uw_context, struct __uws_3*);

static uw_Basis_string __uwn_toXml_1772(uw_context ctx, struct __uws_3* __uwr_x_0) {
restart:
return(__uwn_lam_1806_1806(ctx, __uwr_x_0));
}
static uw_unit __uwn_toXml_1800(uw_context ctx, struct __uws_3* __uwr_x_0) {
restart:
return(__uwn_lam_1807_1807(ctx, __uwr_x_0));
}


#line 16 "/Users/jacksmith/prog/urweb/demo/list.ur"
static struct __uws_3* __uwn_lam_1808_1808(uw_context ctx, struct __uws_3* __uwr_ls_0, struct __uws_3* __uwr_acc_1) {
return(({
struct __uws_3* disc = __uwr_ls_0;

(disc == NULL) ? __uwr_acc_1 : (disc != NULL) && 1 && 1 ? ({
uw_Basis_string __uwr_x_2 = (*disc).__uwf_1;
struct __uws_3* __uwr_lsPRIME_3 = (*disc).__uwf_2;
({
struct __uws_3* arg0 = __uwr_lsPRIME_3;
struct __uws_3* arg1 = ({
struct __uws_3 *tmp = uw_malloc(ctx, sizeof(struct __uws_3));
*tmp = ({ struct __uws_3 tmp = {__uwr_x_2, __uwr_acc_1}; tmp; });
tmp;
});
__uwn__revPRIME_unpoly_1787(ctx, arg0, arg1);
});
}) : ({
struct __uws_3* tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}

static struct __uws_3* __uwn__revPRIME_unpoly_1787(uw_context, struct __uws_3*, struct __uws_3*);

static struct __uws_3* __uwn__revPRIME_unpoly_1787(uw_context ctx, struct __uws_3* __uwr_x_0, struct __uws_3* __uwr_x_1) {
restart:
return(({
struct __uws_3* arg0 = __uwr_x_0;
struct __uws_3* arg1 = __uwr_x_1;
__uwn_lam_1808_1808(ctx, arg0, arg1);
}));
}


#line 6 "/Users/jacksmith/prog/urweb/demo/list.ur"
static uw_Basis_int __uwn_lam_1809_1809(uw_context ctx, struct __uws_3* __uwr_ls_0, uw_Basis_int __uwr_acc_1) {
return(({
struct __uws_3* disc = __uwr_ls_0;

(disc == NULL) ? __uwr_acc_1 : (disc != NULL) && 1 && 1 ? ({
uw_Basis_string __uwr___2 = (*disc).__uwf_1;
struct __uws_3* __uwr_lsPRIME_3 = (*disc).__uwf_2;
({
struct __uws_3* arg0 = __uwr_lsPRIME_3;
uw_Basis_int arg1 = (__uwr_acc_1 + 1LL);
__uwn__lengthPRIME_unpoly_1788(ctx, arg0, arg1);
});
}) : ({
uw_Basis_int tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}

static uw_Basis_int __uwn__lengthPRIME_unpoly_1788(uw_context, struct __uws_3*, uw_Basis_int);

static uw_Basis_int __uwn__lengthPRIME_unpoly_1788(uw_context ctx, struct __uws_3* __uwr_x_0, uw_Basis_int __uwr_x_1) {
restart:
return(({
struct __uws_3* arg0 = __uwr_x_0;
uw_Basis_int arg1 = __uwr_x_1;
__uwn_lam_1809_1809(ctx, arg0, arg1);
}));
}


#line 13 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_unit __uwn_lam_1810_1810(uw_context ctx, struct __uws_3* __uwr_x1_0, struct __uws_2 __uwr_x0_1, uw_unit __uwr___2) {
return(((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\nCurrent list: "), 0), ((uw_Basis_htmlifyString_w(ctx, __uwr_x1_0), ((uw_write(ctx, " :: "), 0), __uwn_toXml_1800(ctx, __uwr_x0_1.__uwf_X))), ((uw_write(ctx, "<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\nReversed list: "), 0), (({
struct __uws_3* __uwr_ls_3 = ({
struct __uws_3* arg0 = ({
struct __uws_3 *tmp = uw_malloc(ctx, sizeof(struct __uws_3));
*tmp = ({ struct __uws_3 tmp = {__uwr_x0_1.__uwf_X, __uwr_x1_0}; tmp; });
tmp;
});
struct __uws_3* arg1 = NULL;
__uwn__revPRIME_unpoly_1787(ctx, arg0, arg1);
});
(uw_write(ctx, ({
struct __uws_3* disc = __uwr_ls_3;

(disc == NULL) ? "[]" : (disc != NULL) && 1 && 1 ? ({
uw_Basis_string __uwr_x_4 = (*disc).__uwf_1;
struct __uws_3* __uwr_lsPRIME_5 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, uw_Basis_htmlifyString(ctx, __uwr_x_4), " :: ", __uwn_toXml_1772(ctx, __uwr_lsPRIME_5), NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0);
}), ((uw_write(ctx, "<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\nLength: "), 0), (uw_Basis_htmlifyInt_w(ctx, ({
struct __uws_3* arg0 = ({
struct __uws_3 *tmp = uw_malloc(ctx, sizeof(struct __uws_3));
*tmp = ({ struct __uws_3 tmp = {__uwr_x0_1.__uwf_X, __uwr_x1_0}; tmp; });
tmp;
});
uw_Basis_int arg1 = 0LL;
__uwn__lengthPRIME_unpoly_1788(ctx, arg0, arg1);
})), ((uw_write(ctx, "<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<form method=\"post\">\nAdd element: <div"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></div> <input type=\"submit\""), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, " />\n</form>\n</body>"), 0)))))))))))))))))))))))))))));
}

#line 13 "/Users/jacksmith/prog/urweb/demo/listFun.ur"
static uw_unit __uwn_wrap__cons_1782(uw_context ctx, struct __uws_3* __uwr_x_0, struct __uws_2 __uwr_x_1, uw_unit __uwr_x_2) {
return(({
struct __uws_3* arg0 = __uwr_x_0;
struct __uws_2 arg1 = __uwr_x_1;
uw_unit arg2 = __uwr_x_2;
__uwn_lam_1810_1810(ctx, arg0, arg1, arg2);
}));
}

#line 16 "/Users/jacksmith/prog/urweb/demo/listShop.ur"
static uw_unit __uwn_lam_1811_1811(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\nCurrent list: []<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\nReversed list: "), 0), (({
struct __uws_1* __uwr_ls_2 = ({
struct __uws_1* arg0 = NULL;
struct __uws_1* arg1 = NULL;
__uwn__revPRIME_unpoly_1785(ctx, arg0, arg1);
});
(uw_write(ctx, ({
struct __uws_1* disc = __uwr_ls_2;

(disc == NULL) ? "[]" : (disc != NULL) && 1 && 1 ? ({
uw_Basis_int __uwr_x_3 = (*disc).__uwf_1;
struct __uws_1* __uwr_lsPRIME_4 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, uw_Basis_htmlifyInt(ctx, __uwr_x_3), " :: ", __uwn_toXml_1759(ctx, __uwr_lsPRIME_4), NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0);
}), ((uw_write(ctx, "<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\nLength: "), 0), (uw_Basis_htmlifyInt_w(ctx, ({
struct __uws_1* arg0 = NULL;
uw_Basis_int arg1 = 0LL;
__uwn__lengthPRIME_unpoly_1786(ctx, arg0, arg1);
})), ((uw_write(ctx, "<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<form method=\"post\""), 0), (0, (0, ((uw_write(ctx, ">\nAdd element: <div"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></div> <input type=\"submit\""), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, " />\n</form>\n</body>"), 0))))))))))))))))))))))))))))));
}

#line 16 "/Users/jacksmith/prog/urweb/demo/listShop.ur"
static uw_unit __uwn_wrap_main_1783(uw_context ctx, uw_unit __uwr_x_0, uw_unit __uwr_x_1) {
return(({
uw_unit arg0 = __uwr_x_0;
uw_unit arg1 = __uwr_x_1;
__uwn_lam_1811_1811(ctx, arg0, arg1);
}));
}

#line 16 "/Users/jacksmith/prog/urweb/demo/listShop.ur"
static uw_unit __uwn_lam_1812_1812(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\nCurrent list: []<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\nReversed list: "), 0), (({
struct __uws_3* __uwr_ls_2 = ({
struct __uws_3* arg0 = NULL;
struct __uws_3* arg1 = NULL;
__uwn__revPRIME_unpoly_1787(ctx, arg0, arg1);
});
(uw_write(ctx, ({
struct __uws_3* disc = __uwr_ls_2;

(disc == NULL) ? "[]" : (disc != NULL) && 1 && 1 ? ({
uw_Basis_string __uwr_x_3 = (*disc).__uwf_1;
struct __uws_3* __uwr_lsPRIME_4 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, uw_Basis_htmlifyString(ctx, __uwr_x_3), " :: ", __uwn_toXml_1772(ctx, __uwr_lsPRIME_4), NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0);
}), ((uw_write(ctx, "<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\nLength: "), 0), (uw_Basis_htmlifyInt_w(ctx, ({
struct __uws_3* arg0 = NULL;
uw_Basis_int arg1 = 0LL;
__uwn__lengthPRIME_unpoly_1788(ctx, arg0, arg1);
})), ((uw_write(ctx, "<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<form method=\"post\""), 0), (0, (0, ((uw_write(ctx, ">\nAdd element: <div"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></div> <input type=\"submit\""), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, " />\n</form>\n</body>"), 0))))))))))))))))))))))))))))));
}

#line 16 "/Users/jacksmith/prog/urweb/demo/listShop.ur"
static uw_unit __uwn_wrap_main_1784(uw_context ctx, uw_unit __uwr_x_0, uw_unit __uwr_x_1) {
return(({
uw_unit arg0 = __uwr_x_0;
uw_unit arg1 = __uwr_x_1;
__uwn_lam_1812_1812(ctx, arg0, arg1);
}));
}

static uw_unit __uwn_wrap_main_1780(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\nPick your poison:<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<li"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> <a"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, " href=\"/ListShop/IL/main\">Integers</a></li>\n<li"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> <a"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, " href=\"/ListShop/SL/main\">Strings</a></li>\n</body>"), 0))))))))))))))))))));
}

/* URL handler helpers */
static struct __uws_1 *unurlify_list_1(uw_context ctx, char **request) {
return ((*request)[0] == '/' ? ++*request : *request,
((!strncmp(*request, "Nil", 3) && ((*request)[3] == 0 || (*request)[3] == '/')) ? (*request += 3, ((*request)[0] == '/' ? ((*request)[0] = 0, ++*request) : NULL), NULL) : ((!strncmp(*request, "Cons", 4) && ((*request)[4] == 0 || (*request)[4] == '/')) ? (*request += 4, ((*request)[0] == '/' ? ++*request : NULL),
({
struct __uws_1 *tmp = uw_malloc(ctx, sizeof(struct __uws_1));
*tmp = ({
uw_Basis_int uwr_1 = uw_Basis_unurlifyInt(ctx, request);
struct __uws_1* uwr_2 = unurlify_list_1(ctx, request);
struct __uws_1 tmp = { uwr_1, uwr_2 };
tmp;
});
tmp;
})) : (uw_error(ctx, FATAL, "Ur/Web: could not decode a list from the URL at this point in the path: %s", *request), NULL))));
}
static struct __uws_3 *unurlify_list_3(uw_context ctx, char **request) {
return ((*request)[0] == '/' ? ++*request : *request,
((!strncmp(*request, "Nil", 3) && ((*request)[3] == 0 || (*request)[3] == '/')) ? (*request += 3, ((*request)[0] == '/' ? ((*request)[0] = 0, ++*request) : NULL), NULL) : ((!strncmp(*request, "Cons", 4) && ((*request)[4] == 0 || (*request)[4] == '/')) ? (*request += 4, ((*request)[0] == '/' ? ++*request : NULL),
({
struct __uws_3 *tmp = uw_malloc(ctx, sizeof(struct __uws_3));
*tmp = ({
uw_Basis_string uwr_1 = uw_Basis_unurlifyString(ctx, request);
struct __uws_3* uwr_2 = unurlify_list_3(ctx, request);
struct __uws_3 tmp = { uwr_1, uwr_2 };
tmp;
});
tmp;
})) : (uw_error(ctx, FATAL, "Ur/Web: could not decode a list from the URL at this point in the path: %s", *request), NULL))));
}

static void uw_setup_limits(void) {
}

void uw_global_custom(void) {
uw_setup_limits();
}

static void uw_initializer(uw_context ctx) {
uw_begin_initializing(ctx);
uw_end_initializing(ctx);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
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
if (!strncmp(request, "/ListShop/IL/cons", 17) && (request[17] == 0 || request[17] == '/')) {
request += 17;
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
struct __uws_1* arg0 = unurlify_list_1(ctx, &request);
struct __uws_2 arg1 = ({
uw_Basis_string uwr_X = uw_Basis_unurlifyString(ctx, &request);
struct __uws_2 tmp = { uwr_X };
tmp;
});
__uwn_wrap__cons_1781(ctx, arg0, arg1, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/ListShop/SL/cons", 17) && (request[17] == 0 || request[17] == '/')) {
request += 17;
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
struct __uws_3* arg0 = unurlify_list_3(ctx, &request);
struct __uws_2 arg1 = ({
uw_Basis_string uwr_X = uw_Basis_unurlifyString(ctx, &request);
struct __uws_2 tmp = { uwr_X };
tmp;
});
__uwn_wrap__cons_1782(ctx, arg0, arg1, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/ListShop/IL/main", 17) && (request[17] == 0 || request[17] == '/')) {
request += 17;
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
__uwn_wrap_main_1783(ctx, arg0, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/ListShop/SL/main", 17) && (request[17] == 0 || request[17] == '/')) {
request += 17;
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
__uwn_wrap_main_1784(ctx, arg0, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/ListShop/main", 14) && (request[14] == 0 || request[14] == '/')) {
request += 14;
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
__uwn_wrap_main_1780(ctx, arg0, 0);
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
