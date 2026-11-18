#define _POSIX_C_SOURCE 200809L

#include <lean/lean.h>
#include "sqlite3.h"

#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  pthread_mutex_t mu;
  sqlite3 *db;
  uint32_t in_use;
  uint8_t closed;
} leanswe_raw_db;

typedef struct {
  pthread_mutex_t mu;
  sqlite3_stmt *stmt;
  sqlite3 *db;
  lean_object *db_obj;
  uint32_t in_use;
  uint8_t closed;
} leanswe_raw_stmt;

static pthread_once_t g_ext_once = PTHREAD_ONCE_INIT;
static lean_external_class *g_db_ext_class = NULL;
static lean_external_class *g_stmt_ext_class = NULL;

static void noop_foreach(void *ptr, b_lean_obj_arg fn) {
  (void)ptr;
  (void)fn;
}

static void finalize_db_ext(void *ptr) {
  leanswe_raw_db *h = (leanswe_raw_db *)ptr;
  if (h == NULL) {
    return;
  }
  if (!h->closed && h->db != NULL) {
    sqlite3_close_v2(h->db);
  }
  pthread_mutex_destroy(&h->mu);
  free(h);
}

static void finalize_stmt_ext(void *ptr) {
  leanswe_raw_stmt *h = (leanswe_raw_stmt *)ptr;
  if (h == NULL) {
    return;
  }
  if (!h->closed && h->stmt != NULL) {
    sqlite3_finalize(h->stmt);
  }
  if (h->db_obj != NULL) {
    lean_dec(h->db_obj);
  }
  pthread_mutex_destroy(&h->mu);
  free(h);
}

static void init_ext_classes(void) {
  g_db_ext_class = lean_register_external_class(finalize_db_ext, noop_foreach);
  g_stmt_ext_class = lean_register_external_class(finalize_stmt_ext, noop_foreach);
}

static const char *safe_str(const char *s) {
  return s != NULL ? s : "";
}

static uint32_t db_error_code(sqlite3 *db, int rc) {
  if (db != NULL && (sqlite3_errcode(db) & 0xff) == (rc & 0xff)) {
    int ext = sqlite3_extended_errcode(db);
    if (ext != SQLITE_OK) {
      return (uint32_t)ext;
    }
  }
  return (uint32_t)rc;
}

static const char *db_error_msg(sqlite3 *db, int rc) {
  if (db != NULL && (sqlite3_errcode(db) & 0xff) == (rc & 0xff)) {
    const char *m = sqlite3_errmsg(db);
    if (m != NULL && m[0] != '\0') {
      return m;
    }
  }
  const char *s = sqlite3_errstr(rc);
  return s != NULL ? s : "sqlite error";
}

static lean_obj_res mk_pair(lean_obj_res a, lean_obj_res b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

static lean_obj_res mk_some(lean_obj_res val) {
  lean_obj_res opt = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(opt, 0, val);
  return opt;
}

static lean_obj_res mk_code_msg(uint32_t code, const char *msg) {
  return mk_pair(lean_box_uint32(code), lean_mk_string(safe_str(msg)));
}

static lean_obj_res mk_code_msg_val(uint32_t code, const char *msg, lean_obj_res val) {
  lean_obj_res inner = mk_pair(lean_mk_string(safe_str(msg)), val);
  return mk_pair(lean_box_uint32(code), inner);
}

static lean_obj_res mk_u8_code_msg(uint8_t flag, uint32_t code, const char *msg) {
  return mk_pair(lean_box(flag), mk_code_msg(code, msg));
}

static lean_obj_res mk_byte_array(const void *ptr, int nbytes) {
  if (ptr == NULL || nbytes <= 0) {
    return lean_alloc_sarray(1, 0, 0);
  }
  lean_obj_res ba = lean_alloc_sarray(1, (size_t)nbytes, (size_t)nbytes);
  memcpy(lean_sarray_cptr(ba), ptr, (size_t)nbytes);
  return ba;
}

static lean_obj_res rc_unit_result(sqlite3 *db, int rc) {
  if (rc == SQLITE_OK) {
    return mk_code_msg(0, "");
  }
  return mk_code_msg(db_error_code(db, rc), db_error_msg(db, rc));
}

static int acquire_db(b_lean_obj_arg obj, leanswe_raw_db **out_h, sqlite3 **out_db) {
  leanswe_raw_db *h = (leanswe_raw_db *)lean_get_external_data(obj);
  pthread_mutex_lock(&h->mu);
  if (h->closed || h->db == NULL) {
    pthread_mutex_unlock(&h->mu);
    return 0;
  }
  h->in_use++;
  *out_h = h;
  *out_db = h->db;
  pthread_mutex_unlock(&h->mu);
  return 1;
}

static void release_db(leanswe_raw_db *h) {
  pthread_mutex_lock(&h->mu);
  if (h->in_use > 0) {
    h->in_use--;
  }
  pthread_mutex_unlock(&h->mu);
}

static int clamp_nonneg_int(uint32_t v) {
  return v <= 0x7fffffffU ? (int)v : -1;
}

static int acquire_stmt(
    b_lean_obj_arg obj, leanswe_raw_stmt **out_h, sqlite3_stmt **out_stmt, sqlite3 **out_db) {
  leanswe_raw_stmt *h = (leanswe_raw_stmt *)lean_get_external_data(obj);
  pthread_mutex_lock(&h->mu);
  if (h->closed || h->stmt == NULL || h->db_obj == NULL) {
    pthread_mutex_unlock(&h->mu);
    return 0;
  }
  leanswe_raw_db *db_h = NULL;
  sqlite3 *pinned_db = NULL;
  if (!acquire_db(h->db_obj, &db_h, &pinned_db)) {
    pthread_mutex_unlock(&h->mu);
    return 0;
  }
  h->in_use++;
  *out_h = h;
  *out_stmt = h->stmt;
  *out_db = pinned_db;
  pthread_mutex_unlock(&h->mu);
  return 1;
}

static void release_stmt(leanswe_raw_stmt *h) {
  pthread_mutex_lock(&h->mu);
  if (h->in_use > 0) {
    h->in_use--;
  }
  lean_object *db_obj = h->db_obj;
  pthread_mutex_unlock(&h->mu);
  if (db_obj != NULL) {
    release_db((leanswe_raw_db *)lean_get_external_data(db_obj));
  }
}

static lean_obj_res alloc_db_ext(sqlite3 *db) {
  leanswe_raw_db *h = (leanswe_raw_db *)calloc(1, sizeof(leanswe_raw_db));
  if (h == NULL) {
    sqlite3_close(db);
    return mk_code_msg_val(SQLITE_NOMEM, "out of memory allocating RawDbExt", lean_box(0));
  }
  pthread_mutex_init(&h->mu, NULL);
  h->db = db;
  lean_obj_res ext = lean_alloc_external(g_db_ext_class, h);
  return mk_code_msg_val(0, "", mk_some(ext));
}

static lean_obj_res alloc_stmt_ext(
    b_lean_obj_arg db_obj, sqlite3 *db, sqlite3_stmt *stmt, size_t consumed) {
  if (stmt == NULL) {
    return mk_code_msg_val(0, "", mk_pair(lean_box(0), lean_usize_to_nat(consumed)));
  }
  leanswe_raw_stmt *h = (leanswe_raw_stmt *)calloc(1, sizeof(leanswe_raw_stmt));
  if (h == NULL) {
    sqlite3_finalize(stmt);
    return mk_code_msg_val(
        SQLITE_NOMEM, "out of memory allocating RawStmtExt", mk_pair(lean_box(0), lean_usize_to_nat(0)));
  }
  pthread_mutex_init(&h->mu, NULL);
  lean_inc(db_obj);
  h->stmt = stmt;
  h->db = db;
  h->db_obj = db_obj;
  lean_obj_res ext = lean_alloc_external(g_stmt_ext_class, h);
  return mk_code_msg_val(0, "", mk_pair(mk_some(ext), lean_usize_to_nat(consumed)));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_open_v2(b_lean_obj_arg path_obj, uint32_t flags) {
  pthread_once(&g_ext_once, init_ext_classes);
  sqlite3 *db = NULL;
  int rc = sqlite3_open_v2(lean_string_cstr(path_obj), &db, (int)flags, NULL);
  if (rc != SQLITE_OK || db == NULL) {
    uint32_t code = db_error_code(db, rc);
    lean_obj_res res = mk_code_msg_val(code, db_error_msg(db, rc), lean_box(0));
    if (db != NULL) {
      sqlite3_close(db);
    }
    return res;
  }
  return alloc_db_ext(db);
}

static lean_obj_res finish_close_db(leanswe_raw_db *h, sqlite3 *db, int rc) {
  lean_obj_res res = rc_unit_result(db, rc);
  pthread_mutex_lock(&h->mu);
  if (h->in_use > 0) {
    h->in_use--;
  }
  if (rc == SQLITE_OK) {
    h->db = NULL;
  } else {
    h->closed = 0;
  }
  pthread_mutex_unlock(&h->mu);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_close(b_lean_obj_arg db_obj) {
  leanswe_raw_db *h = (leanswe_raw_db *)lean_get_external_data(db_obj);
  pthread_mutex_lock(&h->mu);
  if (h->closed || h->db == NULL) {
    pthread_mutex_unlock(&h->mu);
    return mk_code_msg(SQLITE_MISUSE, "invalid or closed database handle");
  }
  if (h->in_use > 0) {
    pthread_mutex_unlock(&h->mu);
    return mk_code_msg(SQLITE_BUSY, "database handle is currently in use");
  }
  h->closed = 1;
  h->in_use++;
  sqlite3 *db = h->db;
  pthread_mutex_unlock(&h->mu);
  int rc = sqlite3_close(db);
  return finish_close_db(h, db, rc);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_extended_result_codes(
    b_lean_obj_arg db_obj, uint8_t onoff) {
  leanswe_raw_db *h = NULL;
  sqlite3 *db = NULL;
  if (!acquire_db(db_obj, &h, &db)) {
    return mk_code_msg(SQLITE_MISUSE, "invalid or closed database handle");
  }
  int rc = sqlite3_extended_result_codes(db, onoff ? 1 : 0);
  lean_obj_res res = rc_unit_result(db, rc);
  release_db(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_busy_timeout(b_lean_obj_arg db_obj, uint32_t ms) {
  leanswe_raw_db *h = NULL;
  sqlite3 *db = NULL;
  if (!acquire_db(db_obj, &h, &db)) {
    return mk_code_msg(SQLITE_MISUSE, "invalid or closed database handle");
  }
  if (ms > 0x7fffffffU) {
    release_db(h);
    return mk_code_msg(SQLITE_MISUSE, "busy_timeout milliseconds exceed INT_MAX");
  }
  int rc = sqlite3_busy_timeout(db, (int)ms);
  lean_obj_res res = rc_unit_result(db, rc);
  release_db(h);
  return res;
}

static size_t compute_consumed(const char *sql, const char *tail, size_t sql_len) {
  if (tail == NULL || tail < sql) {
    return sql_len;
  }
  size_t off = (size_t)(tail - sql);
  return off <= sql_len ? off : sql_len;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_prepare_v2(
    b_lean_obj_arg db_obj, b_lean_obj_arg sql_obj) {
  leanswe_raw_db *h = NULL;
  sqlite3 *db = NULL;
  if (!acquire_db(db_obj, &h, &db)) {
    return mk_code_msg_val(
        SQLITE_MISUSE, "invalid or closed database handle", mk_pair(lean_box(0), lean_usize_to_nat(0)));
  }
  size_t sql_len = lean_string_size(sql_obj) - 1;
  if (sql_len > 0x7fffffffU) {
    release_db(h);
    return mk_code_msg_val(
        SQLITE_TOOBIG,
        safe_str(sqlite3_errstr(SQLITE_TOOBIG)),
        mk_pair(lean_box(0), lean_usize_to_nat(0)));
  }
  const char *sql = lean_string_cstr(sql_obj);
  sqlite3_stmt *stmt = NULL;
  const char *tail = NULL;
  int rc = sqlite3_prepare_v2(db, sql, (int)sql_len, &stmt, &tail);
  lean_obj_res res = rc == SQLITE_OK
      ? alloc_stmt_ext(db_obj, db, stmt, compute_consumed(sql, tail, sql_len))
      : mk_code_msg_val(db_error_code(db, rc), db_error_msg(db, rc), mk_pair(lean_box(0), lean_usize_to_nat(0)));
  release_db(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_step(b_lean_obj_arg stmt_obj) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg_val(SQLITE_MISUSE, "invalid or finalized statement handle", lean_box(0));
  }
  int rc = sqlite3_step(stmt);
  lean_obj_res res = rc == SQLITE_ROW
      ? mk_code_msg_val(0, "", lean_box(1))
      : (rc == SQLITE_DONE
          ? mk_code_msg_val(0, "", lean_box(0))
          : mk_code_msg_val(db_error_code(db, rc), db_error_msg(db, rc), lean_box(0)));
  release_stmt(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_reset(b_lean_obj_arg stmt_obj) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg(SQLITE_MISUSE, "invalid or finalized statement handle");
  }
  int rc = sqlite3_reset(stmt);
  lean_obj_res res = rc_unit_result(db, rc);
  release_stmt(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_clear_bindings(b_lean_obj_arg stmt_obj) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg(SQLITE_MISUSE, "invalid or finalized statement handle");
  }
  int rc = sqlite3_clear_bindings(stmt);
  lean_obj_res res = rc_unit_result(db, rc);
  release_stmt(h);
  return res;
}

static lean_obj_res finalize_with_db_pin(b_lean_obj_arg db_obj, sqlite3_stmt *stmt) {
  leanswe_raw_db *db_h = NULL;
  sqlite3 *pinned_db = NULL;
  int pinned = (db_obj != NULL) ? acquire_db(db_obj, &db_h, &pinned_db) : 0;
  int rc = sqlite3_finalize(stmt);
  lean_obj_res res = rc == SQLITE_OK
      ? mk_u8_code_msg(1, 0, "")
      : (pinned
          ? mk_u8_code_msg(1, db_error_code(pinned_db, rc), db_error_msg(pinned_db, rc))
          : mk_u8_code_msg(1, (uint32_t)rc, safe_str(sqlite3_errstr(rc))));
  if (pinned) {
    release_db(db_h);
  }
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_finalize(b_lean_obj_arg stmt_obj) {
  leanswe_raw_stmt *h = (leanswe_raw_stmt *)lean_get_external_data(stmt_obj);
  pthread_mutex_lock(&h->mu);
  if (h->closed || h->stmt == NULL) {
    pthread_mutex_unlock(&h->mu);
    return mk_u8_code_msg(0, SQLITE_MISUSE, "invalid or already finalized statement handle");
  }
  if (h->in_use > 0) {
    pthread_mutex_unlock(&h->mu);
    return mk_u8_code_msg(0, SQLITE_BUSY, "statement handle is currently in use");
  }
  h->closed = 1;
  sqlite3_stmt *stmt = h->stmt;
  lean_object *db_obj = h->db_obj;
  h->stmt = NULL;
  pthread_mutex_unlock(&h->mu);
  return finalize_with_db_pin(db_obj, stmt);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_param_count(b_lean_obj_arg stmt_obj) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg_val(SQLITE_MISUSE, "invalid or finalized statement handle", lean_box_uint32(0));
  }
  int cnt = sqlite3_bind_parameter_count(stmt);
  release_stmt(h);
  return mk_code_msg_val(0, "", lean_box_uint32(cnt > 0 ? (uint32_t)cnt : 0));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_null(b_lean_obj_arg stmt_obj, uint32_t idx) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg(SQLITE_MISUSE, "invalid or finalized statement handle");
  }
  int rc = sqlite3_bind_null(stmt, clamp_nonneg_int(idx));
  lean_obj_res res = rc_unit_result(db, rc);
  release_stmt(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_int64(
    b_lean_obj_arg stmt_obj, uint32_t idx, uint64_t val) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg(SQLITE_MISUSE, "invalid or finalized statement handle");
  }
  int rc = sqlite3_bind_int64(stmt, clamp_nonneg_int(idx), (sqlite3_int64)(int64_t)val);
  lean_obj_res res = rc_unit_result(db, rc);
  release_stmt(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_double(
    b_lean_obj_arg stmt_obj, uint32_t idx, double val) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg(SQLITE_MISUSE, "invalid or finalized statement handle");
  }
  int rc = sqlite3_bind_double(stmt, clamp_nonneg_int(idx), val);
  lean_obj_res res = rc_unit_result(db, rc);
  release_stmt(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_text(
    b_lean_obj_arg stmt_obj, uint32_t idx, b_lean_obj_arg s_obj) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg(SQLITE_MISUSE, "invalid or finalized statement handle");
  }
  size_t len = lean_string_size(s_obj) - 1;
  const char *txt = len > 0 ? lean_string_cstr(s_obj) : "";
  int rc = sqlite3_bind_text64(
      stmt, clamp_nonneg_int(idx), txt, (sqlite3_uint64)len, SQLITE_TRANSIENT, SQLITE_UTF8);
  lean_obj_res res = rc_unit_result(db, rc);
  release_stmt(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_blob(
    b_lean_obj_arg stmt_obj, uint32_t idx, b_lean_obj_arg ba_obj) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg(SQLITE_MISUSE, "invalid or finalized statement handle");
  }
  size_t len = lean_sarray_size(ba_obj);
  const void *ptr = len > 0 ? (const void *)lean_sarray_cptr(ba_obj) : (const void *)"";
  int rc = sqlite3_bind_blob64(
      stmt, clamp_nonneg_int(idx), ptr, (sqlite3_uint64)len, SQLITE_TRANSIENT);
  lean_obj_res res = rc_unit_result(db, rc);
  release_stmt(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_count(b_lean_obj_arg stmt_obj) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg_val(SQLITE_MISUSE, "invalid or finalized statement handle", lean_box_uint32(0));
  }
  int cnt = sqlite3_column_count(stmt);
  release_stmt(h);
  return mk_code_msg_val(0, "", lean_box_uint32(cnt > 0 ? (uint32_t)cnt : 0));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_type(b_lean_obj_arg stmt_obj, uint32_t col) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg_val(SQLITE_MISUSE, "invalid or finalized statement handle", lean_box_uint32(0));
  }
  int ty = sqlite3_column_type(stmt, clamp_nonneg_int(col));
  release_stmt(h);
  return mk_code_msg_val(0, "", lean_box_uint32((uint32_t)ty));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_int64(b_lean_obj_arg stmt_obj, uint32_t col) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg_val(SQLITE_MISUSE, "invalid or finalized statement handle", lean_box_uint64(0));
  }
  int64_t val = (int64_t)sqlite3_column_int64(stmt, clamp_nonneg_int(col));
  release_stmt(h);
  return mk_code_msg_val(0, "", lean_box_uint64((uint64_t)val));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_double(b_lean_obj_arg stmt_obj, uint32_t col) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg_val(SQLITE_MISUSE, "invalid or finalized statement handle", lean_box_float(0.0));
  }
  double val = sqlite3_column_double(stmt, clamp_nonneg_int(col));
  release_stmt(h);
  return mk_code_msg_val(0, "", lean_box_float(val));
}

static lean_obj_res read_column_text(sqlite3_stmt *stmt, sqlite3 *db, int col_i) {
  sqlite3_mutex *mu = sqlite3_db_mutex(db);
  sqlite3_mutex_enter(mu);
  const unsigned char *txt = sqlite3_column_text(stmt, col_i);
  lean_obj_res res;
  if (txt == NULL && (sqlite3_errcode(db) & 0xff) == SQLITE_NOMEM) {
    res = mk_code_msg_val(
        db_error_code(db, SQLITE_NOMEM),
        db_error_msg(db, SQLITE_NOMEM),
        lean_alloc_sarray(1, 0, 0));
  } else {
    int nbytes = sqlite3_column_bytes(stmt, col_i);
    res = mk_code_msg_val(0, "", mk_byte_array(txt, nbytes));
  }
  sqlite3_mutex_leave(mu);
  return res;
}

static lean_obj_res read_column_blob(sqlite3_stmt *stmt, sqlite3 *db, int col_i) {
  sqlite3_mutex *mu = sqlite3_db_mutex(db);
  sqlite3_mutex_enter(mu);
  const void *blob = sqlite3_column_blob(stmt, col_i);
  lean_obj_res res;
  if (blob == NULL && sqlite3_column_type(stmt, col_i) == SQLITE_NULL &&
      (sqlite3_errcode(db) & 0xff) == SQLITE_NOMEM) {
    res = mk_code_msg_val(
        db_error_code(db, SQLITE_NOMEM),
        db_error_msg(db, SQLITE_NOMEM),
        lean_alloc_sarray(1, 0, 0));
  } else {
    int nbytes = sqlite3_column_bytes(stmt, col_i);
    res = mk_code_msg_val(0, "", mk_byte_array(blob, nbytes));
  }
  sqlite3_mutex_leave(mu);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_text_bytes(
    b_lean_obj_arg stmt_obj, uint32_t col) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg_val(
        SQLITE_MISUSE, "invalid or finalized statement handle", lean_alloc_sarray(1, 0, 0));
  }
  lean_obj_res res = read_column_text(stmt, db, clamp_nonneg_int(col));
  release_stmt(h);
  return res;
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_blob(b_lean_obj_arg stmt_obj, uint32_t col) {
  leanswe_raw_stmt *h = NULL;
  sqlite3_stmt *stmt = NULL;
  sqlite3 *db = NULL;
  if (!acquire_stmt(stmt_obj, &h, &stmt, &db)) {
    return mk_code_msg_val(
        SQLITE_MISUSE, "invalid or finalized statement handle", lean_alloc_sarray(1, 0, 0));
  }
  lean_obj_res res = read_column_blob(stmt, db, clamp_nonneg_int(col));
  release_stmt(h);
  return res;
}
