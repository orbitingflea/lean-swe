#define _POSIX_C_SOURCE 200809L

#include <lean/lean.h>
#include "sqlite3.h"

#include <limits.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  uint64_t id;
  sqlite3 *db;
  uint32_t in_use;
} leanswe_db_slot;

typedef struct {
  uint64_t id;
  uint64_t db_id;
  sqlite3_stmt *stmt;
  uint32_t in_use;
} leanswe_stmt_slot;

static pthread_mutex_t g_sqlite_mu = PTHREAD_MUTEX_INITIALIZER;
static leanswe_db_slot *g_dbs = NULL;
static size_t g_db_len = 0;
static size_t g_db_cap = 0;
static uint64_t g_next_db_id = 1;

static leanswe_stmt_slot *g_stmts = NULL;
static size_t g_stmt_len = 0;
static size_t g_stmt_cap = 0;
static uint64_t g_next_stmt_id = 1;

static lean_obj_res mk_code_msg(uint32_t code, const char *msg) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_box_uint32(code));
  lean_ctor_set(p, 1, lean_mk_string(msg != NULL ? msg : ""));
  return p;
}

static lean_obj_res mk_code_msg_u64(uint32_t code, const char *msg, uint64_t val) {
  lean_obj_res inner = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(inner, 0, lean_mk_string(msg != NULL ? msg : ""));
  lean_ctor_set(inner, 1, lean_box_uint64(val));
  lean_obj_res outer = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(outer, 0, lean_box_uint32(code));
  lean_ctor_set(outer, 1, inner);
  return outer;
}

static lean_obj_res mk_code_msg_u32(uint32_t code, const char *msg, uint32_t val) {
  lean_obj_res inner = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(inner, 0, lean_mk_string(msg != NULL ? msg : ""));
  lean_ctor_set(inner, 1, lean_box_uint32(val));
  lean_obj_res outer = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(outer, 0, lean_box_uint32(code));
  lean_ctor_set(outer, 1, inner);
  return outer;
}

static lean_obj_res mk_code_msg_u8(uint32_t code, const char *msg, uint8_t val) {
  lean_obj_res inner = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(inner, 0, lean_mk_string(msg != NULL ? msg : ""));
  lean_ctor_set(inner, 1, lean_box(val));
  lean_obj_res outer = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(outer, 0, lean_box_uint32(code));
  lean_ctor_set(outer, 1, inner);
  return outer;
}

static size_t find_db_idx(uint64_t db_id) {
  for (size_t i = 0; i < g_db_len; i++) {
    if (g_dbs[i].id == db_id) {
      return i;
    }
  }
  return SIZE_MAX;
}

static size_t find_stmt_idx(uint64_t stmt_id, uint64_t db_id) {
  for (size_t i = 0; i < g_stmt_len; i++) {
    if (g_stmts[i].id == stmt_id && g_stmts[i].db_id == db_id) {
      return i;
    }
  }
  return SIZE_MAX;
}

static int ensure_db_cap(void) {
  if (g_db_len < g_db_cap) {
    return 1;
  }
  size_t new_cap = g_db_cap == 0 ? 16 : g_db_cap * 2;
  leanswe_db_slot *tmp = (leanswe_db_slot *)realloc(g_dbs, new_cap * sizeof(leanswe_db_slot));
  if (tmp == NULL) {
    return 0;
  }
  g_dbs = tmp;
  g_db_cap = new_cap;
  return 1;
}

static int ensure_stmt_cap(void) {
  if (g_stmt_len < g_stmt_cap) {
    return 1;
  }
  size_t new_cap = g_stmt_cap == 0 ? 32 : g_stmt_cap * 2;
  leanswe_stmt_slot *tmp =
      (leanswe_stmt_slot *)realloc(g_stmts, new_cap * sizeof(leanswe_stmt_slot));
  if (tmp == NULL) {
    return 0;
  }
  g_stmts = tmp;
  g_stmt_cap = new_cap;
  return 1;
}

static int has_embedded_nul(b_lean_obj_arg str_obj) {
  size_t sz = lean_string_size(str_obj);
  if (sz == 0) {
    return 1;
  }
  const char *cstr = lean_string_cstr(str_obj);
  return strlen(cstr) != sz - 1;
}

static int is_ascii_ws(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

static int is_memory_uri(const char *path) {
  return strcmp(path, ":memory:") == 0 || strncmp(path, "file::memory:", 13) == 0;
}

static uint32_t db_error_code(sqlite3 *db, int fallback_rc) {
  if (db != NULL) {
    int ext = sqlite3_extended_errcode(db);
    if (ext != SQLITE_OK) {
      return (uint32_t)ext;
    }
  }
  return (uint32_t)fallback_rc;
}

static const char *db_error_msg(sqlite3 *db, int fallback_rc) {
  if (db != NULL) {
    const char *m = sqlite3_errmsg(db);
    if (m != NULL && m[0] != '\0') {
      return m;
    }
  }
  const char *s = sqlite3_errstr(fallback_rc);
  return s != NULL ? s : "sqlite error";
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_open_db(
    b_lean_obj_arg path_obj, uint8_t read_only, uint8_t create_if_missing,
    uint32_t busy_timeout_ms, uint8_t wal_mode, uint8_t foreign_keys, lean_obj_arg w) {
  (void)w;
  if (has_embedded_nul(path_obj)) {
    return lean_io_result_mk_ok(mk_code_msg_u64(
        SQLITE_MISUSE, "database path contains embedded NUL byte", 0));
  }
  const char *cpath = lean_string_cstr(path_obj);
  if (cpath[0] == '\0') {
    return lean_io_result_mk_ok(mk_code_msg_u64(
        SQLITE_MISUSE, "database path must not be empty", 0));
  }
  if (read_only && create_if_missing) {
    return lean_io_result_mk_ok(mk_code_msg_u64(
        SQLITE_MISUSE, "cannot combine readOnly with createIfMissing", 0));
  }
  if (busy_timeout_ms > (uint32_t)INT_MAX) {
    return lean_io_result_mk_ok(mk_code_msg_u64(
        SQLITE_MISUSE, "busyTimeoutMs exceeds int32 max", 0));
  }

  int flags = SQLITE_OPEN_FULLMUTEX;
  if (read_only) {
    flags |= SQLITE_OPEN_READONLY;
  } else if (create_if_missing) {
    flags |= SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE;
  } else {
    flags |= SQLITE_OPEN_READWRITE;
  }

  sqlite3 *db = NULL;
  int rc = sqlite3_open_v2(cpath, &db, flags, NULL);
  if (rc != SQLITE_OK || db == NULL) {
    uint32_t code = db_error_code(db, rc);
    lean_obj_res res = mk_code_msg_u64(code, db_error_msg(db, rc), 0);
    if (db != NULL) {
      sqlite3_close(db);
    }
    return lean_io_result_mk_ok(res);
  }

  sqlite3_extended_result_codes(db, 1);

  rc = sqlite3_busy_timeout(db, (int)busy_timeout_ms);
  if (rc != SQLITE_OK) {
    uint32_t code = db_error_code(db, rc);
    lean_obj_res res = mk_code_msg_u64(code, db_error_msg(db, rc), 0);
    sqlite3_close(db);
    return lean_io_result_mk_ok(res);
  }

  if (foreign_keys) {
    rc = sqlite3_exec(db, "PRAGMA foreign_keys = ON;", NULL, NULL, NULL);
    if (rc != SQLITE_OK) {
      uint32_t code = db_error_code(db, rc);
      lean_obj_res res = mk_code_msg_u64(code, db_error_msg(db, rc), 0);
      sqlite3_close(db);
      return lean_io_result_mk_ok(res);
    }
  }

  if (!read_only && wal_mode && !is_memory_uri(cpath)) {
    rc = sqlite3_exec(db, "PRAGMA journal_mode = WAL;", NULL, NULL, NULL);
    if (rc != SQLITE_OK) {
      uint32_t code = db_error_code(db, rc);
      lean_obj_res res = mk_code_msg_u64(code, db_error_msg(db, rc), 0);
      sqlite3_close(db);
      return lean_io_result_mk_ok(res);
    }
  }

  pthread_mutex_lock(&g_sqlite_mu);
  if (!ensure_db_cap()) {
    pthread_mutex_unlock(&g_sqlite_mu);
    sqlite3_close(db);
    return lean_io_result_mk_ok(mk_code_msg_u64(SQLITE_NOMEM, "out of memory", 0));
  }
  uint64_t db_id = g_next_db_id++;
  g_dbs[g_db_len].id = db_id;
  g_dbs[g_db_len].db = db;
  g_dbs[g_db_len].in_use = 0;
  g_db_len++;
  pthread_mutex_unlock(&g_sqlite_mu);

  return lean_io_result_mk_ok(mk_code_msg_u64(0, "", db_id));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_close_db(uint64_t db_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_db_idx(db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(SQLITE_MISUSE, "invalid or closed database handle"));
  }
  if (g_dbs[idx].in_use > 0) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(SQLITE_BUSY, "database handle is currently in use"));
  }
  sqlite3 *db = g_dbs[idx].db;
  int rc = sqlite3_close(db);
  if (rc != SQLITE_OK) {
    uint32_t code = db_error_code(db, rc);
    lean_obj_res res = mk_code_msg(code, db_error_msg(db, rc));
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(res);
  }
  g_dbs[idx] = g_dbs[g_db_len - 1];
  g_db_len--;
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(mk_code_msg(0, ""));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_prepare(
    uint64_t db_id, b_lean_obj_arg sql_obj, lean_obj_arg w) {
  (void)w;
  if (has_embedded_nul(sql_obj)) {
    return lean_io_result_mk_ok(mk_code_msg_u64(
        SQLITE_MISUSE, "SQL string contains embedded NUL byte", 0));
  }
  size_t sql_len = lean_string_size(sql_obj) - 1;
  if (sql_len > (size_t)INT_MAX) {
    return lean_io_result_mk_ok(mk_code_msg_u64(SQLITE_TOOBIG, "SQL statement too large", 0));
  }
  const char *sql = lean_string_cstr(sql_obj);

  pthread_mutex_lock(&g_sqlite_mu);
  size_t db_idx = find_db_idx(db_id);
  if (db_idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg_u64(
        SQLITE_MISUSE, "invalid or closed database handle", 0));
  }
  sqlite3 *db = g_dbs[db_idx].db;
  g_dbs[db_idx].in_use++;
  pthread_mutex_unlock(&g_sqlite_mu);

  sqlite3_stmt *stmt = NULL;
  const char *tail = NULL;
  int rc = sqlite3_prepare_v2(db, sql, (int)sql_len, &stmt, &tail);

  pthread_mutex_lock(&g_sqlite_mu);
  db_idx = find_db_idx(db_id);
  if (db_idx != SIZE_MAX && g_dbs[db_idx].in_use > 0) {
    g_dbs[db_idx].in_use--;
  }
  if (rc != SQLITE_OK) {
    uint32_t code = db_error_code(db, rc);
    lean_obj_res res = mk_code_msg_u64(code, db_error_msg(db, rc), 0);
    pthread_mutex_unlock(&g_sqlite_mu);
    if (stmt != NULL) {
      sqlite3_finalize(stmt);
    }
    return lean_io_result_mk_ok(res);
  }
  if (stmt == NULL) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg_u64(SQLITE_MISUSE, "empty SQL statement", 0));
  }
  if (tail != NULL) {
    while (*tail != '\0' && is_ascii_ws(*tail)) {
      tail++;
    }
    if (*tail != '\0') {
      pthread_mutex_unlock(&g_sqlite_mu);
      sqlite3_finalize(stmt);
      return lean_io_result_mk_ok(mk_code_msg_u64(
          SQLITE_MISUSE, "multiple SQL statements are not allowed in prepare", 0));
    }
  }
  if (!ensure_stmt_cap()) {
    pthread_mutex_unlock(&g_sqlite_mu);
    sqlite3_finalize(stmt);
    return lean_io_result_mk_ok(mk_code_msg_u64(SQLITE_NOMEM, "out of memory", 0));
  }
  uint64_t stmt_id = g_next_stmt_id++;
  g_stmts[g_stmt_len].id = stmt_id;
  g_stmts[g_stmt_len].db_id = db_id;
  g_stmts[g_stmt_len].stmt = stmt;
  g_stmts[g_stmt_len].in_use = 0;
  g_stmt_len++;
  pthread_mutex_unlock(&g_sqlite_mu);

  return lean_io_result_mk_ok(mk_code_msg_u64(0, "", stmt_id));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_param_count(
    uint64_t stmt_id, uint64_t db_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg_u32(
        SQLITE_MISUSE, "invalid or finalized statement handle", 0));
  }
  int cnt = sqlite3_bind_parameter_count(g_stmts[idx].stmt);
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(mk_code_msg_u32(0, "", (uint32_t)(cnt < 0 ? 0 : cnt)));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_clear_and_reset(
    uint64_t stmt_id, uint64_t db_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(
        SQLITE_MISUSE, "invalid or finalized statement handle"));
  }
  sqlite3_stmt *stmt = g_stmts[idx].stmt;
  sqlite3 *db = sqlite3_db_handle(stmt);
  int rc = sqlite3_reset(stmt);
  if (rc == SQLITE_OK) {
    rc = sqlite3_clear_bindings(stmt);
  }
  lean_obj_res res = rc == SQLITE_OK
      ? mk_code_msg(0, "")
      : mk_code_msg(db_error_code(db, rc), db_error_msg(db, rc));
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_null(
    uint64_t stmt_id, uint64_t db_id, uint32_t param_idx, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(
        SQLITE_MISUSE, "invalid or finalized statement handle"));
  }
  sqlite3_stmt *stmt = g_stmts[idx].stmt;
  sqlite3 *db = sqlite3_db_handle(stmt);
  int rc = sqlite3_bind_null(stmt, (int)param_idx);
  lean_obj_res res = rc == SQLITE_OK
      ? mk_code_msg(0, "")
      : mk_code_msg(db_error_code(db, rc), db_error_msg(db, rc));
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_int64(
    uint64_t stmt_id, uint64_t db_id, uint32_t param_idx, uint64_t val, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(
        SQLITE_MISUSE, "invalid or finalized statement handle"));
  }
  sqlite3_stmt *stmt = g_stmts[idx].stmt;
  sqlite3 *db = sqlite3_db_handle(stmt);
  int rc = sqlite3_bind_int64(stmt, (int)param_idx, (sqlite3_int64)(int64_t)val);
  lean_obj_res res = rc == SQLITE_OK
      ? mk_code_msg(0, "")
      : mk_code_msg(db_error_code(db, rc), db_error_msg(db, rc));
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_double(
    uint64_t stmt_id, uint64_t db_id, uint32_t param_idx, double val, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(
        SQLITE_MISUSE, "invalid or finalized statement handle"));
  }
  sqlite3_stmt *stmt = g_stmts[idx].stmt;
  sqlite3 *db = sqlite3_db_handle(stmt);
  int rc = sqlite3_bind_double(stmt, (int)param_idx, val);
  lean_obj_res res = rc == SQLITE_OK
      ? mk_code_msg(0, "")
      : mk_code_msg(db_error_code(db, rc), db_error_msg(db, rc));
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_text(
    uint64_t stmt_id, uint64_t db_id, uint32_t param_idx, b_lean_obj_arg txt_obj, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(
        SQLITE_MISUSE, "invalid or finalized statement handle"));
  }
  sqlite3_stmt *stmt = g_stmts[idx].stmt;
  sqlite3 *db = sqlite3_db_handle(stmt);
  size_t sz = lean_string_size(txt_obj);
  size_t nbytes = sz > 0 ? sz - 1 : 0;
  const char *cstr = lean_string_cstr(txt_obj);
  int rc = sqlite3_bind_text64(
      stmt, (int)param_idx, cstr, (sqlite3_uint64)nbytes, SQLITE_TRANSIENT, SQLITE_UTF8);
  lean_obj_res res = rc == SQLITE_OK
      ? mk_code_msg(0, "")
      : mk_code_msg(db_error_code(db, rc), db_error_msg(db, rc));
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_bind_blob(
    uint64_t stmt_id, uint64_t db_id, uint32_t param_idx, b_lean_obj_arg ba_obj, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(
        SQLITE_MISUSE, "invalid or finalized statement handle"));
  }
  sqlite3_stmt *stmt = g_stmts[idx].stmt;
  sqlite3 *db = sqlite3_db_handle(stmt);
  size_t nbytes = lean_sarray_size(ba_obj);
  const void *ptr = nbytes == 0 ? (const void *)"" : (const void *)lean_sarray_cptr((lean_object *)ba_obj);
  int rc = sqlite3_bind_blob64(
      stmt, (int)param_idx, ptr, (sqlite3_uint64)nbytes, SQLITE_TRANSIENT);
  lean_obj_res res = rc == SQLITE_OK
      ? mk_code_msg(0, "")
      : mk_code_msg(db_error_code(db, rc), db_error_msg(db, rc));
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_step(
    uint64_t stmt_id, uint64_t db_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg_u8(
        SQLITE_MISUSE, "invalid or finalized statement handle", 0));
  }
  sqlite3_stmt *stmt = g_stmts[idx].stmt;
  sqlite3 *db = sqlite3_db_handle(stmt);
  g_stmts[idx].in_use++;
  size_t db_idx = find_db_idx(db_id);
  if (db_idx != SIZE_MAX) {
    g_dbs[db_idx].in_use++;
  }
  pthread_mutex_unlock(&g_sqlite_mu);

  int rc = sqlite3_step(stmt);

  pthread_mutex_lock(&g_sqlite_mu);
  lean_obj_res res;
  if (rc == SQLITE_DONE) {
    res = mk_code_msg_u8(0, "", 0);
  } else if (rc == SQLITE_ROW) {
    res = mk_code_msg_u8(0, "", 1);
  } else {
    res = mk_code_msg_u8(db_error_code(db, rc), db_error_msg(db, rc), 0);
  }
  idx = find_stmt_idx(stmt_id, db_id);
  if (idx != SIZE_MAX && g_stmts[idx].in_use > 0) {
    g_stmts[idx].in_use--;
  }
  db_idx = find_db_idx(db_id);
  if (db_idx != SIZE_MAX && g_dbs[db_idx].in_use > 0) {
    g_dbs[db_idx].in_use--;
  }
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_count(
    uint64_t stmt_id, uint64_t db_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  uint32_t cnt = 0;
  if (idx != SIZE_MAX) {
    int c = sqlite3_column_count(g_stmts[idx].stmt);
    if (c > 0) {
      cnt = (uint32_t)c;
    }
  }
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(lean_box_uint32(cnt));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_type(
    uint64_t stmt_id, uint64_t db_id, uint32_t col, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  uint32_t ty = SQLITE_NULL;
  if (idx != SIZE_MAX) {
    ty = (uint32_t)sqlite3_column_type(g_stmts[idx].stmt, (int)col);
  }
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(lean_box_uint32(ty));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_int64(
    uint64_t stmt_id, uint64_t db_id, uint32_t col, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  int64_t val = 0;
  if (idx != SIZE_MAX) {
    val = (int64_t)sqlite3_column_int64(g_stmts[idx].stmt, (int)col);
  }
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)val));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_double(
    uint64_t stmt_id, uint64_t db_id, uint32_t col, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  double val = 0.0;
  if (idx != SIZE_MAX) {
    val = sqlite3_column_double(g_stmts[idx].stmt, (int)col);
  }
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(lean_box_float(val));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_text(
    uint64_t stmt_id, uint64_t db_id, uint32_t col, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  lean_obj_res res;
  if (idx == SIZE_MAX) {
    res = lean_mk_string("");
  } else {
    const unsigned char *txt = sqlite3_column_text(g_stmts[idx].stmt, (int)col);
    int nbytes = sqlite3_column_bytes(g_stmts[idx].stmt, (int)col);
    if (txt == NULL || nbytes <= 0) {
      res = lean_mk_string("");
    } else {
      res = lean_mk_string_from_bytes((const char *)txt, (size_t)nbytes);
    }
  }
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_column_blob(
    uint64_t stmt_id, uint64_t db_id, uint32_t col, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  lean_obj_res res;
  if (idx == SIZE_MAX) {
    res = lean_alloc_sarray(1, 0, 0);
  } else {
    const void *blob = sqlite3_column_blob(g_stmts[idx].stmt, (int)col);
    int nbytes = sqlite3_column_bytes(g_stmts[idx].stmt, (int)col);
    if (blob == NULL || nbytes <= 0) {
      res = lean_alloc_sarray(1, 0, 0);
    } else {
      res = lean_alloc_sarray(1, (size_t)nbytes, (size_t)nbytes);
      memcpy(lean_sarray_cptr(res), blob, (size_t)nbytes);
    }
  }
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_finalize(
    uint64_t stmt_id, uint64_t db_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t idx = find_stmt_idx(stmt_id, db_id);
  if (idx == SIZE_MAX) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(
        SQLITE_MISUSE, "invalid or already finalized statement handle"));
  }
  if (g_stmts[idx].in_use > 0) {
    pthread_mutex_unlock(&g_sqlite_mu);
    return lean_io_result_mk_ok(mk_code_msg(SQLITE_BUSY, "statement handle is currently in use"));
  }
  sqlite3_stmt *stmt = g_stmts[idx].stmt;
  sqlite3 *db = sqlite3_db_handle(stmt);
  g_stmts[idx] = g_stmts[g_stmt_len - 1];
  g_stmt_len--;
  int rc = sqlite3_finalize(stmt);
  lean_obj_res res = rc == SQLITE_OK
      ? mk_code_msg(0, "")
      : mk_code_msg(db_error_code(db, rc), db_error_msg(db, rc));
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_active_db_count(lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t count = g_db_len;
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(lean_usize_to_nat(count));
}

LEAN_EXPORT lean_obj_res leanswe_sqlite_active_stmt_count(lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_sqlite_mu);
  size_t count = g_stmt_len;
  pthread_mutex_unlock(&g_sqlite_mu);
  return lean_io_result_mk_ok(lean_usize_to_nat(count));
}
