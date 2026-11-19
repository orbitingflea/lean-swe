#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE

#include <errno.h>
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

extern char **environ;
static char **g_raw_slots = NULL, **g_raw_table = NULL;
static uint32_t g_raw_cap = 0;

typedef struct host_frame {
  int was_null; size_t count; char *buf; char **orig; char **live; struct host_frame *prev;
} host_frame_t;

static host_frame_t *g_host_top = NULL;
static host_frame_t *g_host_retired = NULL;

static void *must_alloc(size_t n) { void *r = malloc(n); if (r == NULL) abort(); return r; }

static void host_free_frame(host_frame_t *f) {
  if (f == NULL) return;
  free(f->buf); free(f->orig); free(f->live); free(f);
}

static uint32_t dup_cstr_no_nul(b_lean_obj_arg obj, char **out) {
  size_t len = lean_sarray_size(obj);
  const char *p = (const char *)lean_sarray_cptr(obj);
  if (len > 0 && memchr(p, '\0', len) != NULL) return (uint32_t)EINVAL;
  char *s = (char *)malloc(len + 1);
  if (s == NULL) return (uint32_t)ENOMEM;
  if (len > 0) memcpy(s, p, len);
  s[len] = '\0';
  *out = s;
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_host_snapshot(void) {
  host_frame_t *f = (host_frame_t *)must_alloc(sizeof(host_frame_t));
  f->was_null = (environ == NULL);
  f->count = 0;
  f->buf = NULL; f->orig = NULL; f->live = NULL;
  if (!f->was_null) {
    size_t count = 0, total = 0;
    while (environ[count] != NULL) { total += strlen(environ[count]) + 1; count++; }
    f->buf = (char *)must_alloc(total + 1);
    f->orig = (char **)must_alloc((count + 1) * sizeof(char *));
    f->live = (char **)must_alloc((count + 1) * sizeof(char *));
    size_t off = 0;
    for (size_t i = 0; i < count; i++) {
      size_t len = strlen(environ[i]) + 1;
      memcpy(f->buf + off, environ[i], len);
      f->orig[i] = f->live[i] = f->buf + off;
      off += len;
    }
    f->orig[f->count = count] = f->live[count] = NULL;
    environ = f->live;
  }
  f->prev = g_host_top;
  g_host_top = f;
  host_free_frame(g_host_retired);
  g_host_retired = NULL;
  return lean_box(0);
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_host_restore(void) {
  if (g_host_top == NULL) return lean_box(0);
  host_frame_t *f = g_host_top;
  g_host_top = f->prev;
  clearenv();
  if (!f->was_null) memcpy(f->live, f->orig, (f->count + 1) * sizeof(char *));
  environ = f->was_null ? NULL : f->live;
  host_free_frame(g_host_retired);
  g_host_retired = f;
  return lean_box(0);
}

LEAN_EXPORT uint32_t leanswe_fuzz_setenv_bytes(b_lean_obj_arg k, b_lean_obj_arg v, uint8_t ovw) {
  char *ks = NULL, *vs = NULL;
  uint32_t ke = dup_cstr_no_nul(k, &ks), ve = ke == 0 ? dup_cstr_no_nul(v, &vs) : 0;
  if (ke != 0 || ve != 0) { free(ks); free(vs); return ke != 0 ? ke : ve; }
  int err = setenv(ks, vs, ovw ? 1 : 0) == 0 ? 0 : errno;
  free(ks); free(vs);
  return (uint32_t)err;
}

LEAN_EXPORT uint32_t leanswe_fuzz_unsetenv_bytes(b_lean_obj_arg k) {
  char *ks = NULL;
  uint32_t ke = dup_cstr_no_nul(k, &ks);
  if (ke != 0) return ke;
  int err = unsetenv(ks) == 0 ? 0 : errno;
  free(ks);
  return (uint32_t)err;
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_clearenv(void) { clearenv(); return lean_box(0); }

LEAN_EXPORT lean_obj_res leanswe_fuzz_raw_end(void) {
  clearenv();
  environ = NULL;
  if (g_raw_slots != NULL) {
    for (uint32_t i = 0; i < g_raw_cap; i++) free(g_raw_slots[i]);
    free(g_raw_slots); g_raw_slots = NULL;
  }
  free(g_raw_table); g_raw_table = NULL; g_raw_cap = 0;
  return lean_box(0);
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_raw_begin(uint32_t cap) {
  leanswe_fuzz_raw_end();
  g_raw_slots = (char **)calloc((size_t)cap + 1, sizeof(char *));
  g_raw_table = (char **)calloc((size_t)cap + 1, sizeof(char *));
  if (g_raw_slots == NULL || g_raw_table == NULL) abort();
  g_raw_cap = cap;
  return lean_box(0);
}

LEAN_EXPORT uint32_t leanswe_fuzz_raw_set(uint32_t idx, b_lean_obj_arg slice) {
  if (g_raw_slots == NULL || g_raw_table == NULL || idx >= g_raw_cap) return (uint32_t)EINVAL;
  char *s = NULL;
  uint32_t err = dup_cstr_no_nul(slice, &s);
  if (err != 0) return err;
  free(g_raw_slots[idx]);
  g_raw_slots[idx] = g_raw_table[idx] = s;
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_raw_install(uint8_t use_null_ptr) { environ = use_null_ptr ? NULL : g_raw_table; return lean_box(0); }