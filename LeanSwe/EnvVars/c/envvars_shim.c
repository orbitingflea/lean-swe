#define _POSIX_C_SOURCE 200809L

#include <lean/lean.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

extern char **environ;

static lean_obj_res mk_byte_array(const char *s, size_t len) {
  lean_obj_res ba = lean_alloc_sarray(1, len, len);
  if (len > 0) {
    memcpy(lean_sarray_cptr(ba), s, len);
  }
  return ba;
}

LEAN_EXPORT lean_obj_res leanswe_envvars_getenv(b_lean_obj_arg key) {
  size_t len = lean_string_size(key) - 1;
  const char *k = lean_string_cstr(key);
  if (len == 0 || memchr(k, '\0', len) != NULL || memchr(k, '=', len) != NULL) {
    return lean_box(0);
  }
  const char *val = getenv(k);
  if (val == NULL) {
    return lean_box(0);
  }
  lean_obj_res opt = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(opt, 0, mk_byte_array(val, strlen(val)));
  return opt;
}

LEAN_EXPORT lean_obj_res leanswe_envvars_environ(void) {
  lean_obj_res arr = lean_mk_empty_array();
  char **envp = environ;
  if (envp == NULL) {
    return arr;
  }
  for (size_t i = 0; envp[i] != NULL; i++) {
    arr = lean_array_push(arr, mk_byte_array(envp[i], strlen(envp[i])));
  }
  return arr;
}
