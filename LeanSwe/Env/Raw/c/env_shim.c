#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <lean/lean.h>
#include <stddef.h>
#include <string.h>

#if defined(__APPLE__)
#include <crt_externs.h>
#define LEANSWE_ENVIRON (*_NSGetEnviron())
#else
extern char **environ;
#define LEANSWE_ENVIRON environ
#endif

static int leanswe_is_valid_utf8(const unsigned char *s, size_t len) {
  size_t i = 0;
  while (i < len) {
    unsigned char b0 = s[i];
    if (b0 <= 0x7Fu) {
      i += 1;
    } else if (b0 >= 0xC2u && b0 <= 0xDFu) {
      if (i + 1 >= len) {
        return 0;
      }
      unsigned char b1 = s[i + 1];
      if ((b1 & 0xC0u) != 0x80u) {
        return 0;
      }
      i += 2;
    } else if (b0 == 0xE0u) {
      if (i + 2 >= len) {
        return 0;
      }
      unsigned char b1 = s[i + 1];
      unsigned char b2 = s[i + 2];
      if (b1 < 0xA0u || b1 > 0xBFu || (b2 & 0xC0u) != 0x80u) {
        return 0;
      }
      i += 3;
    } else if ((b0 >= 0xE1u && b0 <= 0xECu) || (b0 >= 0xEEu && b0 <= 0xEFu)) {
      if (i + 2 >= len) {
        return 0;
      }
      unsigned char b1 = s[i + 1];
      unsigned char b2 = s[i + 2];
      if ((b1 & 0xC0u) != 0x80u || (b2 & 0xC0u) != 0x80u) {
        return 0;
      }
      i += 3;
    } else if (b0 == 0xEDu) {
      if (i + 2 >= len) {
        return 0;
      }
      unsigned char b1 = s[i + 1];
      unsigned char b2 = s[i + 2];
      if (b1 < 0x80u || b1 > 0x9Fu || (b2 & 0xC0u) != 0x80u) {
        return 0;
      }
      i += 3;
    } else if (b0 == 0xF0u) {
      if (i + 3 >= len) {
        return 0;
      }
      unsigned char b1 = s[i + 1];
      unsigned char b2 = s[i + 2];
      unsigned char b3 = s[i + 3];
      if (b1 < 0x90u || b1 > 0xBFu || (b2 & 0xC0u) != 0x80u || (b3 & 0xC0u) != 0x80u) {
        return 0;
      }
      i += 4;
    } else if (b0 >= 0xF1u && b0 <= 0xF3u) {
      if (i + 3 >= len) {
        return 0;
      }
      unsigned char b1 = s[i + 1];
      unsigned char b2 = s[i + 2];
      unsigned char b3 = s[i + 3];
      if ((b1 & 0xC0u) != 0x80u || (b2 & 0xC0u) != 0x80u || (b3 & 0xC0u) != 0x80u) {
        return 0;
      }
      i += 4;
    } else if (b0 == 0xF4u) {
      if (i + 3 >= len) {
        return 0;
      }
      unsigned char b1 = s[i + 1];
      unsigned char b2 = s[i + 2];
      unsigned char b3 = s[i + 3];
      if (b1 < 0x80u || b1 > 0x8Fu || (b2 & 0xC0u) != 0x80u || (b3 & 0xC0u) != 0x80u) {
        return 0;
      }
      i += 4;
    } else {
      return 0;
    }
  }
  return 1;
}

LEAN_EXPORT lean_obj_res leanswe_env_list(lean_obj_arg w) {
  (void)w;
  lean_obj_res arr = lean_mk_empty_array();
  char **envp = LEANSWE_ENVIRON;
  if (envp == NULL) {
    return lean_io_result_mk_ok(arr);
  }
  for (size_t i = 0; envp[i] != NULL; i++) {
    const char *entry = envp[i];
    const char *eq = strchr(entry, '=');
    if (eq == NULL || eq == entry) {
      continue;
    }
    size_t klen = (size_t)(eq - entry);
    const char *val = eq + 1;
    size_t vlen = strlen(val);
    int key_ok = leanswe_is_valid_utf8((const unsigned char *)entry, klen);
    int val_ok = leanswe_is_valid_utf8((const unsigned char *)val, vlen);
    if (!key_ok || !val_ok) {
      lean_dec(arr);
      lean_obj_res msg = lean_mk_string("invalid UTF-8 in environment entry");
      if (key_ok) {
        lean_obj_res kobj = lean_mk_string_from_bytes(entry, klen);
        return lean_io_result_mk_error(
            lean_mk_io_error_invalid_argument_file(kobj, (uint32_t)EINVAL, msg));
      }
      return lean_io_result_mk_error(lean_mk_io_user_error(msg));
    }
    lean_obj_res kobj = lean_mk_string_from_bytes(entry, klen);
    lean_obj_res vobj = lean_mk_string_from_bytes(val, vlen);
    lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, kobj);
    lean_ctor_set(pair, 1, vobj);
    arr = lean_array_push(arr, pair);
  }
  return lean_io_result_mk_ok(arr);
}
