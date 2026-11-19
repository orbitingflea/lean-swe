#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe LinuxSyscall requires Linux on x86_64 or aarch64"
#endif

#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <lean/lean.h>
#include <pwd.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>

#define LEANSWE_PASSWD_MAX_BUF 65536u

static inline lean_obj_res mk_except_ok(lean_obj_res v) {
  lean_obj_res r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, v);
  return r;
}
static inline lean_obj_res mk_except_err(int err) {
  if (err == EFAULT) {
    abort();
  }
  lean_obj_res r = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(r, 0, lean_box_uint32((uint32_t)err));
  return r;
}
static inline lean_obj_res mk_pair(lean_obj_res a, lean_obj_res b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}
static inline int resolve_pw_err(int rc, int saved_errno) {
  if (rc > 0) {
    return rc;
  }
  return saved_errno > 0 ? saved_errno : EIO;
}

static inline lean_obj_res mk_bytes(const char *s) {
  if (s == NULL) {
    return lean_alloc_sarray(1, 0, 0);
  }
  size_t len = strlen(s);
  lean_obj_res ba = lean_alloc_sarray(1, len, len);
  if (len > 0) {
    memcpy(lean_sarray_cptr(ba), s, len);
  }
  return ba;
}

static lean_obj_res mk_some_passwd(const struct passwd *res) {
  lean_obj_res shell = mk_bytes(res->pw_shell);
  lean_obj_res dir = mk_bytes(res->pw_dir);
  lean_obj_res gecos = mk_bytes(res->pw_gecos);
  lean_obj_res gid = lean_box_uint32((uint32_t)res->pw_gid);
  lean_obj_res uid = lean_box_uint32((uint32_t)res->pw_uid);
  lean_obj_res name = mk_bytes(res->pw_name);
  lean_obj_res tuple = mk_pair(name, mk_pair(uid, mk_pair(gid, mk_pair(gecos, mk_pair(dir, shell)))));
  lean_obj_res opt = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(opt, 0, tuple);
  return opt;
}

static lean_obj_res finish_pw_lookup(int rc, int saved_errno, struct passwd *res, char *buf) {
  if (rc != 0) {
    free(buf);
    return mk_except_err(resolve_pw_err(rc, saved_errno));
  }
  lean_obj_res out = (res == NULL) ? lean_box(0) : mk_some_passwd(res);
  free(buf);
  return mk_except_ok(out);
}

static char *dup_cstr_checked(b_lean_obj_arg ba, int *err_out) {
  size_t len = lean_sarray_size(ba);
  const uint8_t *ptr = lean_sarray_cptr(ba);
  if (len > 0 && memchr(ptr, '\0', len) != NULL) {
    *err_out = EINVAL;
    return NULL;
  }
  if (len > 1048576u) {
    *err_out = ENAMETOOLONG;
    return NULL;
  }
  char *out = (char *)malloc(len + 1u);
  if (out == NULL) {
    *err_out = ENOMEM;
    return NULL;
  }
  if (len > 0) {
    memcpy(out, ptr, len);
  }
  out[len] = '\0';
  return out;
}

/** Single-call `getpwuid_r(3)` wrapper returning raw `PasswdEntry` tuple fields. */
LEAN_EXPORT lean_obj_res leanswe_sys_getpwuid_once(uint32_t uid, uint32_t buf_bytes) {
  if (buf_bytes == 0u || buf_bytes > LEANSWE_PASSWD_MAX_BUF) {
    return mk_except_err(EINVAL);
  }
  char *buf = (char *)malloc((size_t)buf_bytes);
  if (buf == NULL) {
    return mk_except_err(ENOMEM);
  }
  struct passwd pwd = {0};
  struct passwd *res = NULL;
  errno = 0;
  int rc = getpwuid_r((uid_t)uid, &pwd, buf, (size_t)buf_bytes, &res);
  return finish_pw_lookup(rc, errno, res, buf);
}

/** Single-call `getpwnam_r(3)` wrapper returning raw `PasswdEntry` tuple fields. */
LEAN_EXPORT lean_obj_res leanswe_sys_getpwnam_once(b_lean_obj_arg name_ba, uint32_t buf_bytes) {
  if (buf_bytes == 0u || buf_bytes > LEANSWE_PASSWD_MAX_BUF) {
    return mk_except_err(EINVAL);
  }
  int cerr = 0;
  char *cname = dup_cstr_checked(name_ba, &cerr);
  if (cname == NULL) {
    return mk_except_err(cerr);
  }
  char *buf = (char *)malloc((size_t)buf_bytes);
  if (buf == NULL) {
    free(cname);
    return mk_except_err(ENOMEM);
  }
  struct passwd pwd = {0};
  struct passwd *res = NULL;
  errno = 0;
  int rc = getpwnam_r(cname, &pwd, buf, (size_t)buf_bytes, &res);
  int saved_errno = errno;
  free(cname);
  return finish_pw_lookup(rc, saved_errno, res, buf);
}
