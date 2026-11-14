#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <lean/lean.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>

LEAN_EXPORT lean_obj_res leanswe_fs_chmod(b_lean_obj_arg path_obj, uint32_t mode, lean_obj_arg w) {
  (void)w;
  const char *cpath = lean_string_cstr(path_obj);
  if (chmod(cpath, (mode_t)mode) != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, path_obj));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_symlink(
    b_lean_obj_arg target_obj, b_lean_obj_arg link_obj, lean_obj_arg w) {
  (void)w;
  const char *target = lean_string_cstr(target_obj);
  const char *linkpath = lean_string_cstr(link_obj);
  if (symlink(target, linkpath) != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, link_obj));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_readlink(b_lean_obj_arg path_obj, lean_obj_arg w) {
  (void)w;
  const char *cpath = lean_string_cstr(path_obj);
  size_t cap = 256;
  for (;;) {
    char *buf = (char *)malloc(cap);
    if (buf == NULL) {
      return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, path_obj));
    }
    ssize_t n = readlink(cpath, buf, cap - 1);
    if (n < 0) {
      int err = errno;
      free(buf);
      return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
    }
    if ((size_t)n < cap - 1) {
      buf[n] = '\0';
      lean_obj_res res = lean_mk_string(buf);
      free(buf);
      return lean_io_result_mk_ok(res);
    }
    free(buf);
    if (cap >= (1u << 20)) {
      return lean_io_result_mk_error(lean_decode_io_error(ENAMETOOLONG, path_obj));
    }
    cap *= 2;
  }
}

LEAN_EXPORT lean_obj_res leanswe_fs_stat_mode(
    b_lean_obj_arg path_obj, uint8_t follow_symlinks, lean_obj_arg w) {
  (void)w;
  const char *cpath = lean_string_cstr(path_obj);
  struct stat st;
  int rc = follow_symlinks ? stat(cpath, &st) : lstat(cpath, &st);
  if (rc != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, path_obj));
  }
  uint32_t perms = (uint32_t)(st.st_mode & 07777);
  return lean_io_result_mk_ok(lean_box_uint32(perms));
}
