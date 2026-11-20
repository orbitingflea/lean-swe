#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "files_shim.c supports only Linux on x86_64 or aarch64"
#endif

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/openat2.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/vfs.h>
#include <unistd.h>
#include "fd_box.h"

#define LEANSWE_MAX_READ_BYTES (16u * 1024u * 1024u)

#ifndef SYS_openat2
#define SYS_openat2 437
#endif

#ifndef SYS_faccessat2
#define SYS_faccessat2 439
#endif

#if defined(__x86_64__)
#ifndef SYS_getdents64
#define SYS_getdents64 217
#endif
#ifndef SYS_renameat2
#define SYS_renameat2 316
#endif
#ifndef SYS_getcwd
#define SYS_getcwd 79
#endif
#ifndef SYS_statx
#define SYS_statx 332
#endif
#elif defined(__aarch64__)
#ifndef SYS_getdents64
#define SYS_getdents64 61
#endif
#ifndef SYS_renameat2
#define SYS_renameat2 276
#endif
#ifndef SYS_getcwd
#define SYS_getcwd 17
#endif
#ifndef SYS_statx
#define SYS_statx 291
#endif
#endif

static inline lean_obj_res mk_pair(lean_obj_res a, lean_obj_res b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

static int ba_to_cstr(b_lean_obj_arg ba, char *stack_buf, size_t stack_cap,
                      const char **out_ptr, char **out_heap) {
  size_t len = lean_sarray_size(ba);
  const uint8_t *src = lean_sarray_cptr(ba);
  if (len > 0 && memchr(src, 0, len) != NULL) return EINVAL;
  if (len < stack_cap) {
    if (len > 0) memcpy(stack_buf, src, len);
    stack_buf[len] = '\0';
    *out_ptr = stack_buf; *out_heap = NULL;
    return 0;
  }
  char *heap = (char *)malloc(len + 1);
  if (heap == NULL) return ENOMEM;
  memcpy(heap, src, len);
  heap[len] = '\0';
  *out_ptr = heap; *out_heap = heap;
  return 0;
}

static int pin_opt_dir(b_lean_obj_arg dir_opt, LeanFdBox **out_box, int *out_dfd) {
  *out_box = NULL;
  *out_dfd = AT_FDCWD;
  if (!lean_is_scalar(dir_opt)) {
    LeanFdBox *box = (LeanFdBox *)lean_get_external_data(lean_ctor_get(dir_opt, 0));
    int perr = leanswe_fd_box_pin(box, out_dfd);
    if (perr != 0) return perr;
    *out_box = box;
  }
  return 0;
}

static char *alloc_read_buf(uint32_t *cap_io) {
  if (*cap_io > LEANSWE_MAX_READ_BYTES) *cap_io = LEANSWE_MAX_READ_BYTES;
  size_t sz = (*cap_io > 0u) ? (size_t)*cap_io : 1u;
  return (char *)malloc(sz);
}

static lean_obj_res finish_read_buf(char *buf, ssize_t n, int err) {
  if (n < 0) {
    free(buf);
    return leanswe_mk_errno(err);
  }
  size_t sz = (size_t)n;
  lean_obj_res ba = lean_alloc_sarray(1, sz, sz);
  if (sz > 0) memcpy(lean_sarray_cptr(ba), buf, sz);
  free(buf);
  return leanswe_mk_ok(ba);
}

static int decode_access_mode(uint32_t acc) {
  if (acc == 0u) return O_RDONLY;
  if (acc == 1u) return O_WRONLY;
  return O_RDWR;
}

static int decode_open_flags(uint32_t bits) {
  uint32_t f = (uint32_t)decode_access_mode(bits & 3u)
    | ((0u - ((bits >> 2) & 1u)) & (uint32_t)O_CREAT)
    | ((0u - ((bits >> 3) & 1u)) & (uint32_t)O_EXCL)
    | ((0u - ((bits >> 4) & 1u)) & (uint32_t)O_TRUNC)
    | ((0u - ((bits >> 5) & 1u)) & (uint32_t)O_APPEND)
    | ((0u - ((bits >> 6) & 1u)) & (uint32_t)O_NOFOLLOW)
    | ((0u - ((bits >> 7) & 1u)) & (uint32_t)O_DIRECTORY)
    | ((0u - ((bits >> 8) & 1u)) & (uint32_t)O_NONBLOCK)
    | ((0u - ((bits >> 9) & 1u)) & (uint32_t)O_CLOEXEC)
    | ((0u - ((bits >> 10) & 1u)) & (uint32_t)O_NOCTTY)
    | ((0u - ((bits >> 11) & 1u)) & (uint32_t)O_PATH);
  return (int)f;
}

static uint64_t decode_resolve_flags(uint64_t bits) {
  uint64_t r = 0;
  if (bits & (1ull << 0)) r |= RESOLVE_NO_XDEV;
  if (bits & (1ull << 1)) r |= RESOLVE_NO_MAGICLINKS;
  if (bits & (1ull << 2)) r |= RESOLVE_NO_SYMLINKS;
  if (bits & (1ull << 3)) r |= RESOLVE_BENEATH;
  if (bits & (1ull << 4)) r |= RESOLVE_IN_ROOT;
  if (bits & (1ull << 5)) r |= RESOLVE_CACHED;
  return r;
}

static int decode_at_flags(uint32_t bits) {
  int f = 0;
  if (bits & (1u << 0)) f |= AT_SYMLINK_NOFOLLOW;
  if (bits & (1u << 1)) f |= AT_EMPTY_PATH;
  if (bits & (1u << 2)) f |= AT_EACCESS;
  return f;
}

static int decode_access_mask(uint32_t bits) {
  if (bits == 0u) return F_OK;
  int m = 0;
  if (bits & (1u << 0)) m |= R_OK;
  if (bits & (1u << 1)) m |= W_OK;
  if (bits & (1u << 2)) m |= X_OK;
  return m;
}

static unsigned int decode_rename_flags(uint32_t bits) {
  unsigned int f = 0;
  if (bits & (1u << 0)) f |= RENAME_NOREPLACE;
  if (bits & (1u << 1)) f |= RENAME_EXCHANGE;
  if (bits & (1u << 2)) f |= RENAME_WHITEOUT;
  return f;
}

static int decode_flock_op(uint32_t bits) {
  int op = 0;
  if (bits & 1u) op |= LOCK_SH;
  else if (bits & 2u) op |= LOCK_EX;
  else if (bits & 4u) op |= LOCK_UN;
  if (bits & 8u) op |= LOCK_NB;
  return op;
}

static lean_obj_res mk_raw_stat_tuple(const struct stat *st) {
  uint8_t kind = 7;
  if (S_ISREG(st->st_mode)) kind = 0;
  else if (S_ISDIR(st->st_mode)) kind = 1;
  else if (S_ISLNK(st->st_mode)) kind = 2;
  else if (S_ISFIFO(st->st_mode)) kind = 3;
  else if (S_ISSOCK(st->st_mode)) kind = 4;
  else if (S_ISCHR(st->st_mode)) kind = 5;
  else if (S_ISBLK(st->st_mode)) kind = 6;
  uint64_t sz = (st->st_size >= 0) ? (uint64_t)st->st_size : 0u;
  uint32_t mode = (uint32_t)(st->st_mode & 07777u);
  lean_obj_res m_sec = lean_int64_to_int((int64_t)st->st_mtim.tv_sec);
  lean_obj_res m_nsec = lean_box_uint32((uint32_t)st->st_mtim.tv_nsec);
  lean_obj_res a_sec = lean_int64_to_int((int64_t)st->st_atim.tv_sec);
  lean_obj_res a_nsec = lean_box_uint32((uint32_t)st->st_atim.tv_nsec);
  return mk_pair(
      lean_box((unsigned)kind),
      mk_pair(
          lean_box_uint64(sz),
          mk_pair(
              lean_box_uint32(mode),
              mk_pair(
                  lean_box_uint64((uint64_t)st->st_ino),
                  mk_pair(
                      lean_box_uint64((uint64_t)st->st_dev),
                      mk_pair(
                          lean_box_uint64((uint64_t)st->st_nlink),
                          mk_pair(m_sec, mk_pair(m_nsec, mk_pair(a_sec, a_nsec)))))))));
}

LEAN_EXPORT lean_obj_res leanswe_sys_openat(
    b_lean_obj_arg dir_opt, b_lean_obj_arg path_ba, uint32_t flags_bits, uint32_t mode) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return leanswe_mk_errno(perr);
  LeanFdBox *dbox = NULL;
  int dfd = AT_FDCWD;
  int dperr = pin_opt_dir(dir_opt, &dbox, &dfd);
  if (dperr != 0) { free(heap); return leanswe_mk_errno(dperr); }
  int fd = openat(dfd, cpath, decode_open_flags(flags_bits), (mode_t)(mode & 07777u));
  int err = errno;
  if (dbox != NULL) leanswe_fd_box_unpin(dbox);
  free(heap);
  if (fd < 0) return leanswe_mk_errno(err);
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_sys_openat2(
    b_lean_obj_arg dir_opt, b_lean_obj_arg path_ba, uint32_t flags_bits, uint32_t mode, uint64_t resolve_bits) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return leanswe_mk_errno(perr);
  LeanFdBox *dbox = NULL;
  int dfd = AT_FDCWD;
  int dperr = pin_opt_dir(dir_opt, &dbox, &dfd);
  if (dperr != 0) { free(heap); return leanswe_mk_errno(dperr); }
  struct open_how how;
  memset(&how, 0, sizeof(how));
  how.flags = (uint64_t)(unsigned int)decode_open_flags(flags_bits);
  how.mode = (uint64_t)mode;
  how.resolve = decode_resolve_flags(resolve_bits);
  long fd = syscall(SYS_openat2, (long)dfd, cpath, &how, (unsigned long)sizeof(how));
  int err = errno;
  if (dbox != NULL) leanswe_fd_box_unpin(dbox);
  free(heap);
  if (fd < 0) return leanswe_mk_errno(err);
  lean_obj_res obj = leanswe_mk_fd_obj((int)fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_sys_close(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int err = leanswe_fd_box_close(box);
  if (err != 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_read(b_lean_obj_arg fd_obj, uint32_t max_bytes) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  char *buf = alloc_read_buf(&max_bytes);
  if (buf == NULL) { leanswe_fd_box_unpin(box); return leanswe_mk_errno(ENOMEM); }
  ssize_t n = read(fd, buf, (size_t)max_bytes);
  int err = errno;
  leanswe_fd_box_unpin(box);
  return finish_read_buf(buf, n, err);
}

LEAN_EXPORT lean_obj_res leanswe_sys_write(b_lean_obj_arg fd_obj, b_lean_obj_arg ba) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  size_t len = lean_sarray_size(ba);
  const void *ptr = (len == 0) ? (const void *)"" : (const void *)lean_sarray_cptr(ba);
  ssize_t n = write(fd, ptr, len);
  int err = errno;
  leanswe_fd_box_unpin(box);
  if (n < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box_uint32((uint32_t)n));
}

LEAN_EXPORT lean_obj_res leanswe_sys_fstat(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  struct stat st;
  int rc = fstat(fd, &st);
  int err = errno;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(mk_raw_stat_tuple(&st));
}

LEAN_EXPORT lean_obj_res leanswe_sys_fstatat(
    b_lean_obj_arg dir_opt, b_lean_obj_arg path_ba, uint32_t flags_bits) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return leanswe_mk_errno(perr);
  LeanFdBox *dbox = NULL;
  int dfd = AT_FDCWD;
  int dperr = pin_opt_dir(dir_opt, &dbox, &dfd);
  if (dperr != 0) { free(heap); return leanswe_mk_errno(dperr); }
  struct stat st;
  int rc = fstatat(dfd, cpath, &st, decode_at_flags(flags_bits));
  int err = errno;
  if (dbox != NULL) leanswe_fd_box_unpin(dbox);
  free(heap);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(mk_raw_stat_tuple(&st));
}

LEAN_EXPORT lean_obj_res leanswe_sys_faccessat(
    b_lean_obj_arg dir_opt, b_lean_obj_arg path_ba, uint32_t mask_bits, uint32_t flags_bits) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return leanswe_mk_errno(perr);
  LeanFdBox *dbox = NULL;
  int dfd = AT_FDCWD;
  int dperr = pin_opt_dir(dir_opt, &dbox, &dfd);
  if (dperr != 0) { free(heap); return leanswe_mk_errno(dperr); }
  long rc = syscall(SYS_faccessat2, (long)dfd, cpath, (long)decode_access_mask(mask_bits), (long)decode_at_flags(flags_bits));
  int err = errno;
  if (dbox != NULL) leanswe_fd_box_unpin(dbox);
  free(heap);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_mkdirat(
    b_lean_obj_arg dir_opt, b_lean_obj_arg path_ba, uint32_t mode) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return leanswe_mk_errno(perr);
  LeanFdBox *dbox = NULL;
  int dfd = AT_FDCWD;
  int dperr = pin_opt_dir(dir_opt, &dbox, &dfd);
  if (dperr != 0) { free(heap); return leanswe_mk_errno(dperr); }
  int rc = mkdirat(dfd, cpath, (mode_t)(mode & 07777u));
  int err = errno;
  if (dbox != NULL) leanswe_fd_box_unpin(dbox);
  free(heap);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_unlinkat(
    b_lean_obj_arg dir_opt, b_lean_obj_arg path_ba, uint8_t remove_dir) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return leanswe_mk_errno(perr);
  LeanFdBox *dbox = NULL;
  int dfd = AT_FDCWD;
  int dperr = pin_opt_dir(dir_opt, &dbox, &dfd);
  if (dperr != 0) { free(heap); return leanswe_mk_errno(dperr); }
  int rc = unlinkat(dfd, cpath, remove_dir ? AT_REMOVEDIR : 0);
  int err = errno;
  if (dbox != NULL) leanswe_fd_box_unpin(dbox);
  free(heap);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_renameat2(
    b_lean_obj_arg old_dir_opt, b_lean_obj_arg old_ba,
    b_lean_obj_arg new_dir_opt, b_lean_obj_arg new_ba,
    uint32_t flags_bits) {
  char osbuf[4096], nsbuf[4096];
  const char *ocpath = NULL, *ncpath = NULL;
  char *oheap = NULL, *nheap = NULL;
  int perr1 = ba_to_cstr(old_ba, osbuf, sizeof(osbuf), &ocpath, &oheap);
  if (perr1 != 0) return leanswe_mk_errno(perr1);
  int perr2 = ba_to_cstr(new_ba, nsbuf, sizeof(nsbuf), &ncpath, &nheap);
  if (perr2 != 0) { free(oheap); return leanswe_mk_errno(perr2); }
  LeanFdBox *obox = NULL, *nbox = NULL;
  int odfd = AT_FDCWD, ndfd = AT_FDCWD;
  int dperr = pin_opt_dir(old_dir_opt, &obox, &odfd);
  if (dperr == 0) dperr = pin_opt_dir(new_dir_opt, &nbox, &ndfd);
  if (dperr != 0) {
    if (obox != NULL) leanswe_fd_box_unpin(obox);
    free(oheap); free(nheap);
    return leanswe_mk_errno(dperr);
  }
  long rc = syscall(SYS_renameat2, (long)odfd, ocpath, (long)ndfd, ncpath, (unsigned long)decode_rename_flags(flags_bits));
  int err = errno;
  if (nbox != NULL) leanswe_fd_box_unpin(nbox);
  if (obox != NULL) leanswe_fd_box_unpin(obox);
  free(oheap);
  free(nheap);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_symlinkat(
    b_lean_obj_arg target_ba, b_lean_obj_arg dir_opt, b_lean_obj_arg link_ba) {
  char tsbuf[4096], lsbuf[4096];
  const char *tcpath = NULL, *lcpath = NULL;
  char *theap = NULL, *lheap = NULL;
  int perr1 = ba_to_cstr(target_ba, tsbuf, sizeof(tsbuf), &tcpath, &theap);
  if (perr1 != 0) return leanswe_mk_errno(perr1);
  int perr2 = ba_to_cstr(link_ba, lsbuf, sizeof(lsbuf), &lcpath, &lheap);
  if (perr2 != 0) { free(theap); return leanswe_mk_errno(perr2); }
  LeanFdBox *dbox = NULL;
  int dfd = AT_FDCWD;
  int dperr = pin_opt_dir(dir_opt, &dbox, &dfd);
  if (dperr != 0) { free(theap); free(lheap); return leanswe_mk_errno(dperr); }
  int rc = symlinkat(tcpath, dfd, lcpath);
  int err = errno;
  if (dbox != NULL) leanswe_fd_box_unpin(dbox);
  free(theap); free(lheap);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_readlinkat(
    b_lean_obj_arg dir_opt, b_lean_obj_arg path_ba, uint32_t cap) {
  char sbuf[4096]; const char *cpath = NULL; char *heap = NULL;
  int perr = ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return leanswe_mk_errno(perr);
  LeanFdBox *dbox = NULL; int dfd = AT_FDCWD;
  int dperr = pin_opt_dir(dir_opt, &dbox, &dfd);
  if (dperr != 0) { free(heap); return leanswe_mk_errno(dperr); }
  char *buf = alloc_read_buf(&cap);
  if (buf == NULL) {
    if (dbox != NULL) leanswe_fd_box_unpin(dbox);
    free(heap); return leanswe_mk_errno(ENOMEM);
  }
  ssize_t n = readlinkat(dfd, cpath, buf, (size_t)cap);
  int err = errno;
  if (dbox != NULL) leanswe_fd_box_unpin(dbox);
  free(heap);
  return finish_read_buf(buf, n, err);
}

LEAN_EXPORT lean_obj_res leanswe_sys_getdents64(b_lean_obj_arg fd_obj, uint32_t buf_bytes) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  char *buf = alloc_read_buf(&buf_bytes);
  if (buf == NULL) { leanswe_fd_box_unpin(box); return leanswe_mk_errno(ENOMEM); }
  long n = syscall(SYS_getdents64, (long)fd, buf, (unsigned long)buf_bytes);
  int err = errno;
  leanswe_fd_box_unpin(box);
  return finish_read_buf(buf, (ssize_t)n, err);
}

LEAN_EXPORT lean_obj_res leanswe_sys_fchmodat(
    b_lean_obj_arg dir_opt, b_lean_obj_arg path_ba, uint32_t mode) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return leanswe_mk_errno(perr);
  LeanFdBox *dbox = NULL;
  int dfd = AT_FDCWD;
  int dperr = pin_opt_dir(dir_opt, &dbox, &dfd);
  if (dperr != 0) { free(heap); return leanswe_mk_errno(dperr); }
  int rc = fchmodat(dfd, cpath, (mode_t)(mode & 07777u), 0);
  int err = errno;
  if (dbox != NULL) leanswe_fd_box_unpin(dbox);
  free(heap);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_fchmod(b_lean_obj_arg fd_obj, uint32_t mode) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int rc = fchmod(fd, (mode_t)(mode & 07777u));
  int err = errno;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_flock(b_lean_obj_arg fd_obj, uint32_t op_bits) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int rc = flock(fd, decode_flock_op(op_bits));
  int err = errno;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

static uint32_t encode_getfl_bits(int rc) {
  int am = rc & O_ACCMODE;
  uint32_t acc = (am == O_RDONLY) ? 0u : ((am == O_WRONLY) ? 1u : ((am == O_RDWR) ? 2u : 3u));
  return acc | ((rc & O_APPEND) ? (1u << 5) : 0u) | ((rc & O_NONBLOCK) ? (1u << 8) : 0u);
}

static int run_fcntl_seal(int fd, uint32_t cmd_tag, uint32_t arg, uint32_t *out) {
  int rc = -1;
  if (cmd_tag == 4u) rc = fcntl(fd, F_ADD_SEALS, (unsigned long)arg);
  else if (cmd_tag == 5u) rc = fcntl(fd, F_GET_SEALS);
  else errno = EINVAL;
  if (rc >= 0) *out = (uint32_t)rc;
  return rc;
}

static int run_fcntl_cmd(int fd, uint32_t cmd_tag, uint32_t arg, uint32_t *out) {
  int rc = -1;
  switch (cmd_tag) {
    case 0u:
      rc = fcntl(fd, F_GETFL);
      if (rc >= 0) *out = encode_getfl_bits(rc);
      return rc;
    case 1u: {
      int fl = ((arg & 1u) ? O_NONBLOCK : 0) | ((arg & 2u) ? O_APPEND : 0);
      return fcntl(fd, F_SETFL, fl);
    }
    case 2u:
      rc = fcntl(fd, F_GETFD);
      if (rc >= 0) *out = (rc & FD_CLOEXEC) ? 1u : 0u;
      return rc;
    case 3u:
      return fcntl(fd, F_SETFD, (arg & 1u) ? FD_CLOEXEC : 0);
    default:
      return run_fcntl_seal(fd, cmd_tag, arg, out);
  }
}

LEAN_EXPORT lean_obj_res leanswe_sys_fcntl(
    b_lean_obj_arg fd_obj, uint32_t cmd_tag, uint32_t arg) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  uint32_t out = 0;
  int rc = run_fcntl_cmd(fd, cmd_tag, arg, &out);
  int err = errno;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box_uint32(out));
}

LEAN_EXPORT lean_obj_res leanswe_sys_fsync(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int rc = fsync(fd);
  int err = errno;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_getcwd(uint32_t cap) {
  char *buf = alloc_read_buf(&cap);
  if (buf == NULL) return leanswe_mk_errno(ENOMEM);
  long n = syscall(SYS_getcwd, buf, (unsigned long)cap);
  if (n <= 0) {
    int err = (n < 0) ? errno : EINVAL;
    free(buf);
    return leanswe_mk_errno(err);
  }
  return finish_read_buf(buf, (ssize_t)(n - 1), 0);
}

static int decode_seek_whence(uint32_t w) {
  if (w == 0u) return SEEK_SET;
  if (w == 1u) return SEEK_CUR;
  if (w == 2u) return SEEK_END;
  return -1;
}

LEAN_EXPORT lean_obj_res leanswe_sys_lseek(
    b_lean_obj_arg fd_obj, uint64_t offset_bits, uint32_t whence_tag) {
  int whence = decode_seek_whence(whence_tag);
  if (whence < 0) return leanswe_mk_errno(EINVAL);
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  off_t rc = lseek(fd, (off_t)(int64_t)offset_bits, whence);
  int err = errno;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box_uint64((uint64_t)rc));
}

static int check_proc_fd_fs(void) {
  struct statfs pfs;
  if (statfs("/proc/", &pfs) < 0) return errno;
  if ((unsigned long)pfs.f_type != 0x9fa0ul) return ENOENT;
  struct statx psx, fdsx;
  memset(&psx, 0, sizeof(psx)); memset(&fdsx, 0, sizeof(fdsx));
  if (syscall(SYS_statx, (long)AT_FDCWD, "/proc/", 0L, (unsigned long)STATX_MNT_ID, &psx) < 0) return errno;
  if (syscall(SYS_statx, (long)AT_FDCWD, "/proc/thread-self/fd/", 0L, (unsigned long)STATX_MNT_ID, &fdsx) < 0) return errno;
  if (psx.stx_mnt_id != fdsx.stx_mnt_id) return ENOENT;
  return 0;
}

static int verify_reopen_inode(int fd, int new_fd) {
  struct statx s0, s1;
  memset(&s0, 0, sizeof(s0)); memset(&s1, 0, sizeof(s1));
  long fl = (long)(AT_EMPTY_PATH | AT_SYMLINK_NOFOLLOW);
  if (syscall(SYS_statx, (long)fd, "", fl, (unsigned long)STATX_INO, &s0) < 0) return errno;
  if (syscall(SYS_statx, (long)new_fd, "", fl, (unsigned long)STATX_INO, &s1) < 0) return errno;
  if (!(s0.stx_mask & STATX_INO) || !(s1.stx_mask & STATX_INO) ||
      s0.stx_ino != s1.stx_ino || s0.stx_dev_major != s1.stx_dev_major || s0.stx_dev_minor != s1.stx_dev_minor)
    return ENOENT;
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_sys_reopen_readonly(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int new_fd = -1;
  int err = check_proc_fd_fs();
  if (err == 0) {
    char path[48];
    snprintf(path, sizeof(path), "/proc/thread-self/fd/%d", fd);
    new_fd = open(path, O_RDONLY | O_CLOEXEC | O_NONBLOCK | O_NOCTTY);
    err = errno;
    if (new_fd >= 0) { int verr = verify_reopen_inode(fd, new_fd); if (verr != 0) { close(new_fd); new_fd = -1; err = verr; } }
  }
  leanswe_fd_box_unpin(box);
  if (new_fd < 0) return leanswe_mk_errno(err);
  lean_obj_res obj = leanswe_mk_fd_obj(new_fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_sys_dup_stdio(uint32_t slot) {
  if (slot > 2u) return leanswe_mk_errno(EINVAL);
  int new_fd = fcntl((int)slot, F_DUPFD_CLOEXEC, 3);
  if (new_fd < 0) {
    return leanswe_mk_errno(errno);
  }
  lean_obj_res obj = leanswe_mk_fd_obj(new_fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}
