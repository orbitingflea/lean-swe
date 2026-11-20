#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "fuzz_env.c supports only Linux on x86_64 or aarch64"
#endif

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/sysmacros.h>
#include <sys/uio.h>
#include <sys/un.h>
#include <sys/vfs.h>
#include <sys/wait.h>
#include <unistd.h>
#include <lean/lean.h>
#include "fd_box.h"

static int fuzz_ba_to_cstr(b_lean_obj_arg ba, char *stack_buf, size_t cap,
                           const char **out_ptr, char **out_heap) {
  size_t len = lean_sarray_size(ba);
  const uint8_t *src = lean_sarray_cptr(ba);
  if (len > 0 && memchr(src, 0, len) != NULL) {
    return EINVAL;
  }
  if (len < cap) {
    if (len > 0) memcpy(stack_buf, src, len);
    stack_buf[len] = '\0';
    *out_ptr = stack_buf;
    *out_heap = NULL;
    return 0;
  }
  char *heap = (char *)malloc(len + 1);
  if (heap == NULL) return ENOMEM;
  memcpy(heap, src, len);
  heap[len] = '\0';
  *out_ptr = heap;
  *out_heap = heap;
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_mkfifo(b_lean_obj_arg path_ba, uint32_t mode) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)perr));
  uint32_t res = 0;
  if (mkfifo(cpath, (mode_t)mode) != 0) res = (uint32_t)errno;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint32(res));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_mksock(b_lean_obj_arg path_ba) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)perr));
  struct sockaddr_un addr;
  memset(&addr, 0, sizeof(addr));
  addr.sun_family = AF_UNIX;
  size_t plen = strlen(cpath);
  if (plen >= sizeof(addr.sun_path)) {
    if (heap != NULL) free(heap);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)ENAMETOOLONG));
  }
  memcpy(addr.sun_path, cpath, plen + 1);
  if (heap != NULL) free(heap);
  int fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
  if (fd < 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)errno));
  uint32_t res = 0;
  if (bind(fd, (const struct sockaddr *)&addr, (socklen_t)sizeof(addr)) != 0) {
    res = (uint32_t)errno;
  }
  close(fd);
  return lean_io_result_mk_ok(lean_box_uint32(res));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_link(b_lean_obj_arg old_ba, b_lean_obj_arg new_ba) {
  char obuf[4096], nbuf[4096];
  const char *oldp = NULL, *newp = NULL;
  char *oheap = NULL, *nheap = NULL;
  int perr = fuzz_ba_to_cstr(old_ba, obuf, sizeof(obuf), &oldp, &oheap);
  if (perr != 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)perr));
  perr = fuzz_ba_to_cstr(new_ba, nbuf, sizeof(nbuf), &newp, &nheap);
  if (perr != 0) {
    if (oheap != NULL) free(oheap);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)perr));
  }
  uint32_t res = 0;
  if (link(oldp, newp) != 0) res = (uint32_t)errno;
  if (oheap != NULL) free(oheap);
  if (nheap != NULL) free(nheap);
  return lean_io_result_mk_ok(lean_box_uint32(res));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_umask(uint32_t mask) {
  mode_t prev = umask((mode_t)(mask & 0777u));
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)prev));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_chmod(b_lean_obj_arg path_ba, uint32_t mode) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)perr));
  uint32_t res = 0;
  if (chmod(cpath, (mode_t)mode) != 0) res = (uint32_t)errno;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint32(res));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_stat_dev(b_lean_obj_arg path_ba) {
  char sbuf[4096]; const char *cpath = NULL; char *heap = NULL;
  if (fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap) != 0) return lean_io_result_mk_ok(lean_box_uint64(0u));
  struct stat st; uint64_t dev = (lstat(cpath, &st) == 0) ? (uint64_t)st.st_dev : 0u;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint64(dev));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_stat_ino(b_lean_obj_arg path_ba) {
  char sbuf[4096]; const char *cpath = NULL; char *heap = NULL;
  if (fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap) != 0) return lean_io_result_mk_ok(lean_box_uint64(0u));
  struct stat st; uint64_t ino = (lstat(cpath, &st) == 0) ? (uint64_t)st.st_ino : 0u;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint64(ino));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_stat_mode(b_lean_obj_arg path_ba) {
  char sbuf[4096]; const char *cpath = NULL; char *heap = NULL;
  if (fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap) != 0) return lean_io_result_mk_ok(lean_box_uint32(0u));
  struct stat st; uint32_t mode = (lstat(cpath, &st) == 0) ? (uint32_t)(st.st_mode & 07777u) : 0u;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint32(mode));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_ignore_sigpipe(void) { signal(SIGPIPE, SIG_IGN); return lean_io_result_mk_ok(lean_box(0)); }
static uint32_t fuzz_chr_kind(dev_t rdev) {
  unsigned int maj = major(rdev), min = minor(rdev);
  if (maj != 1u) return 30;
  return (min == 3u) ? 31 : (min == 5u) ? 32 : (min == 7u) ? 33 : 30;
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_fd_kind(uint32_t fd) {
  struct stat st; uint32_t kind = 0;
  if (fstat((int)fd, &st) == 0) {
    if (S_ISREG(st.st_mode)) kind = 1; else if (S_ISDIR(st.st_mode)) kind = 2;
    else if (S_ISCHR(st.st_mode)) kind = fuzz_chr_kind(st.st_rdev);
    else if (S_ISFIFO(st.st_mode)) kind = 4; else if (S_ISSOCK(st.st_mode)) kind = 5; else kind = 6;
  }
  return lean_io_result_mk_ok(lean_box_uint32(kind));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_supports_seals(b_lean_obj_arg path_ba) {
  char sbuf[4096]; const char *cpath = NULL; char *heap = NULL;
  if (fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap) != 0) return lean_io_result_mk_ok(lean_box(0u));
  struct statfs sfs; uint8_t ok = (statfs(cpath, &sfs) == 0 && (uint64_t)sfs.f_type == 0x01021994ULL) ? 1 : 0;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box((unsigned)ok));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_get_rlimit_fsize_cur(void) {
  struct rlimit rl; uint64_t v = (uint64_t)RLIM_INFINITY;
  if (getrlimit(RLIMIT_FSIZE, &rl) == 0) v = (uint64_t)rl.rlim_cur;
  return lean_io_result_mk_ok(lean_box_uint64(v));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_get_rlimit_fsize_max(void) {
  struct rlimit rl; uint64_t v = (uint64_t)RLIM_INFINITY;
  if (getrlimit(RLIMIT_FSIZE, &rl) == 0) v = (uint64_t)rl.rlim_max;
  return lean_io_result_mk_ok(lean_box_uint64(v));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_set_rlimit_fsize(uint64_t cur, uint64_t max_lim, uint8_t ignore_sig) {
  signal(SIGXFSZ, ignore_sig ? SIG_IGN : SIG_DFL);
  struct rlimit rl; rl.rlim_cur = (rlim_t)cur; rl.rlim_max = (rlim_t)max_lim;
  return lean_io_result_mk_ok(lean_box_uint32(setrlimit(RLIMIT_FSIZE, &rl) != 0 ? (uint32_t)errno : 0u));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_get_rlimit_nofile_cur(void) {
  struct rlimit rl; uint64_t v = (getrlimit(RLIMIT_NOFILE, &rl) == 0) ? (uint64_t)rl.rlim_cur : 0ULL;
  return lean_io_result_mk_ok(lean_box_uint64(v));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_get_rlimit_nofile_max(void) {
  struct rlimit rl; uint64_t v = (getrlimit(RLIMIT_NOFILE, &rl) == 0) ? (uint64_t)rl.rlim_max : 0ULL;
  return lean_io_result_mk_ok(lean_box_uint64(v));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_set_rlimit_nofile(uint64_t cur, uint64_t max_lim) {
  struct rlimit rl;
  if (getrlimit(RLIMIT_NOFILE, &rl) != 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)errno));
  rlim_t target_max = (max_lim == 0) ? rl.rlim_max : (rlim_t)max_lim;
  if (target_max > rl.rlim_max) target_max = rl.rlim_max;
  rlim_t target_cur = (rlim_t)cur;
  if (target_cur > target_max) target_cur = target_max;
  rl.rlim_cur = target_cur; rl.rlim_max = target_max;
  return lean_io_result_mk_ok(lean_box_uint32(setrlimit(RLIMIT_NOFILE, &rl) != 0 ? (uint32_t)errno : 0u));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_get_pid(void) { return lean_io_result_mk_ok(lean_box_uint32((uint32_t)getpid())); }
LEAN_EXPORT lean_obj_res leanswe_fuzz_get_uid(void) { return lean_io_result_mk_ok(lean_box_uint32((uint32_t)geteuid())); }

LEAN_EXPORT lean_obj_res leanswe_fuzz_stat_uid_gid(b_lean_obj_arg path_ba) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return lean_io_result_mk_ok(lean_box_uint64(0xffffffffffffffffULL));
  struct stat st;
  uint64_t ug = 0xffffffffffffffffULL;
  if (lstat(cpath, &st) == 0) ug = (uint64_t)(uint32_t)st.st_uid | (((uint64_t)(uint32_t)st.st_gid) << 32);
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint64(ug));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_stat_follow_uid_gid(b_lean_obj_arg path_ba) {
  char sbuf[4096]; const char *cpath = NULL; char *heap = NULL;
  if (fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap) != 0)
    return lean_io_result_mk_ok(lean_box_uint64(0xffffffffffffffffULL));
  struct stat st; uint64_t ug = 0xffffffffffffffffULL;
  if (stat(cpath, &st) == 0) ug = (uint64_t)(uint32_t)st.st_uid | (((uint64_t)(uint32_t)st.st_gid) << 32);
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint64(ug));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_statfs_type(b_lean_obj_arg path_ba) {
  char sbuf[4096]; const char *cpath = NULL; char *heap = NULL;
  if (fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap) != 0) return lean_io_result_mk_ok(lean_box_uint64(0u));
  struct statfs sfs; uint64_t ftype = (statfs(cpath, &sfs) == 0) ? (uint64_t)sfs.f_type : 0u;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint64(ftype));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_statfs_ro(b_lean_obj_arg path_ba) {
  char sbuf[4096]; const char *cpath = NULL; char *heap = NULL;
  if (fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap) != 0) return lean_io_result_mk_ok(lean_box(0u));
  struct statfs sfs; uint8_t ro = (statfs(cpath, &sfs) == 0 && (sfs.f_flags & 1u) != 0) ? 1 : 0;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box((unsigned)ro));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_stat_mnt_id(b_lean_obj_arg path_ba) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return lean_io_result_mk_ok(lean_box_uint64(0u));
  struct statx stx;
  memset(&stx, 0, sizeof(stx));
  uint64_t mid = 0;
#if defined(__x86_64__)
  long sx_nr = 332;
#else
  long sx_nr = 291;
#endif
  if (syscall(sx_nr, (long)AT_FDCWD, cpath, (long)AT_SYMLINK_NOFOLLOW, (unsigned long)STATX_MNT_ID, &stx) == 0 && (stx.stx_mask & STATX_MNT_ID) != 0)
    mid = (uint64_t)stx.stx_mnt_id;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint64(mid));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_fd_mode(uint32_t fd) {
  struct stat st; uint32_t m = 0;
  if (fstat((int)fd, &st) == 0) m = (uint32_t)st.st_mode;
  return lean_io_result_mk_ok(lean_box_uint32(m));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_fd_uid_gid(uint32_t fd) {
  struct stat st; uint64_t ug = 0xffffffffffffffffULL;
  if (fstat((int)fd, &st) == 0) ug = (uint64_t)(uint32_t)st.st_uid | (((uint64_t)(uint32_t)st.st_gid) << 32);
  return lean_io_result_mk_ok(lean_box_uint64(ug));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_fd_dev(uint32_t fd) {
  struct stat st; uint64_t dev = 0;
  if (fstat((int)fd, &st) == 0) dev = (uint64_t)st.st_dev;
  return lean_io_result_mk_ok(lean_box_uint64(dev));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_fd_ino(uint32_t fd) {
  struct stat st; uint64_t ino = 0;
  if (fstat((int)fd, &st) == 0) ino = (uint64_t)st.st_ino;
  return lean_io_result_mk_ok(lean_box_uint64(ino));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_chroot(b_lean_obj_arg path_ba) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)perr));
  uint32_t res = 0;
  if (chroot(cpath) != 0) res = (uint32_t)errno;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint32(res));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_rmdir(b_lean_obj_arg path_ba) {
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = fuzz_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)perr));
  uint32_t res = 0;
  if (rmdir(cpath) != 0) res = (uint32_t)errno;
  if (heap != NULL) free(heap);
  return lean_io_result_mk_ok(lean_box_uint32(res));
}

LEAN_EXPORT lean_obj_res leanswe_files_fuzz_install_seccomp_errno(
    uint32_t nr1, uint32_t err1, uint32_t nr2, uint32_t err2,
    uint32_t nr3, uint32_t err3) {
  if ((nr1 != 0xffffffffu && (err1 & 0x0fffu) == 0u) ||
      (nr2 != 0xffffffffu && (err2 & 0x0fffu) == 0u) ||
      (nr3 != 0xffffffffu && (err3 & 0x0fffu) == 0u))
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)EINVAL));
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0)
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)errno));
  struct sock_filter filter[] = {
    { (uint16_t)(BPF_LD | BPF_W | BPF_ABS), 0, 0, (uint32_t)offsetof(struct seccomp_data, nr) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 0, 1, nr1 },
    { (uint16_t)(BPF_RET | BPF_K), 0, 0, SECCOMP_RET_ERRNO | (err1 & 0x0fffu) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 0, 1, nr2 },
    { (uint16_t)(BPF_RET | BPF_K), 0, 0, SECCOMP_RET_ERRNO | (err2 & 0x0fffu) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 0, 1, nr3 },
    { (uint16_t)(BPF_RET | BPF_K), 0, 0, SECCOMP_RET_ERRNO | (err3 & 0x0fffu) },
    { (uint16_t)(BPF_RET | BPF_K), 0, 0, SECCOMP_RET_ALLOW },
  };
  struct sock_fprog prog = {
    .len = (unsigned short)(sizeof(filter) / sizeof(filter[0])),
    .filter = filter,
  };
  if (prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog) != 0)
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)errno));
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_open_memfd(void) {
  long r = syscall((long)__NR_memfd_create, "lswf_mfd", (unsigned long)3u);
  if (r < 0) return leanswe_mk_errno(errno);
  lean_obj_res obj = leanswe_mk_fd_obj((int)r);
  return obj ? leanswe_mk_ok(obj) : leanswe_mk_errno(ENOMEM);
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_exit_immediate(uint32_t code) {
  _exit((int)code);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_nr_getcwd(void) { return lean_io_result_mk_ok(lean_box_uint32((uint32_t)__NR_getcwd)); }
LEAN_EXPORT lean_obj_res leanswe_fuzz_nr_fsync(void) { return lean_io_result_mk_ok(lean_box_uint32((uint32_t)__NR_fsync)); }
LEAN_EXPORT lean_obj_res leanswe_fuzz_nr_faccessat2(void) { return lean_io_result_mk_ok(lean_box_uint32(439u)); }
LEAN_EXPORT lean_obj_res leanswe_fuzz_nr_close(void) { return lean_io_result_mk_ok(lean_box_uint32((uint32_t)__NR_close)); }

LEAN_EXPORT lean_obj_res leanswe_fuzz_write_fd_chunk(uint32_t fd, b_lean_obj_arg ba, size_t off) {
  size_t len = lean_sarray_size(ba);
  size_t rem = (off < len) ? (len - off) : 0u;
  struct iovec iov = { .iov_base = (void *)(lean_sarray_cptr(ba) + off), .iov_len = rem };
  long r = syscall(SYS_writev, (long)(int)fd, &iov, (long)1);
  if (r >= 0) {
    lean_obj_res ok = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(ok, 0, lean_box_usize((size_t)r));
    return lean_io_result_mk_ok(ok);
  }
  lean_obj_res er = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(er, 0, lean_box_uint32((uint32_t)errno));
  return lean_io_result_mk_ok(er);
}

LEAN_EXPORT lean_obj_res leanswe_fuzz_fchdir(b_lean_obj_arg rfd) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(rfd);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)perr));
  uint32_t res = 0;
  if (fchdir(fd) != 0) res = (uint32_t)errno;
  leanswe_fd_box_unpin(box);
  return lean_io_result_mk_ok(lean_box_uint32(res));
}

#ifdef __NR_fstat
#define LEANSWE_NR_FSTAT __NR_fstat
#else
#define LEANSWE_NR_FSTAT __NR_newfstatat
#endif
#ifdef __NR_newfstatat
#define LEANSWE_NR_FSTATAT __NR_newfstatat
#else
#define LEANSWE_NR_FSTATAT __NR_fstatat64
#endif
#ifndef __NR_openat2
#define __NR_openat2 437
#endif
#ifndef __NR_renameat2
#if defined(__x86_64__)
#define __NR_renameat2 316
#else
#define __NR_renameat2 276
#endif
#endif

static const uint32_t g_leanswe_files_nrs[21] = {
  (uint32_t)__NR_openat, (uint32_t)__NR_openat2, (uint32_t)__NR_close, (uint32_t)__NR_read, (uint32_t)__NR_write, (uint32_t)LEANSWE_NR_FSTAT, (uint32_t)LEANSWE_NR_FSTATAT, 439u, (uint32_t)__NR_mkdirat, (uint32_t)__NR_unlinkat,
  (uint32_t)__NR_renameat2, (uint32_t)__NR_symlinkat, (uint32_t)__NR_readlinkat, (uint32_t)__NR_getdents64, (uint32_t)__NR_fchmodat, (uint32_t)__NR_fchmod, (uint32_t)__NR_flock, (uint32_t)__NR_fcntl, (uint32_t)__NR_fsync, (uint32_t)__NR_getcwd, (uint32_t)__NR_lseek
};

LEAN_EXPORT lean_obj_res leanswe_fuzz_nr_for_slot(uint32_t slot) {
  uint32_t nr = (slot < 21u) ? g_leanswe_files_nrs[slot] : 0xffffffffu;
  return lean_io_result_mk_ok(lean_box_uint32(nr));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_raw_fd_num(b_lean_obj_arg rfd) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(rfd); int fd = -1;
  int pinned = (leanswe_fd_box_pin(box, &fd) == 0);
  uint32_t res = (pinned && fd >= 0) ? (uint32_t)fd : 0xffffffffu;
  if (pinned) leanswe_fd_box_unpin(box);
  return lean_io_result_mk_ok(lean_box_uint32(res));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_pipe(void) {
  int fds[2];
  uint64_t r = (pipe2(fds, O_CLOEXEC) == 0) ? ((uint64_t)(uint32_t)fds[0] | (((uint64_t)(uint32_t)fds[1]) << 32)) : 0xffffffffffffffffULL;
  return lean_io_result_mk_ok(lean_box_uint64(r));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_close_raw_fd(uint32_t fd) {
  return lean_io_result_mk_ok(lean_box_uint32(close((int)fd) == 0 ? 0u : (uint32_t)errno));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_read_fd_chunk(uint32_t fd) {
  char *buf = (char *)malloc(65536);
  if (!buf) { lean_obj_res r = lean_alloc_ctor(0, 1, 0); lean_ctor_set(r, 0, lean_box_uint32((uint32_t)ENOMEM)); return lean_io_result_mk_ok(r); }
  ssize_t n = read((int)fd, buf, 65536);
  if (n >= 0) {
    lean_obj_res ba = lean_alloc_sarray(1, (size_t)n, (size_t)n);
    if (n > 0) memcpy(lean_sarray_cptr(ba), buf, (size_t)n);
    free(buf); lean_obj_res r = lean_alloc_ctor(1, 1, 0); lean_ctor_set(r, 0, ba); return lean_io_result_mk_ok(r);
  }
  uint32_t err = (uint32_t)errno; free(buf);
  lean_obj_res r = lean_alloc_ctor(0, 1, 0); lean_ctor_set(r, 0, lean_box_uint32(err)); return lean_io_result_mk_ok(r);
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_fork_pid(void) {
  fflush(NULL); pid_t p = fork();
  return lean_io_result_mk_ok(lean_box_uint32(p < 0 ? 0xffffffffu : (uint32_t)p));
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_wait_pid_once(uint32_t pid) {
  int st = 0;
  if (waitpid((pid_t)pid, &st, 0) < 0)
    return lean_io_result_mk_ok(lean_box_uint32((errno == EINTR) ? 9996u : 9998u));
  if (WIFSIGNALED(st)) return lean_io_result_mk_ok(lean_box_uint32(1000u + (uint32_t)WTERMSIG(st)));
  return lean_io_result_mk_ok(lean_box_uint32(WIFEXITED(st) ? 2000u + (uint32_t)WEXITSTATUS(st) : 9997u));
}
static void pin_one_stdio(int s) {
  struct statfs sfs;
  if (fstatfs(s, &sfs) == 0 || errno != EBADF) return;
  int d = open("/dev/null", O_RDWR);
  if (d >= 0 && d != s) { (void)dup2(d, s); close(d); }
}
LEAN_EXPORT lean_obj_res leanswe_fuzz_pin_closed_stdio(void) {
  pin_one_stdio(0); pin_one_stdio(1); pin_one_stdio(2);
  return lean_io_result_mk_ok(lean_box(0));
}
