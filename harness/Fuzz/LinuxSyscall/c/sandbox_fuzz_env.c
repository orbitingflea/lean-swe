#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "sandbox_fuzz_env.c supports only Linux on x86_64 or aarch64"
#endif

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/filter.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>
#include "fd_box.h"

typedef struct { int install; int ready_wfd; int stop_rfd; } SbxSyncArgs;
static pthread_mutex_t g_sbx_sync_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_t g_sbx_sync_tid;
static int g_sbx_sync_active = 0;
static int g_sbx_sync_stop_wfd = -1;
static int g_sbx_sync_stop_rfd = -1;

static int sbx_env_ba_to_cstr(b_lean_obj_arg ba, char *stack_buf, size_t cap,
                              const char **out_ptr, char **out_heap) {
  size_t len = lean_sarray_size(ba);
  const uint8_t *src = lean_sarray_cptr(ba);
  if (len > 0 && memchr(src, 0, len) != NULL) {
    return EINVAL;
  }
  if (len < cap) {
    if (len > 0) {
      memcpy(stack_buf, src, len);
    }
    stack_buf[len] = '\0';
    *out_ptr = stack_buf;
    *out_heap = NULL;
    return 0;
  }
  char *heap = (char *)malloc(len + 1);
  if (heap == NULL) {
    return ENOMEM;
  }
  memcpy(heap, src, len);
  heap[len] = '\0';
  *out_ptr = heap;
  *out_heap = heap;
  return 0;
}

static void *leanswe_sbx_sync_worker(void *arg) {
  SbxSyncArgs sa = *(SbxSyncArgs *)arg;
  free(arg);
  if (sa.install != 0) {
    struct sock_filter allow = { 0x0006, 0, 0, 0x7FFF0000U };
    struct sock_fprog prog = { 1, &allow };
    if (syscall(SYS_prctl, 38UL, 1UL, 0UL, 0UL, 0UL) < 0 ||
        syscall(SYS_seccomp, 1UL, 0UL, &prog) < 0) {
      close(sa.ready_wfd);
      return NULL;
    }
  }
  uint32_t tid = (uint32_t)syscall(SYS_gettid);
  ssize_t wn = write(sa.ready_wfd, &tid, sizeof(tid));
  (void)wn;
  close(sa.ready_wfd);
  char ch = 0;
  ssize_t rn = read(sa.stop_rfd, &ch, 1);
  (void)rn;
  return NULL;
}

static int sbx_dup_above2(int fd) {
  if (fd >= 3) { return fd; }
  int nfd = fcntl(fd, F_DUPFD_CLOEXEC, 3);
  int saved = errno;
  close(fd);
  if (nfd < 0) { errno = saved; }
  return nfd;
}

static int sbx_pipe_above2(int fds[2]) {
  if (pipe2(fds, O_CLOEXEC) < 0) { return -1; }
  int r = sbx_dup_above2(fds[0]);
  int w = sbx_dup_above2(fds[1]);
  if (r < 0 || w < 0) {
    int saved = errno;
    if (r >= 0) { close(r); }
    if (w >= 0) { close(w); }
    fds[0] = -1; fds[1] = -1; errno = saved;
    return -1;
  }
  fds[0] = r; fds[1] = w;
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_sbx_pipe(void) {
  int fds[2] = { -1, -1 };
  if (sbx_pipe_above2(fds) < 0) { return leanswe_mk_errno(errno); }
  uint64_t packed = ((uint64_t)(uint32_t)fds[0]) | (((uint64_t)(uint32_t)fds[1]) << 32);
  return leanswe_mk_ok(lean_box_uint64(packed));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_fork(void) {
  fflush(NULL);
  pid_t pid = fork();
  if (pid < 0) { return leanswe_mk_errno(errno); }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)pid));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_waitpid(uint32_t pid) {
  int status = 0;
  pid_t rc = waitpid((pid_t)pid, &status, 0);
  if (rc < 0) { return leanswe_mk_errno(errno); }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)status));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_exit(uint32_t code) {
  _exit((int)code);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_write_bytes(uint32_t fd, b_lean_obj_arg ba) {
  ssize_t n = write((int)fd, lean_sarray_cptr(ba), lean_sarray_size(ba));
  if (n < 0) { return leanswe_mk_errno(errno); }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)n));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_read_bytes(uint32_t fd, uint32_t max_bytes) {
  size_t cap = (size_t)max_bytes;
  if (cap > 65536u) { cap = 65536u; }
  lean_obj_res arr = lean_alloc_sarray(1, 0, cap);
  if (arr == NULL) { return leanswe_mk_errno(ENOMEM); }
  ssize_t n = read((int)fd, lean_sarray_cptr(arr), cap);
  if (n < 0) {
    int saved = errno;
    lean_dec(arr);
    return leanswe_mk_errno(saved);
  }
  lean_sarray_set_size(arr, (size_t)n);
  return leanswe_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res leanswe_sbx_peek_raw_fd(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  pthread_mutex_lock(&box->mu);
  int fd = (box->closed || box->fd < 0) ? -1 : box->fd;
  pthread_mutex_unlock(&box->mu);
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_close_raw(uint32_t fd) {
  close((int)fd);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_enter_userns(void) {
  if (unshare(CLONE_NEWUSER) < 0) { return leanswe_mk_errno(errno); }
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_set_no_new_privs(void) {
  if (syscall(SYS_prctl, 38UL, 1UL, 0UL, 0UL, 0UL) < 0) { return leanswe_mk_errno(errno); }
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_get_no_new_privs(void) {
  long rc = syscall(SYS_prctl, 39UL, 0UL, 0UL, 0UL, 0UL);
  if (rc < 0) { return leanswe_mk_errno(errno); }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)rc));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_install_raw_seccomp(uint32_t flags, b_lean_obj_arg filter_ba) {
  size_t len = lean_sarray_size(filter_ba);
  if (len == 0u || (len % sizeof(struct sock_filter)) != 0u) { return leanswe_mk_errno(EINVAL); }
  size_t cnt = len / sizeof(struct sock_filter);
  if (cnt > 65535u) { return leanswe_mk_errno(EINVAL); }
  struct sock_filter *insns = (struct sock_filter *)malloc(len);
  if (insns == NULL) { return leanswe_mk_errno(ENOMEM); }
  memcpy(insns, lean_sarray_cptr(filter_ba), len);
  struct sock_fprog prog = { (unsigned short)cnt, insns };
  long rc = syscall(SYS_seccomp, 1UL, (unsigned long)flags, &prog);
  int saved = errno;
  free(insns);
  if (rc < 0) { return leanswe_mk_errno(saved); }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)rc));
}

static void sbx_close_pair(int fds[2]) {
  if (fds[0] >= 0) { close(fds[0]); }
  if (fds[1] >= 0) { close(fds[1]); }
}

static pthread_once_t g_sbx_atfork_once = PTHREAD_ONCE_INIT;

static void sbx_atfork_child(void) {
  g_sbx_sync_active = 0; g_sbx_sync_stop_wfd = -1; g_sbx_sync_stop_rfd = -1;
}

static void sbx_register_atfork(void) {
  pthread_atfork(NULL, NULL, sbx_atfork_child);
}

LEAN_EXPORT lean_obj_res leanswe_sbx_spawn_sync_thread(uint32_t install_filter) {
  pthread_once(&g_sbx_atfork_once, sbx_register_atfork);
  int ready_fds[2] = { -1, -1 }, stop_fds[2] = { -1, -1 };
  SbxSyncArgs *sa = (SbxSyncArgs *)malloc(sizeof(*sa));
  if (sa == NULL) { return leanswe_mk_errno(ENOMEM); }
  pthread_mutex_lock(&g_sbx_sync_mu);
  if (g_sbx_sync_active != 0) {
    pthread_mutex_unlock(&g_sbx_sync_mu); free(sa); return leanswe_mk_errno(EBUSY);
  }
  if (sbx_pipe_above2(ready_fds) < 0 || sbx_pipe_above2(stop_fds) < 0) {
    int saved = errno; pthread_mutex_unlock(&g_sbx_sync_mu); free(sa);
    sbx_close_pair(ready_fds); sbx_close_pair(stop_fds);
    return leanswe_mk_errno(saved);
  }
  sa->install = (install_filter != 0u) ? 1 : 0;
  sa->ready_wfd = ready_fds[1];
  sa->stop_rfd = stop_fds[0];
  int rc = pthread_create(&g_sbx_sync_tid, NULL, leanswe_sbx_sync_worker, sa);
  if (rc != 0) {
    pthread_mutex_unlock(&g_sbx_sync_mu); free(sa);
    sbx_close_pair(ready_fds); sbx_close_pair(stop_fds);
    return leanswe_mk_errno(rc);
  }
  g_sbx_sync_stop_rfd = stop_fds[0];
  g_sbx_sync_stop_wfd = stop_fds[1];
  g_sbx_sync_active = 1;
  pthread_mutex_unlock(&g_sbx_sync_mu);
  return leanswe_mk_ok(lean_box_uint32((uint32_t)ready_fds[0]));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_stop_sync_thread(void) {
  pthread_mutex_lock(&g_sbx_sync_mu);
  if (g_sbx_sync_active == 0) {
    pthread_mutex_unlock(&g_sbx_sync_mu);
    return leanswe_mk_ok(lean_box(0));
  }
  pthread_t tid = g_sbx_sync_tid;
  int wfd = g_sbx_sync_stop_wfd, rfd = g_sbx_sync_stop_rfd;
  g_sbx_sync_active = 0; g_sbx_sync_stop_wfd = -1; g_sbx_sync_stop_rfd = -1;
  pthread_mutex_unlock(&g_sbx_sync_mu);
  char ch = 1;
  ssize_t wn = write(wfd, &ch, 1);
  (void)wn;
  pthread_join(tid, NULL);
  close(wfd);
  close(rfd);
  return leanswe_mk_ok(lean_box(0));
}

static int sbx_write_text(const char *path, const char *txt) {
  int fd = open(path, O_WRONLY | O_CLOEXEC);
  if (fd < 0) { return -1; }
  size_t len = strlen(txt);
  ssize_t wn = write(fd, txt, len);
  int saved = errno;
  close(fd);
  if (wn < 0) { errno = saved; return -1; }
  if (wn != (ssize_t)len) { errno = EIO; return -1; }
  return 0;
}

static int sbx_setup_idmap(uid_t uid, gid_t gid) {
  char ubuf[64], gbuf[64];
  snprintf(ubuf, sizeof(ubuf), "0 %u 1\n", (unsigned)uid);
  snprintf(gbuf, sizeof(gbuf), "0 %u 1\n", (unsigned)gid);
  if (sbx_write_text("/proc/self/setgroups", "deny\n") != 0) { return -1; }
  if (sbx_write_text("/proc/self/uid_map", ubuf) != 0) { return -1; }
  if (sbx_write_text("/proc/self/gid_map", gbuf) != 0) { return -1; }
  return 0;
}

static int sbx_mkdir_sub(const char *base, const char *sub) {
  char p[4096];
  int n = snprintf(p, sizeof(p), "%s/%s", base, sub);
  if (n < 0 || (size_t)n >= sizeof(p)) { errno = ENAMETOOLONG; return -1; }
  if (mkdir(p, 0700) < 0 && errno != EEXIST) { return -1; }
  return 0;
}

static int sbx_touch_sub(const char *base, const char *sub) {
  char p[4096];
  int n = snprintf(p, sizeof(p), "%s/%s", base, sub);
  if (n < 0 || (size_t)n >= sizeof(p)) { errno = ENAMETOOLONG; return -1; }
  int fd = open(p, O_WRONLY | O_CREAT | O_CLOEXEC, 0600);
  if (fd < 0) { return -1; }
  close(fd);
  return 0;
}

static int sbx_remount_ro(const char *path) {
  struct statvfs sv;
  if (statvfs(path, &sv) != 0) { return -1; }
  unsigned long fl = MS_BIND | MS_REMOUNT | MS_RDONLY;
  if ((sv.f_flag & ST_NODEV) != 0) { fl |= MS_NODEV; }
  if ((sv.f_flag & ST_NOSUID) != 0) { fl |= MS_NOSUID; }
  if ((sv.f_flag & ST_NOEXEC) != 0) { fl |= MS_NOEXEC; }
  if ((sv.f_flag & ST_NODIRATIME) != 0) { fl |= MS_NODIRATIME; }
  if ((sv.f_flag & ST_NOATIME) != 0) { fl |= MS_NOATIME; }
#ifdef ST_RELATIME
  if ((sv.f_flag & ST_RELATIME) != 0) { fl |= MS_RELATIME; }
#endif
#if defined(ST_NOSYMFOLLOW) && defined(MS_NOSYMFOLLOW)
  if ((sv.f_flag & ST_NOSYMFOLLOW) != 0) { fl |= MS_NOSYMFOLLOW; }
#endif
  return mount(NULL, path, NULL, fl, NULL);
}

static int sbx_do_mounts(const char *base) {
  if (strlen(base) >= 900u) { errno = ENAMETOOLONG; return -1; }
  char lo[1024], up[1024], wk[1024], ov[1024], dp[1024], bm[1024], bs[1024], ro[1024], opt[3200];
  snprintf(lo, sizeof(lo), "%s/lo", base);
  snprintf(up, sizeof(up), "%s/up", base);
  snprintf(wk, sizeof(wk), "%s/wk", base);
  snprintf(ov, sizeof(ov), "%s/ov", base);
  snprintf(dp, sizeof(dp), "%s/dp", base);
  snprintf(bm, sizeof(bm), "%s/bm", base);
  snprintf(bs, sizeof(bs), "%s/bs", base);
  snprintf(ro, sizeof(ro), "%s/ro", base);
  snprintf(opt, sizeof(opt), "lowerdir=%s,upperdir=%s,workdir=%s", lo, up, wk);
  if (mount("overlay", ov, "overlay", 0, opt) < 0) { return -1; }
  if (mount("devpts", dp, "devpts", 0, "newinstance,ptmxmode=0666") < 0) { return -1; }
  if (sbx_touch_sub(bs, "f.txt") < 0) { return -1; }
  if (mount(bs, bm, NULL, MS_BIND, NULL) < 0) { return -1; }
  if (mount(bs, ro, NULL, MS_BIND, NULL) < 0) { return -1; }
  if (sbx_remount_ro(ro) < 0) { return -1; }
  if (sbx_touch_sub(ov, "f.txt") < 0) { return -1; }
  return 0;
}

static int sbx_make_mnt_dirs_part1(const char *cbase) {
  if (mkdir(cbase, 0700) < 0 && errno != EEXIST) { return -1; }
  if (sbx_mkdir_sub(cbase, "lo") < 0) { return -1; }
  if (sbx_mkdir_sub(cbase, "up") < 0) { return -1; }
  if (sbx_mkdir_sub(cbase, "wk") < 0) { return -1; }
  if (sbx_mkdir_sub(cbase, "ov") < 0) { return -1; }
  return 0;
}

static int sbx_make_mnt_dirs(const char *cbase) {
  if (sbx_make_mnt_dirs_part1(cbase) < 0) { return -1; }
  if (sbx_mkdir_sub(cbase, "dp") < 0) { return -1; }
  if (sbx_mkdir_sub(cbase, "bm") < 0) { return -1; }
  if (sbx_mkdir_sub(cbase, "bs") < 0) { return -1; }
  if (sbx_mkdir_sub(cbase, "ro") < 0) { return -1; }
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_sbx_setup_mnt_ns(b_lean_obj_arg base_ba) {
  uid_t uid = getuid();
  gid_t gid = getgid();
  if (unshare(CLONE_NEWUSER | CLONE_NEWNS) < 0) { return leanswe_mk_errno(errno); }
  if (sbx_setup_idmap(uid, gid) != 0) {
    int err = errno;
    return leanswe_mk_ok(lean_box_uint32((uint32_t)(err > 0 ? err : EIO)));
  }
  char sbuf[4096];
  const char *cbase = NULL;
  char *heap = NULL;
  int perr = sbx_env_ba_to_cstr(base_ba, sbuf, sizeof(sbuf), &cbase, &heap);
  if (perr != 0) { return leanswe_mk_ok(lean_box_uint32((uint32_t)perr)); }
  int rc = sbx_make_mnt_dirs(cbase);
  if (rc == 0) { rc = sbx_do_mounts(cbase); }
  int saved = errno;
  if (heap != NULL) { free(heap); }
  if (rc != 0) { return leanswe_mk_ok(lean_box_uint32((uint32_t)(saved > 0 ? saved : EIO))); }
  return leanswe_mk_ok(lean_box_uint32(0u));
}
