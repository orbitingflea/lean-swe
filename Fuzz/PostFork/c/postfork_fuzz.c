#define _GNU_SOURCE

#include "postfork.h"
#include "../../../LeanSwe/LinuxSyscall/c/fd_box.h"

#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <unistd.h>

typedef struct PfChildCfg {
  int32_t is_close_only;
  uint32_t pf_flags;
  int32_t sync_r, stdin_fd, stdout_fd, stderr_fd, rep_w, extra_keep_fd, close_out_fd;
  int32_t slot0_src, slot0_clo, slot1_src, slot1_clo, slot2_src, slot2_clo;
  int32_t close_stage0, close_stage1, close_stage2;
  int32_t rlim_nofile, env_flags, sigpipe_mode, sigusr1_mode, sigusr2_mode;
} PfChildCfg;

static int pf_hi_fd(int fd, uint32_t clo) {
  if (fd < 0 || fd >= 3) return fd;
  int nfd = fcntl(fd, clo ? F_DUPFD_CLOEXEC : F_DUPFD, 3), e = errno;
  (void)close(fd); errno = e; return nfd;
}
static lean_obj_res pf_ok(lean_obj_arg v) {
  lean_obj_res r = lean_alloc_ctor(1, 1, 0); lean_ctor_set(r, 0, v);
  return lean_io_result_mk_ok(r);
}
static lean_obj_res pf_err(uint32_t err) {
  lean_obj_res r = lean_alloc_ctor(0, 1, 0); lean_ctor_set(r, 0, lean_box_uint32(err));
  return lean_io_result_mk_ok(r);
}
#if defined(__aarch64__)
#define PF_AUDIT_ARCH AUDIT_ARCH_AARCH64
#else
#define PF_AUDIT_ARCH AUDIT_ARCH_X86_64
#endif
#ifdef SYS_dup2
#define PF_SYS_DUP2 SYS_dup2
#define PF_DUP2_USES_DUP3 0u
#else
#define PF_SYS_DUP2 SYS_dup3
#define PF_DUP2_USES_DUP3 1u
#endif
LEAN_EXPORT lean_obj_res leanswe_pf_get_rlim_nofile(void) {
  struct rlimit rl;
  uint64_t val = (getrlimit(RLIMIT_NOFILE, &rl) != 0 || rl.rlim_cur == RLIM_INFINITY)
    ? 2147483648ULL : (uint64_t)rl.rlim_cur;
  return lean_io_result_mk_ok(lean_box_uint64(val));
}
LEAN_EXPORT lean_obj_res leanswe_pf_geteuid(void) {
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)geteuid()));
}
LEAN_EXPORT lean_obj_res leanswe_pf_sigpipe_disp(void) {
  struct sigaction sa;
  int32_t d = (sigaction(SIGPIPE, NULL, &sa) != 0) ? -1 : (sa.sa_handler == SIG_DFL ? 0 : (sa.sa_handler == SIG_IGN ? 1 : 2));
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)d));
}
LEAN_EXPORT lean_obj_res leanswe_pf_sigmask_usr1(uint32_t block) {
  sigset_t ss; sigemptyset(&ss); sigaddset(&ss, SIGUSR1);
  return sigprocmask(block ? SIG_BLOCK : SIG_UNBLOCK, &ss, NULL) != 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box(0));
}
LEAN_EXPORT uint32_t leanswe_pf_seccomp_const(uint32_t idx) {
  static const uint32_t tbl[18] = {
    PF_AUDIT_ARCH, SYS_read, SYS_write, SYS_close, SYS_rt_sigaction, PF_SYS_DUP2, SYS_execve, SYS_fcntl, SYS_chdir,
    SYS_setpgid, SYS_getdents64, SYS_openat, SYS_close_range, SYS_memfd_create, (uint32_t)O_DIRECTORY, PF_DUP2_USES_DUP3, (uint32_t)SYS_rt_sigprocmask, (uint32_t)SIG_UNBLOCK
  };
  return idx < 18 ? tbl[idx] : 0xffffffffu;
}
LEAN_EXPORT lean_obj_res leanswe_pf_realpath(b_lean_obj_arg path) {
  char *res = realpath(lean_string_cstr(path), NULL);
  if (!res) return pf_err((uint32_t)errno);
  lean_obj_res s = lean_mk_string(res);
  free(res);
  return pf_ok(s);
}
LEAN_EXPORT lean_obj_res leanswe_pf_pipe2(uint32_t cloexec) {
  int fds[2] = {-1, -1};
  if (pipe2(fds, cloexec ? O_CLOEXEC : 0) != 0) return pf_err((uint32_t)errno);
  fds[0] = pf_hi_fd(fds[0], cloexec); int e0 = errno; fds[1] = pf_hi_fd(fds[1], cloexec);
  if (fds[0] < 0 || fds[1] < 0) {
    int e = fds[0] < 0 ? e0 : errno;
    if (fds[0] >= 0) close(fds[0]);
    if (fds[1] >= 0) close(fds[1]);
    return pf_err((uint32_t)e);
  }
  lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_box_uint32((uint32_t)(int32_t)fds[0]));
  lean_ctor_set(pair, 1, lean_box_uint32((uint32_t)(int32_t)fds[1]));
  return pf_ok(pair);
}
LEAN_EXPORT lean_obj_res leanswe_pf_memfd(uint32_t cloexec) {
  int fd = pf_hi_fd((int)syscall(SYS_memfd_create, "pf_fuzz", (unsigned int)(cloexec ? MFD_CLOEXEC : 0)), cloexec);
  return fd < 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box_uint32((uint32_t)(int32_t)fd));
}
LEAN_EXPORT lean_obj_res leanswe_pf_dup_from(uint32_t oldfd, uint32_t minfd, uint32_t cloexec) {
  int fd = fcntl((int)(int32_t)oldfd, cloexec ? F_DUPFD_CLOEXEC : F_DUPFD, (int)(int32_t)minfd);
  return fd < 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box_uint32((uint32_t)(int32_t)fd));
}
LEAN_EXPORT lean_obj_res leanswe_pf_fcntl_getfd(uint32_t fd) {
  int fl = fcntl((int)(int32_t)fd, F_GETFD, 0);
  return fl < 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box_uint32((uint32_t)(int32_t)fl));
}
LEAN_EXPORT lean_obj_res leanswe_pf_fcntl_setfd(uint32_t fd, uint32_t fl) {
  return fcntl((int)(int32_t)fd, F_SETFD, (int)(int32_t)fl) != 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leanswe_pf_fstat_dev_ino(uint32_t fd) {
  struct stat st;
  if (fstat((int)(int32_t)fd, &st) != 0) return pf_err((uint32_t)errno);
  lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_box_uint64((uint64_t)st.st_dev));
  lean_ctor_set(pair, 1, lean_box_uint64((uint64_t)st.st_ino));
  return pf_ok(pair);
}
LEAN_EXPORT lean_obj_res leanswe_pf_close(uint32_t fd) {
  return close((int)(int32_t)fd) != 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leanswe_pf_read_once(uint32_t fd, uint64_t max_bytes) {
  size_t cap = (max_bytes > 1048576ULL) ? 1048576u : (size_t)max_bytes;
  uint8_t *buf = (uint8_t *)malloc(cap > 0 ? cap : 1u);
  if (buf == NULL) return pf_err((uint32_t)ENOMEM);
  ssize_t n = read((int)(int32_t)fd, buf, cap);
  int err = errno;
  if (n < 0) { free(buf); return pf_err((uint32_t)err); }
  lean_obj_res ba = lean_alloc_sarray(1, (size_t)n, (size_t)n);
  if (n > 0) memcpy(lean_sarray_cptr(ba), buf, (size_t)n);
  free(buf);
  return pf_ok(ba);
}
LEAN_EXPORT lean_obj_res leanswe_pf_write_once(uint32_t fd, b_lean_obj_arg ba, uint64_t off, uint64_t len) {
  size_t total = lean_sarray_size(ba);
  if (off > total || len > total - off) return pf_err((uint32_t)EINVAL);
  ssize_t n = write((int)(int32_t)fd, lean_sarray_cptr(ba) + off, (size_t)len);
  return n < 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box_uint64((uint64_t)n));
}
LEAN_EXPORT lean_obj_res leanswe_pf_rawfd_num(b_lean_obj_arg h_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(h_obj);
  int fd = -1, perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return pf_err((uint32_t)perr);
  leanswe_fd_box_unpin(box);
  return pf_ok(lean_box_uint32((uint32_t)(int32_t)fd));
}
LEAN_EXPORT lean_obj_res leanswe_pf_rawfd_fstat_dev_ino(b_lean_obj_arg h_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(h_obj);
  int fd = -1, perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return pf_err((uint32_t)perr);
  struct stat st;
  int rc = fstat(fd, &st), err = errno;
  leanswe_fd_box_unpin(box);
  if (rc != 0) return pf_err((uint32_t)err);
  lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_box_uint64((uint64_t)st.st_dev));
  lean_ctor_set(pair, 1, lean_box_uint64((uint64_t)st.st_ino));
  return pf_ok(pair);
}
LEAN_EXPORT lean_obj_res leanswe_pf_rawfd_setfd(b_lean_obj_arg h_obj, uint32_t fl) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(h_obj);
  int fd = -1, perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return pf_err((uint32_t)perr);
  int rc = fcntl(fd, F_SETFD, (int)(int32_t)fl), err = errno;
  leanswe_fd_box_unpin(box);
  return rc != 0 ? pf_err((uint32_t)err) : pf_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leanswe_pf_getpid_sid(void) {
  lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_box_uint32((uint32_t)(int32_t)getpid()));
  lean_ctor_set(pair, 1, lean_box_uint32((uint32_t)(int32_t)getsid(0)));
  return lean_io_result_mk_ok(pair);
}
LEAN_EXPORT lean_obj_res leanswe_pf_getpgrp(void) {
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(int32_t)getpgrp()));
}
LEAN_EXPORT lean_obj_res leanswe_pf_symlink(b_lean_obj_arg target, b_lean_obj_arg linkpath) {
  int rc = symlink(lean_string_cstr(target), lean_string_cstr(linkpath));
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(int32_t)(rc == 0 ? 0 : errno)));
}
LEAN_EXPORT lean_obj_res leanswe_pf_chmod(b_lean_obj_arg path, uint32_t mode) {
  return chmod(lean_string_cstr(path), (mode_t)mode) != 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leanswe_pf_mkdir(b_lean_obj_arg path, uint32_t mode) {
  return mkdir(lean_string_cstr(path), (mode_t)mode) != 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leanswe_pf_rmdir_unlink(b_lean_obj_arg path, uint32_t is_dir) {
  const char *p = lean_string_cstr(path);
  int rc = is_dir ? rmdir(p) : unlink(p);
  return rc != 0 ? pf_err((uint32_t)errno) : pf_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leanswe_pf_create_file(b_lean_obj_arg path, b_lean_obj_arg data, uint32_t mode) {
  int fd = open(lean_string_cstr(path), O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, (mode_t)mode);
  if (fd < 0) return pf_err((uint32_t)errno);
  size_t len = lean_sarray_size(data);
  ssize_t w = len > 0 ? write(fd, lean_sarray_cptr(data), len) : 0;
  int saved = errno;
  close(fd);
  if (w < 0 || (size_t)w != len) return pf_err((uint32_t)(w < 0 ? saved : EIO));
  return pf_ok(lean_box(0));
}
static void pf_dummy_handler(int s) { (void)s; }
static void pf_apply_sig(int sig, int32_t mode) {
  struct sigaction sa;
  memset(&sa, 0, sizeof(sa));
  sa.sa_handler = (mode == 1) ? SIG_IGN : ((mode == 2) ? pf_dummy_handler : SIG_DFL);
  sigemptyset(&sa.sa_mask);
  (void)sigaction(sig, &sa, NULL);
}
static void pf_apply_sigpipe_block(int32_t env_flags) {
  if (!(env_flags & 8)) return;
  sigset_t ss; sigemptyset(&ss); sigaddset(&ss, SIGPIPE);
  if (sigprocmask(SIG_BLOCK, &ss, NULL) != 0) _exit(124);
}
static void pf_apply_slot(int dst, int32_t src, int32_t clo) {
  if (src == -1) { (void)close(dst); }
  else if (src >= 0) {
    if (src != dst) (void)dup2((int)src, dst);
    (void)fcntl(dst, F_SETFD, clo ? FD_CLOEXEC : 0);
  }
}
static void pf_close_opt(int32_t fd) { if (fd >= 3) (void)close((int)fd); }
static void pf_apply_proc_ns(const PfChildCfg *cfg) {
  if (!(cfg->env_flags & 4)) return;
  if (!(cfg->env_flags & 2) && unshare(CLONE_NEWUSER | CLONE_NEWNS) != 0) _exit(124);
  if (mount(NULL, "/", NULL, MS_REC | MS_PRIVATE, NULL) != 0) _exit(124);
  if (mount("tmpfs", "/proc", "tmpfs", 0, NULL) != 0) _exit(124);
}
static void pf_apply_env(const PfChildCfg *cfg) {
  if ((cfg->env_flags & 1) && setsid() < 0) _exit(124);
  pf_apply_proc_ns(cfg);
  if (cfg->rlim_nofile >= 0) {
    struct rlimit rl = { (rlim_t)cfg->rlim_nofile, (rlim_t)cfg->rlim_nofile };
    if (setrlimit(RLIMIT_NOFILE, &rl) != 0) _exit(124);
  }
}
static void pf_apply_seccomp(const uint8_t *bpf, size_t len) {
  if (len == 0) return;
  if ((len % sizeof(struct sock_filter)) != 0 || len / sizeof(struct sock_filter) > UINT16_MAX) _exit(124);
  struct sock_fprog prog = { (unsigned short)(len / sizeof(struct sock_filter)), (struct sock_filter *)(void *)bpf };
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) _exit(124);
  if (syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, 0, &prog) != 0) _exit(124);
}
static void pf_dump_close_bits(int out_fd, int32_t rc) {
  uint8_t buf[132];
  memset(buf, 0, sizeof(buf));
  memcpy(buf, &rc, sizeof(rc));
  for (int fd = 0; fd < 1024; fd++) {
    struct stat st;
    if (fcntl(fd, F_GETFD, 0) != -1 || fstat(fd, &st) == 0) buf[4 + (fd >> 3)] |= (uint8_t)(1u << (fd & 7));
  }
  struct iovec iov = { buf, sizeof(buf) };
  ssize_t w = writev(out_fd, &iov, 1);
  (void)w;
}
static void pf_dispatch_child(const PfChildCfg *cfg, const int32_t *closes, size_t nc,
    const int32_t *keeps, size_t nk, const char *cwd, const char *path, const char *const *argv, const char *const *envp) {
  if (cfg->is_close_only == 0) {
    LeanswePostForkChildArgs a = {
      cfg->pf_flags, cfg->sync_r, cfg->stdin_fd, cfg->stdout_fd, cfg->stderr_fd,
      cfg->rep_w, closes, nc, keeps, nk, cwd, path, argv, envp
    };
    leanswe_postfork_run_child(&a);
  } else {
    int32_t rc = leanswe_postfork_close_fds_above2_except(cfg->extra_keep_fd, keeps, nk);
    pf_dump_close_bits((int)cfg->close_out_fd, rc);
    _exit(rc == 0 ? 0 : (int)(rc & 0xff));
  }
}
static int pf_wait_eintr(pid_t pid, int *st) {
  int rc;
  while ((rc = waitpid(pid, st, 0)) < 0 && errno == EINTR) {}
  return rc;
}
static void pf_maybe_pidns_child(const PfChildCfg *cfg) {
  if (!(cfg->env_flags & 2)) return;
  int uflags = CLONE_NEWUSER | CLONE_NEWPID | ((cfg->env_flags & 4) ? CLONE_NEWNS : 0);
  if (unshare(uflags) != 0) _exit(124);
  pid_t gc = fork();
  if (gc < 0) _exit(124);
  if (gc > 0) {
    int st = 0;
    if (pf_wait_eintr(gc, &st) < 0) _exit(124);
    if (WIFEXITED(st)) _exit(WEXITSTATUS(st));
    if (WIFSIGNALED(st)) {
      int sig = WTERMSIG(st);
      pf_apply_sig(sig, 0);
      (void)kill(getpid(), sig);
      _exit(128 + sig);
    }
    _exit(124);
  }
}
static const char **pf_alloc_strs(b_lean_obj_arg arr) {
  size_t n = lean_array_size(arr);
  const char **p = (const char **)calloc(n + 1, sizeof(const char *));
  if (p == NULL) return NULL;
  for (size_t i = 0; i < n; i++) p[i] = lean_string_cstr(lean_array_get_core(arr, i));
  p[n] = NULL;
  return p;
}
static void pf_child_entry(const PfChildCfg *cfg, const int32_t *closes, size_t nc, const int32_t *keeps,
    size_t nk, const uint8_t *bpf, size_t blen, const char *cwd, const char *path, const char *const *argv, const char *const *envp) {
  pf_maybe_pidns_child(cfg);
  pf_apply_slot(0, cfg->slot0_src, cfg->slot0_clo);
  pf_apply_slot(1, cfg->slot1_src, cfg->slot1_clo);
  pf_apply_slot(2, cfg->slot2_src, cfg->slot2_clo);
  pf_close_opt(cfg->close_stage0);
  pf_close_opt(cfg->close_stage1);
  pf_close_opt(cfg->close_stage2);
  pf_apply_sig(SIGPIPE, cfg->sigpipe_mode);
  pf_apply_sig(SIGUSR1, cfg->sigusr1_mode);
  pf_apply_sig(SIGUSR2, cfg->sigusr2_mode);
  pf_apply_sigpipe_block(cfg->env_flags);
  pf_apply_env(cfg);
  pf_apply_seccomp(bpf, blen);
  pf_dispatch_child(cfg, closes, nc, keeps, nk, cwd, path, argv, envp);
  _exit(126);
}
LEAN_EXPORT lean_obj_res leanswe_pf_fork_run(b_lean_obj_arg cfg_ba, b_lean_obj_arg close_ba, b_lean_obj_arg keep_ba,
    b_lean_obj_arg bpf_ba, b_lean_obj_arg cwd_opt, b_lean_obj_arg path_str, b_lean_obj_arg argv_arr, b_lean_obj_arg env_arr) {
  if (lean_sarray_size(cfg_ba) != sizeof(PfChildCfg)) return pf_err(EINVAL);
  const PfChildCfg *cfg = (const PfChildCfg *)(const void *)lean_sarray_cptr(cfg_ba);
  const int32_t *closes = (const int32_t *)(const void *)lean_sarray_cptr(close_ba);
  size_t n_close = lean_sarray_size(close_ba) / 4;
  const int32_t *keeps = (const int32_t *)(const void *)lean_sarray_cptr(keep_ba);
  size_t n_keep = lean_sarray_size(keep_ba) / 4;
  const uint8_t *bpf = lean_sarray_cptr(bpf_ba);
  size_t bpf_len = lean_sarray_size(bpf_ba);
  const char *cwd = lean_is_scalar(cwd_opt) ? NULL : lean_string_cstr(lean_ctor_get(cwd_opt, 0));
  const char *path = lean_string_cstr(path_str);
  const char **av = pf_alloc_strs(argv_arr), **ev = pf_alloc_strs(env_arr);
  if (av == NULL || ev == NULL) { free((void *)av); free((void *)ev); return pf_err(ENOMEM); }
  pid_t pid = fork();
  if (pid < 0) { int e = errno; free((void *)av); free((void *)ev); return pf_err((uint32_t)e); }
  if (pid == 0) pf_child_entry(cfg, closes, n_close, keeps, n_keep, bpf, bpf_len, cwd, path, av, ev);
  free((void *)av); free((void *)ev);
  return pf_ok(lean_box_uint32((uint32_t)(int32_t)pid));
}
static const int32_t *pf_bad_ptr(uint32_t mode, size_t *out_len) {
  static const int32_t ok_fd = 9999;
  static _Alignas(int32_t) const char align_buf[8] = { 0 };
  const int32_t *ptrs[4] = { &ok_fd, NULL, (const int32_t *)(const void *)(align_buf + 1), &ok_fd };
  const size_t lens[4] = { 0u, 1u, 1u, (size_t)(PTRDIFF_MAX / sizeof(int32_t)) + 1u };
  uint32_t idx = mode & 3u;
  *out_len = lens[idx];
  return ptrs[idx];
}
static void pf_abi_dispatch(uint32_t kind, uint32_t na, int32_t rw, const int32_t *cf, size_t nc,
    const int32_t *kf, size_t nk, const char *p, const char *const *av, const char *const *ev) {
  if (kind == 0) {
    LeanswePostForkChildArgs a = { 0u, -1, -1, -1, -1, rw, cf, nc, kf, nk, NULL, p, av, ev };
    leanswe_postfork_run_child(na ? NULL : &a);
  } else {
    int32_t rc = leanswe_postfork_close_fds_above2_except(-1, kf, nk);
    _exit(rc == 22 ? 0 : (int)(rc & 0xff));
  }
}
LEAN_EXPORT lean_obj_res leanswe_pf_abi_guard_fork(uint32_t kind, uint32_t rep_w, uint32_t flags) {
  pid_t pid = fork();
  if (pid < 0) return pf_err((uint32_t)errno);
  if (pid == 0) {
    static const char *const empty_vec[1] = { NULL };
    size_t nc = 0, nk = 0;
    const int32_t *cf = pf_bad_ptr((flags >> 4) & 3u, &nc), *kf = pf_bad_ptr((flags >> 6) & 3u, &nk);
    pf_abi_dispatch(kind, flags & 1u, (int32_t)rep_w, cf, nc, kf, nk,
      (flags & 2u) ? NULL : "/nonexistent_pf_abi",
      (flags & 4u) ? NULL : empty_vec,
      (flags & 8u) ? NULL : empty_vec);
    _exit(126);
  }
  return pf_ok(lean_box_uint32((uint32_t)(int32_t)pid));
}
static void pf_sigpipe_child(int p1, uint32_t pidns, uint32_t sig_mode, uint32_t block_sp) {
  PfChildCfg cfg = {0};
  cfg.env_flags = pidns ? 2 : 0;
  pf_maybe_pidns_child(&cfg);
  pf_apply_sig(SIGPIPE, (int32_t)sig_mode);
  if (block_sp) { sigset_t ss; sigemptyset(&ss); sigaddset(&ss, SIGPIPE); (void)sigprocmask(SIG_BLOCK, &ss, NULL); }
  ssize_t w = write(p1, "abc", 3);
  int e = (w < 0) ? errno : 0;
  _exit(w < 0 ? e : 0);
}
LEAN_EXPORT lean_obj_res leanswe_pf_sigpipe_write_fork(uint32_t pidns, uint32_t sig_mode, uint32_t block_sp) {
  int p[2] = {-1, -1};
  if (pipe2(p, O_CLOEXEC) != 0) return pf_err((uint32_t)errno);
  close(p[0]);
  pid_t pid = fork();
  if (pid < 0) { int e = errno; close(p[1]); return pf_err((uint32_t)e); }
  if (pid == 0) pf_sigpipe_child(p[1], pidns, sig_mode, block_sp);
  close(p[1]);
  return pf_ok(lean_box_uint32((uint32_t)(int32_t)pid));
}
