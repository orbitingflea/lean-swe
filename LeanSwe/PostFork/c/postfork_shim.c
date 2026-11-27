#define _GNU_SOURCE
#include "../../LinuxSyscall/c/fd_box.h"

#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

#ifndef SYS_close_range
#define SYS_close_range 436
#endif

enum {
  PF_FLAG_SET_PGID = 1u, PF_FLAG_RESET_SIGPIPE = 2u, PF_FLAG_REDIRECT_STDIO = 4u, PF_ALL_FLAGS = 7u,
  PF_STAGE_PGID = 2u, PF_STAGE_SIG = 3u, PF_STAGE_FD = 4u,
  PF_STAGE_CLOSE = 5u, PF_STAGE_CHDIR = 6u, PF_STAGE_EXEC = 7u
};

typedef struct { uint32_t stage, err; } PfErrPkt;
typedef struct {
  uint32_t flags;
  int32_t in_fd, out_fd, err_fd;
  const char *cwd, *path, *const *argv, *const *envp;
  int max_fd;
} PfChildCfg;

static uint32_t pf_norm_err(int e) { return (e >= 1 && e <= 4095) ? (uint32_t)e : (uint32_t)EIO; }

static lean_obj_res pf_wrap(uint8_t tag, lean_obj_arg v) {
  lean_obj_res r = lean_alloc_ctor(tag, 1, 0);
  lean_ctor_set(r, 0, v);
  return r;
}

static lean_obj_res pf_mk_sys(int err) {
  leanswe_abort_on_efault(err);
  lean_obj_res e = lean_alloc_ctor(0, 0, sizeof(uint32_t));
  lean_ctor_set_uint32(e, 0, pf_norm_err(err));
  return pf_wrap(0u, e);
}

static lean_obj_res pf_mk_child(lean_obj_arg wait, uint32_t stage, uint32_t err) {
  lean_obj_res e = lean_alloc_ctor(1, 1, 2u * sizeof(uint32_t));
  lean_ctor_set(e, 0, wait);
  lean_ctor_set_uint32(e, sizeof(void *), stage);
  lean_ctor_set_uint32(e, sizeof(void *) + sizeof(uint32_t), pf_norm_err((int)err));
  return pf_wrap(0u, e);
}

static int pf_pin_ref(b_lean_obj_arg opt_h, int32_t raw_fd, LeanFdBox **box_out, int32_t *fd_out) {
  *box_out = NULL;
  if (lean_is_scalar(opt_h)) { *fd_out = raw_fd; return 0; }
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(lean_ctor_get(opt_h, 0));
  int fd = -1, rc = leanswe_fd_box_pin(box, &fd);
  if (rc != 0) return rc;
  *box_out = box;
  *fd_out = (int32_t)fd;
  return 0;
}

static void pf_unpin_boxes(LeanFdBox *boxes[3]) {
  for (size_t i = 0; i < 3u; i++) if (boxes[i] != NULL) leanswe_fd_box_unpin(boxes[i]);
}

static const char **pf_alloc_argv(b_lean_obj_arg arr, int *err_out) {
  size_t n = lean_array_size(arr);
  const char **ptrs = (const char **)calloc(n + 1u, sizeof(const char *));
  if (ptrs == NULL) { *err_out = ENOMEM; return NULL; }
  for (size_t i = 0; i < n; i++) {
    b_lean_obj_arg s = lean_array_get_core(arr, i);
    const char *cs = lean_string_cstr(s);
    if (strlen(cs) + 1u != lean_string_size(s)) { free((void *)ptrs); *err_out = EINVAL; return NULL; }
    ptrs[i] = cs;
  }
  return ptrs;
}

static const char **pf_alloc_envp(b_lean_obj_arg arr, int *err_out) {
  size_t n = lean_array_size(arr);
  const char **ptrs = (const char **)calloc(n + 1u, sizeof(const char *));
  if (ptrs == NULL) { *err_out = ENOMEM; return NULL; }
  for (size_t i = 0; i < n; i++) {
    b_lean_obj_arg b = lean_array_get_core(arr, i);
    size_t sz = lean_sarray_size(b);
    const uint8_t *raw = lean_sarray_cptr(b);
    if (sz == 0 || raw[sz - 1u] != 0 || memchr(raw, 0, sz - 1u) != NULL) {
      free((void *)ptrs); *err_out = EINVAL; return NULL;
    }
    ptrs[i] = (const char *)raw;
  }
  return ptrs;
}

/* Strictly async-signal-safe post-fork child helpers */

static _Noreturn void pf_child_fail(int rep_w, uint32_t stage, int err) {
  struct sigaction sa;
  memset(&sa, 0, sizeof(sa));
  sa.sa_handler = SIG_IGN;
  (void)sigaction(SIGPIPE, &sa, NULL);
  PfErrPkt pkt = { stage, pf_norm_err(err) };
  const uint8_t *p = (const uint8_t *)&pkt;
  for (size_t off = 0; off < sizeof(pkt);) {
    ssize_t n = write(rep_w, p + off, sizeof(pkt) - off);
    if (n > 0) off += (size_t)n;
    else if (n < 0 && errno != EINTR) break;
  }
  _exit(127);
}

static int pf_dup_slot(int src, int dst) {
  if (src != dst) { while (dup2(src, dst) < 0) if (errno != EINTR) return -1; }
  int fl = fcntl(dst, F_GETFD, 0);
  return fl < 0 ? -1 : fcntl(dst, F_SETFD, fl & ~FD_CLOEXEC);
}

static void pf_close_pair(int a, int b) {
  int saved = errno;
  if (a >= 0) (void)close(a);
  if (b >= 0) (void)close(b);
  errno = saved;
}

static int pf_setup_stdio(const PfChildCfg *c) {
  int s0 = c->in_fd, s1 = c->out_fd, s2 = c->err_fd, sv0 = -1, sv1 = -1;
  if (s0 != 0 && (s1 == 0 || s2 == 0)) {
    sv0 = fcntl(0, F_DUPFD_CLOEXEC, 3);
    if (sv0 < 0) return -1;
    if (s1 == 0) s1 = sv0;
    if (s2 == 0) s2 = sv0;
  }
  int rc = pf_dup_slot(s0, 0);
  if (rc == 0 && s1 != 1 && s2 == 1) { sv1 = fcntl(1, F_DUPFD_CLOEXEC, 3); rc = (sv1 >= 0) - 1; s2 = sv1; }
  if (rc == 0 && pf_dup_slot(s1, 1) == 0 && pf_dup_slot(s2, 2) == 0) { pf_close_pair(sv1, sv0); return 0; }
  pf_close_pair(sv1, sv0);
  return -1;
}

static int pf_close_above2(int rep_w, int max_fd) {
  int r1 = (rep_w > 3) ? (int)syscall(SYS_close_range, 3u, (uint32_t)(rep_w - 1), 0u) : 0;
  int r2 = (r1 == 0 && (uint32_t)rep_w < UINT32_MAX)
    ? (int)syscall(SYS_close_range, (uint32_t)rep_w + 1u, UINT32_MAX, 0u) : r1;
  if (r2 == 0) return 0;
  if (errno != ENOSYS && errno != EPERM) return -1;
  for (int fd = 3; fd < max_fd; fd++)
    if (fd != rep_w && close(fd) != 0 && errno != EBADF && errno != EINTR) return -1;
  return 0;
}

static int pf_reset_sigpipe(void) {
  struct sigaction sa; memset(&sa, 0, sizeof(sa)); sa.sa_handler = SIG_DFL;
  sigset_t sp; sigemptyset(&sp); sigaddset(&sp, SIGPIPE);
  return (sigaction(SIGPIPE, &sa, NULL) == 0 && sigprocmask(SIG_UNBLOCK, &sp, NULL) == 0) ? 0 : -1;
}

static _Noreturn void pf_run_child(const PfChildCfg *c, int rep_w) {
  if ((c->flags & PF_FLAG_SET_PGID) != 0 && setpgid(0, 0) != 0) pf_child_fail(rep_w, PF_STAGE_PGID, errno);
  if ((c->flags & PF_FLAG_RESET_SIGPIPE) != 0 && pf_reset_sigpipe() != 0) pf_child_fail(rep_w, PF_STAGE_SIG, errno);
  if ((c->flags & PF_FLAG_REDIRECT_STDIO) != 0 && pf_setup_stdio(c) != 0) pf_child_fail(rep_w, PF_STAGE_FD, errno);
  if (pf_close_above2(rep_w, c->max_fd) != 0) pf_child_fail(rep_w, PF_STAGE_CLOSE, errno);
  if (c->cwd != NULL && chdir(c->cwd) != 0) pf_child_fail(rep_w, PF_STAGE_CHDIR, errno);
  execve(c->path, (char *const *)c->argv, (char *const *)c->envp);
  pf_child_fail(rep_w, PF_STAGE_EXEC, errno);
}

/* Parent orchestration */

static int pf_reloc_above2(int *fd) {
  if (*fd >= 3) return 0;
  int nfd = fcntl(*fd, F_DUPFD_CLOEXEC, 3);
  if (nfd < 0) return errno == EINVAL ? EMFILE : errno;
  (void)close(*fd); *fd = nfd; return 0;
}

static int pf_read_errpipe(int fd, PfErrPkt *pkt, size_t *out_n) {
  uint8_t buf[sizeof(PfErrPkt) + 1u];
  size_t total = 0;
  while (total < sizeof(buf)) {
    ssize_t n = read(fd, buf + total, sizeof(buf) - total);
    if (n == 0) break;
    if (n > 0) total += (size_t)n;
    else if (errno != EINTR) return errno;
  }
  if (total == sizeof(PfErrPkt)) memcpy(pkt, buf, sizeof(PfErrPkt));
  *out_n = total; return 0;
}

static int pf_wait_child(pid_t pid, lean_obj_res *out_wst) {
  int st = 0;
  while (waitpid(pid, &st, 0) < 0) if (errno != EINTR) return errno;
  uint8_t tag = WIFSIGNALED(st) ? 1u : 0u;
  uint32_t code = WIFSIGNALED(st) ? (uint32_t)WTERMSIG(st) : (WIFEXITED(st) ? (uint32_t)WEXITSTATUS(st) : 127u);
  lean_obj_res o = lean_alloc_ctor(tag, 0, sizeof(uint32_t));
  lean_ctor_set_uint32(o, 0, code);
  *out_wst = o; return 0;
}

static lean_obj_res pf_finish_parent(pid_t pid, uint32_t flags, int err_r) {
  if ((flags & PF_FLAG_SET_PGID) != 0) (void)setpgid(pid, pid);
  PfErrPkt pkt = { 0u, (uint32_t)EIO };
  size_t nread = 0;
  int rerr = pf_read_errpipe(err_r, &pkt, &nread);
  (void)close(err_r);
  if (rerr == 0 && nread == 0) return pf_wrap(1u, lean_box_uint32((uint32_t)(int32_t)pid));
  lean_obj_res wst = NULL;
  int werr = pf_wait_child(pid, &wst);
  if (rerr != 0 || werr != 0) { if (wst != NULL) lean_dec(wst); return pf_mk_sys(rerr != 0 ? rerr : werr); }
  return nread == sizeof(pkt) ? pf_mk_child(wst, pkt.stage, pkt.err) : pf_mk_child(wst, 0u, (uint32_t)EIO);
}

static lean_obj_res pf_fork_and_wait(const PfChildCfg *c) {
  int ep[2] = { -1, -1 };
  if (pipe2(ep, O_CLOEXEC) != 0) return pf_mk_sys(errno);
  int perr = pf_reloc_above2(&ep[0]);
  if (perr == 0) perr = pf_reloc_above2(&ep[1]);
  if (perr != 0) { pf_close_pair(ep[0], ep[1]); return pf_mk_sys(perr); }
  pid_t pid = fork();
  if (pid == 0) { (void)close(ep[0]); pf_run_child(c, ep[1]); }
  int ferr = errno; (void)close(ep[1]);
  if (pid < 0) { (void)close(ep[0]); return pf_mk_sys(ferr); }
  return pf_finish_parent(pid, c->flags, ep[0]);
}

static int pf_probe_stdio(const PfChildCfg *c) {
  if ((c->flags & PF_FLAG_REDIRECT_STDIO) == 0) return 0;
  if (c->in_fd < 0 || c->out_fd < 0 || c->err_fd < 0) return EBADF;
  if (fcntl(c->in_fd, F_GETFD, 0) < 0 || fcntl(c->out_fd, F_GETFD, 0) < 0 || fcntl(c->err_fd, F_GETFD, 0) < 0)
    return errno;
  return 0;
}

static int pf_pin_stdio(
    b_lean_obj_arg in_h, uint32_t in_raw, b_lean_obj_arg out_h, uint32_t out_raw,
    b_lean_obj_arg err_h, uint32_t err_raw, LeanFdBox *boxes[3], int32_t fds[3]) {
  int rc = pf_pin_ref(in_h, (int32_t)in_raw, &boxes[0], &fds[0]);
  if (rc == 0) rc = pf_pin_ref(out_h, (int32_t)out_raw, &boxes[1], &fds[1]);
  if (rc == 0) rc = pf_pin_ref(err_h, (int32_t)err_raw, &boxes[2], &fds[2]);
  return rc;
}

static int pf_max_fd(void) {
  long om = sysconf(_SC_OPEN_MAX);
  return om <= 0 ? 1024 : (om > 1048576L ? 1048576 : (int)om);
}

LEAN_EXPORT lean_obj_res leanswe_postfork_spawn(
    uint32_t flags, b_lean_obj_arg in_h, uint32_t in_raw,
    b_lean_obj_arg out_h, uint32_t out_raw, b_lean_obj_arg err_h, uint32_t err_raw,
    b_lean_obj_arg cwd_opt, b_lean_obj_arg path_str, b_lean_obj_arg argv_arr, b_lean_obj_arg envp_arr) {
  if ((flags & ~PF_ALL_FLAGS) != 0) return pf_mk_sys(EINVAL);
  LeanFdBox *boxes[3] = { NULL, NULL, NULL };
  int32_t fds[3] = { -1, -1, -1 };
  int rc = pf_pin_stdio(in_h, in_raw, out_h, out_raw, err_h, err_raw, boxes, fds);
  if (rc != 0) { pf_unpin_boxes(boxes); return pf_mk_sys(rc); }
  int arg_err = 0, env_err = 0;
  const char **argv = pf_alloc_argv(argv_arr, &arg_err);
  const char **envp = pf_alloc_envp(envp_arr, &env_err);
  PfChildCfg cfg = { flags, fds[0], fds[1], fds[2],
    lean_is_scalar(cwd_opt) ? NULL : lean_string_cstr(lean_ctor_get(cwd_opt, 0)),
    lean_string_cstr(path_str), argv, envp, pf_max_fd() };
  int perr = (argv == NULL) ? arg_err : (envp == NULL ? env_err : pf_probe_stdio(&cfg));
  lean_obj_res res = perr != 0 ? pf_mk_sys(perr) : pf_fork_and_wait(&cfg);
  free((void *)argv); free((void *)envp); pf_unpin_boxes(boxes);
  return res;
}
