#define _GNU_SOURCE
#include "postfork.h"
#include "../../LinuxSyscall/c/fd_box.h"

#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

typedef struct PfSpawnReq {
  const LeanswePostForkChildArgs *args;
  sigset_t caller_mask;
  pid_t child_pid;
  int fork_errno, done;
  struct PfSpawnReq *next;
} PfSpawnReq;

typedef struct PfTrackedPipeFd { int32_t fd; dev_t dev; ino_t ino; } PfTrackedPipeFd;

static pthread_mutex_t g_pf_spawner_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t g_pf_spawner_cond = PTHREAD_COND_INITIALIZER;
static pthread_cond_t g_pf_spawner_done = PTHREAD_COND_INITIALIZER;
static PfSpawnReq *g_pf_spawner_head = NULL;
static int g_pf_spawner_ready = 0;

static pthread_mutex_t g_pf_pipe_mu = PTHREAD_MUTEX_INITIALIZER;
static PfTrackedPipeFd *g_pf_pipes = NULL;
static size_t g_pf_pipes_len = 0;
static size_t g_pf_pipes_cap = 0;
static lean_external_class *g_pf_pipe_fd_class = NULL;
static pthread_once_t g_pf_pipe_fd_class_once = PTHREAD_ONCE_INIT;

static lean_obj_res pf_mk_ok(lean_obj_arg v) {
  lean_obj_res r = lean_alloc_ctor(1, 1, 0); lean_ctor_set(r, 0, v); return r;
}

static lean_obj_res pf_mk_err(uint32_t err) {
  leanswe_abort_on_efault((int)err);
  lean_obj_res r = lean_alloc_ctor(0, 1, 0); lean_ctor_set(r, 0, lean_box_uint32(err)); return r;
}

static lean_obj_res pf_mk_wait(uint8_t tag, uint32_t code) {
  lean_obj_res o = lean_alloc_ctor(tag, 0, sizeof(uint32_t)); lean_ctor_set_uint32(o, 0, code); return o;
}

static const char *pf_opt_cstr(b_lean_obj_arg opt) {
  return lean_is_scalar(opt) ? NULL : lean_string_cstr(lean_ctor_get(opt, 0));
}

static int32_t pf_resolve_slot(int32_t slot, const int32_t *pinned, size_t n_pinned) {
  if (slot > -2) return slot;
  size_t idx = (size_t)((uint32_t)0 - (uint32_t)slot - 2u);
  return idx < n_pinned ? pinned[idx] : -1;
}

static int pf_i32_has(const int32_t *arr, size_t n, int32_t fd) {
  for (size_t i = 0; i < n; i++) if (arr[i] == fd) return 1;
  return 0;
}

static int pf_pin_handles(b_lean_obj_arg handles, const int32_t *cs, size_t nc, int32_t **out_fds, size_t *out_n) {
  size_t n = lean_array_size(handles);
  *out_n = 0; *out_fds = NULL;
  if (n == 0) return 0;
  int32_t *fds = (int32_t *)malloc(n * sizeof(int32_t));
  if (fds == NULL) return ENOMEM;
  for (size_t i = 0; i < n; i++) {
    LeanFdBox *box = (LeanFdBox *)lean_get_external_data(lean_array_get_core(handles, i));
    int fd = -1, rc = leanswe_fd_box_pin(box, &fd);
    if (rc == EBADF && i <= (size_t)INT32_MAX - 2u && pf_i32_has(cs, nc, (int32_t)(0u - (uint32_t)i - 2u))) {
      fds[i] = -1; continue;
    }
    if (rc != 0) { *out_fds = fds; *out_n = i; return rc; }
    fds[i] = (int32_t)fd;
  }
  *out_fds = fds; *out_n = n; return 0;
}

static void pf_unpin_handles(b_lean_obj_arg handles, size_t n, int32_t *fds) {
  for (size_t i = 0; i < n; i++) {
    if (fds[i] < 0) continue;
    LeanFdBox *box = (LeanFdBox *)lean_get_external_data(lean_array_get_core(handles, i));
    leanswe_fd_box_unpin(box);
  }
  free(fds);
}

static int pf_is_internal_child_pipe(uint32_t flags, int32_t sync_fd, int32_t rep_fd, int32_t slot) {
  if (slot < 0) return 0;
  if (slot == rep_fd) return 1;
  return ((flags & LEANSWE_PF_FLAG_HAS_SYNC_BARRIER) != 0 && slot == sync_fd) ? 1 : 0;
}

static int pf_resolve_vec(
    const int32_t *slots, size_t n, const int32_t *pinned, size_t np,
    uint32_t flags, int32_t sync_fd, int32_t rep_fd, int filter_raw, int32_t **out) {
  *out = NULL;
  if (n == 0) return 0;
  int32_t *vec = (int32_t *)malloc(n * sizeof(int32_t));
  if (vec == NULL) return ENOMEM;
  for (size_t i = 0; i < n; i++) {
    vec[i] = (filter_raw && pf_is_internal_child_pipe(flags, sync_fd, rep_fd, slots[i]))
      ? -1 : pf_resolve_slot(slots[i], pinned, np);
  }
  *out = vec;
  return 0;
}

static const char **pf_alloc_cstr_ptrs(b_lean_obj_arg arr, int *err_out) {
  size_t n = lean_array_size(arr);
  const char **ptrs = (const char **)calloc(n + 1, sizeof(const char *));
  if (ptrs == NULL) { *err_out = ENOMEM; return NULL; }
  for (size_t i = 0; i < n; i++) {
    b_lean_obj_arg b = lean_array_get_core(arr, i); size_t sz = lean_sarray_size(b);
    if (sz == 0 || lean_sarray_cptr(b)[sz - 1] != 0) { free((void *)ptrs); *err_out = EINVAL; return NULL; }
    ptrs[i] = (const char *)lean_sarray_cptr(b);
  } return ptrs;
}

static char *pf_format_fd_arg(const char *pfx, int32_t fd, const char *sfx) {
  size_t len = strlen(pfx) + strlen(sfx) + 24;
  char *buf = (char *)malloc(len);
  if (buf != NULL) snprintf(buf, len, "%s%d%s", pfx, (int)fd, sfx);
  return buf;
}

static void pf_free_arg_ptrs(const char **ptrs, char **owned, size_t n) {
  if (owned != NULL) {
    for (size_t i = 0; i < n; i++) free(owned[i]);
    free(owned);
  }
  free((void *)ptrs);
}

static const char **pf_alloc_arg_ptrs(
    b_lean_obj_arg pfxs, b_lean_obj_arg sfxs, const int32_t *slots,
    const int32_t *pinned, size_t np, char ***owned_out) {
  size_t n = lean_array_size(pfxs);
  const char **ptrs = (const char **)calloc(n + 1, sizeof(const char *));
  char **owned = (char **)calloc(n > 0 ? n : 1u, sizeof(char *));
  if (ptrs == NULL || owned == NULL) { free((void *)ptrs); free(owned); return NULL; }
  for (size_t i = 0; i < n; i++) {
    const char *p = lean_string_cstr(lean_array_get_core(pfxs, i));
    if (slots[i] == -1) {
      ptrs[i] = p;
    } else {
      const char *s = lean_string_cstr(lean_array_get_core(sfxs, i));
      owned[i] = pf_format_fd_arg(p, pf_resolve_slot(slots[i], pinned, np), s);
      if (owned[i] == NULL) {
        pf_free_arg_ptrs(ptrs, owned, i); *owned_out = NULL; return NULL;
      }
      ptrs[i] = owned[i];
    }
  }
  *owned_out = owned;
  return ptrs;
}

static int pf_prune_pipes_locked(int32_t query_fd) {
  size_t w = 0; int hit = 0;
  for (size_t i = 0; i < g_pf_pipes_len; i++) {
    struct stat st; PfTrackedPipeFd e = g_pf_pipes[i];
    if (e.fd >= 0 && fstat((int)e.fd, &st) == 0 && st.st_dev == e.dev && st.st_ino == e.ino) {
      if (e.fd == query_fd) hit = 1;
      g_pf_pipes[w++] = e;
    }
  }
  g_pf_pipes_len = w; return hit;
}

static int pf_track_pipe_pair_locked(int fd0, int fd1) {
  struct stat st0, st1;
  if (fstat(fd0, &st0) != 0 || fstat(fd1, &st1) != 0) return errno != 0 ? errno : EIO;
  if (g_pf_pipes_len + 2 > g_pf_pipes_cap) {
    size_t ncap = g_pf_pipes_cap == 0 ? 16u : g_pf_pipes_cap * 2u;
    PfTrackedPipeFd *nbuf = (PfTrackedPipeFd *)realloc(g_pf_pipes, ncap * sizeof(PfTrackedPipeFd));
    if (nbuf == NULL) return ENOMEM;
    g_pf_pipes = nbuf;
    g_pf_pipes_cap = ncap;
  }
  g_pf_pipes[g_pf_pipes_len++] = (PfTrackedPipeFd){ (int32_t)fd0, st0.st_dev, st0.st_ino };
  g_pf_pipes[g_pf_pipes_len++] = (PfTrackedPipeFd){ (int32_t)fd1, st1.st_dev, st1.st_ino };
  return 0;
}

static void pf_untrack_fd_locked(int32_t fd) {
  size_t w = 0;
  for (size_t i = 0; i < g_pf_pipes_len; i++) {
    if (g_pf_pipes[i].fd != fd) g_pf_pipes[w++] = g_pf_pipes[i];
  }
  g_pf_pipes_len = w;
}

static int pf_child_uses_fd(const LeanswePostForkChildArgs *a, int32_t fd) {
  if (fd < 0 || fd == a->rep_w) return 1;
  if ((a->flags & LEANSWE_PF_FLAG_HAS_SYNC_BARRIER) != 0 && fd == a->sync_r) return 1;
  if ((a->flags & LEANSWE_PF_FLAG_REDIRECT_STDIO) != 0 &&
      (fd == a->stdin_fd || fd == a->stdout_fd || fd == a->stderr_fd)) return 1;
  return pf_i32_has(a->keep_fds, a->n_keep_fds, fd);
}

static int pf_raw_uses_fd(uint32_t flags, const int32_t *ms, const int32_t *rk, size_t nk, int32_t fd) {
  int std_hit = ((flags & LEANSWE_PF_FLAG_REDIRECT_STDIO) != 0) && pf_i32_has(ms + 2, 3, fd);
  return std_hit || pf_i32_has(rk, nk, fd);
}

static int pf_append_tracked_closes_locked(
    LeanswePostForkChildArgs *a, const int32_t *ms, const int32_t *rk, size_t nk, int32_t **buf_out) {
  (void)pf_prune_pipes_locked(-1);
  size_t base_n = a->n_close_fds, cap = base_n + g_pf_pipes_len;
  *buf_out = NULL;
  if (cap == 0) return 0;
  int32_t *full = (int32_t *)malloc(cap * sizeof(int32_t));
  if (full == NULL) return ENOMEM;
  if (base_n > 0) memcpy(full, a->close_fds, base_n * sizeof(int32_t));
  size_t out_n = base_n;
  for (size_t i = 0; i < g_pf_pipes_len; i++) {
    int32_t fd = g_pf_pipes[i].fd, fl = fcntl((int)fd, F_GETFD, 0);
    if (fl >= 0 && pf_raw_uses_fd(a->flags, ms, rk, nk, fd)) {
      free(full); return EBADF;
    }
    if (fl >= 0 && (fl & FD_CLOEXEC) != 0 && !pf_child_uses_fd(a, fd) && !pf_i32_has(full, out_n, fd))
      full[out_n++] = fd;
  }
  a->close_fds = full; a->n_close_fds = out_n; *buf_out = full;
  return 0;
}

static PfSpawnReq *pf_spawner_pop_req(void) {
  pthread_mutex_lock(&g_pf_spawner_mu);
  while (g_pf_spawner_head == NULL) pthread_cond_wait(&g_pf_spawner_cond, &g_pf_spawner_mu);
  PfSpawnReq *req = g_pf_spawner_head;
  g_pf_spawner_head = req->next; req->next = NULL;
  pthread_mutex_unlock(&g_pf_spawner_mu);
  return req;
}

static pid_t pf_raw_fork(void) { return (pid_t)syscall(SYS_clone, (unsigned long)SIGCHLD, 0UL, 0UL, 0UL, 0UL); }

static void *pf_spawner_thread_main(void *arg) {
  (void)arg;
  for (;;) {
    PfSpawnReq *req = pf_spawner_pop_req();
    pid_t pid = pf_raw_fork();
    if (pid == 0) {
      (void)sigprocmask(SIG_SETMASK, &req->caller_mask, NULL);
      leanswe_postfork_run_child(req->args);
      _exit(127);
    }
    int ferr = (pid < 0) ? errno : 0;
    pthread_mutex_lock(&g_pf_spawner_mu);
    req->child_pid = pid;
    req->fork_errno = ferr;
    req->done = 1;
    pthread_cond_broadcast(&g_pf_spawner_done);
    pthread_mutex_unlock(&g_pf_spawner_mu);
  }
  return NULL;
}

static int pf_init_spawner_once(void) {
  if (g_pf_spawner_ready) return 0;
  pthread_t thr;
  sigset_t all_sigs, old_sigs;
  sigfillset(&all_sigs);
  int masked = (pthread_sigmask(SIG_SETMASK, &all_sigs, &old_sigs) == 0);
  int rc = pthread_create(&thr, NULL, pf_spawner_thread_main, NULL);
  if (rc == 0) { pthread_detach(thr); g_pf_spawner_ready = 1; }
  if (masked) pthread_sigmask(SIG_SETMASK, &old_sigs, NULL);
  return rc;
}

static pid_t pf_spawn_via_spawner(const LeanswePostForkChildArgs *args, int *err_out) {
  PfSpawnReq req;
  req.args = args;
  sigemptyset(&req.caller_mask);
  (void)pthread_sigmask(SIG_SETMASK, NULL, &req.caller_mask);
  req.child_pid = -1; req.fork_errno = 0; req.done = 0; req.next = NULL;
  pthread_mutex_lock(&g_pf_spawner_mu);
  int irc = pf_init_spawner_once();
  if (irc != 0) {
    pthread_mutex_unlock(&g_pf_spawner_mu);
    *err_out = irc;
    return -1;
  }
  req.next = g_pf_spawner_head;
  g_pf_spawner_head = &req;
  pthread_cond_signal(&g_pf_spawner_cond);
  while (!req.done) pthread_cond_wait(&g_pf_spawner_done, &g_pf_spawner_mu);
  pthread_mutex_unlock(&g_pf_spawner_mu);
  *err_out = req.fork_errno;
  return req.child_pid;
}

static pid_t pf_dispatch_fork(
    uint32_t immortal, LeanswePostForkChildArgs *args, const int32_t *ms, const int32_t *rk, size_t nk, int *err_out) {
  int32_t *extra_closes = NULL;
  pthread_mutex_lock(&g_pf_pipe_mu);
  int crc = pf_append_tracked_closes_locked(args, ms, rk, nk, &extra_closes);
  if (crc != 0) {
    pthread_mutex_unlock(&g_pf_pipe_mu);
    *err_out = crc;
    return -1;
  }
  pid_t pid = -1;
  if (immortal != 0) {
    pid = pf_spawn_via_spawner(args, err_out);
  } else {
    pid = pf_raw_fork();
    if (pid == 0) { leanswe_postfork_run_child(args); _exit(127); }
    *err_out = (pid < 0) ? errno : 0;
  }
  pthread_mutex_unlock(&g_pf_pipe_mu);
  free(extra_closes);
  return pid;
}

LEAN_EXPORT lean_obj_res leanswe_postfork_host_probe_fd(uint32_t fd) {
  int ifd = (int)(int32_t)fd;
  if (ifd < 0) return pf_mk_err((uint32_t)EBADF);
  pthread_mutex_lock(&g_pf_pipe_mu);
  if (pf_prune_pipes_locked((int32_t)ifd)) {
    pthread_mutex_unlock(&g_pf_pipe_mu); return pf_mk_err((uint32_t)EBADF);
  }
  int rc = fcntl(ifd, F_GETFD, 0), err = errno;
  pthread_mutex_unlock(&g_pf_pipe_mu);
  return (rc == -1) ? pf_mk_err((uint32_t)err) : pf_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_postfork_host_probe_handle(b_lean_obj_arg h_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(h_obj);
  int fd = -1, perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return pf_mk_err((uint32_t)perr);
  int rc = fcntl(fd, F_GETFD, 0), err = errno;
  leanswe_fd_box_unpin(box);
  return rc == -1 ? pf_mk_err((uint32_t)err) : pf_mk_ok(lean_box(0));
}

static void pf_pipe_fd_box_finalize(void *ptr) {
  int saved = errno;
  LeanFdBox *box = (LeanFdBox *)ptr;
  if (box != NULL) {
    pthread_mutex_lock(&g_pf_pipe_mu);
    if (!box->closed && box->fd >= 0) {
      int fd = box->fd;
      close(fd);
      box->fd = -1;
      box->closed = 1;
      pf_untrack_fd_locked((int32_t)fd);
    }
    pthread_mutex_unlock(&g_pf_pipe_mu);
    pthread_mutex_destroy(&box->mu);
    free(box);
  }
  errno = saved;
}

static void pf_pipe_fd_box_foreach(void *ptr, b_lean_obj_arg f) { (void)ptr; (void)f; }

static void pf_init_pipe_fd_class(void) {
  g_pf_pipe_fd_class = lean_register_external_class(pf_pipe_fd_box_finalize, pf_pipe_fd_box_foreach);
}

static lean_obj_res pf_mk_pipe_fd_obj(int fd) {
  pthread_once(&g_pf_pipe_fd_class_once, pf_init_pipe_fd_class);
  LeanFdBox *box = (LeanFdBox *)malloc(sizeof(LeanFdBox));
  if (box == NULL) return NULL;
  pthread_mutex_init(&box->mu, NULL);
  box->fd = fd;
  box->in_use = 0;
  box->closed = 0;
  return lean_alloc_external(g_pf_pipe_fd_class, box);
}

static void pf_cleanup_failed_pipe_objs(int fds[2], lean_obj_res r_obj, lean_obj_res w_obj) {
  if (r_obj != NULL) lean_dec(r_obj);
  if (w_obj != NULL) lean_dec(w_obj);
  pthread_mutex_lock(&g_pf_pipe_mu);
  if (r_obj == NULL) { close(fds[0]); pf_untrack_fd_locked((int32_t)fds[0]); }
  if (w_obj == NULL) { close(fds[1]); pf_untrack_fd_locked((int32_t)fds[1]); }
  pthread_mutex_unlock(&g_pf_pipe_mu);
}

static int pf_reloc_above2(int *fd) {
  if (*fd >= 3) return 0;
  int nfd = fcntl(*fd, F_DUPFD_CLOEXEC, 3);
  if (nfd < 0) return errno == EINVAL ? EMFILE : (errno != 0 ? errno : EIO);
  close(*fd); *fd = nfd; return 0;
}

LEAN_EXPORT lean_obj_res leanswe_postfork_host_pipe_cloexec(void) {
  int fds[2] = { -1, -1 };
  pthread_mutex_lock(&g_pf_pipe_mu);
  (void)pf_prune_pipes_locked(-1);
  int prc = pipe2(fds, O_CLOEXEC);
  int perr = (prc != 0) ? errno : pf_reloc_above2(&fds[0]);
  if (perr == 0) perr = pf_reloc_above2(&fds[1]);
  if (perr == 0) perr = pf_track_pipe_pair_locked(fds[0], fds[1]);
  if (perr != 0 && prc == 0) { close(fds[0]); close(fds[1]); }
  pthread_mutex_unlock(&g_pf_pipe_mu);
  if (perr != 0) return pf_mk_err((uint32_t)perr);
  lean_obj_res r_obj = pf_mk_pipe_fd_obj(fds[0]);
  lean_obj_res w_obj = pf_mk_pipe_fd_obj(fds[1]);
  if (r_obj == NULL || w_obj == NULL) {
    pf_cleanup_failed_pipe_objs(fds, r_obj, w_obj);
    return pf_mk_err((uint32_t)ENOMEM);
  }
  lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, r_obj);
  lean_ctor_set(pair, 1, w_obj);
  return pf_mk_ok(pair);
}

LEAN_EXPORT lean_obj_res leanswe_postfork_host_close_fd(b_lean_obj_arg h_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(h_obj);
  int fd = -1;
  pthread_mutex_lock(&g_pf_pipe_mu);
  if (leanswe_fd_box_pin(box, &fd) == 0) leanswe_fd_box_unpin(box);
  int rc = leanswe_fd_box_close(box);
  if (fd >= 0 && (rc == 0 || leanswe_is_kernel_close_detach_err(rc))) pf_untrack_fd_locked((int32_t)fd);
  pthread_mutex_unlock(&g_pf_pipe_mu);
  return rc != 0 ? pf_mk_err((uint32_t)rc) : pf_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_postfork_host_setpgid(uint32_t pid, uint32_t pgid) {
  if ((int32_t)pid <= 0 || (int32_t)pgid <= 0) return pf_mk_err((uint32_t)EINVAL);
  return setpgid((pid_t)(int32_t)pid, (pid_t)(int32_t)pgid) != 0 ? pf_mk_err((uint32_t)errno) : pf_mk_ok(lean_box(0));
}

static int pf_mask_sigpipe(sigset_t *old_set, int *was_blocked) {
  sigset_t pipe_set;
  sigemptyset(&pipe_set);
  sigaddset(&pipe_set, SIGPIPE);
  int ok = (pthread_sigmask(SIG_BLOCK, &pipe_set, old_set) == 0);
  *was_blocked = ok && sigismember(old_set, SIGPIPE);
  return ok;
}

static void pf_restore_sigpipe(int masked, int was_blocked, const sigset_t *old_set, int drain) {
  if (!masked) return;
  if (!was_blocked && drain) {
    sigset_t pipe_set;
    struct timespec zero_ts = { 0, 0 };
    sigemptyset(&pipe_set);
    sigaddset(&pipe_set, SIGPIPE);
    (void)sigtimedwait(&pipe_set, NULL, &zero_ts);
  }
  pthread_sigmask(SIG_SETMASK, old_set, NULL);
}

LEAN_EXPORT lean_obj_res leanswe_postfork_host_write_once(
    b_lean_obj_arg h_obj, b_lean_obj_arg ba, uint64_t off, uint64_t len) {
  size_t total = lean_sarray_size(ba);
  if (off > total || len > total - off) return pf_mk_err((uint32_t)EINVAL);
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(h_obj);
  int fd = -1, perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return pf_mk_err((uint32_t)perr);
  sigset_t old_set;
  int was_blocked = 0, masked = pf_mask_sigpipe(&old_set, &was_blocked);
  ssize_t n = write(fd, lean_sarray_cptr(ba) + off, (size_t)len);
  int err = (n < 0) ? errno : 0;
  pf_restore_sigpipe(masked, was_blocked, &old_set, n < 0 && err == EPIPE);
  leanswe_fd_box_unpin(box);
  return n < 0 ? pf_mk_err((uint32_t)err) : pf_mk_ok(lean_box_uint64((uint64_t)n));
}

static lean_obj_res pf_finish_read(ssize_t n, int err, uint8_t *buf) {
  if (n < 0) { free(buf); return pf_mk_err((uint32_t)err); }
  lean_obj_res ba = lean_alloc_sarray(1, (size_t)n, (size_t)n);
  if (n > 0) memcpy(lean_sarray_cptr(ba), buf, (size_t)n);
  free(buf);
  return pf_mk_ok(ba);
}

LEAN_EXPORT lean_obj_res leanswe_postfork_host_read_once(b_lean_obj_arg h_obj, uint64_t max_bytes) {
  size_t cap = (max_bytes > 1048576ULL) ? 1048576u : (size_t)max_bytes;
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(h_obj);
  int fd = -1, perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return pf_mk_err((uint32_t)perr);
  uint8_t *buf = (uint8_t *)malloc(cap > 0 ? cap : 1u);
  if (buf == NULL) { leanswe_fd_box_unpin(box); return pf_mk_err((uint32_t)ENOMEM); }
  ssize_t n = read(fd, buf, cap);
  int err = errno;
  leanswe_fd_box_unpin(box);
  return pf_finish_read(n, err, buf);
}

LEAN_EXPORT lean_obj_res leanswe_postfork_host_wait_once(uint32_t pid) {
  if ((int32_t)pid <= 0) return pf_mk_err((uint32_t)EINVAL);
  int st = 0;
  if (waitpid((pid_t)(int32_t)pid, &st, 0) < 0) return pf_mk_err((uint32_t)errno);
  if (WIFEXITED(st)) return pf_mk_ok(pf_mk_wait(0, (uint32_t)WEXITSTATUS(st)));
  if (WIFSIGNALED(st)) return pf_mk_ok(pf_mk_wait(1, (uint32_t)WTERMSIG(st)));
  return pf_mk_err((uint32_t)ECHILD);
}

LEAN_EXPORT lean_obj_res leanswe_postfork_host_fork_run(
    uint32_t flags, uint32_t immortal, b_lean_obj_arg handles, b_lean_obj_arg meta_ba,
    b_lean_obj_arg close_ba, b_lean_obj_arg keep_ba, b_lean_obj_arg pfxs, b_lean_obj_arg sfxs,
    b_lean_obj_arg arg_slots_ba, b_lean_obj_arg cwd_opt, b_lean_obj_arg path_str, b_lean_obj_arg envp_arr) {
  size_t n_args = lean_array_size(pfxs), nc = lean_sarray_size(close_ba) / 4, nk = lean_sarray_size(keep_ba) / 4;
  if (lean_sarray_size(meta_ba) != 20 || lean_array_size(sfxs) != n_args || lean_sarray_size(arg_slots_ba) != n_args * 4)
    return pf_mk_err((uint32_t)EINVAL);
  int32_t *pinned = NULL, *closes = NULL, *keeps = NULL;
  size_t np = 0;
  const int32_t *cs = (const int32_t *)(const void *)lean_sarray_cptr(close_ba);
  int rc = pf_pin_handles(handles, cs, nc, &pinned, &np);
  if (rc != 0) { pf_unpin_handles(handles, np, pinned); return pf_mk_err((uint32_t)rc); }
  const int32_t *ms = (const int32_t *)(const void *)lean_sarray_cptr(meta_ba);
  const int32_t *rk = (const int32_t *)(const void *)lean_sarray_cptr(keep_ba);
  int32_t sync_fd = pf_resolve_slot(ms[0], pinned, np), rep_fd = pf_resolve_slot(ms[1], pinned, np);
  char **owned = NULL;
  const char **argv = pf_alloc_arg_ptrs(pfxs, sfxs, (const int32_t *)(const void *)lean_sarray_cptr(arg_slots_ba), pinned, np, &owned);
  int env_err = 0; const char **envp = pf_alloc_cstr_ptrs(envp_arr, &env_err);
  int rc1 = pf_resolve_vec(cs, nc, pinned, np, flags, sync_fd, rep_fd, 1, &closes);
  int rc2 = pf_resolve_vec(rk, nk, pinned, np, 0u, -1, -1, 0, &keeps);
  if (argv == NULL || owned == NULL || envp == NULL || rc1 != 0 || rc2 != 0) {
    pf_free_arg_ptrs(argv, owned, n_args); free((void *)envp); free(closes); free(keeps);
    pf_unpin_handles(handles, np, pinned); return pf_mk_err((uint32_t)(env_err ? env_err : ENOMEM));
  }
  LeanswePostForkChildArgs args = { flags, sync_fd, pf_resolve_slot(ms[2], pinned, np),
    pf_resolve_slot(ms[3], pinned, np), pf_resolve_slot(ms[4], pinned, np), rep_fd,
    closes, nc, keeps, nk, pf_opt_cstr(cwd_opt), lean_string_cstr(path_str), argv, envp };
  int ferr = 0;
  pid_t pid = pf_dispatch_fork(immortal, &args, ms, rk, nk, &ferr);
  pf_free_arg_ptrs(argv, owned, n_args); free((void *)envp); free(closes); free(keeps);
  pf_unpin_handles(handles, np, pinned);
  return pid < 0 ? pf_mk_err((uint32_t)ferr) : pf_mk_ok(lean_box_uint32((uint32_t)(int32_t)pid));
}
