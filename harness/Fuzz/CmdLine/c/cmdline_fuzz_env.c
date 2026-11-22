#define _GNU_SOURCE

#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdio_ext.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>

extern char **environ;
static int g_saved_fds[3] = {-1, -1, -1};
static int g_saved_init = 0;

static int has_nul_byte(b_lean_obj_arg ba) {
  size_t n = lean_sarray_size(ba);
  return n > 0u && memchr(lean_sarray_cptr(ba), 0, n) != NULL;
}

static char *dup_ba_cstr(b_lean_obj_arg ba) {
  size_t n = lean_sarray_size(ba);
  char *buf = (char *)malloc(n + 1u);
  if (buf == NULL) {
    return NULL;
  }
  if (n > 0u) {
    memcpy(buf, lean_sarray_cptr(ba), n);
  }
  buf[n] = '\0';
  return buf;
}

static int ensure_hi_fd(int fd) {
  if (fd >= 0 && fd < 3) {
    int hi = fcntl(fd, F_DUPFD_CLOEXEC, 3);
    close(fd);
    return hi;
  }
  if (fd >= 3) {
    (void)fcntl(fd, F_SETFD, FD_CLOEXEC);
  }
  return fd;
}

static int open_pty_pair(int *master_out, int *slave_out) {
  char pts_name[128];
  int m = ensure_hi_fd(posix_openpt(O_RDWR | O_NOCTTY | O_CLOEXEC));
  int s;
  if (m < 0) {
    return -1;
  }
  if (grantpt(m) != 0 || unlockpt(m) != 0 || ptsname_r(m, pts_name, sizeof(pts_name)) != 0) {
    close(m);
    return -1;
  }
  s = ensure_hi_fd(open(pts_name, O_RDWR | O_NOCTTY | O_CLOEXEC));
  if (s < 0) {
    close(m);
    return -1;
  }
  *master_out = m;
  *slave_out = s;
  return 0;
}

static int open_pty_hungup(int keep_master) {
  int m = -1;
  int s = -1;
  if (open_pty_pair(&m, &s) < 0) return -1;
  if (keep_master) { close(s); return m; }
  close(m);
  return s;
}

static int open_special_fd(uint8_t kind) {
  static const char *const paths[5] = {
    "/dev/null", "/dev/full", "/tmp", "/dev/null", "/dev/null"
  };
  static const int flags[5] = {
    O_RDWR | O_CLOEXEC, O_RDWR | O_CLOEXEC,
    O_RDONLY | O_DIRECTORY | O_CLOEXEC, O_WRONLY | O_CLOEXEC, O_RDONLY | O_CLOEXEC
  };
  int p[2];
  if (kind < 5u) return ensure_hi_fd(open(paths[kind], flags[kind]));
  if (kind == 6u || kind == 7u) return open_pty_hungup(kind == 6u);
  if (pipe2(p, O_CLOEXEC) < 0) return -1;
  p[0] = ensure_hi_fd(p[0]);
  p[1] = ensure_hi_fd(p[1]);
  close(p[0]);
  return p[1];
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_save_stdio(uint32_t unused) {
  int saved_errno = errno;
  (void)unused;
  if (g_saved_init == 0) {
    g_saved_fds[0] = fcntl(0, F_DUPFD_CLOEXEC, 3);
    g_saved_fds[1] = fcntl(1, F_DUPFD_CLOEXEC, 3);
    g_saved_fds[2] = fcntl(2, F_DUPFD_CLOEXEC, 3);
    g_saved_init = 1;
  }
  errno = saved_errno;
  return (g_saved_fds[0] < 0 && g_saved_fds[1] < 0 && g_saved_fds[2] < 0) ? 1u : 0u;
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_reset_streams(uint32_t unused) {
  (void)unused;
  __fpurge(stdin);
  clearerr(stdin);
  __fpurge(stdout);
  clearerr(stdout);
  __fpurge(stderr);
  clearerr(stderr);
  errno = 0;
  return 0u;
}

static uint32_t ret_saved_errno(int saved_errno, uint32_t rc) {
  errno = saved_errno;
  return rc;
}

static void restore_slot(int i) {
  if (g_saved_fds[i] >= 0) {
    dup2(g_saved_fds[i], i);
  } else if (g_saved_init != 0) {
    close(i);
  }
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_restore_stdio(uint32_t unused) {
  (void)unused;
  leanswe_cmdfuzz_reset_streams(0u);
  restore_slot(0);
  restore_slot(1);
  restore_slot(2);
  errno = 0;
  return 0u;
}

static void purge_slot(uint8_t slot) {
  if (slot == 0u) {
    __fpurge(stdin);
    clearerr(stdin);
  } else if (slot == 1u) {
    __fpurge(stdout);
    clearerr(stdout);
  } else if (slot == 2u) {
    __fpurge(stderr);
    clearerr(stderr);
  }
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_close_slot(uint8_t slot) {
  int saved_errno = errno;
  uint32_t rc = 1u;
  if (slot <= 2u) {
    purge_slot(slot);
    rc = close((int)slot) < 0 ? (uint32_t)errno : 0u;
  }
  return ret_saved_errno(saved_errno, rc);
}

static int setup_pipe_write(int wfd, b_lean_obj_arg ba) {
  size_t n = lean_sarray_size(ba);
  if (fcntl(wfd, F_SETFL, O_NONBLOCK) < 0) {
    return -1;
  }
  if (n == 0u) {
    return 0;
  }
  if (fcntl(wfd, F_GETPIPE_SZ) < (int)n) {
    (void)fcntl(wfd, F_SETPIPE_SZ, 65536);
  }
  return write(wfd, lean_sarray_cptr(ba), n) == (ssize_t)n ? 0 : -1;
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_setup_pipe_in(b_lean_obj_arg ba, uint8_t nonblock, uint8_t close_writer) {
  int saved_errno = errno;
  int p[2];
  if (pipe2(p, O_CLOEXEC) < 0) {
    return ret_saved_errno(saved_errno, 0xfffffffeu);
  }
  p[0] = ensure_hi_fd(p[0]);
  p[1] = ensure_hi_fd(p[1]);
  if (p[0] < 0 || p[1] < 0) {
    if (p[0] >= 0) close(p[0]);
    if (p[1] >= 0) close(p[1]);
    return ret_saved_errno(saved_errno, 0xfffffffeu);
  }
  if (setup_pipe_write(p[1], ba) < 0) {
    close(p[0]);
    close(p[1]);
    return ret_saved_errno(saved_errno, 0xfffffffdu);
  }
  if (nonblock != 0u && fcntl(p[0], F_SETFL, O_NONBLOCK) < 0) {
    close(p[0]);
    close(p[1]);
    return ret_saved_errno(saved_errno, 0xfffffffeu);
  }
  purge_slot(0u);
  if (dup2(p[0], 0) < 0) {
    close(p[0]);
    close(p[1]);
    return ret_saved_errno(saved_errno, 0xfffffffeu);
  }
  close(p[0]);
  if (close_writer != 0u) {
    close(p[1]);
    return ret_saved_errno(saved_errno, 0xffffffffu);
  }
  return ret_saved_errno(saved_errno, (uint32_t)p[1]);
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_setup_memfd_in(b_lean_obj_arg ba) {
  int saved_errno = errno;
  int fd = ensure_hi_fd((int)syscall(SYS_memfd_create, "cmdfuzz", 1u));
  size_t n = lean_sarray_size(ba);
  ssize_t w = 0;
  purge_slot(0u);
  if (fd < 0) {
    return ret_saved_errno(saved_errno, 1u);
  }
  if (n > 0u) {
    w = write(fd, lean_sarray_cptr(ba), n);
  }
  if (w < 0 || (size_t)w != n || lseek(fd, 0, SEEK_SET) < 0 || dup2(fd, 0) < 0) {
    close(fd);
    return ret_saved_errno(saved_errno, 1u);
  }
  close(fd);
  return ret_saved_errno(saved_errno, 0u);
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_setup_special(uint8_t slot, uint8_t kind) {
  int saved_errno = errno;
  int fd;
  if (slot > 2u) {
    return ret_saved_errno(saved_errno, 1u);
  }
  purge_slot(slot);
  fd = open_special_fd(kind);
  if (fd < 0) {
    return ret_saved_errno(saved_errno, 1u);
  }
  if (dup2(fd, (int)slot) < 0) {
    close(fd);
    return ret_saved_errno(saved_errno, 1u);
  }
  close(fd);
  return ret_saved_errno(saved_errno, 0u);
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_setup_capture(uint8_t slot, uint8_t nonblock) {
  int saved_errno = errno;
  int p[2];
  if (slot > 2u || pipe2(p, O_CLOEXEC) < 0) {
    return ret_saved_errno(saved_errno, 0xfffffffeu);
  }
  p[0] = ensure_hi_fd(p[0]);
  p[1] = ensure_hi_fd(p[1]);
  if (p[0] < 0 || p[1] < 0) {
    if (p[0] >= 0) close(p[0]);
    if (p[1] >= 0) close(p[1]);
    return ret_saved_errno(saved_errno, 0xfffffffeu);
  }
  purge_slot(slot);
  (void)fcntl(p[1], F_SETPIPE_SZ, nonblock != 0u ? 4096 : 65536);
  if ((nonblock != 0u && fcntl(p[1], F_SETFL, O_NONBLOCK) < 0) || fcntl(p[0], F_SETFL, O_NONBLOCK) < 0 || dup2(p[1], (int)slot) < 0) {
    close(p[0]);
    close(p[1]);
    return ret_saved_errno(saved_errno, 0xfffffffeu);
  }
  close(p[1]);
  return ret_saved_errno(saved_errno, (uint32_t)p[0]);
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_get_pipe_cap(uint8_t slot) {
  int saved_errno = errno;
  int cap = fcntl((int)slot, F_GETPIPE_SZ);
  return ret_saved_errno(saved_errno, cap > 0 ? (uint32_t)cap : 65536u);
}

LEAN_EXPORT lean_obj_res leanswe_cmdfuzz_drain_fd(uint32_t fd_u, uint32_t cap) {
  int saved_errno = errno;
  uint8_t buf[65536];
  size_t want = (size_t)(cap > 65536u ? 65536u : cap);
  ssize_t got = want > 0u ? read((int)fd_u, buf, want) : 0;
  size_t len = got > 0 ? (size_t)got : 0u;
  lean_obj_res ba = lean_alloc_sarray(1, len, len);
  if (len > 0u) {
    memcpy(lean_sarray_cptr(ba), buf, len);
  }
  errno = saved_errno;
  return ba;
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_write_fd(uint32_t fd_u, b_lean_obj_arg ba) {
  int saved_errno = errno;
  size_t n = lean_sarray_size(ba);
  ssize_t w = write((int)fd_u, lean_sarray_cptr(ba), n);
  uint32_t rc = w < 0 ? (0x80000000u | (uint32_t)errno) : (uint32_t)w;
  return ret_saved_errno(saved_errno, rc);
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_close_fd(uint32_t fd_u) {
  int saved_errno = errno;
  if ((int)fd_u >= 3) {
    close((int)fd_u);
  }
  errno = saved_errno;
  return 0u;
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_setup_pty(uint8_t echo_off) {
  int saved_errno = errno;
  int m = -1;
  int s = -1;
  struct termios tio;
  purge_slot(0u);
  if (open_pty_pair(&m, &s) < 0) {
    return ret_saved_errno(saved_errno, 0xfffffffeu);
  }
  if (echo_off != 0u && tcgetattr(s, &tio) == 0) {
    tio.c_lflag &= ~(tcflag_t)(ECHO | ECHONL);
    tcsetattr(s, TCSANOW, &tio);
  }
  if (dup2(s, 0) < 0) {
    close(m);
    close(s);
    return ret_saved_errno(saved_errno, 0xfffffffeu);
  }
  close(s);
  (void)fcntl(m, F_SETFD, FD_CLOEXEC);
  (void)fcntl(m, F_SETFL, O_NONBLOCK);
  return ret_saved_errno(saved_errno, (uint32_t)m);
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_set_env_bytes(b_lean_obj_arg k_ba, b_lean_obj_arg v_ba, uint8_t ovw) {
  char *k;
  char *v;
  uint32_t rc = 0u;
  if (has_nul_byte(k_ba) || has_nul_byte(v_ba)) {
    errno = EINVAL;
    return (uint32_t)EINVAL;
  }
  k = dup_ba_cstr(k_ba);
  v = dup_ba_cstr(v_ba);
  if (k == NULL || v == NULL) {
    errno = ENOMEM;
    rc = (uint32_t)ENOMEM;
  } else if (setenv(k, v, ovw ? 1 : 0) < 0) {
    rc = (uint32_t)errno;
  }
  free(k);
  free(v);
  return rc;
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_unset_env_bytes(b_lean_obj_arg k_ba) {
  char *k;
  uint32_t rc = 0u;
  if (has_nul_byte(k_ba)) {
    errno = EINVAL;
    return (uint32_t)EINVAL;
  }
  k = dup_ba_cstr(k_ba);
  if (k == NULL) {
    errno = ENOMEM;
    return (uint32_t)ENOMEM;
  }
  if (unsetenv(k) < 0) {
    rc = (uint32_t)errno;
  }
  free(k);
  return rc;
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_clear_env(uint32_t unused) {
  (void)unused;
  return clearenv() < 0 ? (uint32_t)errno : 0u;
}

static void exec_child_setup(uint8_t dfl_sigpipe, uint8_t broken_stdout) {
  if (dfl_sigpipe != 0u) {
    signal(SIGPIPE, SIG_DFL);
  }
  if (broken_stdout != 0u) {
    int fd = open_special_fd(5u);
    if (fd < 0 || dup2(fd, 1) < 0) {
      _exit(126);
    }
    close(fd);
  }
}

static int wait_child_masked(pid_t pid, int *st) {
  sigset_t blk, old;
  int rc;
  sigemptyset(&blk);
  sigaddset(&blk, SIGALRM);
  (void)pthread_sigmask(SIG_BLOCK, &blk, &old);
  rc = waitpid(pid, st, 0);
  while (rc < 0 && errno == EINTR) {
    rc = waitpid(pid, st, 0);
  }
  (void)pthread_sigmask(SIG_SETMASK, &old, NULL);
  return rc;
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_exec_raw(b_lean_obj_arg exe_ba, b_lean_obj_arg a1_ba,
    b_lean_obj_arg a2_ba, b_lean_obj_arg a3_ba, uint8_t dfl_sigpipe, uint8_t broken_stdout) {
  int saved_errno = errno;
  char *c_exe = has_nul_byte(exe_ba) ? NULL : dup_ba_cstr(exe_ba);
  char *c_a1 = dup_ba_cstr(a1_ba);
  char *c_a2 = dup_ba_cstr(a2_ba);
  char *c_a3 = dup_ba_cstr(a3_ba);
  char *argv_buf[5] = {c_exe, c_a1, c_a2, c_a3, NULL};
  pid_t pid;
  int st = 0;
  if (c_exe == NULL || c_a1 == NULL || c_a2 == NULL || c_a3 == NULL) {
    free(c_exe); free(c_a1); free(c_a2); free(c_a3);
    return ret_saved_errno(saved_errno, 1000u);
  }
  pid = fork();
  if (pid == 0) {
    exec_child_setup(dfl_sigpipe, broken_stdout);
    execve(c_exe, argv_buf, environ);
    _exit(127);
  }
  free(c_exe); free(c_a1); free(c_a2); free(c_a3);
  if (pid < 0 || wait_child_masked(pid, &st) < 0) {
    return ret_saved_errno(saved_errno, 1000u);
  }
  if (WIFEXITED(st)) {
    return ret_saved_errno(saved_errno, (uint32_t)WEXITSTATUS(st));
  }
  return ret_saved_errno(saved_errno, WIFSIGNALED(st) ? 256u + (uint32_t)WTERMSIG(st) : 1000u);
}

extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

static void *cmdfuzz_stack_worker(void *arg) {
  lean_obj_res fn = (lean_obj_res)arg;
  lean_initialize_thread();
  lean_obj_res res = lean_apply_2(fn, lean_box(0), lean_io_mk_world());
  uint32_t rc = lean_io_result_is_ok(res) ? lean_unbox_uint32(lean_io_result_get_value(res)) : 99u;
  lean_dec_ref(res);
  lean_finalize_thread();
  return (void *)(uintptr_t)rc;
}

LEAN_EXPORT uint32_t leanswe_cmdfuzz_run_on_1mib_stack(lean_obj_arg fn) {
  pthread_attr_t attr;
  pthread_t th;
  void *ret = NULL;
  if (pthread_attr_init(&attr) != 0) { lean_dec(fn); return 98u; }
  if (pthread_attr_setstacksize(&attr, 1048576u) != 0 || pthread_create(&th, &attr, cmdfuzz_stack_worker, (void *)fn) != 0) {
    (void)pthread_attr_destroy(&attr); lean_dec(fn); return 98u;
  }
  (void)pthread_join(th, &ret);
  (void)pthread_attr_destroy(&attr);
  return (uint32_t)(uintptr_t)ret;
}
