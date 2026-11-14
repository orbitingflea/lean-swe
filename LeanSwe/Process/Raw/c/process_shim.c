#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

typedef struct ProcessSlot {
  uint64_t handle_id;
  pid_t pid;
  pid_t pgid;
  int stdin_fd;
  int stdout_fd;
  int stderr_fd;
  uint8_t waited;
  uint32_t exit_code;
  uint32_t term_signal;
  uint8_t *stdout_buf;
  size_t stdout_len;
  uint8_t *stderr_buf;
  size_t stderr_len;
  struct ProcessSlot *next;
} ProcessSlot;

static pthread_mutex_t g_proc_mu = PTHREAD_MUTEX_INITIALIZER;
static ProcessSlot *g_proc_list = NULL;
static uint64_t g_next_handle_id = 1;
static size_t g_active_count = 0;

static int has_embedded_nul(b_lean_obj_arg s) {
  size_t sz = lean_string_size(s);
  if (sz == 0) {
    return 0;
  }
  const char *cstr = lean_string_cstr(s);
  return strlen(cstr) != sz - 1;
}

static int set_cloexec(int fd) {
  int flags = fcntl(fd, F_GETFD, 0);
  if (flags < 0) {
    return -1;
  }
  return fcntl(fd, F_SETFD, flags | FD_CLOEXEC);
}

static int clear_cloexec(int fd) {
  int flags = fcntl(fd, F_GETFD, 0);
  if (flags < 0) {
    return -1;
  }
  return fcntl(fd, F_SETFD, flags & ~FD_CLOEXEC);
}

static int set_nonblock(int fd) {
  int flags = fcntl(fd, F_GETFL, 0);
  if (flags < 0) {
    return -1;
  }
  return fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

static void close_if_open(int *fd) {
  if (*fd >= 0) {
    close(*fd);
    *fd = -1;
  }
}

static void free_str_array(char **arr, size_t count) {
  if (arr == NULL) {
    return;
  }
  for (size_t i = 0; i < count; i++) {
    free(arr[i]);
  }
  free(arr);
}

static char **build_argv(b_lean_obj_arg prog_obj, b_lean_obj_arg args_obj, int *err_out) {
  size_t nargs = lean_array_size(args_obj);
  char **argv = (char **)calloc(nargs + 2, sizeof(char *));
  if (argv == NULL) {
    *err_out = ENOMEM;
    return NULL;
  }
  argv[0] = strdup(lean_string_cstr(prog_obj));
  if (argv[0] == NULL) {
    free(argv);
    *err_out = ENOMEM;
    return NULL;
  }
  for (size_t i = 0; i < nargs; i++) {
    b_lean_obj_arg arg_obj = lean_array_get_core(args_obj, i);
    if (has_embedded_nul(arg_obj)) {
      free_str_array(argv, i + 1);
      *err_out = EINVAL;
      return NULL;
    }
    argv[i + 1] = strdup(lean_string_cstr(arg_obj));
    if (argv[i + 1] == NULL) {
      free_str_array(argv, i + 1);
      *err_out = ENOMEM;
      return NULL;
    }
  }
  argv[nargs + 1] = NULL;
  return argv;
}

static char **build_envp(
    uint8_t inherit_env,
    b_lean_obj_arg keys_obj,
    b_lean_obj_arg has_vals_obj,
    b_lean_obj_arg vals_obj,
    int *err_out) {
  size_t n_overrides = lean_array_size(keys_obj);
  if (lean_sarray_size(has_vals_obj) != n_overrides || lean_array_size(vals_obj) != n_overrides) {
    *err_out = EINVAL;
    return NULL;
  }
  size_t base_count = 0;
  if (inherit_env && environ != NULL) {
    while (environ[base_count] != NULL) {
      base_count++;
    }
  }
  size_t cap = base_count + n_overrides + 1;
  char **envp = (char **)calloc(cap, sizeof(char *));
  if (envp == NULL) {
    *err_out = ENOMEM;
    return NULL;
  }
  size_t count = 0;
  for (size_t i = 0; i < base_count; i++) {
    envp[count] = strdup(environ[i]);
    if (envp[count] == NULL) {
      free_str_array(envp, count);
      *err_out = ENOMEM;
      return NULL;
    }
    count++;
  }
  const uint8_t *has_vals = lean_sarray_cptr(has_vals_obj);
  for (size_t i = 0; i < n_overrides; i++) {
    b_lean_obj_arg k_obj = lean_array_get_core(keys_obj, i);
    b_lean_obj_arg v_obj = lean_array_get_core(vals_obj, i);
    if (has_embedded_nul(k_obj)) {
      free_str_array(envp, count);
      *err_out = EINVAL;
      return NULL;
    }
    const char *k = lean_string_cstr(k_obj);
    size_t klen = strlen(k);
    if (klen == 0 || strchr(k, '=') != NULL) {
      free_str_array(envp, count);
      *err_out = EINVAL;
      return NULL;
    }
    for (size_t j = 0; j < count;) {
      if (strncmp(envp[j], k, klen) == 0 && envp[j][klen] == '=') {
        free(envp[j]);
        envp[j] = envp[count - 1];
        envp[count - 1] = NULL;
        count--;
      } else {
        j++;
      }
    }
    if (has_vals[i]) {
      if (has_embedded_nul(v_obj)) {
        free_str_array(envp, count);
        *err_out = EINVAL;
        return NULL;
      }
      const char *v = lean_string_cstr(v_obj);
      size_t vlen = strlen(v);
      char *entry = (char *)malloc(klen + 1 + vlen + 1);
      if (entry == NULL) {
        free_str_array(envp, count);
        *err_out = ENOMEM;
        return NULL;
      }
      memcpy(entry, k, klen);
      entry[klen] = '=';
      memcpy(entry + klen + 1, v, vlen + 1);
      envp[count++] = entry;
    }
  }
  envp[count] = NULL;
  return envp;
}

static size_t count_str_array(char **arr) {
  size_t n = 0;
  if (arr == NULL) {
    return 0;
  }
  while (arr[n] != NULL) {
    n++;
  }
  return n;
}

static ProcessSlot *find_slot_locked(uint64_t handle_id) {
  ProcessSlot *cur = g_proc_list;
  while (cur != NULL) {
    if (cur->handle_id == handle_id) {
      return cur;
    }
    cur = cur->next;
  }
  return NULL;
}

static ProcessSlot *detach_slot_locked(uint64_t handle_id) {
  ProcessSlot **prev = &g_proc_list;
  while (*prev != NULL) {
    if ((*prev)->handle_id == handle_id) {
      ProcessSlot *found = *prev;
      *prev = found->next;
      found->next = NULL;
      if (g_active_count > 0) {
        g_active_count--;
      }
      return found;
    }
    prev = &(*prev)->next;
  }
  return NULL;
}

typedef struct SpawnErrMsg {
  int errnum;
  int phase;
} SpawnErrMsg;

static void write_all_fd(int fd, const void *buf, size_t len) {
  const uint8_t *p = (const uint8_t *)buf;
  size_t off = 0;
  while (off < len) {
    ssize_t n = write(fd, p + off, len - off);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      break;
    }
    off += (size_t)n;
  }
}

LEAN_EXPORT lean_obj_res leanswe_process_spawn(
    b_lean_obj_arg prog_obj,
    b_lean_obj_arg args_obj,
    uint8_t has_cwd,
    b_lean_obj_arg cwd_obj,
    uint8_t inherit_env,
    b_lean_obj_arg env_keys_obj,
    b_lean_obj_arg env_has_vals_obj,
    b_lean_obj_arg env_vals_obj,
    lean_obj_arg w) {
  (void)w;
  if (has_embedded_nul(prog_obj) || lean_string_size(prog_obj) <= 1) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, prog_obj));
  }
  if (has_cwd && has_embedded_nul(cwd_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, cwd_obj));
  }

  int prep_err = 0;
  char **argv = build_argv(prog_obj, args_obj, &prep_err);
  if (argv == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(prep_err, prog_obj));
  }
  char **envp = build_envp(inherit_env, env_keys_obj, env_has_vals_obj, env_vals_obj, &prep_err);
  if (envp == NULL) {
    free_str_array(argv, count_str_array(argv));
    return lean_io_result_mk_error(lean_decode_io_error(prep_err, prog_obj));
  }

  int in_pipe[2] = {-1, -1};
  int out_pipe[2] = {-1, -1};
  int err_pipe[2] = {-1, -1};
  int exec_pipe[2] = {-1, -1};

  if (pipe(in_pipe) != 0 || pipe(out_pipe) != 0 || pipe(err_pipe) != 0 || pipe(exec_pipe) != 0) {
    int err = errno;
    close_if_open(&in_pipe[0]);
    close_if_open(&in_pipe[1]);
    close_if_open(&out_pipe[0]);
    close_if_open(&out_pipe[1]);
    close_if_open(&err_pipe[0]);
    close_if_open(&err_pipe[1]);
    close_if_open(&exec_pipe[0]);
    close_if_open(&exec_pipe[1]);
    free_str_array(argv, count_str_array(argv));
    free_str_array(envp, count_str_array(envp));
    return lean_io_result_mk_error(lean_decode_io_error(err, prog_obj));
  }

  (void)set_cloexec(exec_pipe[0]);
  (void)set_cloexec(exec_pipe[1]);
  (void)set_cloexec(in_pipe[0]);
  (void)set_cloexec(in_pipe[1]);
  (void)set_cloexec(out_pipe[0]);
  (void)set_cloexec(out_pipe[1]);
  (void)set_cloexec(err_pipe[0]);
  (void)set_cloexec(err_pipe[1]);

  const char *prog_cstr = lean_string_cstr(prog_obj);
  const char *cwd_cstr = has_cwd ? lean_string_cstr(cwd_obj) : NULL;

  pid_t pid = fork();
  if (pid < 0) {
    int err = errno;
    close_if_open(&in_pipe[0]);
    close_if_open(&in_pipe[1]);
    close_if_open(&out_pipe[0]);
    close_if_open(&out_pipe[1]);
    close_if_open(&err_pipe[0]);
    close_if_open(&err_pipe[1]);
    close_if_open(&exec_pipe[0]);
    close_if_open(&exec_pipe[1]);
    free_str_array(argv, count_str_array(argv));
    free_str_array(envp, count_str_array(envp));
    return lean_io_result_mk_error(lean_decode_io_error(err, prog_obj));
  }

  if (pid == 0) {
    setpgid(0, 0);
    signal(SIGPIPE, SIG_DFL);

    close_if_open(&in_pipe[1]);
    close_if_open(&out_pipe[0]);
    close_if_open(&err_pipe[0]);
    close_if_open(&exec_pipe[0]);

    if (dup2(in_pipe[0], STDIN_FILENO) < 0 ||
        dup2(out_pipe[1], STDOUT_FILENO) < 0 ||
        dup2(err_pipe[1], STDERR_FILENO) < 0) {
      SpawnErrMsg msg = {errno, 2};
      write_all_fd(exec_pipe[1], &msg, sizeof(msg));
      _exit(127);
    }

    if (in_pipe[0] > STDERR_FILENO) close_if_open(&in_pipe[0]);
    if (out_pipe[1] > STDERR_FILENO) close_if_open(&out_pipe[1]);
    if (err_pipe[1] > STDERR_FILENO) close_if_open(&err_pipe[1]);
    (void)clear_cloexec(STDIN_FILENO);
    (void)clear_cloexec(STDOUT_FILENO);
    (void)clear_cloexec(STDERR_FILENO);

    if (has_cwd && cwd_cstr != NULL) {
      if (chdir(cwd_cstr) != 0) {
        SpawnErrMsg msg = {errno, 1};
        write_all_fd(exec_pipe[1], &msg, sizeof(msg));
        _exit(127);
      }
    }

    environ = envp;
    execvp(prog_cstr, argv);
    SpawnErrMsg msg = {errno, 2};
    write_all_fd(exec_pipe[1], &msg, sizeof(msg));
    _exit(127);
  }

  /* Parent also calls setpgid to eliminate the fork/execpgid race before any kill(-pgid). */
  (void)setpgid(pid, pid);

  close_if_open(&in_pipe[0]);
  close_if_open(&out_pipe[1]);
  close_if_open(&err_pipe[1]);
  close_if_open(&exec_pipe[1]);

  free_str_array(argv, count_str_array(argv));
  free_str_array(envp, count_str_array(envp));

  SpawnErrMsg msg = {0, 0};
  ssize_t got = 0;
  uint8_t *mp = (uint8_t *)&msg;
  while ((size_t)got < sizeof(msg)) {
    ssize_t n = read(exec_pipe[0], mp + got, sizeof(msg) - (size_t)got);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      msg.errnum = errno;
      msg.phase = 2;
      got = (ssize_t)sizeof(msg);
      break;
    }
    if (n == 0) {
      break;
    }
    got += n;
  }
  close_if_open(&exec_pipe[0]);

  if (got > 0) {
    close_if_open(&in_pipe[1]);
    close_if_open(&out_pipe[0]);
    close_if_open(&err_pipe[0]);
    int st = 0;
    while (waitpid(pid, &st, 0) < 0 && errno == EINTR) {
    }
    b_lean_obj_arg err_path = (msg.phase == 1 && has_cwd) ? cwd_obj : prog_obj;
    return lean_io_result_mk_error(lean_decode_io_error(msg.errnum, err_path));
  }

  ProcessSlot *slot = (ProcessSlot *)calloc(1, sizeof(ProcessSlot));
  if (slot == NULL) {
    close_if_open(&in_pipe[1]);
    close_if_open(&out_pipe[0]);
    close_if_open(&err_pipe[0]);
    kill(-pid, SIGKILL);
    int st = 0;
    while (waitpid(pid, &st, 0) < 0 && errno == EINTR) {
    }
    return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, prog_obj));
  }

  slot->pid = pid;
  slot->pgid = pid;
  slot->stdin_fd = in_pipe[1];
  slot->stdout_fd = out_pipe[0];
  slot->stderr_fd = err_pipe[0];

  pthread_mutex_lock(&g_proc_mu);
  uint64_t hid = g_next_handle_id++;
  slot->handle_id = hid;
  slot->next = g_proc_list;
  g_proc_list = slot;
  g_active_count++;
  pthread_mutex_unlock(&g_proc_mu);

  return lean_io_result_mk_ok(lean_box_uint64(hid));
}

LEAN_EXPORT lean_obj_res leanswe_process_pid(uint64_t handle_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proc_mu);
  ProcessSlot *slot = find_slot_locked(handle_id);
  uint32_t pid_u = (slot != NULL && slot->pid > 0) ? (uint32_t)slot->pid : 0;
  pthread_mutex_unlock(&g_proc_mu);
  return lean_io_result_mk_ok(lean_box_uint32(pid_u));
}

static uint64_t mono_now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000ULL + (uint64_t)(ts.tv_nsec / 1000000L);
}

static int append_bytes(uint8_t **buf, size_t *len, size_t *cap, const uint8_t *src, size_t n) {
  if (n == 0) {
    return 0;
  }
  if (*len + n > *cap) {
    size_t new_cap = (*cap == 0) ? 4096 : *cap;
    while (new_cap < *len + n) {
      if (new_cap > SIZE_MAX / 2) {
        new_cap = *len + n;
        break;
      }
      new_cap *= 2;
    }
    uint8_t *nb = (uint8_t *)realloc(*buf, new_cap);
    if (nb == NULL) {
      return -1;
    }
    *buf = nb;
    *cap = new_cap;
  }
  memcpy(*buf + *len, src, n);
  *len += n;
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_process_await_output(
    uint64_t handle_id,
    b_lean_obj_arg stdin_obj,
    uint8_t has_timeout,
    uint64_t timeout_ms,
    uint8_t has_limit,
    uint64_t max_output_bytes,
    lean_obj_arg w) {
  (void)w;

  pthread_mutex_lock(&g_proc_mu);
  ProcessSlot *slot = find_slot_locked(handle_id);
  if (slot == NULL) {
    pthread_mutex_unlock(&g_proc_mu);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("invalid process handle")));
  }
  pid_t pid = slot->pid;
  int in_fd = slot->stdin_fd;
  int out_fd = slot->stdout_fd;
  int err_fd = slot->stderr_fd;
  slot->stdin_fd = -1;
  slot->stdout_fd = -1;
  slot->stderr_fd = -1;
  pthread_mutex_unlock(&g_proc_mu);

  const uint8_t *stdin_data = lean_sarray_cptr(stdin_obj);
  size_t stdin_len = lean_sarray_size(stdin_obj);
  size_t stdin_pos = 0;

  if (stdin_len == 0) {
    close_if_open(&in_fd);
  } else if (in_fd >= 0) {
    (void)set_nonblock(in_fd);
  }
  if (out_fd >= 0) (void)set_nonblock(out_fd);
  if (err_fd >= 0) (void)set_nonblock(err_fd);

  sigset_t pipe_set, old_set;
  sigemptyset(&pipe_set);
  sigaddset(&pipe_set, SIGPIPE);
  int masked_sigpipe = (pthread_sigmask(SIG_BLOCK, &pipe_set, &old_set) == 0);
  int was_already_blocked = masked_sigpipe && sigismember(&old_set, SIGPIPE);

  uint64_t start_ms = has_timeout ? mono_now_ms() : 0;
  uint8_t *out_buf = NULL;
  size_t out_len = 0, out_cap = 0;
  uint8_t *err_buf = NULL;
  size_t err_len = 0, err_cap = 0;

  int timed_out = 0;
  int limit_exceeded = 0;
  int io_err = 0;
  uint8_t tmp[8192];

  while (out_fd >= 0 || err_fd >= 0) {
    struct pollfd fds[3];
    nfds_t nfds = 0;
    int idx_in = -1, idx_out = -1, idx_err = -1;

    if (in_fd >= 0) {
      idx_in = (int)nfds;
      fds[nfds].fd = in_fd;
      fds[nfds].events = POLLOUT;
      fds[nfds].revents = 0;
      nfds++;
    }
    if (out_fd >= 0) {
      idx_out = (int)nfds;
      fds[nfds].fd = out_fd;
      fds[nfds].events = POLLIN;
      fds[nfds].revents = 0;
      nfds++;
    }
    if (err_fd >= 0) {
      idx_err = (int)nfds;
      fds[nfds].fd = err_fd;
      fds[nfds].events = POLLIN;
      fds[nfds].revents = 0;
      nfds++;
    }

    int poll_to = -1;
    if (has_timeout) {
      uint64_t now = mono_now_ms();
      uint64_t elapsed = (now >= start_ms) ? (now - start_ms) : 0;
      if (elapsed >= timeout_ms) {
        timed_out = 1;
        break;
      }
      uint64_t rem = timeout_ms - elapsed;
      poll_to = (rem > (uint64_t)INT32_MAX) ? INT32_MAX : (int)rem;
    }

    int rc = poll(fds, nfds, poll_to);
    if (rc < 0) {
      if (errno == EINTR) {
        continue;
      }
      io_err = errno;
      break;
    }
    if (rc == 0) {
      timed_out = 1;
      break;
    }

    if (idx_in >= 0) {
      short rev = fds[idx_in].revents;
      if (rev & (POLLERR | POLLHUP | POLLNVAL)) {
        close_if_open(&in_fd);
      } else if (rev & POLLOUT) {
        while (stdin_pos < stdin_len) {
          if (has_timeout && (mono_now_ms() - start_ms) >= timeout_ms) {
            timed_out = 1;
            break;
          }
          ssize_t n = write(in_fd, stdin_data + stdin_pos, stdin_len - stdin_pos);
          if (n > 0) {
            stdin_pos += (size_t)n;
          } else if (n < 0 && errno == EINTR) {
            continue;
          } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
            break;
          } else {
            close_if_open(&in_fd);
            break;
          }
        }
        if (timed_out) {
          break;
        }
        if (stdin_pos >= stdin_len) {
          close_if_open(&in_fd);
        }
      }
    }

    if (idx_out >= 0 && (fds[idx_out].revents & (POLLIN | POLLHUP | POLLERR))) {
      size_t iter_bytes = 0;
      for (;;) {
        if (has_timeout && (mono_now_ms() - start_ms) >= timeout_ms) {
          timed_out = 1;
          break;
        }
        ssize_t n = read(out_fd, tmp, sizeof(tmp));
        if (n > 0) {
          iter_bytes += (size_t)n;
          size_t total = out_len + err_len;
          if (has_limit && (uint64_t)total + (uint64_t)n > max_output_bytes) {
            size_t keep = (max_output_bytes > (uint64_t)total)
                              ? (size_t)(max_output_bytes - (uint64_t)total)
                              : 0;
            if (keep > 0 && append_bytes(&out_buf, &out_len, &out_cap, tmp, keep) != 0) {
              io_err = ENOMEM;
              break;
            }
            limit_exceeded = 1;
            break;
          }
          if (append_bytes(&out_buf, &out_len, &out_cap, tmp, (size_t)n) != 0) {
            io_err = ENOMEM;
            break;
          }
          if (iter_bytes >= 65536) {
            break;
          }
        } else if (n == 0) {
          close_if_open(&out_fd);
          break;
        } else {
          if (errno == EINTR) continue;
          if (errno == EAGAIN || errno == EWOULDBLOCK) break;
          io_err = errno;
          close_if_open(&out_fd);
          break;
        }
      }
      if (timed_out || limit_exceeded || io_err != 0) {
        break;
      }
    }

    if (idx_err >= 0 && (fds[idx_err].revents & (POLLIN | POLLHUP | POLLERR))) {
      size_t iter_bytes = 0;
      for (;;) {
        if (has_timeout && (mono_now_ms() - start_ms) >= timeout_ms) {
          timed_out = 1;
          break;
        }
        ssize_t n = read(err_fd, tmp, sizeof(tmp));
        if (n > 0) {
          iter_bytes += (size_t)n;
          size_t total = out_len + err_len;
          if (has_limit && (uint64_t)total + (uint64_t)n > max_output_bytes) {
            size_t keep = (max_output_bytes > (uint64_t)total)
                              ? (size_t)(max_output_bytes - (uint64_t)total)
                              : 0;
            if (keep > 0 && append_bytes(&err_buf, &err_len, &err_cap, tmp, keep) != 0) {
              io_err = ENOMEM;
              break;
            }
            limit_exceeded = 1;
            break;
          }
          if (append_bytes(&err_buf, &err_len, &err_cap, tmp, (size_t)n) != 0) {
            io_err = ENOMEM;
            break;
          }
          if (iter_bytes >= 65536) {
            break;
          }
        } else if (n == 0) {
          close_if_open(&err_fd);
          break;
        } else {
          if (errno == EINTR) continue;
          if (errno == EAGAIN || errno == EWOULDBLOCK) break;
          io_err = errno;
          close_if_open(&err_fd);
          break;
        }
      }
      if (timed_out || limit_exceeded || io_err != 0) {
        break;
      }
    }
  }

  close_if_open(&in_fd);
  close_if_open(&out_fd);
  close_if_open(&err_fd);

  if (masked_sigpipe) {
    if (!was_already_blocked) {
      sigset_t pending;
      sigemptyset(&pending);
      if (sigpending(&pending) == 0 && sigismember(&pending, SIGPIPE)) {
        int sig = 0;
        sigwait(&pipe_set, &sig);
      }
    }
    pthread_sigmask(SIG_SETMASK, &old_set, NULL);
  }

  if (io_err != 0) {
    free(out_buf);
    free(err_buf);
    return lean_io_result_mk_error(lean_decode_io_error(io_err, lean_mk_string("process")));
  }

  uint8_t outcome_tag = 0;
  uint8_t waited = 0;
  uint32_t exit_code = 0;
  uint32_t term_signal = 0;

  if (timed_out) {
    outcome_tag = 2;
  } else if (limit_exceeded) {
    outcome_tag = 3;
  } else {
    int st = 0;
    if (!has_timeout) {
      while (waitpid(pid, &st, 0) < 0) {
        if (errno == EINTR) continue;
        if (errno == ECHILD) break;
        free(out_buf);
        free(err_buf);
        return lean_io_result_mk_error(lean_decode_io_error(errno, lean_mk_string("waitpid")));
      }
      waited = 1;
    } else {
      for (;;) {
        pid_t w_rc = waitpid(pid, &st, WNOHANG);
        if (w_rc == pid) {
          waited = 1;
          break;
        }
        if (w_rc < 0) {
          if (errno == EINTR) continue;
          if (errno == ECHILD) {
            waited = 1;
            break;
          }
          free(out_buf);
          free(err_buf);
          return lean_io_result_mk_error(lean_decode_io_error(errno, lean_mk_string("waitpid")));
        }
        uint64_t now = mono_now_ms();
        uint64_t elapsed = (now >= start_ms) ? (now - start_ms) : 0;
        if (elapsed >= timeout_ms) {
          timed_out = 1;
          break;
        }
        uint64_t rem = timeout_ms - elapsed;
        uint64_t sleep_ms = (rem < 5) ? rem : 5;
        struct timespec req_ts;
        req_ts.tv_sec = (time_t)(sleep_ms / 1000ULL);
        req_ts.tv_nsec = (long)((sleep_ms % 1000ULL) * 1000000ULL);
        nanosleep(&req_ts, NULL);
      }
    }
    if (timed_out) {
      outcome_tag = 2;
    } else if (WIFEXITED(st)) {
      outcome_tag = 0;
      exit_code = (uint32_t)WEXITSTATUS(st);
    } else if (WIFSIGNALED(st)) {
      outcome_tag = 1;
      term_signal = (uint32_t)WTERMSIG(st);
    } else {
      outcome_tag = 0;
      exit_code = 1;
    }
  }

  pthread_mutex_lock(&g_proc_mu);
  slot = find_slot_locked(handle_id);
  if (slot == NULL) {
    pthread_mutex_unlock(&g_proc_mu);
    free(out_buf);
    free(err_buf);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("process handle vanished")));
  }
  free(slot->stdout_buf);
  free(slot->stderr_buf);
  slot->stdout_buf = out_buf;
  slot->stdout_len = out_len;
  slot->stderr_buf = err_buf;
  slot->stderr_len = err_len;
  slot->waited = waited;
  slot->exit_code = exit_code;
  slot->term_signal = term_signal;
  pthread_mutex_unlock(&g_proc_mu);

  return lean_io_result_mk_ok(lean_box(outcome_tag));
}

LEAN_EXPORT lean_obj_res leanswe_process_take_stdout(uint64_t handle_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proc_mu);
  ProcessSlot *slot = find_slot_locked(handle_id);
  uint8_t *buf = NULL;
  size_t len = 0;
  if (slot != NULL) {
    buf = slot->stdout_buf;
    len = slot->stdout_len;
    slot->stdout_buf = NULL;
    slot->stdout_len = 0;
  }
  pthread_mutex_unlock(&g_proc_mu);

  lean_obj_res arr = lean_alloc_sarray(1, len, len);
  if (len > 0 && buf != NULL) {
    memcpy(lean_sarray_cptr(arr), buf, len);
  }
  free(buf);
  return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res leanswe_process_take_stderr(uint64_t handle_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proc_mu);
  ProcessSlot *slot = find_slot_locked(handle_id);
  uint8_t *buf = NULL;
  size_t len = 0;
  if (slot != NULL) {
    buf = slot->stderr_buf;
    len = slot->stderr_len;
    slot->stderr_buf = NULL;
    slot->stderr_len = 0;
  }
  pthread_mutex_unlock(&g_proc_mu);

  lean_obj_res arr = lean_alloc_sarray(1, len, len);
  if (len > 0 && buf != NULL) {
    memcpy(lean_sarray_cptr(arr), buf, len);
  }
  free(buf);
  return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res leanswe_process_exit_code(uint64_t handle_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proc_mu);
  ProcessSlot *slot = find_slot_locked(handle_id);
  uint32_t code = (slot != NULL) ? slot->exit_code : 1;
  pthread_mutex_unlock(&g_proc_mu);
  return lean_io_result_mk_ok(lean_box_uint32(code));
}

LEAN_EXPORT lean_obj_res leanswe_process_term_signal(uint64_t handle_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proc_mu);
  ProcessSlot *slot = find_slot_locked(handle_id);
  uint32_t sig = (slot != NULL) ? slot->term_signal : 0;
  pthread_mutex_unlock(&g_proc_mu);
  return lean_io_result_mk_ok(lean_box_uint32(sig));
}

LEAN_EXPORT lean_obj_res leanswe_process_kill_group(uint64_t handle_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proc_mu);
  ProcessSlot *slot = find_slot_locked(handle_id);
  pid_t pgid = (slot != NULL) ? slot->pgid : -1;
  pthread_mutex_unlock(&g_proc_mu);

  if (pgid <= 0) {
    return lean_io_result_mk_ok(lean_box(0));
  }

  if (kill(-pgid, SIGTERM) != 0) {
    if (errno == ESRCH) {
      return lean_io_result_mk_ok(lean_box(0));
    }
    return lean_io_result_mk_error(lean_decode_io_error(errno, lean_mk_string("kill")));
  }

  struct timespec ts = {0, 5000000L}; /* 5 ms grace steps, 25 ms total before SIGKILL */
  for (int i = 0; i < 5; i++) {
    nanosleep(&ts, NULL);
    if (kill(-pgid, 0) != 0 && errno == ESRCH) {
      return lean_io_result_mk_ok(lean_box(0));
    }
  }

  if (kill(-pgid, SIGKILL) != 0 && errno != ESRCH) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, lean_mk_string("kill")));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_process_reap(uint64_t handle_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proc_mu);
  ProcessSlot *slot = detach_slot_locked(handle_id);
  pthread_mutex_unlock(&g_proc_mu);

  if (slot == NULL) {
    return lean_io_result_mk_ok(lean_box(0));
  }

  close_if_open(&slot->stdin_fd);
  close_if_open(&slot->stdout_fd);
  close_if_open(&slot->stderr_fd);
  free(slot->stdout_buf);
  free(slot->stderr_buf);

  pid_t pid = slot->pid;
  uint8_t waited = slot->waited;
  free(slot);

  if (!waited && pid > 0) {
    int st = 0;
    while (waitpid(pid, &st, 0) < 0) {
      if (errno == EINTR) continue;
      if (errno == ECHILD) break;
      return lean_io_result_mk_error(lean_decode_io_error(errno, lean_mk_string("waitpid")));
    }
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_process_active_count(lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proc_mu);
  size_t count = g_active_count;
  pthread_mutex_unlock(&g_proc_mu);
  return lean_io_result_mk_ok(lean_usize_to_nat(count));
}
