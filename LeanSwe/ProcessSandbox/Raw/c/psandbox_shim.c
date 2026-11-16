#define _GNU_SOURCE

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
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

static lean_obj_res mk_err_tuple4(
    uint8_t tag, uint32_t errnum, const char *path, const char *msg) {
  lean_obj_res p3 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p3, 0, lean_mk_string(path != NULL ? path : ""));
  lean_ctor_set(p3, 1, lean_mk_string(msg != NULL ? msg : ""));
  lean_obj_res p2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p2, 0, lean_box_uint32(errnum));
  lean_ctor_set(p2, 1, p3);
  lean_obj_res p1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p1, 0, lean_box((unsigned)tag));
  lean_ctor_set(p1, 1, p2);
  return p1;
}

static lean_obj_res mk_err_tuple5_u64(
    uint8_t tag, uint32_t errnum, const char *path, const char *msg, uint64_t val) {
  lean_obj_res p4 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p4, 0, lean_mk_string(msg != NULL ? msg : ""));
  lean_ctor_set(p4, 1, lean_box_uint64(val));
  lean_obj_res p3 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p3, 0, lean_mk_string(path != NULL ? path : ""));
  lean_ctor_set(p3, 1, p4);
  lean_obj_res p2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p2, 0, lean_box_uint32(errnum));
  lean_ctor_set(p2, 1, p3);
  lean_obj_res p1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p1, 0, lean_box((unsigned)tag));
  lean_ctor_set(p1, 1, p2);
  return p1;
}

static lean_obj_res mk_spawn_tuple(
    uint8_t tag,
    uint32_t errnum,
    const char *path,
    const char *msg,
    uint64_t hid,
    uint32_t pid,
    uint32_t pgid,
    uint32_t pidfd) {
  lean_obj_res t7 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t7, 0, lean_box_uint32(pgid));
  lean_ctor_set(t7, 1, lean_box_uint32(pidfd));
  lean_obj_res t6 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t6, 0, lean_box_uint32(pid));
  lean_ctor_set(t6, 1, t7);
  lean_obj_res t5 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t5, 0, lean_box_uint64(hid));
  lean_ctor_set(t5, 1, t6);
  lean_obj_res t4 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t4, 0, lean_mk_string(msg != NULL ? msg : ""));
  lean_ctor_set(t4, 1, t5);
  lean_obj_res t3 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t3, 0, lean_mk_string(path != NULL ? path : ""));
  lean_ctor_set(t3, 1, t4);
  lean_obj_res t2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t2, 0, lean_box_uint32(errnum));
  lean_ctor_set(t2, 1, t3);
  lean_obj_res t1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t1, 0, lean_box((unsigned)tag));
  lean_ctor_set(t1, 1, t2);
  return t1;
}

static lean_obj_res mk_read_tuple(
    uint8_t tag,
    uint32_t errnum,
    const char *path,
    const char *msg,
    uint8_t outcome_tag,
    uint32_t exit_or_sig,
    lean_obj_arg out_ba,
    lean_obj_arg err_ba) {
  lean_obj_res t7 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t7, 0, out_ba);
  lean_ctor_set(t7, 1, err_ba);
  lean_obj_res t6 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t6, 0, lean_box_uint32(exit_or_sig));
  lean_ctor_set(t6, 1, t7);
  lean_obj_res t5 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t5, 0, lean_box((unsigned)outcome_tag));
  lean_ctor_set(t5, 1, t6);
  lean_obj_res t4 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t4, 0, lean_mk_string(msg != NULL ? msg : ""));
  lean_ctor_set(t4, 1, t5);
  lean_obj_res t3 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t3, 0, lean_mk_string(path != NULL ? path : ""));
  lean_ctor_set(t3, 1, t4);
  lean_obj_res t2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t2, 0, lean_box_uint32(errnum));
  lean_ctor_set(t2, 1, t3);
  lean_obj_res t1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t1, 0, lean_box((unsigned)tag));
  lean_ctor_set(t1, 1, t2);
  return t1;
}

#ifdef __linux__

#include <arpa/inet.h>
#include <limits.h>
#include <linux/landlock.h>
#include <linux/seccomp.h>
#include <netinet/in.h>
#include <poll.h>
#include <pwd.h>
#include <stdatomic.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/wait.h>

#include "psandbox_init_embed.h"

#ifndef __NR_close_range
#define __NR_close_range 436
#endif
#ifndef __NR_getdents64
#if defined(__x86_64__)
#define __NR_getdents64 217
#elif defined(__aarch64__)
#define __NR_getdents64 61
#endif
#endif

#ifndef __NR_landlock_create_ruleset
#define __NR_landlock_create_ruleset 444
#endif
#ifndef __NR_seccomp
#define __NR_seccomp 317
#endif
#ifndef __NR_pidfd_open
#define __NR_pidfd_open 434
#endif
#ifndef __NR_pidfd_send_signal
#define __NR_pidfd_send_signal 424
#endif
#ifndef __NR_memfd_create
#if defined(__x86_64__)
#define __NR_memfd_create 319
#elif defined(__aarch64__)
#define __NR_memfd_create 279
#endif
#endif

#ifndef MFD_CLOEXEC
#define MFD_CLOEXEC 0x0001U
#endif
#ifndef MFD_ALLOW_SEALING
#define MFD_ALLOW_SEALING 0x0002U
#endif
#ifndef F_ADD_SEALS
#define F_ADD_SEALS 1033
#endif
#ifndef F_SEAL_SEAL
#define F_SEAL_SEAL 0x0001
#define F_SEAL_SHRINK 0x0002
#define F_SEAL_GROW 0x0004
#define F_SEAL_WRITE 0x0008
#endif

#define PS_TAG_OK 0
#define PS_TAG_UNAVAILABLE 1
#define PS_TAG_NOT_FOUND 2
#define PS_TAG_PERM_DENIED 3
#define PS_TAG_INVALID_INPUT 4
#define PS_TAG_IO_ERROR 5

#define PS_STATUS_READY 1
#define PS_STATUS_INIT_ERR 2
#define PS_STATUS_EXEC_ERR 3
#define PS_STATUS_EXITED 4
#define PS_STATUS_SIGNALED 5

#define PS_MAX_RELAY_SLOTS 128
#define PS_RING_CAP 16384

typedef struct InitStatusMsg {
  uint8_t kind;
  uint8_t flag;
  uint8_t pad[2];
  int32_t value;
} InitStatusMsg;

typedef struct ShimSysEntry {
  uint8_t tag;
  char *path;
  char *target;
} ShimSysEntry;

typedef struct ShimMount {
  uint8_t tag;
  char *host_path;
  char *box_path;
} ShimMount;

typedef struct PlanSlot {
  uint64_t handle_id;
  int plan_memfd;
  int init_memfd;
  int hosts_memfd;
  uint8_t has_memory_max;
  uint64_t memory_max_bytes;
  uint8_t has_pids_max;
  uint64_t pids_max;
  char *program;
  char *cwd;
  uint32_t n_sys;
  ShimSysEntry *sys;
  uint32_t n_etc;
  char **etc_paths;
  uint32_t n_masks;
  char **masks;
  uint32_t n_mounts;
  ShimMount *mounts;
  uint32_t n_fwds;
  struct PlanSlot *next;
} PlanSlot;

typedef struct BoxSlot {
  uint64_t handle_id;
  pid_t pid;
  pid_t pgid;
  int pidfd;
  int stdin_fd;
  int stdout_fd;
  int stderr_fd;
  int status_fd;
  int go_fd;
  uint8_t read_started;
  uint8_t fwds_taken;
  uint32_t n_listeners;
  int *listener_fds;
  char *cgroup_dir;
  char *program;
  char *cwd;
  struct BoxSlot *next;
} BoxSlot;

typedef struct RingBuf {
  uint8_t data[PS_RING_CAP];
  size_t head;
  size_t len;
} RingBuf;

typedef struct RelayConn {
  uint8_t in_use;
  int box_fd;
  int host_fd;
  uint16_t host_port;
  uint8_t host_connecting;
  uint8_t box_eof_in;
  uint8_t host_eof_in;
  uint8_t box_shutdown_wr;
  uint8_t host_shutdown_wr;
  RingBuf b2h;
  RingBuf h2b;
} RelayConn;

typedef struct ForwarderSlot {
  uint64_t handle_id;
  uint64_t box_handle_id;
  uint32_t n_listeners;
  int *listener_fds;
  uint16_t *host_ports;
  int wake_read_fd;
  int wake_write_fd;
  pthread_t thread;
  uint8_t thread_started;
  struct ForwarderSlot *next;
} ForwarderSlot;

typedef struct SpawnRequest {
  const char *bwrap_path;
  char **bwrap_argv;
  int cg_sync_read_fd;
  int cg_sync_write_fd;
  int bwrap_err_read_fd;
  int bwrap_err_write_fd;
  int stdin_read_fd;
  int stdout_write_fd;
  int stderr_write_fd;
  int status_write_fd;
  int go_read_fd;
  int ctrl_write_fd;
  int init_fd;
  int hosts_fd;
  int plan_fd;
  int done;
  pid_t child_pid;
  int fork_errno;
  struct SpawnRequest *next;
} SpawnRequest;

static pthread_mutex_t g_mu = PTHREAD_MUTEX_INITIALIZER;
static uint64_t g_next_handle_id = 1;
static PlanSlot *g_plans = NULL;
static BoxSlot *g_boxes = NULL;
static ForwarderSlot *g_fwds = NULL;
static size_t g_open_plans = 0;
static size_t g_active_boxes = 0;
static size_t g_active_fwds = 0;
static atomic_uint_fast64_t g_cg_seq = 1;

static pthread_once_t g_spawner_once = PTHREAD_ONCE_INIT;
static pthread_mutex_t g_spawner_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t g_spawner_cond = PTHREAD_COND_INITIALIZER;
static pthread_cond_t g_spawner_done_cond = PTHREAD_COND_INITIALIZER;
static SpawnRequest *g_spawner_head = NULL;
static int g_spawner_init_ok = 0;

static void close_fd(int *fd) {
  if (*fd >= 0) {
    close(*fd);
    *fd = -1;
  }
}

static int clear_cloexec_fd(int fd) {
  if (fd < 0) {
    return 0;
  }
  return fcntl(fd, F_SETFD, 0);
}

static int set_nonblock_fd(int fd) {
  int fl = fcntl(fd, F_GETFL, 0);
  if (fl < 0) {
    return -1;
  }
  return fcntl(fd, F_SETFL, fl | O_NONBLOCK);
}

static int write_all_fd(int fd, const void *buf, size_t len) {
  const uint8_t *p = (const uint8_t *)buf;
  size_t off = 0;
  while (off < len) {
    ssize_t n = write(fd, p + off, len - off);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

static int write_text_file(const char *path, const char *text) {
  int fd = open(path, O_WRONLY | O_CLOEXEC);
  if (fd < 0) {
    return -1;
  }
  int rc = write_all_fd(fd, text, strlen(text));
  int err = errno;
  close(fd);
  errno = err;
  return rc;
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
    size_t ncap = (*cap == 0) ? 4096 : *cap;
    while (ncap < *len + n) {
      if (ncap > SIZE_MAX / 2) {
        ncap = *len + n;
        break;
      }
      ncap *= 2;
    }
    uint8_t *nb = (uint8_t *)realloc(*buf, ncap);
    if (nb == NULL) {
      return -1;
    }
    *buf = nb;
    *cap = ncap;
  }
  memcpy(*buf + *len, src, n);
  *len += n;
  return 0;
}

typedef struct PsDirent64 {
  uint64_t d_ino;
  int64_t d_off;
  uint16_t d_reclen;
  uint8_t d_type;
  char d_name[];
} PsDirent64;

static void close_fds_above2_except(const int *keep, size_t n_keep) {
  int sorted[16];
  size_t nk = 0;
  for (size_t i = 0; i < n_keep && nk < 16; i++) {
    int fd = keep[i];
    if (fd <= STDERR_FILENO) {
      continue;
    }
    int dup = 0;
    for (size_t j = 0; j < nk; j++) {
      if (sorted[j] == fd) {
        dup = 1;
        break;
      }
    }
    if (!dup) {
      sorted[nk++] = fd;
    }
  }
  for (size_t i = 1; i < nk; i++) {
    int v = sorted[i];
    size_t j = i;
    while (j > 0 && sorted[j - 1] > v) {
      sorted[j] = sorted[j - 1];
      j--;
    }
    sorted[j] = v;
  }

  unsigned int lo = 3U;
  int range_ok = 1;
  for (size_t i = 0; i < nk; i++) {
    unsigned int kfd = (unsigned int)sorted[i];
    if (kfd > lo) {
      if (syscall(__NR_close_range, lo, kfd - 1U, 0U) != 0) {
        range_ok = 0;
        break;
      }
    }
    lo = kfd + 1U;
  }
  if (range_ok) {
    if (syscall(__NR_close_range, lo, ~0U, 0U) == 0) {
      return;
    }
  }

  int dirfd = open("/proc/self/fd", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  if (dirfd >= 0) {
    char buf[2048];
    for (;;) {
      long nread = syscall(__NR_getdents64, dirfd, buf, (long)sizeof(buf));
      if (nread <= 0) {
        break;
      }
      long pos = 0;
      while (pos < nread) {
        const PsDirent64 *d = (const PsDirent64 *)(buf + pos);
        if (d->d_reclen == 0) {
          pos = nread;
          break;
        }
        if (d->d_name[0] >= '0' && d->d_name[0] <= '9') {
          int fd = 0;
          int valid = 1;
          for (const char *p = d->d_name; *p != '\0'; p++) {
            if (*p < '0' || *p > '9' || fd > 100000000) {
              valid = 0;
              break;
            }
            fd = fd * 10 + (*p - '0');
          }
          if (valid && fd > STDERR_FILENO && fd != dirfd) {
            int kept = 0;
            for (size_t j = 0; j < nk; j++) {
              if (sorted[j] == fd) {
                kept = 1;
                break;
              }
            }
            if (!kept) {
              close(fd);
            }
          }
        }
        pos += d->d_reclen;
      }
    }
    close(dirfd);
    return;
  }

  long max_fd = sysconf(_SC_OPEN_MAX);
  if (max_fd <= 0 || max_fd > 65536L) {
    max_fd = 65536L;
  }
  for (int fd = 3; fd < (int)max_fd; fd++) {
    int kept = 0;
    for (size_t j = 0; j < nk; j++) {
      if (sorted[j] == fd) {
        kept = 1;
        break;
      }
    }
    if (!kept) {
      close(fd);
    }
  }
}

static void *spawner_thread_main(void *arg) {
  (void)arg;
  for (;;) {
    pthread_mutex_lock(&g_spawner_mu);
    while (g_spawner_head == NULL) {
      pthread_cond_wait(&g_spawner_cond, &g_spawner_mu);
    }
    SpawnRequest *req = g_spawner_head;
    g_spawner_head = req->next;
    req->next = NULL;
    pthread_mutex_unlock(&g_spawner_mu);

    pid_t pid = fork();
    if (pid == 0) {
      (void)setpgid(0, 0);
      signal(SIGPIPE, SIG_DFL);

      close_fd(&req->cg_sync_write_fd);
      close_fd(&req->bwrap_err_read_fd);

      uint8_t go = 0;
      ssize_t sr = -1;
      for (;;) {
        sr = read(req->cg_sync_read_fd, &go, 1);
        if (sr < 0 && errno == EINTR) {
          continue;
        }
        break;
      }
      close_fd(&req->cg_sync_read_fd);
      if (sr != 1) {
        _exit(125);
      }

      if (dup2(req->stdin_read_fd, STDIN_FILENO) < 0 ||
          dup2(req->stdout_write_fd, STDOUT_FILENO) < 0 ||
          dup2(req->stderr_write_fd, STDERR_FILENO) < 0) {
        int err = errno ? errno : EIO;
        (void)write_all_fd(req->bwrap_err_write_fd, &err, sizeof(err));
        _exit(127);
      }
      if (req->stdin_read_fd > STDERR_FILENO) {
        close_fd(&req->stdin_read_fd);
      }
      if (req->stdout_write_fd > STDERR_FILENO) {
        close_fd(&req->stdout_write_fd);
      }
      if (req->stderr_write_fd > STDERR_FILENO) {
        close_fd(&req->stderr_write_fd);
      }
      (void)clear_cloexec_fd(STDIN_FILENO);
      (void)clear_cloexec_fd(STDOUT_FILENO);
      (void)clear_cloexec_fd(STDERR_FILENO);
      (void)clear_cloexec_fd(req->status_write_fd);
      (void)clear_cloexec_fd(req->go_read_fd);
      (void)clear_cloexec_fd(req->ctrl_write_fd);
      (void)clear_cloexec_fd(req->init_fd);
      (void)clear_cloexec_fd(req->hosts_fd);
      (void)clear_cloexec_fd(req->plan_fd);

      const int keep_fds[7] = {
          req->bwrap_err_write_fd,
          req->status_write_fd,
          req->go_read_fd,
          req->ctrl_write_fd,
          req->init_fd,
          req->hosts_fd,
          req->plan_fd,
      };
      close_fds_above2_except(keep_fds, 7);

      execv(req->bwrap_path, req->bwrap_argv);
      int err = errno ? errno : ENOENT;
      (void)write_all_fd(req->bwrap_err_write_fd, &err, sizeof(err));
      _exit(127);
    }

    int ferr = (pid < 0) ? errno : 0;
    pthread_mutex_lock(&g_spawner_mu);
    req->child_pid = pid;
    req->fork_errno = ferr;
    req->done = 1;
    pthread_cond_broadcast(&g_spawner_done_cond);
    pthread_mutex_unlock(&g_spawner_mu);
  }
  return NULL;
}

static void init_spawner_once(void) {
  pthread_t thr;
  if (pthread_create(&thr, NULL, spawner_thread_main, NULL) == 0) {
    pthread_detach(thr);
    g_spawner_init_ok = 1;
  }
}

static pid_t spawn_via_spawner(SpawnRequest *req, int *err_out) {
  pthread_once(&g_spawner_once, init_spawner_once);
  if (!g_spawner_init_ok) {
    *err_out = EAGAIN;
    return -1;
  }
  req->done = 0;
  req->child_pid = -1;
  req->fork_errno = 0;
  req->next = NULL;

  pthread_mutex_lock(&g_spawner_mu);
  req->next = g_spawner_head;
  g_spawner_head = req;
  pthread_cond_signal(&g_spawner_cond);
  while (!req->done) {
    pthread_cond_wait(&g_spawner_done_cond, &g_spawner_mu);
  }
  pthread_mutex_unlock(&g_spawner_mu);

  *err_out = req->fork_errno;
  return req->child_pid;
}

static char *resolve_bwrap_path(void) {
  const char *env_path = getenv("PATH");
  if (env_path == NULL || env_path[0] == '\0') {
    env_path = "/usr/bin:/bin";
  }
  char *copy = strdup(env_path);
  if (copy == NULL) {
    return NULL;
  }
  char *saveptr = NULL;
  for (char *tok = strtok_r(copy, ":", &saveptr); tok != NULL; tok = strtok_r(NULL, ":", &saveptr)) {
    const char *dir = (tok[0] == '\0') ? "." : tok;
    size_t dlen = strlen(dir);
    size_t need = dlen + 7;
    char *cand = (char *)malloc(need);
    if (cand == NULL) {
      continue;
    }
    snprintf(cand, need, "%s/bwrap", dir);
    struct stat st;
    if (stat(cand, &st) == 0 && S_ISREG(st.st_mode) && access(cand, X_OK) == 0) {
      free(copy);
      return cand;
    }
    free(cand);
  }
  free(copy);
  struct stat st;
  if (stat("/usr/bin/bwrap", &st) == 0 && S_ISREG(st.st_mode) && access("/usr/bin/bwrap", X_OK) == 0) {
    return strdup("/usr/bin/bwrap");
  }
  return NULL;
}

static int create_sealed_memfd(const char *name, const void *data, size_t len) {
  int fd = (int)syscall(__NR_memfd_create, name, MFD_CLOEXEC | MFD_ALLOW_SEALING);
  if (fd < 0) {
    return -1;
  }
  if (len > 0 && write_all_fd(fd, data, len) != 0) {
    int err = errno;
    close(fd);
    errno = err;
    return -1;
  }
  if (fcntl(fd, F_ADD_SEALS, F_SEAL_SEAL | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE) != 0) {
    int err = errno;
    close(fd);
    errno = err;
    return -1;
  }
  return fd;
}

static int reopen_memfd_ro_cloexec(int memfd) {
  char path[64];
  snprintf(path, sizeof(path), "/proc/self/fd/%d", memfd);
  return open(path, O_RDONLY | O_CLOEXEC);
}

static int find_delegated_cgroup_parent(char *out, size_t out_sz) {
  int fd = open("/proc/self/cgroup", O_RDONLY | O_CLOEXEC);
  if (fd < 0) {
    return -1;
  }
  char buf[4096];
  size_t len = 0;
  while (len + 1 < sizeof(buf)) {
    ssize_t n = read(fd, buf + len, sizeof(buf) - 1 - len);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      int err = errno;
      close(fd);
      errno = err;
      return -1;
    }
    if (n == 0) {
      break;
    }
    len += (size_t)n;
  }
  close(fd);
  buf[len] = '\0';

  const char *v2_rel = NULL;
  char *saveptr = NULL;
  for (char *line = strtok_r(buf, "\n", &saveptr); line != NULL; line = strtok_r(NULL, "\n", &saveptr)) {
    if (strncmp(line, "0::", 3) == 0) {
      v2_rel = line + 3;
      break;
    }
  }
  if (v2_rel == NULL || v2_rel[0] != '/') {
    errno = ENOENT;
    return -1;
  }
  size_t rlen = strlen(v2_rel);
  while (rlen > 1 && v2_rel[rlen - 1] == '/') {
    rlen--;
  }
  const char *slash = NULL;
  for (size_t i = rlen; i > 0; i--) {
    if (v2_rel[i - 1] == '/') {
      slash = v2_rel + (i - 1);
      break;
    }
  }
  size_t parent_rel_len = (slash != NULL && slash > v2_rel) ? (size_t)(slash - v2_rel) : 0;
  int n = 0;
  if (parent_rel_len == 0) {
    n = snprintf(out, out_sz, "/sys/fs/cgroup");
  } else {
    n = snprintf(out, out_sz, "/sys/fs/cgroup%.*s", (int)parent_rel_len, v2_rel);
  }
  if (n < 0 || (size_t)n >= out_sz) {
    errno = ENAMETOOLONG;
    return -1;
  }
  return 0;
}

static int create_sibling_cgroup(char *cg_dir, size_t cg_dir_sz) {
  char parent[PATH_MAX];
  if (find_delegated_cgroup_parent(parent, sizeof(parent)) != 0) {
    return -1;
  }
  uint64_t seq = atomic_fetch_add(&g_cg_seq, 1);
  int n = snprintf(
      cg_dir, cg_dir_sz, "%s/leanswe-psandbox-%ld-%llu",
      parent, (long)getpid(), (unsigned long long)seq);
  if (n < 0 || (size_t)n >= cg_dir_sz) {
    errno = ENAMETOOLONG;
    return -1;
  }
  if (mkdir(cg_dir, 0755) != 0) {
    return -1;
  }
  return 0;
}

static int cgroup_subfile(const char *cg_dir, const char *name, char *out, size_t out_sz) {
  int n = snprintf(out, out_sz, "%s/%s", cg_dir, name);
  if (n < 0 || (size_t)n >= out_sz) {
    errno = ENAMETOOLONG;
    return -1;
  }
  return 0;
}

static int configure_cgroup_memory(
    const char *cg_dir, const char *mem_limit, const char **failed_file, int *err_out) {
  static const struct {
    const char *name;
    const char *val;
  } k_mem_opts[] = {
    {"memory.swap.max", "0"},
    {"memory.oom.group", "1"},
  };
  char path[PATH_MAX];
  if (cgroup_subfile(cg_dir, "memory.max", path, sizeof(path)) != 0 ||
      write_text_file(path, mem_limit) != 0) {
    *err_out = errno ? errno : EACCES;
    *failed_file = "memory.max";
    return -1;
  }
  for (size_t i = 0; i < sizeof(k_mem_opts) / sizeof(k_mem_opts[0]); i++) {
    if (cgroup_subfile(cg_dir, k_mem_opts[i].name, path, sizeof(path)) != 0 ||
        (write_text_file(path, k_mem_opts[i].val) != 0 && errno != ENOENT)) {
      *err_out = errno ? errno : EACCES;
      *failed_file = k_mem_opts[i].name;
      return -1;
    }
  }
  return 0;
}

static int cleanup_cgroup_dir(const char *cg_dir) {
  if (cg_dir == NULL || cg_dir[0] == '\0') {
    return 0;
  }
  char path[PATH_MAX];
  if (cgroup_subfile(cg_dir, "cgroup.kill", path, sizeof(path)) == 0) {
    (void)write_text_file(path, "1");
  }
  if (cgroup_subfile(cg_dir, "cgroup.events", path, sizeof(path)) == 0) {
    for (int i = 0; i < 200; i++) {
      int fd = open(path, O_RDONLY | O_CLOEXEC);
      if (fd < 0) {
        break;
      }
      char buf[256];
      ssize_t n = read(fd, buf, sizeof(buf) - 1);
      close(fd);
      if (n > 0) {
        buf[n] = '\0';
        if (strstr(buf, "populated 0") != NULL) {
          break;
        }
      }
      struct timespec ts = {0, 2000000L};
      nanosleep(&ts, NULL);
    }
  }
  for (int i = 0; i < 200; i++) {
    if (rmdir(cg_dir) == 0 || errno == ENOENT) {
      return 0;
    }
    if (errno != EBUSY && errno != EINTR) {
      return -1;
    }
    struct timespec ts = {0, 2000000L};
    nanosleep(&ts, NULL);
  }
  if (rmdir(cg_dir) == 0 || errno == ENOENT) {
    return 0;
  }
  return -1;
}

static int is_under_system_root_lexical(const char *p) {
  static const char *const k_roots[] = {
    "/usr/", "/bin/", "/sbin/", "/lib/", "/lib64/"
  };
  for (size_t i = 0; i < sizeof(k_roots) / sizeof(k_roots[0]); i++) {
    size_t rlen = strlen(k_roots[i]);
    if (strncmp(p, k_roots[i], rlen) == 0 && p[rlen] != '\0') {
      return 1;
    }
  }
  return 0;
}

static char *normalize_abs_lexical(const char *p) {
  if (p == NULL || p[0] != '/') {
    return NULL;
  }
  size_t len = strlen(p);
  char *tmp = strdup(p);
  char *out = (char *)malloc(len + 2);
  if (tmp == NULL || out == NULL) {
    free(tmp);
    free(out);
    return NULL;
  }
  size_t out_len = 0;
  char *saveptr = NULL;
  for (char *seg = strtok_r(tmp, "/", &saveptr); seg != NULL; seg = strtok_r(NULL, "/", &saveptr)) {
    if (strcmp(seg, ".") == 0 || seg[0] == '\0') {
      continue;
    }
    if (strcmp(seg, "..") == 0) {
      free(tmp);
      free(out);
      return NULL;
    }
    out[out_len++] = '/';
    size_t slen = strlen(seg);
    memcpy(out + out_len, seg, slen);
    out_len += slen;
  }
  if (out_len == 0) {
    out[out_len++] = '/';
  }
  out[out_len] = '\0';
  free(tmp);
  return out;
}

static void free_plan_slot(PlanSlot *p) {
  if (p == NULL) {
    return;
  }
  close_fd(&p->plan_memfd);
  close_fd(&p->init_memfd);
  close_fd(&p->hosts_memfd);
  free(p->program);
  free(p->cwd);
  if (p->sys != NULL) {
    for (uint32_t i = 0; i < p->n_sys; i++) {
      free(p->sys[i].path);
      free(p->sys[i].target);
    }
    free(p->sys);
  }
  if (p->etc_paths != NULL) {
    for (uint32_t i = 0; i < p->n_etc; i++) {
      free(p->etc_paths[i]);
    }
    free(p->etc_paths);
  }
  if (p->masks != NULL) {
    for (uint32_t i = 0; i < p->n_masks; i++) {
      free(p->masks[i]);
    }
    free(p->masks);
  }
  if (p->mounts != NULL) {
    for (uint32_t i = 0; i < p->n_mounts; i++) {
      free(p->mounts[i].host_path);
      free(p->mounts[i].box_path);
    }
    free(p->mounts);
  }
  free(p);
}

typedef struct BufReader {
  const uint8_t *data;
  size_t len;
  size_t pos;
} BufReader;

static int br_u8(BufReader *r, uint8_t *out) {
  if (r->pos + 1 > r->len) {
    return -1;
  }
  *out = r->data[r->pos++];
  return 0;
}

static int br_u16(BufReader *r, uint16_t *out) {
  if (r->pos + 2 > r->len) {
    return -1;
  }
  *out = (uint16_t)r->data[r->pos] | ((uint16_t)r->data[r->pos + 1] << 8);
  r->pos += 2;
  return 0;
}

static int br_u32(BufReader *r, uint32_t *out) {
  if (r->pos + 4 > r->len) {
    return -1;
  }
  *out = (uint32_t)r->data[r->pos] |
         ((uint32_t)r->data[r->pos + 1] << 8) |
         ((uint32_t)r->data[r->pos + 2] << 16) |
         ((uint32_t)r->data[r->pos + 3] << 24);
  r->pos += 4;
  return 0;
}

static int br_u64(BufReader *r, uint64_t *out) {
  if (r->pos + 8 > r->len) {
    return -1;
  }
  uint64_t v = 0;
  for (int i = 0; i < 8; i++) {
    v |= ((uint64_t)r->data[r->pos + (size_t)i]) << (8 * i);
  }
  r->pos += 8;
  *out = v;
  return 0;
}

static int br_str(BufReader *r, char **out) {
  uint32_t slen = 0;
  if (br_u32(r, &slen) != 0 || slen > r->len - r->pos) {
    return -1;
  }
  const uint8_t *src = r->data + r->pos;
  for (uint32_t i = 0; i < slen; i++) {
    if (src[i] == 0) {
      return -1;
    }
  }
  char *s = (char *)malloc((size_t)slen + 1);
  if (s == NULL) {
    return -1;
  }
  if (slen > 0) {
    memcpy(s, src, slen);
  }
  s[slen] = '\0';
  r->pos += slen;
  *out = s;
  return 0;
}

static int parse_plan_for_shim(const uint8_t *data, size_t len, PlanSlot *p) {
  if (len < 8 || memcmp(data, "LSWP0001", 8) != 0) {
    return -1;
  }
  BufReader r = {data, len, 8};

  uint8_t empty_root = 0, unshare_all = 0, mount_proc = 0, mount_dev = 0;
  uint8_t direct_cg = 0, allow_lo = 0, block_unix = 0, allow_pair = 0;
  uint8_t clone3_enosys = 0, seccomp_deny = 0, no_new_privs = 0, rlimit_core0 = 0;
  uint8_t subreaper = 0, clean_env = 0, has_fsize = 0, has_out = 0;
  uint32_t ll_abi = 0;
  uint64_t timeout_ms = 0, fsize_max = 0, out_max = 0;

  if (br_u8(&r, &empty_root) != 0 ||
      br_u8(&r, &unshare_all) != 0 ||
      br_u8(&r, &mount_proc) != 0 ||
      br_u8(&r, &mount_dev) != 0 ||
      br_u8(&r, &direct_cg) != 0 ||
      br_u32(&r, &ll_abi) != 0 ||
      br_u8(&r, &allow_lo) != 0 ||
      br_u8(&r, &block_unix) != 0 ||
      br_u8(&r, &allow_pair) != 0 ||
      br_u8(&r, &clone3_enosys) != 0 ||
      br_u8(&r, &seccomp_deny) != 0 ||
      br_u8(&r, &no_new_privs) != 0 ||
      br_u8(&r, &rlimit_core0) != 0 ||
      br_u8(&r, &subreaper) != 0 ||
      br_u8(&r, &clean_env) != 0 ||
      br_u64(&r, &timeout_ms) != 0 ||
      br_u8(&r, &p->has_memory_max) != 0 || br_u64(&r, &p->memory_max_bytes) != 0 ||
      br_u8(&r, &p->has_pids_max) != 0 || br_u64(&r, &p->pids_max) != 0 ||
      br_u8(&r, &has_fsize) != 0 || br_u64(&r, &fsize_max) != 0 ||
      br_u8(&r, &has_out) != 0 || br_u64(&r, &out_max) != 0) {
    return -1;
  }

  (void)allow_lo;
  (void)timeout_ms;
  (void)has_fsize;
  (void)fsize_max;
  (void)has_out;
  (void)out_max;

  if (!empty_root || !unshare_all || !mount_proc || !mount_dev || !direct_cg ||
      ll_abi < 4 || !block_unix || !allow_pair || !clone3_enosys ||
      !seccomp_deny || !no_new_privs || !rlimit_core0 || !subreaper || !clean_env) {
    return -1;
  }

  if (br_str(&r, &p->program) != 0 || br_str(&r, &p->cwd) != 0) {
    return -1;
  }
  if (p->program[0] == '\0' || p->cwd[0] != '/') {
    return -1;
  }

  uint32_t argc = 0;
  if (br_u32(&r, &argc) != 0 || argc > 65536U) {
    return -1;
  }
  for (uint32_t i = 0; i < argc; i++) {
    char *s = NULL;
    if (br_str(&r, &s) != 0) {
      return -1;
    }
    free(s);
  }

  uint32_t envc = 0;
  if (br_u32(&r, &envc) != 0 || envc > 65536U) {
    return -1;
  }
  for (uint32_t i = 0; i < envc; i++) {
    char *k = NULL, *v = NULL;
    if (br_str(&r, &k) != 0 || br_str(&r, &v) != 0) {
      free(k);
      free(v);
      return -1;
    }
    free(k);
    free(v);
  }

  if (br_u32(&r, &p->n_sys) != 0 || p->n_sys > 1024U) {
    return -1;
  }
  p->sys = (ShimSysEntry *)calloc((size_t)p->n_sys + 1U, sizeof(ShimSysEntry));
  if (p->sys == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_sys; i++) {
    if (br_u8(&r, &p->sys[i].tag) != 0 || br_str(&r, &p->sys[i].path) != 0) {
      return -1;
    }
    if (p->sys[i].tag == 1) {
      if (br_str(&r, &p->sys[i].target) != 0) {
        return -1;
      }
    } else if (p->sys[i].tag != 0) {
      return -1;
    }
  }

  if (br_u32(&r, &p->n_etc) != 0 || p->n_etc > 1024U) {
    return -1;
  }
  p->etc_paths = (char **)calloc((size_t)p->n_etc + 1U, sizeof(char *));
  if (p->etc_paths == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_etc; i++) {
    if (br_str(&r, &p->etc_paths[i]) != 0) {
      return -1;
    }
  }

  if (br_u32(&r, &p->n_masks) != 0 || p->n_masks > 1024U) {
    return -1;
  }
  p->masks = (char **)calloc((size_t)p->n_masks + 1U, sizeof(char *));
  if (p->masks == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_masks; i++) {
    if (br_str(&r, &p->masks[i]) != 0) {
      return -1;
    }
  }

  if (br_u32(&r, &p->n_mounts) != 0 || p->n_mounts > 4096U) {
    return -1;
  }
  p->mounts = (ShimMount *)calloc((size_t)p->n_mounts + 1U, sizeof(ShimMount));
  if (p->mounts == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_mounts; i++) {
    if (br_u8(&r, &p->mounts[i].tag) != 0) {
      return -1;
    }
    if (p->mounts[i].tag == 0 || p->mounts[i].tag == 1) {
      if (br_str(&r, &p->mounts[i].host_path) != 0 ||
          br_str(&r, &p->mounts[i].box_path) != 0) {
        return -1;
      }
    } else if (p->mounts[i].tag == 2) {
      if (br_str(&r, &p->mounts[i].box_path) != 0) {
        return -1;
      }
    } else {
      return -1;
    }
  }

  if (br_u32(&r, &p->n_fwds) != 0 || p->n_fwds > 1024U) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_fwds; i++) {
    uint16_t bp = 0, hp = 0;
    if (br_u16(&r, &bp) != 0 || br_u16(&r, &hp) != 0 || bp == 0 || hp == 0) {
      return -1;
    }
  }

  if (r.pos != r.len) {
    return -1;
  }
  return 0;
}

static int probe_bwrap_namespaces(const char *bwrap_path) {
  int init_memfd = create_sealed_memfd(
      "leanswe-psandbox-probe", g_psandbox_init_elf, g_psandbox_init_elf_len);
  if (init_memfd < 0) {
    return -1;
  }
  int init_fd = reopen_memfd_ro_cloexec(init_memfd);
  int saved_err = errno;
  close(init_memfd);
  if (init_fd < 0) {
    errno = saved_err;
    return -1;
  }

  char init_fd_str[32];
  snprintf(init_fd_str, sizeof(init_fd_str), "%d", init_fd);

  char *argv[64];
  size_t ac = 0;
  argv[ac++] = (char *)bwrap_path;
  argv[ac++] = "--unshare-all";
  argv[ac++] = "--as-pid-1";
  argv[ac++] = "--die-with-parent";
  argv[ac++] = "--clearenv";

  static const char *const k_sys[] = {"/usr", "/bin", "/sbin", "/lib", "/lib64"};
  char *link_targets[5] = {NULL, NULL, NULL, NULL, NULL};
  for (size_t i = 0; i < 5; i++) {
    struct stat st;
    if (lstat(k_sys[i], &st) != 0) {
      continue;
    }
    if (S_ISLNK(st.st_mode)) {
      char tbuf[PATH_MAX];
      ssize_t rn = readlink(k_sys[i], tbuf, sizeof(tbuf) - 1);
      if (rn > 0) {
        tbuf[rn] = '\0';
        link_targets[i] = strdup(tbuf);
        if (link_targets[i] != NULL) {
          argv[ac++] = "--symlink";
          argv[ac++] = link_targets[i];
          argv[ac++] = (char *)k_sys[i];
        }
      }
    } else if (S_ISDIR(st.st_mode)) {
      argv[ac++] = "--ro-bind";
      argv[ac++] = (char *)k_sys[i];
      argv[ac++] = (char *)k_sys[i];
    }
  }
  struct stat ld_st;
  if (stat("/etc/ld.so.cache", &ld_st) == 0) {
    argv[ac++] = "--ro-bind";
    argv[ac++] = "/etc/ld.so.cache";
    argv[ac++] = "/etc/ld.so.cache";
  }
  argv[ac++] = "--perms";
  argv[ac++] = "0555";
  argv[ac++] = "--ro-bind-data";
  argv[ac++] = init_fd_str;
  argv[ac++] = "/etc/.leanswe-psandbox-init";
  argv[ac++] = "--remount-ro";
  argv[ac++] = "/";
  argv[ac++] = "--";
  argv[ac++] = "/etc/.leanswe-psandbox-init";
  argv[ac++] = "--probe";
  argv[ac++] = NULL;

  int devnull = open("/dev/null", O_RDWR | O_CLOEXEC);
  int err_pipe[2] = {-1, -1};
  int sync_pipe[2] = {-1, -1};
  if (pipe2(err_pipe, O_CLOEXEC) != 0 || pipe2(sync_pipe, O_CLOEXEC) != 0) {
    int err = errno;
    if (devnull >= 0) close(devnull);
    if (err_pipe[0] >= 0) close(err_pipe[0]);
    if (err_pipe[1] >= 0) close(err_pipe[1]);
    if (sync_pipe[0] >= 0) close(sync_pipe[0]);
    if (sync_pipe[1] >= 0) close(sync_pipe[1]);
    for (size_t i = 0; i < 5; i++) free(link_targets[i]);
    close(init_fd);
    errno = err;
    return -1;
  }

  SpawnRequest req;
  memset(&req, 0, sizeof(req));
  req.bwrap_path = bwrap_path;
  req.bwrap_argv = argv;
  req.cg_sync_read_fd = sync_pipe[0];
  req.cg_sync_write_fd = sync_pipe[1];
  req.bwrap_err_read_fd = err_pipe[0];
  req.bwrap_err_write_fd = err_pipe[1];
  req.stdin_read_fd = devnull >= 0 ? devnull : 0;
  req.stdout_write_fd = devnull >= 0 ? devnull : 1;
  req.stderr_write_fd = devnull >= 0 ? devnull : 2;
  req.status_write_fd = -1;
  req.go_read_fd = -1;
  req.ctrl_write_fd = -1;
  req.init_fd = init_fd;
  req.hosts_fd = -1;
  req.plan_fd = -1;

  int ferr = 0;
  pid_t pid = spawn_via_spawner(&req, &ferr);
  if (pid < 0) {
    close(sync_pipe[0]);
    close(sync_pipe[1]);
    close(err_pipe[0]);
    close(err_pipe[1]);
    if (devnull >= 0) close(devnull);
    for (size_t i = 0; i < 5; i++) free(link_targets[i]);
    close(init_fd);
    errno = ferr;
    return -1;
  }

  uint8_t go = 'G';
  (void)write_all_fd(sync_pipe[1], &go, 1);
  close(sync_pipe[1]);
  close(sync_pipe[0]);
  close(err_pipe[1]);
  if (devnull >= 0) close(devnull);
  close(init_fd);

  int exec_err = 0;
  ssize_t en = read(err_pipe[0], &exec_err, sizeof(exec_err));
  close(err_pipe[0]);
  for (size_t i = 0; i < 5; i++) free(link_targets[i]);

  int st = 0;
  while (waitpid(pid, &st, 0) < 0 && errno == EINTR) {
  }
  if (en > 0) {
    errno = exec_err ? exec_err : ENOENT;
    return -1;
  }
  if (!WIFEXITED(st) || WEXITSTATUS(st) != 0) {
    errno = EPERM;
    return -1;
  }
  return 0;
}

static uint64_t alloc_handle_id_locked(void) {
  uint64_t id = g_next_handle_id++;
  if (id == 0) {
    id = g_next_handle_id++;
  }
  return id;
}

static PlanSlot *find_plan_locked(uint64_t hid) {
  for (PlanSlot *cur = g_plans; cur != NULL; cur = cur->next) {
    if (cur->handle_id == hid) {
      return cur;
    }
  }
  return NULL;
}

static PlanSlot *detach_plan_locked(uint64_t hid) {
  PlanSlot **prev = &g_plans;
  while (*prev != NULL) {
    if ((*prev)->handle_id == hid) {
      PlanSlot *found = *prev;
      *prev = found->next;
      found->next = NULL;
      if (g_open_plans > 0) {
        g_open_plans--;
      }
      return found;
    }
    prev = &(*prev)->next;
  }
  return NULL;
}

static BoxSlot *find_box_locked(uint64_t hid) {
  for (BoxSlot *cur = g_boxes; cur != NULL; cur = cur->next) {
    if (cur->handle_id == hid) {
      return cur;
    }
  }
  return NULL;
}

static BoxSlot *detach_box_locked(uint64_t hid) {
  BoxSlot **prev = &g_boxes;
  while (*prev != NULL) {
    if ((*prev)->handle_id == hid) {
      BoxSlot *found = *prev;
      *prev = found->next;
      found->next = NULL;
      if (g_active_boxes > 0) {
        g_active_boxes--;
      }
      return found;
    }
    prev = &(*prev)->next;
  }
  return NULL;
}

static ForwarderSlot *detach_fwd_locked(uint64_t hid) {
  ForwarderSlot **prev = &g_fwds;
  while (*prev != NULL) {
    if ((*prev)->handle_id == hid) {
      ForwarderSlot *found = *prev;
      *prev = found->next;
      found->next = NULL;
      if (g_active_fwds > 0) {
        g_active_fwds--;
      }
      return found;
    }
    prev = &(*prev)->next;
  }
  return NULL;
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_preflight(
    uint8_t need_mem, uint8_t need_pids, lean_obj_arg w) {
  (void)w;
  char *bwrap_path = resolve_bwrap_path();
  if (bwrap_path == NULL) {
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_UNAVAILABLE, ENOENT, "", "bwrap executable not found in PATH"));
  }

  long ll_abi = syscall(__NR_landlock_create_ruleset, NULL, 0, 1U);
  if (ll_abi < 4) {
    int err = (ll_abi < 0) ? errno : ENOSYS;
    free(bwrap_path);
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_UNAVAILABLE, (uint32_t)err, "", "Landlock ABI >= 4 is required"));
  }

  uint32_t act = SECCOMP_RET_ERRNO;
  if (syscall(__NR_seccomp, SECCOMP_GET_ACTION_AVAIL, 0, &act) != 0) {
    int err = errno;
    free(bwrap_path);
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_UNAVAILABLE, (uint32_t)err, "", "seccomp filter support is required"));
  }

  if (probe_bwrap_namespaces(bwrap_path) != 0) {
    int err = errno;
    free(bwrap_path);
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_UNAVAILABLE, (uint32_t)err, "", "bwrap unprivileged namespaces unavailable"));
  }
  free(bwrap_path);

  char cg_dir[PATH_MAX];
  if (create_sibling_cgroup(cg_dir, sizeof(cg_dir)) != 0) {
    int err = errno;
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_UNAVAILABLE, (uint32_t)err, "", "direct /sys/fs/cgroup sibling directory unavailable"));
  }

  char path[PATH_MAX];
  char fail_msg_buf[128];
  int fail_err = 0;
  const char *fail_msg = NULL;

  if (cgroup_subfile(cg_dir, "cgroup.kill", path, sizeof(path)) != 0 ||
      access(path, W_OK) != 0) {
    fail_err = errno ? errno : ENOENT;
    fail_msg = "cgroup v2 cgroup.kill is unavailable";
  } else if (cgroup_subfile(cg_dir, "cgroup.events", path, sizeof(path)) != 0 ||
             access(path, R_OK) != 0) {
    fail_err = errno ? errno : ENOENT;
    fail_msg = "cgroup v2 cgroup.events is unavailable";
  }

  if (fail_msg == NULL && need_mem) {
    const char *failed_file = NULL;
    if (configure_cgroup_memory(cg_dir, "max", &failed_file, &fail_err) != 0) {
      if (strcmp(failed_file, "memory.max") == 0) {
        fail_msg = "direct cgroup v2 memory controller unavailable";
      } else {
        snprintf(fail_msg_buf, sizeof(fail_msg_buf), "direct cgroup v2 %s unavailable", failed_file);
        fail_msg = fail_msg_buf;
      }
    }
  }

  if (fail_msg == NULL && need_pids) {
    if (cgroup_subfile(cg_dir, "pids.max", path, sizeof(path)) != 0 ||
        write_text_file(path, "max") != 0) {
      fail_err = errno ? errno : EACCES;
      fail_msg = "direct cgroup v2 pids controller unavailable";
    }
  }

  (void)cleanup_cgroup_dir(cg_dir);
  if (fail_msg != NULL) {
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_UNAVAILABLE, (uint32_t)fail_err, "", fail_msg));
  }
  return lean_io_result_mk_ok(mk_err_tuple4(PS_TAG_OK, 0, "", ""));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_discover_preset(lean_obj_arg w) {
  (void)w;
  lean_obj_res sys_arr = lean_mk_empty_array();
  static const char *const k_sys_roots[] = {"/usr", "/bin", "/sbin", "/lib", "/lib64"};
  for (size_t i = 0; i < 5; i++) {
    struct stat st;
    if (lstat(k_sys_roots[i], &st) != 0) {
      continue;
    }
    if (S_ISLNK(st.st_mode)) {
      char tbuf[PATH_MAX];
      ssize_t rn = readlink(k_sys_roots[i], tbuf, sizeof(tbuf) - 1);
      if (rn > 0) {
        tbuf[rn] = '\0';
        lean_obj_res p3 = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(p3, 0, lean_mk_string(k_sys_roots[i]));
        lean_ctor_set(p3, 1, lean_mk_string(tbuf));
        lean_obj_res elem = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(elem, 0, lean_box(1));
        lean_ctor_set(elem, 1, p3);
        sys_arr = lean_array_push(sys_arr, elem);
      }
    } else if (S_ISDIR(st.st_mode)) {
      lean_obj_res p3 = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(p3, 0, lean_mk_string(k_sys_roots[i]));
      lean_ctor_set(p3, 1, lean_mk_string(""));
      lean_obj_res elem = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(elem, 0, lean_box(0));
      lean_ctor_set(elem, 1, p3);
      sys_arr = lean_array_push(sys_arr, elem);
    }
  }

  lean_obj_res etc_arr = lean_mk_empty_array();
  static const char *const k_etc_paths[] = {
    "/etc/ld.so.cache",
    "/etc/passwd",
    "/etc/group",
    "/etc/nsswitch.conf",
    "/etc/localtime",
    "/etc/os-release",
    "/etc/alternatives",
    "/etc/ssl/certs",
    "/etc/ssl/openssl.cnf"
  };
  for (size_t i = 0; i < sizeof(k_etc_paths) / sizeof(k_etc_paths[0]); i++) {
    struct stat st;
    if (stat(k_etc_paths[i], &st) == 0) {
      etc_arr = lean_array_push(etc_arr, lean_mk_string(k_etc_paths[i]));
    }
  }

  lean_obj_res home_arr = lean_mk_empty_array();
  const char *candidates[2] = {getenv("HOME"), NULL};
  struct passwd pw;
  struct passwd *pw_res = NULL;
  char *pw_buf = NULL;
  long pw_sz = sysconf(_SC_GETPW_R_SIZE_MAX);
  size_t bufsz = (pw_sz > 0) ? (size_t)pw_sz : 4096U;
  pw_buf = (char *)malloc(bufsz);
  if (pw_buf != NULL) {
    if (getpwuid_r(getuid(), &pw, pw_buf, bufsz, &pw_res) == 0 && pw_res != NULL) {
      candidates[1] = pw_res->pw_dir;
    }
  }
  char *seen[2] = {NULL, NULL};
  for (int i = 0; i < 2; i++) {
    char *norm = normalize_abs_lexical(candidates[i]);
    if (norm == NULL) {
      continue;
    }
    if (is_under_system_root_lexical(norm)) {
      struct stat st;
      if (stat(norm, &st) == 0 && S_ISDIR(st.st_mode)) {
        int dup = 0;
        for (int j = 0; j < i; j++) {
          if (seen[j] != NULL && strcmp(seen[j], norm) == 0) {
            dup = 1;
            break;
          }
        }
        if (!dup) {
          seen[i] = norm;
          home_arr = lean_array_push(home_arr, lean_mk_string(norm));
          norm = NULL;
        }
      }
    }
    free(norm);
  }
  free(seen[0]);
  free(seen[1]);
  free(pw_buf);

  lean_obj_res d2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(d2, 0, etc_arr);
  lean_ctor_set(d2, 1, home_arr);
  lean_obj_res d1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(d1, 0, sys_arr);
  lean_ctor_set(d1, 1, d2);
  lean_obj_res t3 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t3, 0, lean_mk_string(""));
  lean_ctor_set(t3, 1, d1);
  lean_obj_res t2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t2, 0, lean_box_uint32(0));
  lean_ctor_set(t2, 1, t3);
  lean_obj_res t1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t1, 0, lean_box(PS_TAG_OK));
  lean_ctor_set(t1, 1, t2);
  return lean_io_result_mk_ok(t1);
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_seal_plan(
    b_lean_obj_arg plan_bytes_obj, lean_obj_arg w) {
  (void)w;
  size_t len = lean_sarray_size(plan_bytes_obj);
  const uint8_t *data = (len > 0) ? lean_sarray_cptr((lean_object *)plan_bytes_obj) : NULL;

  PlanSlot *slot = (PlanSlot *)calloc(1, sizeof(PlanSlot));
  if (slot == NULL) {
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_IO_ERROR, ENOMEM, "", "out of memory", 0));
  }
  slot->plan_memfd = -1;
  slot->init_memfd = -1;
  slot->hosts_memfd = -1;

  if (data == NULL || parse_plan_for_shim(data, len, slot) != 0) {
    free_plan_slot(slot);
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_INVALID_INPUT, EINVAL, "", "invalid compiled sandbox plan", 0));
  }

  slot->plan_memfd = create_sealed_memfd("leanswe-psandbox-plan", data, len);
  if (slot->plan_memfd < 0) {
    int err = errno;
    free_plan_slot(slot);
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_IO_ERROR, (uint32_t)err, "", "failed to seal plan memfd", 0));
  }

  slot->init_memfd = create_sealed_memfd(
      "leanswe-psandbox-init", g_psandbox_init_elf, g_psandbox_init_elf_len);
  if (slot->init_memfd < 0) {
    int err = errno;
    free_plan_slot(slot);
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_IO_ERROR, (uint32_t)err, "", "failed to seal init memfd", 0));
  }

  static const char k_hosts[] = "127.0.0.1 localhost\n::1 localhost\n";
  slot->hosts_memfd = create_sealed_memfd("leanswe-psandbox-hosts", k_hosts, sizeof(k_hosts) - 1);
  if (slot->hosts_memfd < 0) {
    int err = errno;
    free_plan_slot(slot);
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_IO_ERROR, (uint32_t)err, "", "failed to seal hosts memfd", 0));
  }

  pthread_mutex_lock(&g_mu);
  uint64_t hid = alloc_handle_id_locked();
  slot->handle_id = hid;
  slot->next = g_plans;
  g_plans = slot;
  g_open_plans++;
  pthread_mutex_unlock(&g_mu);

  return lean_io_result_mk_ok(mk_err_tuple5_u64(PS_TAG_OK, 0, "", "", hid));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_close_plan(uint64_t plan_hid, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_mu);
  PlanSlot *slot = detach_plan_locked(plan_hid);
  pthread_mutex_unlock(&g_mu);
  if (slot == NULL) {
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_INVALID_INPUT, EINVAL, "", "invalid or closed plan handle"));
  }
  free_plan_slot(slot);
  return lean_io_result_mk_ok(mk_err_tuple4(PS_TAG_OK, 0, "", ""));
}

static uint8_t map_errno_to_path_tag(int err) {
  if (err == ENOENT || err == ENOTDIR) {
    return PS_TAG_NOT_FOUND;
  }
  if (err == EACCES || err == EPERM) {
    return PS_TAG_PERM_DENIED;
  }
  return PS_TAG_IO_ERROR;
}

static int recv_fds_scm(int ctrl_fd, int *out_fds, uint32_t expected, int status_fd) {
  uint32_t got = 0;
  while (got < expected) {
    struct pollfd pfds[2];
    pfds[0].fd = ctrl_fd;
    pfds[0].events = POLLIN;
    pfds[0].revents = 0;
    pfds[1].fd = status_fd;
    pfds[1].events = POLLIN;
    pfds[1].revents = 0;

    int rc = poll(pfds, 2, -1);
    if (rc < 0) {
      if (errno == EINTR) {
        continue;
      }
      int saved = errno ? errno : EIO;
      for (uint32_t j = 0; j < got; j++) {
        close_fd(&out_fds[j]);
      }
      errno = saved;
      return -1;
    }
    if (pfds[0].revents & POLLIN) {
      uint8_t dummy = 0;
      struct iovec iov;
      iov.iov_base = &dummy;
      iov.iov_len = 1;
      uint8_t cbuf[CMSG_SPACE(32 * sizeof(int))];
      memset(cbuf, 0, sizeof(cbuf));
      struct msghdr msg;
      memset(&msg, 0, sizeof(msg));
      msg.msg_iov = &iov;
      msg.msg_iovlen = 1;
      msg.msg_control = cbuf;
      msg.msg_controllen = sizeof(cbuf);

      ssize_t rn = recvmsg(ctrl_fd, &msg, MSG_CMSG_CLOEXEC);
      if (rn < 0) {
        if (errno == EINTR) {
          continue;
        }
        int saved = errno ? errno : EIO;
        for (uint32_t j = 0; j < got; j++) {
          close_fd(&out_fds[j]);
        }
        errno = saved;
        return -1;
      }
      if (rn == 0) {
        for (uint32_t j = 0; j < got; j++) {
          close_fd(&out_fds[j]);
        }
        errno = EPROTO;
        return -1;
      }
      struct cmsghdr *cmsg = CMSG_FIRSTHDR(&msg);
      if (cmsg == NULL || cmsg->cmsg_level != SOL_SOCKET || cmsg->cmsg_type != SCM_RIGHTS) {
        for (uint32_t j = 0; j < got; j++) {
          close_fd(&out_fds[j]);
        }
        errno = EPROTO;
        return -1;
      }
      size_t data_bytes = (size_t)cmsg->cmsg_len - CMSG_LEN(0);
      uint32_t n_in_msg = (uint32_t)(data_bytes / sizeof(int));
      if (n_in_msg == 0 || got + n_in_msg > expected) {
        int tmp_fds[32];
        if (n_in_msg <= 32) {
          memcpy(tmp_fds, CMSG_DATA(cmsg), (size_t)n_in_msg * sizeof(int));
          for (uint32_t k = 0; k < n_in_msg; k++) {
            close(tmp_fds[k]);
          }
        }
        for (uint32_t j = 0; j < got; j++) {
          close_fd(&out_fds[j]);
        }
        errno = EPROTO;
        return -1;
      }
      memcpy(out_fds + got, CMSG_DATA(cmsg), (size_t)n_in_msg * sizeof(int));
      got += n_in_msg;
      continue;
    }
    if ((pfds[0].revents & (POLLERR | POLLHUP | POLLNVAL)) ||
        (pfds[1].revents & (POLLIN | POLLHUP | POLLERR | POLLNVAL))) {
      for (uint32_t j = 0; j < got; j++) {
        close_fd(&out_fds[j]);
      }
      errno = EPROTO;
      return -1;
    }
  }
  return 0;
}

static void drain_stderr_snippet(int fd, char *out, size_t out_sz) {
  if (out_sz == 0) {
    return;
  }
  out[0] = '\0';
  if (fd < 0) {
    return;
  }
  (void)set_nonblock_fd(fd);
  size_t off = 0;
  while (off + 1 < out_sz) {
    ssize_t n = read(fd, out + off, out_sz - 1 - off);
    if (n <= 0) {
      break;
    }
    off += (size_t)n;
  }
  while (off > 0 && (out[off - 1] == '\n' || out[off - 1] == '\r')) {
    off--;
  }
  out[off] = '\0';
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_spawn_box(uint64_t plan_hid, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_mu);
  PlanSlot *pslot = find_plan_locked(plan_hid);
  if (pslot == NULL) {
    pthread_mutex_unlock(&g_mu);
    return lean_io_result_mk_ok(
        mk_spawn_tuple(PS_TAG_INVALID_INPUT, EINVAL, "", "invalid or closed plan handle", 0, 0, 0, 0));
  }

  int init_fd = reopen_memfd_ro_cloexec(pslot->init_memfd);
  int hosts_fd = reopen_memfd_ro_cloexec(pslot->hosts_memfd);
  int plan_fd = reopen_memfd_ro_cloexec(pslot->plan_memfd);
  if (init_fd < 0 || hosts_fd < 0 || plan_fd < 0) {
    int err = errno;
    pthread_mutex_unlock(&g_mu);
    close_fd(&init_fd);
    close_fd(&hosts_fd);
    close_fd(&plan_fd);
    return lean_io_result_mk_ok(
        mk_spawn_tuple(PS_TAG_IO_ERROR, (uint32_t)err, "", "failed to reopen sealed memfd", 0, 0, 0, 0));
  }

  uint8_t has_mem = pslot->has_memory_max;
  uint64_t mem_max = pslot->memory_max_bytes;
  uint8_t has_pids = pslot->has_pids_max;
  uint64_t pids_max = pslot->pids_max;
  uint32_t n_fwds = pslot->n_fwds;
  uint32_t n_sys = pslot->n_sys;
  uint32_t n_etc = pslot->n_etc;
  uint32_t n_masks = pslot->n_masks;
  uint32_t n_mounts = pslot->n_mounts;

  char *program = strdup(pslot->program);
  char *cwd = strdup(pslot->cwd);
  ShimSysEntry *sys = (ShimSysEntry *)calloc((size_t)n_sys + 1U, sizeof(ShimSysEntry));
  char **etc_paths = (char **)calloc((size_t)n_etc + 1U, sizeof(char *));
  char **masks = (char **)calloc((size_t)n_masks + 1U, sizeof(char *));
  ShimMount *mounts = (ShimMount *)calloc((size_t)n_mounts + 1U, sizeof(ShimMount));

  int alloc_ok = (program != NULL && cwd != NULL && sys != NULL && etc_paths != NULL && masks != NULL && mounts != NULL);
  if (alloc_ok) {
    for (uint32_t i = 0; i < n_sys; i++) {
      sys[i].tag = pslot->sys[i].tag;
      sys[i].path = strdup(pslot->sys[i].path);
      sys[i].target = pslot->sys[i].target != NULL ? strdup(pslot->sys[i].target) : NULL;
      if (sys[i].path == NULL || (pslot->sys[i].target != NULL && sys[i].target == NULL)) {
        alloc_ok = 0;
      }
    }
    for (uint32_t i = 0; i < n_etc; i++) {
      etc_paths[i] = strdup(pslot->etc_paths[i]);
      if (etc_paths[i] == NULL) alloc_ok = 0;
    }
    for (uint32_t i = 0; i < n_masks; i++) {
      masks[i] = strdup(pslot->masks[i]);
      if (masks[i] == NULL) alloc_ok = 0;
    }
    for (uint32_t i = 0; i < n_mounts; i++) {
      mounts[i].tag = pslot->mounts[i].tag;
      mounts[i].box_path = strdup(pslot->mounts[i].box_path);
      mounts[i].host_path = pslot->mounts[i].host_path != NULL ? strdup(pslot->mounts[i].host_path) : NULL;
      if (mounts[i].box_path == NULL || (pslot->mounts[i].host_path != NULL && mounts[i].host_path == NULL)) {
        alloc_ok = 0;
      }
    }
  }
  pthread_mutex_unlock(&g_mu);

  char *bwrap_path = NULL;
  char **bwrap_argv = NULL;
  int cg_sync_pipe[2] = {-1, -1};
  int bwrap_err_pipe[2] = {-1, -1};
  int stdin_pipe[2] = {-1, -1};
  int stdout_pipe[2] = {-1, -1};
  int stderr_pipe[2] = {-1, -1};
  int status_pipe[2] = {-1, -1};
  int go_pipe[2] = {-1, -1};
  int ctrl_sock[2] = {-1, -1};
  int *listener_fds = NULL;
  char cg_dir[PATH_MAX];
  cg_dir[0] = '\0';
  uint8_t err_tag = PS_TAG_UNAVAILABLE;
  uint32_t err_code = 0;
  char err_path[PATH_MAX];
  err_path[0] = '\0';
  char err_msg[768];
  err_msg[0] = '\0';
  pid_t child_pid = -1;
  int pidfd = -1;

  if (!alloc_ok) {
    err_tag = PS_TAG_IO_ERROR;
    err_code = ENOMEM;
    snprintf(err_msg, sizeof(err_msg), "out of memory");
    goto fail;
  }

  bwrap_path = resolve_bwrap_path();
  if (bwrap_path == NULL) {
    err_tag = PS_TAG_UNAVAILABLE;
    err_code = ENOENT;
    snprintf(err_msg, sizeof(err_msg), "bwrap executable not found in PATH");
    goto fail;
  }

  for (uint32_t i = 0; i < n_mounts; i++) {
    if (mounts[i].tag == 0 || mounts[i].tag == 1) {
      struct stat st;
      if (stat(mounts[i].host_path, &st) != 0) {
        int e = errno;
        err_tag = map_errno_to_path_tag(e);
        err_code = (uint32_t)e;
        snprintf(err_path, sizeof(err_path), "%s", mounts[i].host_path);
        snprintf(err_msg, sizeof(err_msg), "host mount path error: %s", strerror(e));
        goto fail;
      }
    }
  }

  if (create_sibling_cgroup(cg_dir, sizeof(cg_dir)) != 0) {
    int e = errno;
    err_tag = PS_TAG_UNAVAILABLE;
    err_code = (uint32_t)e;
    snprintf(err_msg, sizeof(err_msg), "failed to create direct cgroup v2 directory: %s", strerror(e));
    goto fail;
  }

  char cg_file[PATH_MAX];
  if (cgroup_subfile(cg_dir, "cgroup.kill", cg_file, sizeof(cg_file)) != 0 ||
      access(cg_file, W_OK) != 0) {
    int e = errno ? errno : ENOENT;
    err_tag = PS_TAG_UNAVAILABLE;
    err_code = (uint32_t)e;
    snprintf(err_msg, sizeof(err_msg), "direct cgroup v2 cgroup.kill unavailable");
    goto fail;
  }

  if (has_mem) {
    char numbuf[32];
    const char *failed_file = NULL;
    int e = 0;
    snprintf(numbuf, sizeof(numbuf), "%llu", (unsigned long long)mem_max);
    if (configure_cgroup_memory(cg_dir, numbuf, &failed_file, &e) != 0) {
      err_tag = PS_TAG_UNAVAILABLE;
      err_code = (uint32_t)e;
      snprintf(err_msg, sizeof(err_msg), "failed to set direct cgroup v2 %s: %s", failed_file, strerror(e));
      goto fail;
    }
  }

  if (has_pids) {
    uint64_t capped_pids = (pids_max <= UINT64_MAX - 2ULL) ? (pids_max + 2ULL) : UINT64_MAX;
    char numbuf[32];
    snprintf(numbuf, sizeof(numbuf), "%llu", (unsigned long long)capped_pids);
    if (cgroup_subfile(cg_dir, "pids.max", cg_file, sizeof(cg_file)) != 0 ||
        write_text_file(cg_file, numbuf) != 0) {
      int e = errno ? errno : EACCES;
      err_tag = PS_TAG_UNAVAILABLE;
      err_code = (uint32_t)e;
      snprintf(err_msg, sizeof(err_msg), "failed to set direct cgroup v2 pids.max: %s", strerror(e));
      goto fail;
    }
  }

  if (pipe2(cg_sync_pipe, O_CLOEXEC) != 0 ||
      pipe2(bwrap_err_pipe, O_CLOEXEC) != 0 ||
      pipe2(stdin_pipe, O_CLOEXEC) != 0 ||
      pipe2(stdout_pipe, O_CLOEXEC) != 0 ||
      pipe2(stderr_pipe, O_CLOEXEC) != 0 ||
      pipe2(status_pipe, O_CLOEXEC) != 0 ||
      pipe2(go_pipe, O_CLOEXEC) != 0) {
    int e = errno;
    err_tag = PS_TAG_IO_ERROR;
    err_code = (uint32_t)e;
    snprintf(err_msg, sizeof(err_msg), "pipe2 failed: %s", strerror(e));
    goto fail;
  }

  if (n_fwds > 0) {
    if (socketpair(AF_UNIX, SOCK_SEQPACKET | SOCK_CLOEXEC, 0, ctrl_sock) != 0) {
      int e = errno;
      err_tag = PS_TAG_IO_ERROR;
      err_code = (uint32_t)e;
      snprintf(err_msg, sizeof(err_msg), "socketpair failed: %s", strerror(e));
      goto fail;
    }
    listener_fds = (int *)calloc((size_t)n_fwds, sizeof(int));
    if (listener_fds == NULL) {
      err_tag = PS_TAG_IO_ERROR;
      err_code = ENOMEM;
      snprintf(err_msg, sizeof(err_msg), "out of memory");
      goto fail;
    }
    for (uint32_t i = 0; i < n_fwds; i++) {
      listener_fds[i] = -1;
    }
  }

  size_t max_args = 32 + (size_t)n_sys * 3 + (size_t)n_etc * 3 + (size_t)n_masks * 6 + (size_t)n_mounts * 5 + 16;
  bwrap_argv = (char **)calloc(max_args, sizeof(char *));
  if (bwrap_argv == NULL) {
    err_tag = PS_TAG_IO_ERROR;
    err_code = ENOMEM;
    snprintf(err_msg, sizeof(err_msg), "out of memory");
    goto fail;
  }

  char init_fd_str[32], hosts_fd_str[32], plan_fd_str[32];
  char status_fd_str[32], go_fd_str[32], ctrl_fd_str[32];
  snprintf(init_fd_str, sizeof(init_fd_str), "%d", init_fd);
  snprintf(hosts_fd_str, sizeof(hosts_fd_str), "%d", hosts_fd);
  snprintf(plan_fd_str, sizeof(plan_fd_str), "%d", plan_fd);
  snprintf(status_fd_str, sizeof(status_fd_str), "%d", status_pipe[1]);
  snprintf(go_fd_str, sizeof(go_fd_str), "%d", go_pipe[0]);
  snprintf(ctrl_fd_str, sizeof(ctrl_fd_str), "%d", ctrl_sock[1]);

  size_t ac = 0;
  bwrap_argv[ac++] = bwrap_path;
  bwrap_argv[ac++] = "--unshare-all";
  bwrap_argv[ac++] = "--as-pid-1";
  bwrap_argv[ac++] = "--die-with-parent";
  bwrap_argv[ac++] = "--clearenv";
  bwrap_argv[ac++] = "--proc";
  bwrap_argv[ac++] = "/proc";
  bwrap_argv[ac++] = "--dev";
  bwrap_argv[ac++] = "/dev";
  bwrap_argv[ac++] = "--perms";
  bwrap_argv[ac++] = "0755";
  bwrap_argv[ac++] = "--dir";
  bwrap_argv[ac++] = "/etc";

  for (uint32_t i = 0; i < n_sys; i++) {
    if (sys[i].tag == 0) {
      bwrap_argv[ac++] = "--ro-bind";
      bwrap_argv[ac++] = sys[i].path;
      bwrap_argv[ac++] = sys[i].path;
    }
  }
  for (uint32_t i = 0; i < n_sys; i++) {
    if (sys[i].tag == 1) {
      bwrap_argv[ac++] = "--symlink";
      bwrap_argv[ac++] = sys[i].target;
      bwrap_argv[ac++] = sys[i].path;
    }
  }
  for (uint32_t i = 0; i < n_etc; i++) {
    bwrap_argv[ac++] = "--ro-bind";
    bwrap_argv[ac++] = etc_paths[i];
    bwrap_argv[ac++] = etc_paths[i];
  }
  bwrap_argv[ac++] = "--perms";
  bwrap_argv[ac++] = "0444";
  bwrap_argv[ac++] = "--ro-bind-data";
  bwrap_argv[ac++] = hosts_fd_str;
  bwrap_argv[ac++] = "/etc/hosts";

  bwrap_argv[ac++] = "--perms";
  bwrap_argv[ac++] = "0555";
  bwrap_argv[ac++] = "--ro-bind-data";
  bwrap_argv[ac++] = init_fd_str;
  bwrap_argv[ac++] = "/etc/.leanswe-psandbox-init";

  for (uint32_t i = 0; i < n_masks; i++) {
    bwrap_argv[ac++] = "--perms";
    bwrap_argv[ac++] = "0000";
    bwrap_argv[ac++] = "--tmpfs";
    bwrap_argv[ac++] = masks[i];
    bwrap_argv[ac++] = "--remount-ro";
    bwrap_argv[ac++] = masks[i];
  }

  for (uint32_t i = 0; i < n_mounts; i++) {
    if (mounts[i].tag == 0) {
      bwrap_argv[ac++] = "--ro-bind";
      bwrap_argv[ac++] = mounts[i].host_path;
      bwrap_argv[ac++] = mounts[i].box_path;
    } else if (mounts[i].tag == 1) {
      bwrap_argv[ac++] = "--bind";
      bwrap_argv[ac++] = mounts[i].host_path;
      bwrap_argv[ac++] = mounts[i].box_path;
    } else {
      bwrap_argv[ac++] = "--perms";
      bwrap_argv[ac++] = "1777";
      bwrap_argv[ac++] = "--tmpfs";
      bwrap_argv[ac++] = mounts[i].box_path;
    }
  }

  bwrap_argv[ac++] = "--remount-ro";
  bwrap_argv[ac++] = "/";
  bwrap_argv[ac++] = "--";
  bwrap_argv[ac++] = "/etc/.leanswe-psandbox-init";
  bwrap_argv[ac++] = "--plan-fd";
  bwrap_argv[ac++] = plan_fd_str;
  bwrap_argv[ac++] = "--status-fd";
  bwrap_argv[ac++] = status_fd_str;
  bwrap_argv[ac++] = "--go-fd";
  bwrap_argv[ac++] = go_fd_str;
  bwrap_argv[ac++] = "--ctrl-fd";
  bwrap_argv[ac++] = ctrl_fd_str;
  bwrap_argv[ac++] = NULL;

  SpawnRequest sreq;
  memset(&sreq, 0, sizeof(sreq));
  sreq.bwrap_path = bwrap_path;
  sreq.bwrap_argv = bwrap_argv;
  sreq.cg_sync_read_fd = cg_sync_pipe[0];
  sreq.cg_sync_write_fd = cg_sync_pipe[1];
  sreq.bwrap_err_read_fd = bwrap_err_pipe[0];
  sreq.bwrap_err_write_fd = bwrap_err_pipe[1];
  sreq.stdin_read_fd = stdin_pipe[0];
  sreq.stdout_write_fd = stdout_pipe[1];
  sreq.stderr_write_fd = stderr_pipe[1];
  sreq.status_write_fd = status_pipe[1];
  sreq.go_read_fd = go_pipe[0];
  sreq.ctrl_write_fd = ctrl_sock[1];
  sreq.init_fd = init_fd;
  sreq.hosts_fd = hosts_fd;
  sreq.plan_fd = plan_fd;

  int fork_err = 0;
  child_pid = spawn_via_spawner(&sreq, &fork_err);
  if (child_pid < 0) {
    err_tag = PS_TAG_UNAVAILABLE;
    err_code = (uint32_t)fork_err;
    snprintf(err_msg, sizeof(err_msg), "failed to fork bwrap: %s", strerror(fork_err));
    goto fail;
  }

  (void)setpgid(child_pid, child_pid);
  pidfd = (int)syscall(__NR_pidfd_open, child_pid, 0);
  if (pidfd < 0) {
    int e = errno;
    err_tag = PS_TAG_UNAVAILABLE;
    err_code = (uint32_t)e;
    snprintf(err_msg, sizeof(err_msg), "pidfd_open failed: %s", strerror(e));
    close_fd(&cg_sync_pipe[1]);
    goto fail;
  }

  char pid_str[32];
  snprintf(pid_str, sizeof(pid_str), "%ld", (long)child_pid);
  if (cgroup_subfile(cg_dir, "cgroup.procs", cg_file, sizeof(cg_file)) != 0 ||
      write_text_file(cg_file, pid_str) != 0) {
    int e = errno ? errno : EACCES;
    err_tag = PS_TAG_UNAVAILABLE;
    err_code = (uint32_t)e;
    snprintf(err_msg, sizeof(err_msg), "failed to attach child to cgroup.procs: %s", strerror(e));
    close_fd(&cg_sync_pipe[1]);
    goto fail;
  }

  uint8_t cg_go = 'G';
  if (write_all_fd(cg_sync_pipe[1], &cg_go, 1) != 0) {
    int e = errno;
    err_tag = PS_TAG_IO_ERROR;
    err_code = (uint32_t)e;
    snprintf(err_msg, sizeof(err_msg), "cgroup sync write failed");
    close_fd(&cg_sync_pipe[1]);
    goto fail;
  }
  close_fd(&cg_sync_pipe[1]);
  close_fd(&cg_sync_pipe[0]);

  close_fd(&init_fd);
  close_fd(&hosts_fd);
  close_fd(&plan_fd);
  close_fd(&stdin_pipe[0]);
  close_fd(&stdout_pipe[1]);
  close_fd(&stderr_pipe[1]);
  close_fd(&bwrap_err_pipe[1]);
  close_fd(&status_pipe[1]);
  close_fd(&go_pipe[0]);
  close_fd(&ctrl_sock[1]);

  int bw_err = 0;
  ssize_t bn = 0;
  for (;;) {
    bn = read(bwrap_err_pipe[0], &bw_err, sizeof(bw_err));
    if (bn < 0 && errno == EINTR) {
      continue;
    }
    break;
  }
  close_fd(&bwrap_err_pipe[0]);
  if (bn > 0) {
    err_tag = PS_TAG_UNAVAILABLE;
    err_code = (uint32_t)(bw_err ? bw_err : ENOENT);
    snprintf(err_msg, sizeof(err_msg), "execvp bwrap failed: %s", strerror((int)err_code));
    goto fail;
  }

  if (n_fwds > 0) {
    if (recv_fds_scm(ctrl_sock[0], listener_fds, n_fwds, status_pipe[0]) != 0) {
      char snip[256];
      drain_stderr_snippet(stderr_pipe[0], snip, sizeof(snip));
      err_tag = PS_TAG_UNAVAILABLE;
      err_code = errno ? (uint32_t)errno : EIO;
      if (snip[0] != '\0') {
        snprintf(err_msg, sizeof(err_msg), "sandbox setup failed: %s", snip);
      } else {
        snprintf(err_msg, sizeof(err_msg), "failed to receive box port listener descriptors");
      }
      goto fail;
    }
  }
  close_fd(&ctrl_sock[0]);

  InitStatusMsg smsg;
  memset(&smsg, 0, sizeof(smsg));
  size_t sgot = 0;
  uint8_t *sp = (uint8_t *)&smsg;
  while (sgot < sizeof(smsg)) {
    ssize_t n = read(status_pipe[0], sp + sgot, sizeof(smsg) - sgot);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      break;
    }
    if (n == 0) {
      break;
    }
    sgot += (size_t)n;
  }

  if (sgot != sizeof(smsg) || smsg.kind != PS_STATUS_READY) {
    char snip[256];
    drain_stderr_snippet(stderr_pipe[0], snip, sizeof(snip));
    err_tag = PS_TAG_UNAVAILABLE;
    if (sgot == sizeof(smsg) && smsg.kind == PS_STATUS_INIT_ERR) {
      err_code = (uint32_t)smsg.value;
    } else {
      err_code = errno ? (uint32_t)errno : EPERM;
    }
    if (snip[0] != '\0') {
      snprintf(err_msg, sizeof(err_msg), "sandbox init failed before execvp: %s", snip);
    } else {
      snprintf(err_msg, sizeof(err_msg), "sandbox init failed before execvp: %s", strerror((int)err_code));
    }
    goto fail;
  }

  BoxSlot *bslot = (BoxSlot *)calloc(1, sizeof(BoxSlot));
  if (bslot == NULL) {
    err_tag = PS_TAG_IO_ERROR;
    err_code = ENOMEM;
    snprintf(err_msg, sizeof(err_msg), "out of memory");
    goto fail;
  }

  bslot->pid = child_pid;
  bslot->pgid = child_pid;
  bslot->pidfd = pidfd;
  bslot->stdin_fd = stdin_pipe[1];
  bslot->stdout_fd = stdout_pipe[0];
  bslot->stderr_fd = stderr_pipe[0];
  bslot->status_fd = status_pipe[0];
  bslot->go_fd = go_pipe[1];
  bslot->n_listeners = n_fwds;
  bslot->listener_fds = listener_fds;
  bslot->cgroup_dir = strdup(cg_dir);
  bslot->program = program;
  bslot->cwd = cwd;
  if (bslot->cgroup_dir == NULL) {
    free(bslot);
    err_tag = PS_TAG_IO_ERROR;
    err_code = ENOMEM;
    snprintf(err_msg, sizeof(err_msg), "out of memory");
    goto fail;
  }

  free(bwrap_path);
  free(bwrap_argv);
  for (uint32_t i = 0; i < n_sys; i++) {
    free(sys[i].path);
    free(sys[i].target);
  }
  free(sys);
  for (uint32_t i = 0; i < n_etc; i++) free(etc_paths[i]);
  free(etc_paths);
  for (uint32_t i = 0; i < n_masks; i++) free(masks[i]);
  free(masks);
  for (uint32_t i = 0; i < n_mounts; i++) {
    free(mounts[i].host_path);
    free(mounts[i].box_path);
  }
  free(mounts);

  pthread_mutex_lock(&g_mu);
  uint64_t bhid = alloc_handle_id_locked();
  bslot->handle_id = bhid;
  bslot->next = g_boxes;
  g_boxes = bslot;
  g_active_boxes++;
  pthread_mutex_unlock(&g_mu);

  return lean_io_result_mk_ok(
      mk_spawn_tuple(PS_TAG_OK, 0, "", "", bhid, (uint32_t)child_pid, (uint32_t)child_pid, (uint32_t)pidfd));

fail:
  close_fd(&init_fd);
  close_fd(&hosts_fd);
  close_fd(&plan_fd);
  close_fd(&cg_sync_pipe[0]);
  close_fd(&cg_sync_pipe[1]);
  close_fd(&bwrap_err_pipe[0]);
  close_fd(&bwrap_err_pipe[1]);
  close_fd(&stdin_pipe[0]);
  close_fd(&stdin_pipe[1]);
  close_fd(&stdout_pipe[0]);
  close_fd(&stdout_pipe[1]);
  close_fd(&stderr_pipe[0]);
  close_fd(&stderr_pipe[1]);
  close_fd(&status_pipe[0]);
  close_fd(&status_pipe[1]);
  close_fd(&go_pipe[0]);
  close_fd(&go_pipe[1]);
  close_fd(&ctrl_sock[0]);
  close_fd(&ctrl_sock[1]);
  if (listener_fds != NULL) {
    for (uint32_t i = 0; i < n_fwds; i++) {
      close_fd(&listener_fds[i]);
    }
    free(listener_fds);
  }
  if (child_pid > 0) {
    (void)kill(-child_pid, SIGKILL);
    if (pidfd >= 0) {
      (void)syscall(__NR_pidfd_send_signal, pidfd, SIGKILL, NULL, 0);
    }
    if (cg_dir[0] != '\0') {
      char kpath[PATH_MAX];
      if (cgroup_subfile(cg_dir, "cgroup.kill", kpath, sizeof(kpath)) == 0) {
        (void)write_text_file(kpath, "1");
      }
    }
    int st = 0;
    while (waitpid(child_pid, &st, 0) < 0 && errno == EINTR) {
    }
  }
  close_fd(&pidfd);
  if (cg_dir[0] != '\0') {
    (void)cleanup_cgroup_dir(cg_dir);
  }
  free(bwrap_path);
  free(bwrap_argv);
  free(program);
  free(cwd);
  if (sys != NULL) {
    for (uint32_t i = 0; i < n_sys; i++) {
      free(sys[i].path);
      free(sys[i].target);
    }
    free(sys);
  }
  if (etc_paths != NULL) {
    for (uint32_t i = 0; i < n_etc; i++) free(etc_paths[i]);
    free(etc_paths);
  }
  if (masks != NULL) {
    for (uint32_t i = 0; i < n_masks; i++) free(masks[i]);
    free(masks);
  }
  if (mounts != NULL) {
    for (uint32_t i = 0; i < n_mounts; i++) {
      free(mounts[i].host_path);
      free(mounts[i].box_path);
    }
    free(mounts);
  }
  return lean_io_result_mk_ok(mk_spawn_tuple(err_tag, err_code, err_path, err_msg, 0, 0, 0, 0));
}

static size_t ring_write_from_fd(RingBuf *rb, int fd, uint8_t *eof_out, uint8_t *err_out) {
  size_t avail = PS_RING_CAP - rb->len;
  if (avail == 0) {
    return 0;
  }
  size_t total = 0;
  while (avail > 0) {
    size_t tail = (rb->head + rb->len) % PS_RING_CAP;
    size_t contig = PS_RING_CAP - tail;
    if (contig > avail) {
      contig = avail;
    }
    ssize_t n = recv(fd, rb->data + tail, contig, 0);
    if (n > 0) {
      rb->len += (size_t)n;
      avail -= (size_t)n;
      total += (size_t)n;
    } else if (n == 0) {
      *eof_out = 1;
      break;
    } else {
      if (errno == EINTR) {
        continue;
      }
      if (errno == EAGAIN || errno == EWOULDBLOCK) {
        break;
      }
      *err_out = 1;
      break;
    }
  }
  return total;
}

static size_t ring_flush_to_fd(RingBuf *rb, int fd, uint8_t *err_out) {
  size_t total = 0;
  while (rb->len > 0) {
    size_t contig = PS_RING_CAP - rb->head;
    if (contig > rb->len) {
      contig = rb->len;
    }
    ssize_t n = send(fd, rb->data + rb->head, contig, MSG_NOSIGNAL);
    if (n > 0) {
      rb->head = (rb->head + (size_t)n) % PS_RING_CAP;
      rb->len -= (size_t)n;
      total += (size_t)n;
    } else if (n < 0 && errno == EINTR) {
      continue;
    } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
      break;
    } else {
      *err_out = 1;
      break;
    }
  }
  return total;
}

static void *forwarder_thread_main(void *arg) {
  ForwarderSlot *f = (ForwarderSlot *)arg;
  RelayConn relays[PS_MAX_RELAY_SLOTS];
  memset(relays, 0, sizeof(relays));
  for (int i = 0; i < PS_MAX_RELAY_SLOTS; i++) {
    relays[i].box_fd = -1;
    relays[i].host_fd = -1;
  }
  size_t active_slots = 0;

  nfds_t max_pfds = 1 + (nfds_t)f->n_listeners + 2 * PS_MAX_RELAY_SLOTS;
  struct pollfd *pfds = (struct pollfd *)calloc(max_pfds, sizeof(struct pollfd));
  int *pfd_kind = (int *)calloc(max_pfds, sizeof(int));
  size_t *pfd_idx = (size_t *)calloc(max_pfds, sizeof(size_t));

  if (pfds == NULL || pfd_kind == NULL || pfd_idx == NULL) {
    free(pfds);
    free(pfd_kind);
    free(pfd_idx);
    return NULL;
  }

  for (;;) {
    nfds_t npfds = 0;
    pfds[npfds].fd = f->wake_read_fd;
    pfds[npfds].events = POLLIN;
    pfds[npfds].revents = 0;
    pfd_kind[npfds] = 0;
    pfd_idx[npfds] = 0;
    npfds++;

    for (uint32_t i = 0; i < f->n_listeners; i++) {
      pfds[npfds].fd = (active_slots < PS_MAX_RELAY_SLOTS) ? f->listener_fds[i] : -1;
      pfds[npfds].events = (active_slots < PS_MAX_RELAY_SLOTS) ? POLLIN : 0;
      pfds[npfds].revents = 0;
      pfd_kind[npfds] = 1;
      pfd_idx[npfds] = (size_t)i;
      npfds++;
    }

    int slot_b_pfd[PS_MAX_RELAY_SLOTS];
    int slot_h_pfd[PS_MAX_RELAY_SLOTS];
    for (int i = 0; i < PS_MAX_RELAY_SLOTS; i++) {
      slot_b_pfd[i] = -1;
      slot_h_pfd[i] = -1;
      if (!relays[i].in_use) {
        continue;
      }
      short bev = 0;
      if (!relays[i].box_eof_in && relays[i].b2h.len < PS_RING_CAP) {
        bev |= POLLIN;
      }
      if (relays[i].h2b.len > 0) {
        bev |= POLLOUT;
      }
      slot_b_pfd[i] = (int)npfds;
      pfds[npfds].fd = (bev != 0) ? relays[i].box_fd : -1;
      pfds[npfds].events = bev;
      pfds[npfds].revents = 0;
      pfd_kind[npfds] = 2;
      pfd_idx[npfds] = (size_t)i;
      npfds++;

      short hev = 0;
      if (relays[i].host_connecting) {
        hev |= POLLOUT;
      } else {
        if (!relays[i].host_eof_in && relays[i].h2b.len < PS_RING_CAP) {
          hev |= POLLIN;
        }
        if (relays[i].b2h.len > 0) {
          hev |= POLLOUT;
        }
      }
      slot_h_pfd[i] = (int)npfds;
      pfds[npfds].fd = (hev != 0) ? relays[i].host_fd : -1;
      pfds[npfds].events = hev;
      pfds[npfds].revents = 0;
      pfd_kind[npfds] = 3;
      pfd_idx[npfds] = (size_t)i;
      npfds++;
    }

    int prc = poll(pfds, npfds, -1);
    if (prc < 0) {
      if (errno == EINTR) {
        continue;
      }
      break;
    }

    if (pfds[0].revents & (POLLIN | POLLHUP | POLLERR)) {
      break;
    }

    for (nfds_t k = 1; k < npfds; k++) {
      if (pfd_kind[k] != 1 || !(pfds[k].revents & POLLIN)) {
        continue;
      }
      uint32_t li = (uint32_t)pfd_idx[k];
      int lfd = f->listener_fds[li];
      uint16_t hport = f->host_ports[li];
      while (active_slots < PS_MAX_RELAY_SLOTS) {
        int bfd = accept4(lfd, NULL, NULL, SOCK_NONBLOCK | SOCK_CLOEXEC);
        if (bfd < 0) {
          if (errno == EINTR) {
            continue;
          }
          break;
        }
        int hfd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
        if (hfd < 0) {
          close(bfd);
          continue;
        }
        struct sockaddr_in hsa;
        memset(&hsa, 0, sizeof(hsa));
        hsa.sin_family = AF_INET;
        hsa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
        hsa.sin_port = htons(hport);
        int crc = connect(hfd, (struct sockaddr *)&hsa, sizeof(hsa));
        uint8_t connecting = 0;
        if (crc != 0) {
          if (errno == EINPROGRESS) {
            connecting = 1;
          } else {
            close(hfd);
            close(bfd);
            continue;
          }
        }
        int free_idx = -1;
        for (int s = 0; s < PS_MAX_RELAY_SLOTS; s++) {
          if (!relays[s].in_use) {
            free_idx = s;
            break;
          }
        }
        if (free_idx < 0) {
          close(hfd);
          close(bfd);
          break;
        }
        memset(&relays[free_idx], 0, sizeof(relays[free_idx]));
        relays[free_idx].in_use = 1;
        relays[free_idx].box_fd = bfd;
        relays[free_idx].host_fd = hfd;
        relays[free_idx].host_port = hport;
        relays[free_idx].host_connecting = connecting;
        active_slots++;
      }
    }

    for (int i = 0; i < PS_MAX_RELAY_SLOTS; i++) {
      if (!relays[i].in_use) {
        continue;
      }
      int bp = slot_b_pfd[i];
      int hp = slot_h_pfd[i];
      if (bp < 0 || hp < 0) {
        continue;
      }
      short brev = pfds[bp].revents;
      short hrev = pfds[hp].revents;
      uint8_t slot_failed = 0;

      if ((brev & POLLNVAL) || (hrev & POLLNVAL)) {
        slot_failed = 1;
      }

      if (!slot_failed && relays[i].host_connecting && (hrev & (POLLOUT | POLLERR | POLLHUP))) {
        int so_err = 0;
        socklen_t slen = sizeof(so_err);
        if (getsockopt(relays[i].host_fd, SOL_SOCKET, SO_ERROR, &so_err, &slen) != 0 || so_err != 0) {
          slot_failed = 1;
        } else {
          relays[i].host_connecting = 0;
        }
      }

      if (!slot_failed && !relays[i].box_eof_in && (brev & (POLLIN | POLLHUP | POLLERR))) {
        (void)ring_write_from_fd(
            &relays[i].b2h, relays[i].box_fd, &relays[i].box_eof_in, &slot_failed);
      }

      if (!slot_failed && !relays[i].host_connecting && !relays[i].host_eof_in &&
          (hrev & (POLLIN | POLLHUP | POLLERR))) {
        (void)ring_write_from_fd(
            &relays[i].h2b, relays[i].host_fd, &relays[i].host_eof_in, &slot_failed);
      }

      if (!slot_failed && !relays[i].host_connecting) {
        if (relays[i].b2h.len > 0) {
          (void)ring_flush_to_fd(&relays[i].b2h, relays[i].host_fd, &slot_failed);
        }
        if (!slot_failed && relays[i].box_eof_in && relays[i].b2h.len == 0 && !relays[i].host_shutdown_wr) {
          (void)shutdown(relays[i].host_fd, SHUT_WR);
          relays[i].host_shutdown_wr = 1;
        }
      }

      if (!slot_failed) {
        if (relays[i].h2b.len > 0) {
          (void)ring_flush_to_fd(&relays[i].h2b, relays[i].box_fd, &slot_failed);
        }
        if (!slot_failed && relays[i].host_eof_in && relays[i].h2b.len == 0 && !relays[i].box_shutdown_wr) {
          (void)shutdown(relays[i].box_fd, SHUT_WR);
          relays[i].box_shutdown_wr = 1;
        }
      }

      if (slot_failed ||
          (relays[i].box_eof_in && relays[i].b2h.len == 0 &&
           relays[i].host_eof_in && relays[i].h2b.len == 0)) {
        close_fd(&relays[i].box_fd);
        close_fd(&relays[i].host_fd);
        relays[i].in_use = 0;
        if (active_slots > 0) {
          active_slots--;
        }
      }
    }
  }

  for (int i = 0; i < PS_MAX_RELAY_SLOTS; i++) {
    if (relays[i].in_use) {
      close_fd(&relays[i].box_fd);
      close_fd(&relays[i].host_fd);
    }
  }
  free(pfds);
  free(pfd_kind);
  free(pfd_idx);
  return NULL;
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_start_forwarders(
    uint64_t box_hid,
    b_lean_obj_arg box_ports_obj,
    b_lean_obj_arg host_ports_obj,
    lean_obj_arg w) {
  (void)w;
  size_t n_ports = lean_array_size(box_ports_obj);
  if (n_ports != lean_array_size(host_ports_obj)) {
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_INVALID_INPUT, EINVAL, "", "mismatched port forward arrays", 0));
  }

  pthread_mutex_lock(&g_mu);
  BoxSlot *bslot = find_box_locked(box_hid);
  if (bslot == NULL) {
    pthread_mutex_unlock(&g_mu);
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_INVALID_INPUT, EINVAL, "", "invalid box handle", 0));
  }
  if (bslot->fwds_taken || bslot->n_listeners != n_ports) {
    pthread_mutex_unlock(&g_mu);
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_INVALID_INPUT, EINVAL, "", "forwarders already started or port count mismatch", 0));
  }

  int *lfds = bslot->listener_fds;
  uint32_t n_lfds = bslot->n_listeners;
  bslot->listener_fds = NULL;
  bslot->n_listeners = 0;
  bslot->fwds_taken = 1;
  pthread_mutex_unlock(&g_mu);

  ForwarderSlot *fslot = (ForwarderSlot *)calloc(1, sizeof(ForwarderSlot));
  if (fslot == NULL) {
    for (uint32_t i = 0; i < n_lfds; i++) close(lfds[i]);
    free(lfds);
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_IO_ERROR, ENOMEM, "", "out of memory", 0));
  }
  fslot->box_handle_id = box_hid;
  fslot->n_listeners = n_lfds;
  fslot->listener_fds = lfds;
  fslot->wake_read_fd = -1;
  fslot->wake_write_fd = -1;

  if (n_lfds > 0) {
    fslot->host_ports = (uint16_t *)calloc((size_t)n_lfds, sizeof(uint16_t));
    if (fslot->host_ports == NULL) {
      for (uint32_t i = 0; i < n_lfds; i++) close(lfds[i]);
      free(lfds);
      free(fslot);
      return lean_io_result_mk_ok(
          mk_err_tuple5_u64(PS_TAG_IO_ERROR, ENOMEM, "", "out of memory", 0));
    }
    for (uint32_t i = 0; i < n_lfds; i++) {
      uint16_t hp = lean_unbox(lean_array_get_core(host_ports_obj, i));
      fslot->host_ports[i] = hp;
    }
  }

  int wpipe[2] = {-1, -1};
  if (pipe2(wpipe, O_NONBLOCK | O_CLOEXEC) != 0) {
    int err = errno;
    for (uint32_t i = 0; i < n_lfds; i++) close(lfds[i]);
    free(lfds);
    free(fslot->host_ports);
    free(fslot);
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_IO_ERROR, (uint32_t)err, "", "pipe2 failed", 0));
  }
  fslot->wake_read_fd = wpipe[0];
  fslot->wake_write_fd = wpipe[1];

  if (pthread_create(&fslot->thread, NULL, forwarder_thread_main, fslot) != 0) {
    int err = errno;
    close_fd(&fslot->wake_read_fd);
    close_fd(&fslot->wake_write_fd);
    for (uint32_t i = 0; i < n_lfds; i++) close(lfds[i]);
    free(lfds);
    free(fslot->host_ports);
    free(fslot);
    return lean_io_result_mk_ok(
        mk_err_tuple5_u64(PS_TAG_IO_ERROR, (uint32_t)err, "", "pthread_create failed", 0));
  }
  fslot->thread_started = 1;

  pthread_mutex_lock(&g_mu);
  uint64_t fhid = alloc_handle_id_locked();
  fslot->handle_id = fhid;
  fslot->next = g_fwds;
  g_fwds = fslot;
  g_active_fwds++;
  pthread_mutex_unlock(&g_mu);

  return lean_io_result_mk_ok(mk_err_tuple5_u64(PS_TAG_OK, 0, "", "", fhid));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_stop_forwarders(uint64_t fwd_hid, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_mu);
  ForwarderSlot *fslot = detach_fwd_locked(fwd_hid);
  pthread_mutex_unlock(&g_mu);

  if (fslot == NULL) {
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_INVALID_INPUT, EINVAL, "", "invalid or stopped forwarder handle"));
  }

  uint8_t b = 1;
  ssize_t wr = write(fslot->wake_write_fd, &b, 1);
  (void)wr;
  close_fd(&fslot->wake_write_fd);
  if (fslot->thread_started) {
    pthread_join(fslot->thread, NULL);
  }
  close_fd(&fslot->wake_read_fd);
  if (fslot->listener_fds != NULL) {
    for (uint32_t i = 0; i < fslot->n_listeners; i++) {
      close_fd(&fslot->listener_fds[i]);
    }
    free(fslot->listener_fds);
  }
  free(fslot->host_ports);
  free(fslot);
  return lean_io_result_mk_ok(mk_err_tuple4(PS_TAG_OK, 0, "", ""));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_read_output(
    uint64_t box_hid,
    b_lean_obj_arg stdin_obj,
    uint64_t timeout_ms,
    uint8_t has_limit,
    uint64_t max_output_bytes,
    lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_mu);
  BoxSlot *bslot = find_box_locked(box_hid);
  if (bslot == NULL || bslot->read_started) {
    pthread_mutex_unlock(&g_mu);
    return lean_io_result_mk_ok(
        mk_read_tuple(PS_TAG_INVALID_INPUT, EINVAL, "", "invalid box handle",
                      0, 0, lean_alloc_sarray(1, 0, 0), lean_alloc_sarray(1, 0, 0)));
  }
  bslot->read_started = 1;
  int in_fd = bslot->stdin_fd;
  int out_fd = bslot->stdout_fd;
  int err_fd = bslot->stderr_fd;
  int status_fd = bslot->status_fd;
  int go_fd = bslot->go_fd;
  bslot->stdin_fd = -1;
  bslot->stdout_fd = -1;
  bslot->stderr_fd = -1;
  bslot->status_fd = -1;
  bslot->go_fd = -1;
  char *prog = bslot->program != NULL ? strdup(bslot->program) : strdup("");
  char *cwd = bslot->cwd != NULL ? strdup(bslot->cwd) : strdup("");
  pthread_mutex_unlock(&g_mu);

  uint8_t go_b = 'G';
  if (go_fd >= 0) {
    (void)write_all_fd(go_fd, &go_b, 1);
    close_fd(&go_fd);
  }

  const uint8_t *stdin_data = lean_sarray_cptr((lean_object *)stdin_obj);
  size_t stdin_len = lean_sarray_size(stdin_obj);
  size_t stdin_pos = 0;

  if (stdin_len == 0) {
    close_fd(&in_fd);
  } else if (in_fd >= 0) {
    (void)set_nonblock_fd(in_fd);
  }
  if (out_fd >= 0) (void)set_nonblock_fd(out_fd);
  if (err_fd >= 0) (void)set_nonblock_fd(err_fd);

  sigset_t pipe_set, old_set;
  sigemptyset(&pipe_set);
  sigaddset(&pipe_set, SIGPIPE);
  int masked_sigpipe = (pthread_sigmask(SIG_BLOCK, &pipe_set, &old_set) == 0);
  int was_blocked = masked_sigpipe && sigismember(&old_set, SIGPIPE);

  uint64_t start_ms = mono_now_ms();
  uint8_t *out_buf = NULL;
  size_t out_len = 0, out_cap = 0;
  uint8_t *err_buf = NULL;
  size_t err_len = 0, err_cap = 0;

  int timed_out = 0;
  int limit_exceeded = 0;
  int io_err = 0;
  int exec_err = 0;
  uint8_t exec_is_cwd = 0;
  uint8_t got_status = 0;
  uint8_t outcome_tag = 1;
  uint32_t exit_or_sig = 9;

  InitStatusMsg smsg;
  memset(&smsg, 0, sizeof(smsg));
  size_t sgot = 0;
  uint8_t tmp[8192];

  while (out_fd >= 0 || err_fd >= 0 || status_fd >= 0) {
    struct pollfd pfds[4];
    nfds_t npfds = 0;
    int idx_in = -1, idx_out = -1, idx_err = -1, idx_st = -1;

    if (in_fd >= 0) {
      idx_in = (int)npfds;
      pfds[npfds].fd = in_fd;
      pfds[npfds].events = POLLOUT;
      pfds[npfds].revents = 0;
      npfds++;
    }
    if (out_fd >= 0) {
      idx_out = (int)npfds;
      pfds[npfds].fd = out_fd;
      pfds[npfds].events = POLLIN;
      pfds[npfds].revents = 0;
      npfds++;
    }
    if (err_fd >= 0) {
      idx_err = (int)npfds;
      pfds[npfds].fd = err_fd;
      pfds[npfds].events = POLLIN;
      pfds[npfds].revents = 0;
      npfds++;
    }
    if (status_fd >= 0) {
      idx_st = (int)npfds;
      pfds[npfds].fd = status_fd;
      pfds[npfds].events = POLLIN;
      pfds[npfds].revents = 0;
      npfds++;
    }

    uint64_t now = mono_now_ms();
    uint64_t elapsed = (now >= start_ms) ? (now - start_ms) : 0;
    if (elapsed >= timeout_ms) {
      timed_out = 1;
      break;
    }
    uint64_t rem = timeout_ms - elapsed;
    int poll_to = (rem > (uint64_t)INT32_MAX) ? INT32_MAX : (int)rem;

    int prc = poll(pfds, npfds, poll_to);
    if (prc < 0) {
      if (errno == EINTR) {
        continue;
      }
      io_err = errno;
      break;
    }
    if (prc == 0) {
      timed_out = 1;
      break;
    }

    if (idx_in >= 0) {
      short rev = pfds[idx_in].revents;
      if (rev & (POLLERR | POLLHUP | POLLNVAL)) {
        close_fd(&in_fd);
      } else if (rev & POLLOUT) {
        while (stdin_pos < stdin_len) {
          if ((mono_now_ms() - start_ms) >= timeout_ms) {
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
            close_fd(&in_fd);
            break;
          }
        }
        if (timed_out) {
          break;
        }
        if (stdin_pos >= stdin_len) {
          close_fd(&in_fd);
        }
      }
    }

    if (idx_out >= 0 && (pfds[idx_out].revents & (POLLIN | POLLHUP | POLLERR))) {
      size_t iter = 0;
      for (;;) {
        if ((mono_now_ms() - start_ms) >= timeout_ms) {
          timed_out = 1;
          break;
        }
        ssize_t n = read(out_fd, tmp, sizeof(tmp));
        if (n > 0) {
          iter += (size_t)n;
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
          if (iter >= 65536) {
            break;
          }
        } else if (n == 0) {
          close_fd(&out_fd);
          break;
        } else {
          if (errno == EINTR) continue;
          if (errno == EAGAIN || errno == EWOULDBLOCK) break;
          io_err = errno;
          close_fd(&out_fd);
          break;
        }
      }
      if (timed_out || limit_exceeded || io_err != 0) {
        break;
      }
    }

    if (idx_err >= 0 && (pfds[idx_err].revents & (POLLIN | POLLHUP | POLLERR))) {
      size_t iter = 0;
      for (;;) {
        if ((mono_now_ms() - start_ms) >= timeout_ms) {
          timed_out = 1;
          break;
        }
        ssize_t n = read(err_fd, tmp, sizeof(tmp));
        if (n > 0) {
          iter += (size_t)n;
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
          if (iter >= 65536) {
            break;
          }
        } else if (n == 0) {
          close_fd(&err_fd);
          break;
        } else {
          if (errno == EINTR) continue;
          if (errno == EAGAIN || errno == EWOULDBLOCK) break;
          io_err = errno;
          close_fd(&err_fd);
          break;
        }
      }
      if (timed_out || limit_exceeded || io_err != 0) {
        break;
      }
    }

    if (idx_st >= 0 && (pfds[idx_st].revents & (POLLIN | POLLHUP | POLLERR))) {
      uint8_t *sp = (uint8_t *)&smsg;
      for (;;) {
        if (sgot >= sizeof(smsg)) {
          break;
        }
        ssize_t n = read(status_fd, sp + sgot, sizeof(smsg) - sgot);
        if (n > 0) {
          sgot += (size_t)n;
          if (sgot == sizeof(smsg)) {
            got_status = 1;
            close_fd(&status_fd);
            break;
          }
        } else if (n == 0) {
          close_fd(&status_fd);
          break;
        } else {
          if (errno == EINTR) continue;
          if (errno == EAGAIN || errno == EWOULDBLOCK) break;
          close_fd(&status_fd);
          break;
        }
      }
      if (got_status && smsg.kind == PS_STATUS_EXEC_ERR) {
        exec_err = smsg.value ? smsg.value : EIO;
        exec_is_cwd = smsg.flag;
        break;
      }
      if (got_status && smsg.kind == PS_STATUS_INIT_ERR) {
        break;
      }
    }
  }

  close_fd(&in_fd);
  close_fd(&out_fd);
  close_fd(&err_fd);
  close_fd(&status_fd);

  if (masked_sigpipe) {
    if (!was_blocked) {
      sigset_t pending;
      sigemptyset(&pending);
      if (sigpending(&pending) == 0 && sigismember(&pending, SIGPIPE)) {
        int sig = 0;
        sigwait(&pipe_set, &sig);
      }
    }
    pthread_sigmask(SIG_SETMASK, &old_set, NULL);
  }

  if (exec_err != 0) {
    free(out_buf);
    free(err_buf);
    uint8_t etag = map_errno_to_path_tag(exec_err);
    const char *epath = exec_is_cwd ? cwd : prog;
    char emsg[256];
    snprintf(emsg, sizeof(emsg), "%s: %s", exec_is_cwd ? "chdir" : "execvp", strerror(exec_err));
    lean_obj_res res = mk_read_tuple(
        etag, (uint32_t)exec_err, epath, emsg, 0, 0,
        lean_alloc_sarray(1, 0, 0), lean_alloc_sarray(1, 0, 0));
    free(prog);
    free(cwd);
    return lean_io_result_mk_ok(res);
  }

  free(prog);
  free(cwd);

  if (!timed_out && !limit_exceeded && got_status && smsg.kind == PS_STATUS_INIT_ERR) {
    int init_err = smsg.value ? smsg.value : EPERM;
    char imsg[256];
    snprintf(imsg, sizeof(imsg), "sandbox init failed before execvp: %s", strerror(init_err));
    free(out_buf);
    free(err_buf);
    return lean_io_result_mk_ok(
        mk_read_tuple(PS_TAG_UNAVAILABLE, (uint32_t)init_err, "", imsg,
                      0, 0, lean_alloc_sarray(1, 0, 0), lean_alloc_sarray(1, 0, 0)));
  }

  if (io_err != 0) {
    free(out_buf);
    free(err_buf);
    return lean_io_result_mk_ok(
        mk_read_tuple(PS_TAG_IO_ERROR, (uint32_t)io_err, "", strerror(io_err),
                      0, 0, lean_alloc_sarray(1, 0, 0), lean_alloc_sarray(1, 0, 0)));
  }

  if (timed_out) {
    outcome_tag = 2;
    exit_or_sig = 0;
  } else if (limit_exceeded) {
    outcome_tag = 3;
    exit_or_sig = 0;
  } else if (got_status) {
    if (smsg.kind == PS_STATUS_EXITED) {
      outcome_tag = 0;
      exit_or_sig = (uint32_t)smsg.value;
    } else if (smsg.kind == PS_STATUS_SIGNALED) {
      outcome_tag = 1;
      exit_or_sig = (uint32_t)smsg.value;
    } else {
      outcome_tag = 1;
      exit_or_sig = 9;
    }
  } else {
    outcome_tag = 1;
    exit_or_sig = 9;
  }

  lean_obj_res out_ba = lean_alloc_sarray(1, out_len, out_len);
  if (out_len > 0 && out_buf != NULL) {
    memcpy(lean_sarray_cptr(out_ba), out_buf, out_len);
  }
  lean_obj_res err_ba = lean_alloc_sarray(1, err_len, err_len);
  if (err_len > 0 && err_buf != NULL) {
    memcpy(lean_sarray_cptr(err_ba), err_buf, err_len);
  }
  free(out_buf);
  free(err_buf);

  return lean_io_result_mk_ok(
      mk_read_tuple(PS_TAG_OK, 0, "", "", outcome_tag, exit_or_sig, out_ba, err_ba));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_kill_pg(uint64_t box_hid, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_mu);
  BoxSlot *bslot = find_box_locked(box_hid);
  pid_t pgid = (bslot != NULL) ? bslot->pgid : -1;
  pthread_mutex_unlock(&g_mu);

  if (bslot == NULL) {
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_INVALID_INPUT, EINVAL, "", "invalid box handle"));
  }
  if (pgid > 0 && kill(-pgid, SIGKILL) != 0 && errno != ESRCH) {
    int err = errno;
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_IO_ERROR, (uint32_t)err, "", strerror(err)));
  }
  return lean_io_result_mk_ok(mk_err_tuple4(PS_TAG_OK, 0, "", ""));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_pidfd_kill(uint64_t box_hid, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_mu);
  BoxSlot *bslot = find_box_locked(box_hid);
  int pidfd = (bslot != NULL) ? bslot->pidfd : -1;
  pthread_mutex_unlock(&g_mu);

  if (bslot == NULL) {
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_INVALID_INPUT, EINVAL, "", "invalid box handle"));
  }
  if (pidfd >= 0) {
    if (syscall(__NR_pidfd_send_signal, pidfd, SIGKILL, NULL, 0) != 0 && errno != ESRCH) {
      int err = errno;
      return lean_io_result_mk_ok(
          mk_err_tuple4(PS_TAG_IO_ERROR, (uint32_t)err, "", strerror(err)));
    }
  }
  return lean_io_result_mk_ok(mk_err_tuple4(PS_TAG_OK, 0, "", ""));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_reap_box(uint64_t box_hid, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_mu);
  BoxSlot *bslot = detach_box_locked(box_hid);
  pthread_mutex_unlock(&g_mu);

  if (bslot == NULL) {
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_INVALID_INPUT, EINVAL, "", "invalid or reaped box handle"));
  }

  close_fd(&bslot->stdin_fd);
  close_fd(&bslot->stdout_fd);
  close_fd(&bslot->stderr_fd);
  close_fd(&bslot->status_fd);
  close_fd(&bslot->go_fd);
  if (bslot->listener_fds != NULL) {
    for (uint32_t i = 0; i < bslot->n_listeners; i++) {
      close_fd(&bslot->listener_fds[i]);
    }
    free(bslot->listener_fds);
  }

  if (bslot->cgroup_dir != NULL) {
    char kpath[PATH_MAX];
    if (cgroup_subfile(bslot->cgroup_dir, "cgroup.kill", kpath, sizeof(kpath)) == 0) {
      (void)write_text_file(kpath, "1");
    }
  }

  if (bslot->pid > 0) {
    int st = 0;
    while (waitpid(bslot->pid, &st, 0) < 0) {
      if (errno == EINTR) {
        continue;
      }
      break;
    }
  }
  close_fd(&bslot->pidfd);

  int cg_rc = cleanup_cgroup_dir(bslot->cgroup_dir);
  int cg_err = errno;
  free(bslot->cgroup_dir);
  free(bslot->program);
  free(bslot->cwd);
  free(bslot);

  if (cg_rc != 0) {
    return lean_io_result_mk_ok(
        mk_err_tuple4(PS_TAG_IO_ERROR, (uint32_t)cg_err, "", "failed to remove box cgroup directory"));
  }
  return lean_io_result_mk_ok(mk_err_tuple4(PS_TAG_OK, 0, "", ""));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_active_counts(lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_mu);
  size_t np = g_open_plans;
  size_t nb = g_active_boxes;
  size_t nf = g_active_fwds;
  pthread_mutex_unlock(&g_mu);

  lean_obj_res p2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p2, 0, lean_usize_to_nat(nb));
  lean_ctor_set(p2, 1, lean_usize_to_nat(nf));
  lean_obj_res p1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p1, 0, lean_usize_to_nat(np));
  lean_ctor_set(p1, 1, p2);
  return lean_io_result_mk_ok(p1);
}

#else

LEAN_EXPORT lean_obj_res leanswe_psandbox_preflight(
    uint8_t need_mem, uint8_t need_pids, lean_obj_arg w) {
  (void)need_mem;
  (void)need_pids;
  (void)w;
  return lean_io_result_mk_ok(
      mk_err_tuple4(1, ENOTSUP, "", "ProcessSandbox requires Linux"));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_discover_preset(lean_obj_arg w) {
  (void)w;
  lean_obj_res d2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(d2, 0, lean_mk_empty_array());
  lean_ctor_set(d2, 1, lean_mk_empty_array());
  lean_obj_res d1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(d1, 0, lean_mk_empty_array());
  lean_ctor_set(d1, 1, d2);
  lean_obj_res t3 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t3, 0, lean_mk_string("ProcessSandbox requires Linux"));
  lean_ctor_set(t3, 1, d1);
  lean_obj_res t2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t2, 0, lean_box_uint32(ENOTSUP));
  lean_ctor_set(t2, 1, t3);
  lean_obj_res t1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(t1, 0, lean_box(1));
  lean_ctor_set(t1, 1, t2);
  return lean_io_result_mk_ok(t1);
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_seal_plan(
    b_lean_obj_arg plan_bytes_obj, lean_obj_arg w) {
  (void)plan_bytes_obj;
  (void)w;
  return lean_io_result_mk_ok(
      mk_err_tuple5_u64(1, ENOTSUP, "", "ProcessSandbox requires Linux", 0));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_close_plan(uint64_t plan_hid, lean_obj_arg w) {
  (void)plan_hid;
  (void)w;
  return lean_io_result_mk_ok(
      mk_err_tuple4(4, EINVAL, "", "invalid plan handle"));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_spawn_box(uint64_t plan_hid, lean_obj_arg w) {
  (void)plan_hid;
  (void)w;
  return lean_io_result_mk_ok(
      mk_spawn_tuple(1, ENOTSUP, "", "ProcessSandbox requires Linux", 0, 0, 0, 0));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_start_forwarders(
    uint64_t box_hid,
    b_lean_obj_arg box_ports_obj,
    b_lean_obj_arg host_ports_obj,
    lean_obj_arg w) {
  (void)box_hid;
  (void)box_ports_obj;
  (void)host_ports_obj;
  (void)w;
  return lean_io_result_mk_ok(
      mk_err_tuple5_u64(1, ENOTSUP, "", "ProcessSandbox requires Linux", 0));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_stop_forwarders(uint64_t fwd_hid, lean_obj_arg w) {
  (void)fwd_hid;
  (void)w;
  return lean_io_result_mk_ok(
      mk_err_tuple4(4, EINVAL, "", "invalid forwarder handle"));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_read_output(
    uint64_t box_hid,
    b_lean_obj_arg stdin_obj,
    uint64_t timeout_ms,
    uint8_t has_limit,
    uint64_t max_output_bytes,
    lean_obj_arg w) {
  (void)box_hid;
  (void)stdin_obj;
  (void)timeout_ms;
  (void)has_limit;
  (void)max_output_bytes;
  (void)w;
  return lean_io_result_mk_ok(
      mk_read_tuple(1, ENOTSUP, "", "ProcessSandbox requires Linux",
                    0, 0, lean_alloc_sarray(1, 0, 0), lean_alloc_sarray(1, 0, 0)));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_kill_pg(uint64_t box_hid, lean_obj_arg w) {
  (void)box_hid;
  (void)w;
  return lean_io_result_mk_ok(
      mk_err_tuple4(4, EINVAL, "", "invalid box handle"));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_pidfd_kill(uint64_t box_hid, lean_obj_arg w) {
  (void)box_hid;
  (void)w;
  return lean_io_result_mk_ok(
      mk_err_tuple4(4, EINVAL, "", "invalid box handle"));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_reap_box(uint64_t box_hid, lean_obj_arg w) {
  (void)box_hid;
  (void)w;
  return lean_io_result_mk_ok(
      mk_err_tuple4(4, EINVAL, "", "invalid box handle"));
}

LEAN_EXPORT lean_obj_res leanswe_psandbox_active_counts(lean_obj_arg w) {
  (void)w;
  lean_obj_res p2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p2, 0, lean_usize_to_nat(0));
  lean_ctor_set(p2, 1, lean_usize_to_nat(0));
  lean_obj_res p1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p1, 0, lean_usize_to_nat(0));
  lean_ctor_set(p1, 1, p2);
  return lean_io_result_mk_ok(p1);
}

#endif
