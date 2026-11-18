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
#include <sys/resource.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>
#include "fd_box.h"

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
  int ready_wfd = (int)(intptr_t)arg;
  struct sock_filter allow = { 0x0006, 0, 0, 0x7FFF0000U };
  struct sock_fprog prog = { 1, &allow };
  (void)syscall(SYS_prctl, 38UL, 1UL, 0UL, 0UL, 0UL);
  (void)syscall(SYS_seccomp, 1U, 0U, &prog);
  uint32_t tid = (uint32_t)syscall(SYS_gettid);
  ssize_t wn = write(ready_wfd, &tid, sizeof(tid));
  (void)wn;
  close(ready_wfd);
  char ch = 0;
  ssize_t rn = read(g_sbx_sync_stop_rfd, &ch, 1);
  (void)rn;
  return NULL;
}

LEAN_EXPORT lean_obj_res leanswe_sbx_pipe(lean_obj_arg w) {
  (void)w;
  int fds[2] = { -1, -1 };
  if (pipe2(fds, O_CLOEXEC) < 0) {
    return leanswe_mk_errno(errno);
  }
  uint64_t packed = ((uint64_t)(uint32_t)fds[0]) | (((uint64_t)(uint32_t)fds[1]) << 32);
  return leanswe_mk_ok(lean_box_uint64(packed));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_fork(lean_obj_arg w) {
  (void)w;
  fflush(NULL);
  pid_t pid = fork();
  if (pid < 0) {
    return leanswe_mk_errno(errno);
  }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)pid));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_waitpid(uint32_t pid, lean_obj_arg w) {
  (void)w;
  int status = 0;
  pid_t rc = waitpid((pid_t)pid, &status, 0);
  if (rc < 0) {
    return leanswe_mk_errno(errno);
  }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)status));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_exit(uint32_t code, lean_obj_arg w) {
  (void)w;
  _exit((int)code);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_write_bytes(
    uint32_t fd, b_lean_obj_arg ba, lean_obj_arg w) {
  (void)w;
  ssize_t n = write((int)fd, lean_sarray_cptr(ba), lean_sarray_size(ba));
  if (n < 0) {
    return leanswe_mk_errno(errno);
  }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)n));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_read_bytes(
    uint32_t fd, uint32_t max_bytes, lean_obj_arg w) {
  (void)w;
  size_t cap = (size_t)max_bytes;
  if (cap > 65536u) {
    cap = 65536u;
  }
  lean_obj_res arr = lean_alloc_sarray(1, 0, cap);
  if (arr == NULL) {
    return leanswe_mk_errno(ENOMEM);
  }
  ssize_t n = read((int)fd, lean_sarray_cptr(arr), cap);
  if (n < 0) {
    lean_dec(arr);
    return leanswe_mk_errno(errno);
  }
  lean_sarray_set_size(arr, (size_t)n);
  return leanswe_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res leanswe_sbx_close_raw(uint32_t fd, lean_obj_arg w) {
  (void)w;
  close((int)fd);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_open_host_fd(
    b_lean_obj_arg path_ba, uint32_t kind, lean_obj_arg w) {
  (void)w;
  static const int k_open_flags[5] = {
    O_RDONLY | O_DIRECTORY | O_CLOEXEC,
    O_PATH | O_DIRECTORY | O_CLOEXEC,
    O_RDONLY | O_CLOEXEC,
    O_PATH | O_CLOEXEC,
    O_RDWR | O_CREAT | O_CLOEXEC
  };
  if (kind >= 5u) {
    return leanswe_mk_errno(EINVAL);
  }
  char sbuf[4096];
  const char *cpath = NULL;
  char *heap = NULL;
  int perr = sbx_env_ba_to_cstr(path_ba, sbuf, sizeof(sbuf), &cpath, &heap);
  if (perr != 0) {
    return leanswe_mk_errno(perr);
  }
  int fd = open(cpath, k_open_flags[kind], 0600);
  int saved = errno;
  if (heap != NULL) {
    free(heap);
  }
  if (fd < 0) {
    return leanswe_mk_errno(saved);
  }
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) {
    return leanswe_mk_errno(ENOMEM);
  }
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_sbx_open_pipe_fd(uint32_t as_o_path, lean_obj_arg w) {
  (void)w;
  int fds[2] = { -1, -1 };
  if (pipe2(fds, O_CLOEXEC) < 0) {
    return leanswe_mk_errno(errno);
  }
  close(fds[1]);
  int target = fds[0];
  if (as_o_path != 0u) {
    char pbuf[64];
    snprintf(pbuf, sizeof(pbuf), "/proc/self/fd/%d", fds[0]);
    target = open(pbuf, O_PATH | O_CLOEXEC);
    int saved = errno;
    close(fds[0]);
    if (target < 0) {
      return leanswe_mk_errno(saved);
    }
  }
  lean_obj_res obj = leanswe_mk_fd_obj(target);
  if (obj == NULL) {
    return leanswe_mk_errno(ENOMEM);
  }
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_sbx_close_fd(b_lean_obj_arg fd_obj, lean_obj_arg w) {
  (void)w;
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int err = leanswe_fd_box_close(box);
  if (err != 0) {
    return leanswe_mk_errno(err);
  }
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_enter_userns(lean_obj_arg w) {
  (void)w;
  if (unshare(CLONE_NEWUSER) < 0) {
    return leanswe_mk_errno(errno);
  }
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_get_rlimit(uint32_t tag, lean_obj_arg w) {
  (void)w;
  static const int k_rlimit_resources[3] = { RLIMIT_CORE, RLIMIT_FSIZE, RLIMIT_NOFILE };
  if (tag >= 3u) {
    return leanswe_mk_errno(EINVAL);
  }
  struct rlimit rl;
  if (getrlimit(k_rlimit_resources[tag], &rl) < 0) {
    return leanswe_mk_errno(errno);
  }
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_box_uint64((uint64_t)rl.rlim_cur));
  lean_ctor_set(p, 1, lean_box_uint64((uint64_t)rl.rlim_max));
  return leanswe_mk_ok(p);
}

LEAN_EXPORT lean_obj_res leanswe_sbx_get_tid(lean_obj_arg w) {
  (void)w;
  uint32_t tid = (uint32_t)syscall(SYS_gettid);
  return lean_io_result_mk_ok(lean_box_uint32(tid));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_geteuid(lean_obj_arg w) {
  (void)w;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)geteuid()));
}

static void sbx_close_pair(int fds[2]) {
  if (fds[0] >= 0) { close(fds[0]); }
  if (fds[1] >= 0) { close(fds[1]); }
}

LEAN_EXPORT lean_obj_res leanswe_sbx_spawn_sync_thread(lean_obj_arg w) {
  (void)w;
  if (g_sbx_sync_active != 0) { return leanswe_mk_errno(EBUSY); }
  int ready_fds[2] = { -1, -1 };
  int stop_fds[2] = { -1, -1 };
  if (pipe2(ready_fds, O_CLOEXEC) < 0) { return leanswe_mk_errno(errno); }
  if (pipe2(stop_fds, O_CLOEXEC) < 0) {
    int saved = errno;
    sbx_close_pair(ready_fds);
    return leanswe_mk_errno(saved);
  }
  g_sbx_sync_stop_rfd = stop_fds[0];
  g_sbx_sync_stop_wfd = stop_fds[1];
  int rc = pthread_create(
      &g_sbx_sync_tid, NULL, leanswe_sbx_sync_worker, (void *)(intptr_t)ready_fds[1]);
  if (rc != 0) {
    sbx_close_pair(ready_fds);
    sbx_close_pair(stop_fds);
    return leanswe_mk_errno(rc);
  }
  uint32_t tid = 0;
  ssize_t rn = read(ready_fds[0], &tid, sizeof(tid));
  close(ready_fds[0]);
  if (rn != (ssize_t)sizeof(tid)) {
    char ch = 1;
    ssize_t wn = write(g_sbx_sync_stop_wfd, &ch, 1);
    (void)wn;
    pthread_join(g_sbx_sync_tid, NULL);
    sbx_close_pair(stop_fds);
    return leanswe_mk_errno(EIO);
  }
  g_sbx_sync_active = 1;
  return leanswe_mk_ok(lean_box_uint32(tid));
}

LEAN_EXPORT lean_obj_res leanswe_sbx_stop_sync_thread(lean_obj_arg w) {
  (void)w;
  if (g_sbx_sync_active == 0) {
    return leanswe_mk_ok(lean_box(0));
  }
  char ch = 1;
  ssize_t wn = write(g_sbx_sync_stop_wfd, &ch, 1);
  (void)wn;
  pthread_join(g_sbx_sync_tid, NULL);
  close(g_sbx_sync_stop_wfd);
  close(g_sbx_sync_stop_rfd);
  g_sbx_sync_stop_wfd = -1;
  g_sbx_sync_stop_rfd = -1;
  g_sbx_sync_active = 0;
  return leanswe_mk_ok(lean_box(0));
}
