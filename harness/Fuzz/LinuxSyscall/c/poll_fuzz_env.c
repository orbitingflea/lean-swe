#define _GNU_SOURCE
#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe.LinuxSyscall.Poll requires Linux x86_64 or aarch64"
#endif

#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>
#include "fd_box.h"

#ifndef MFD_CLOEXEC
#define MFD_CLOEXEC 0x0001U
#endif

static lean_obj_res mk_fd_pair(int fd0, int fd1) {
  lean_obj_res o0 = leanswe_mk_fd_obj(fd0);
  if (o0 == NULL) {
    close(fd1);
    return leanswe_mk_errno(ENOMEM);
  }
  lean_obj_res o1 = leanswe_mk_fd_obj(fd1);
  if (o1 == NULL) {
    lean_dec_ref(o0);
    return leanswe_mk_errno(ENOMEM);
  }
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, o0);
  lean_ctor_set(p, 1, o1);
  return leanswe_mk_ok(p);
}

static int write_byte_nosigpipe(int fd, uint8_t b, ssize_t *n_out) {
  ssize_t n = send(fd, &b, 1, MSG_NOSIGNAL);
  if (n >= 0 || errno != ENOTSOCK) {
    *n_out = n;
    return (n < 0) ? errno : 0;
  }
  sigset_t pipe_set, prev_set;
  sigemptyset(&pipe_set);
  sigaddset(&pipe_set, SIGPIPE);
  sigset_t pend;
  sigpending(&pend);
  int was_pending = sigismember(&pend, SIGPIPE) == 1;
  pthread_sigmask(SIG_BLOCK, &pipe_set, &prev_set);
  n = write(fd, &b, 1);
  int err = (n < 0) ? errno : 0;
  if (!was_pending && n < 0 && err == EPIPE) {
    struct timespec z = {0, 0};
    sigtimedwait(&pipe_set, NULL, &z);
  }
  pthread_sigmask(SIG_SETMASK, &prev_set, NULL);
  *n_out = n;
  return err;
}

static int open_poll_test_fd(uint32_t kind) {
  if (kind == 0) return open("/dev/null", O_RDWR | O_CLOEXEC);
  if (kind == 1) return open("/dev/shm", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  if (kind == 2) return open("/dev/null", O_PATH | O_CLOEXEC);
  int fd = (int)syscall(SYS_memfd_create, "leanswe-poll-tmp", MFD_CLOEXEC);
  if (fd < 0 && errno == ENOSYS) {
    fd = open("/dev/shm", O_TMPFILE | O_RDWR | O_CLOEXEC, 0600);
  }
  return fd;
}

LEAN_EXPORT lean_obj_res leanswe_poll_close_fd(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int err = leanswe_fd_box_close(box);
  if (err != 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_poll_efd_write(b_lean_obj_arg fd_obj, uint64_t val) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  ssize_t n = write(fd, &val, sizeof(val));
  int err = (n < 0) ? errno : ((n != (ssize_t)sizeof(val)) ? EIO : 0);
  leanswe_fd_box_unpin(box);
  if (err != 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_poll_efd_read(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  uint64_t val = 0;
  ssize_t n = read(fd, &val, sizeof(val));
  int err = (n < 0) ? errno : ((n != (ssize_t)sizeof(val)) ? EIO : 0);
  leanswe_fd_box_unpin(box);
  if (err != 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box_uint64(val));
}

LEAN_EXPORT lean_obj_res leanswe_poll_open_pipe(void) {
  int fds[2] = {-1, -1};
  if (pipe2(fds, O_NONBLOCK | O_CLOEXEC) < 0) return leanswe_mk_errno(errno);
  return mk_fd_pair(fds[0], fds[1]);
}

LEAN_EXPORT lean_obj_res leanswe_poll_open_kind(uint32_t kind) {
  int fd = open_poll_test_fd(kind);
  if (fd < 0) return leanswe_mk_errno(errno);
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_poll_open_sockpair(void) {
  int fds[2] = {-1, -1};
  if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0, fds) < 0) {
    return leanswe_mk_errno(errno);
  }
  return mk_fd_pair(fds[0], fds[1]);
}

LEAN_EXPORT lean_obj_res leanswe_poll_pipe_write1(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  ssize_t n = 0;
  int err = write_byte_nosigpipe(fd, 0x5a, &n);
  leanswe_fd_box_unpin(box);
  if (err != 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box((uint8_t)n));
}

LEAN_EXPORT lean_obj_res leanswe_poll_pipe_read1(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  uint8_t b = 0;
  ssize_t n = read(fd, &b, 1);
  int err = (n < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (n < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box((uint8_t)n));
}

LEAN_EXPORT lean_obj_res leanswe_poll_rlimit_nofile(uint8_t do_set, uint64_t new_cur) {
  struct rlimit rl;
  if (getrlimit(RLIMIT_NOFILE, &rl) < 0) return leanswe_mk_errno(errno);
  if (do_set) {
    rlim_t target = (rlim_t)new_cur;
    if (target > rl.rlim_max) target = rl.rlim_max;
    rl.rlim_cur = target;
    if (setrlimit(RLIMIT_NOFILE, &rl) < 0) return leanswe_mk_errno(errno);
  }
  return leanswe_mk_ok(lean_box_uint64((uint64_t)rl.rlim_cur));
}

LEAN_EXPORT lean_obj_res leanswe_poll_get_fd_flags(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int fdf = fcntl(fd, F_GETFD);
  int flf = fcntl(fd, F_GETFL);
  int err = (fdf < 0 || flf < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (err != 0) return leanswe_mk_errno(err);
  uint32_t bits = ((fdf & FD_CLOEXEC) ? 1u : 0u) | ((flf & O_NONBLOCK) ? 2u : 0u);
  return leanswe_mk_ok(lean_box_uint32(bits));
}

static int bind_loopback_inet(int fd, uint16_t *port_out) {
  struct sockaddr_in sin;
  memset(&sin, 0, sizeof(sin));
  sin.sin_family = AF_INET;
  sin.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  sin.sin_port = 0;
  if (bind(fd, (const struct sockaddr *)&sin, sizeof(sin)) < 0) return -1;
  socklen_t slen = (socklen_t)sizeof(sin);
  if (getsockname(fd, (struct sockaddr *)&sin, &slen) < 0) return -1;
  *port_out = ntohs(sin.sin_port);
  return 0;
}

static int connect_loopback_inet(int fd, uint16_t port) {
  struct sockaddr_in sin;
  memset(&sin, 0, sizeof(sin));
  sin.sin_family = AF_INET;
  sin.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  sin.sin_port = htons(port);
  return connect(fd, (const struct sockaddr *)&sin, sizeof(sin));
}

LEAN_EXPORT lean_obj_res leanswe_poll_open_seqpair(void) {
  int fds[2] = {-1, -1};
  if (socketpair(AF_UNIX, SOCK_SEQPACKET | SOCK_NONBLOCK | SOCK_CLOEXEC, 0, fds) < 0) {
    return leanswe_mk_errno(errno);
  }
  return mk_fd_pair(fds[0], fds[1]);
}

LEAN_EXPORT lean_obj_res leanswe_poll_open_tcp_listener(void) {
  int fd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
  if (fd < 0) return leanswe_mk_errno(errno);
  uint16_t port = 0;
  if (bind_loopback_inet(fd, &port) < 0 || listen(fd, 4) < 0) {
    int err = errno;
    close(fd);
    return leanswe_mk_errno(err);
  }
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, obj);
  lean_ctor_set(p, 1, lean_box_uint32((uint32_t)port));
  return leanswe_mk_ok(p);
}

LEAN_EXPORT lean_obj_res leanswe_poll_tcp_connect_loopback(uint32_t port) {
  if (port > 0xFFFFu) return leanswe_mk_errno(EINVAL);
  int fd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
  if (fd < 0) return leanswe_mk_errno(errno);
  (void)connect_loopback_inet(fd, (uint16_t)port);
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_poll_accept4(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int cfd = accept4(fd, NULL, NULL, SOCK_NONBLOCK | SOCK_CLOEXEC);
  int err = (cfd < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (cfd < 0) return leanswe_mk_errno(err);
  lean_obj_res obj = leanswe_mk_fd_obj(cfd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_poll_open_udp_socket(void) {
  int fd = socket(AF_INET, SOCK_DGRAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
  if (fd < 0) return leanswe_mk_errno(errno);
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_poll_open_udp_pair(void) {
  int u0 = socket(AF_INET, SOCK_DGRAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
  if (u0 < 0) return leanswe_mk_errno(errno);
  int u1 = socket(AF_INET, SOCK_DGRAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
  if (u1 < 0) {
    int err = errno;
    close(u0);
    return leanswe_mk_errno(err);
  }
  uint16_t p0 = 0, p1 = 0;
  if (bind_loopback_inet(u0, &p0) < 0 || bind_loopback_inet(u1, &p1) < 0 ||
      connect_loopback_inet(u0, p1) < 0 || connect_loopback_inet(u1, p0) < 0) {
    int err = errno;
    close(u0);
    close(u1);
    return leanswe_mk_errno(err);
  }
  return mk_fd_pair(u0, u1);
}

LEAN_EXPORT lean_obj_res leanswe_poll_sendto_dontwait(b_lean_obj_arg fd_obj, b_lean_obj_arg data_ba) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  size_t len = lean_sarray_size(data_ba);
  const void *ptr = (len == 0) ? (const void *)"" : (const void *)lean_sarray_cptr(data_ba);
  ssize_t n = sendto(fd, ptr, len, MSG_DONTWAIT, NULL, 0);
  int err = (n < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (n < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box_uint32((uint32_t)n));
}

LEAN_EXPORT lean_obj_res leanswe_poll_recv_dontwait(
    b_lean_obj_arg fd_obj, uint32_t max_bytes, uint8_t peek) {
  size_t cap = (max_bytes > 65536u) ? 65536u : (size_t)max_bytes;
  uint8_t sbuf[4096];
  uint8_t *heap = NULL;
  uint8_t *buf = sbuf;
  if (cap > sizeof(sbuf)) {
    heap = (uint8_t *)malloc(cap);
    if (heap == NULL) return leanswe_mk_errno(ENOMEM);
    buf = heap;
  }
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) {
    free(heap);
    return leanswe_mk_errno(perr);
  }
  int flags = MSG_DONTWAIT | (peek ? MSG_PEEK : 0);
  ssize_t n = recv(fd, buf, cap, flags);
  int err = (n < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  free(heap);
  if (n < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box_uint32((uint32_t)n));
}
