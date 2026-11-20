#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe.LinuxSyscall.Process requires Linux x86_64 or aarch64"
#endif

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>
#include "fd_box.h"

#ifndef SYS_pidfd_open
#define SYS_pidfd_open 434
#endif
#ifndef SYS_pidfd_send_signal
#define SYS_pidfd_send_signal 424
#endif
#ifndef PIDFD_NONBLOCK
#define PIDFD_NONBLOCK O_NONBLOCK
#endif
#ifndef PIDFD_THREAD
#define PIDFD_THREAD O_EXCL
#endif

#ifndef O_NOTIFICATION_PIPE
#define O_NOTIFICATION_PIPE O_EXCL
#endif

#ifndef O_DIRECT
#ifdef __aarch64__
#define O_DIRECT 0200000
#else
#define O_DIRECT 040000
#endif
#endif

#ifndef PIDFD_SIGNAL_THREAD
#define PIDFD_SIGNAL_THREAD (1U << 0)
#endif

#ifndef PIDFD_SIGNAL_THREAD_GROUP
#define PIDFD_SIGNAL_THREAD_GROUP (1U << 1)
#endif

#ifndef PIDFD_SIGNAL_PROCESS_GROUP
#define PIDFD_SIGNAL_PROCESS_GROUP (1U << 2)
#endif

static inline lean_obj_res mk_pair(lean_obj_res a, lean_obj_res b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

static int decode_signal(uint8_t tag, int32_t raw_arg) {
  switch (tag) {
    case 0: return 0;
    case 1: return SIGHUP;
    case 2: return SIGINT;
    case 3: return SIGKILL;
    case 4: return SIGUSR1;
    case 5: return SIGUSR2;
    case 6: return SIGTERM;
    case 7: return SIGCONT;
    case 8: return SIGSTOP;
    default: return (int)raw_arg;
  }
}

static int decode_pipe_flags(uint64_t bits) {
  int flags = 0;
  if (bits & (1ull << 0)) flags |= O_CLOEXEC;
  if (bits & (1ull << 1)) flags |= O_NONBLOCK;
  if (bits & (1ull << 2)) flags |= O_DIRECT;
  if (bits & (1ull << 3)) flags |= O_NOTIFICATION_PIPE;
  if ((bits >> 4) != 0ull) flags |= (int)0x80000000u;
  return flags;
}

static int decode_wait_options(uint64_t opt_bits) {
  unsigned int opts = 0u;
  if (opt_bits & (1ull << 0)) opts |= (unsigned int)WNOHANG;
  if (opt_bits & (1ull << 1)) opts |= (unsigned int)WUNTRACED;
  if (opt_bits & (1ull << 2)) opts |= (unsigned int)WCONTINUED;
  if (opt_bits & (1ull << 3)) opts |= (unsigned int)__WALL;
  if (opt_bits & (1ull << 4)) opts |= (unsigned int)__WCLONE;
  if (opt_bits & (1ull << 5)) opts |= (unsigned int)__WNOTHREAD;
  if ((opt_bits >> 6) != 0ull) opts |= 0x10u;
  return (int)opts;
}

static unsigned int decode_pidfd_open_flags(uint64_t bits) {
  unsigned int flags = 0u;
  if (bits & (1ull << 0)) flags |= (unsigned int)PIDFD_NONBLOCK;
  if (bits & (1ull << 1)) flags |= (unsigned int)PIDFD_THREAD;
  if ((bits >> 2) != 0ull) flags |= 0x80000000u;
  return flags;
}

static unsigned int decode_pidfd_signal_flags(uint64_t bits) {
  unsigned int flags = 0u;
  if (bits & (1ull << 0)) flags |= (unsigned int)PIDFD_SIGNAL_THREAD;
  if (bits & (1ull << 1)) flags |= (unsigned int)PIDFD_SIGNAL_THREAD_GROUP;
  if (bits & (1ull << 2)) flags |= (unsigned int)PIDFD_SIGNAL_PROCESS_GROUP;
  if ((bits >> 3) != 0ull) flags |= 0x80000000u;
  return flags;
}

LEAN_EXPORT lean_obj_res leanswe_sys_pipe2(uint64_t bits) {
  int flags = decode_pipe_flags(bits);
  int fds[2] = {-1, -1};
  if (pipe2(fds, flags) < 0) return leanswe_mk_errno(errno);
  lean_obj_res r_obj = leanswe_mk_fd_obj(fds[0]);
  if (r_obj == NULL) {
    close(fds[1]);
    return leanswe_mk_errno(ENOMEM);
  }
  lean_obj_res w_obj = leanswe_mk_fd_obj(fds[1]);
  if (w_obj == NULL) {
    lean_dec_ref(r_obj);
    return leanswe_mk_errno(ENOMEM);
  }
  return leanswe_mk_ok(mk_pair(r_obj, w_obj));
}

LEAN_EXPORT lean_obj_res leanswe_sys_waitpid(uint32_t pid_bits, uint64_t opt_bits) {
  int opts = decode_wait_options(opt_bits);
  int status = 0;
  pid_t rc = wait4((pid_t)(int32_t)pid_bits, &status, opts, NULL);
  if (rc < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(mk_pair(lean_box_uint32((uint32_t)(int32_t)rc), lean_box_uint32((uint32_t)status)));
}

LEAN_EXPORT lean_obj_res leanswe_sys_kill(
    uint32_t pid_bits, uint8_t sig_tag, uint32_t sig_arg_bits) {
  int sig = decode_signal(sig_tag, (int32_t)sig_arg_bits);
  if (kill((pid_t)(int32_t)pid_bits, sig) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_pidfd_open(uint32_t pid_u32, uint64_t bits) {
  unsigned int flags = decode_pidfd_open_flags(bits);
  long fd = syscall(SYS_pidfd_open, (long)(int32_t)pid_u32, (unsigned long)flags);
  if (fd < 0) return leanswe_mk_errno(errno);
  lean_obj_res obj = leanswe_mk_fd_obj((int)fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_sys_pidfd_send_signal(
    b_lean_obj_arg fd_obj, uint8_t sig_tag, uint32_t sig_arg_bits, uint64_t bits) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  unsigned int flags = decode_pidfd_signal_flags(bits);
  int sig = decode_signal(sig_tag, (int32_t)sig_arg_bits);
  long rc = syscall(SYS_pidfd_send_signal, (long)fd, (long)sig, (void *)NULL, (unsigned long)flags);
  int err = errno;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_getpid(void) {
  long rc = syscall(SYS_getpid);
  if (rc < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box_uint32((uint32_t)rc));
}

LEAN_EXPORT lean_obj_res leanswe_sys_getuid(void) {
  long rc = syscall(SYS_getuid);
  if (rc < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box_uint32((uint32_t)rc));
}
