#define _GNU_SOURCE
#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe.LinuxSyscall.Net requires Linux x86_64 or aarch64"
#endif

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <unistd.h>
#include "fd_box.h"

LEAN_EXPORT lean_obj_res leanswe_net_close_fd(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int err = leanswe_fd_box_close(box);
  if (err != 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_net_open_nonsock(void) {
  int fd = open("/dev/null", O_RDONLY | O_CLOEXEC);
  if (fd < 0) return leanswe_mk_errno(errno);
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_net_get_fd_flags(b_lean_obj_arg fd_obj) {
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

LEAN_EXPORT lean_obj_res leanswe_net_reset_sigpipe_dfl(void) {
  signal(SIGPIPE, SIG_DFL);
  return lean_box(0);
}
