#define _GNU_SOURCE
#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe.LinuxSyscall.Poll requires Linux x86_64 or aarch64"
#endif

#include <errno.h>
#include <poll.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/eventfd.h>
#include <time.h>
#include <unistd.h>
#include "fd_box.h"

static short decode_poll_events(uint8_t bits) {
  short ev = 0;
  if (bits & (1u << 0)) ev |= POLLIN;
  if (bits & (1u << 1)) ev |= POLLOUT;
  return ev;
}

static uint8_t encode_poll_revents(short rev) {
  uint8_t bits = 0;
  if (rev & POLLIN) bits |= (1u << 0);
  if (rev & POLLOUT) bits |= (1u << 1);
  if (rev & POLLERR) bits |= (1u << 2);
  if (rev & POLLHUP) bits |= (1u << 3);
  if (rev & POLLNVAL) bits |= (1u << 4);
  return bits;
}

static int decode_efd_flags(uint32_t bits) {
  int f = 0;
  if (bits & (1u << 0)) f |= EFD_NONBLOCK;
  if (bits & (1u << 1)) f |= EFD_CLOEXEC;
  if (bits & (1u << 2)) f |= EFD_SEMAPHORE;
  return f | (int)(bits & ~7u);
}

static int pin_poll_box(LeanFdBox *box, int *out_fd) {
  int err = leanswe_fd_box_pin(box, out_fd);
  return (err == EOVERFLOW) ? ENOMEM : err;
}

static int pin_poll_fds(b_lean_obj_arg fds_arr, const uint8_t *req, struct pollfd *pfds,
                        size_t nfds, size_t *pinned_out) {
  for (size_t i = 0; i < nfds; i++) {
    LeanFdBox *box = (LeanFdBox *)lean_get_external_data(lean_array_get_core(fds_arr, i));
    int fd = -1;
    int perr = pin_poll_box(box, &fd);
    if (perr != 0) {
      *pinned_out = i;
      return perr;
    }
    if (pfds != NULL) {
      pfds[i].fd = fd;
      pfds[i].events = decode_poll_events(req[i]);
      pfds[i].revents = 0;
    }
  }
  *pinned_out = nfds;
  return 0;
}

static void unpin_poll_fds(b_lean_obj_arg fds_arr, size_t count) {
  for (size_t i = 0; i < count; i++) {
    LeanFdBox *box = (LeanFdBox *)lean_get_external_data(lean_array_get_core(fds_arr, i));
    leanswe_fd_box_unpin(box);
  }
}

static void copy_poll_revents(const struct pollfd *pfds, uint8_t *out, size_t nfds) {
  for (size_t i = 0; i < nfds; i++) {
    out[i] = encode_poll_revents(pfds[i].revents);
  }
}

LEAN_EXPORT lean_obj_res leanswe_sys_ppoll(
    b_lean_obj_arg fds_arr, b_lean_obj_arg req_ba, uint8_t has_to, uint64_t sec_bits,
    uint32_t nsec) {
  size_t nfds = lean_array_size(fds_arr);
  if (nfds != lean_sarray_size(req_ba)) return leanswe_mk_errno(EINVAL);
  struct pollfd *pfds = NULL;
  if (nfds > 0) {
    pfds = (struct pollfd *)calloc(nfds, sizeof(struct pollfd));
    size_t pinned = 0;
    int perr = pin_poll_fds(fds_arr, lean_sarray_cptr(req_ba), pfds, nfds, &pinned);
    if (perr != 0 || pfds == NULL) {
      unpin_poll_fds(fds_arr, pinned);
      free(pfds);
      return leanswe_mk_errno((perr != 0) ? perr : ENOMEM);
    }
  }
  struct timespec ts;
  ts.tv_sec = (time_t)(int64_t)sec_bits;
  ts.tv_nsec = (long)nsec;
  int rc = ppoll(pfds, (nfds_t)nfds, has_to ? &ts : NULL, NULL);
  int err = (rc < 0) ? errno : 0;
  unpin_poll_fds(fds_arr, nfds);
  if (rc < 0) {
    free(pfds);
    return leanswe_mk_errno(err);
  }
  lean_obj_res out_ba = lean_alloc_sarray(1, nfds, nfds + 1);
  copy_poll_revents(pfds, lean_sarray_cptr(out_ba), nfds);
  free(pfds);
  return leanswe_mk_ok(out_ba);
}

LEAN_EXPORT lean_obj_res leanswe_sys_eventfd2(uint32_t initval, uint32_t flags_bits) {
  int fd = eventfd((unsigned int)initval, decode_efd_flags(flags_bits));
  if (fd < 0) return leanswe_mk_errno(errno);
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}
