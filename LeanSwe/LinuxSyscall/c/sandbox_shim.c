#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "sandbox_shim.c supports only Linux on x86_64 or aarch64"
#endif
#if !defined(__LP64__) || __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "sandbox_shim.c requires LP64 little-endian"
#endif

#define _GNU_SOURCE
#include <errno.h>
#include <linux/filter.h>
#include <linux/prctl.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <unistd.h>
#include "fd_box.h"

#ifndef SYS_landlock_create_ruleset
#define SYS_landlock_create_ruleset 444
#endif
#ifndef SYS_landlock_add_rule
#define SYS_landlock_add_rule 445
#endif
#ifndef SYS_landlock_restrict_self
#define SYS_landlock_restrict_self 446
#endif
#ifndef SYS_seccomp
#ifdef __x86_64__
#define SYS_seccomp 317
#else
#define SYS_seccomp 277
#endif
#endif
#ifndef SYS_memfd_create
#ifdef __x86_64__
#define SYS_memfd_create 319
#else
#define SYS_memfd_create 279
#endif
#endif
#ifndef SYS_prctl
#ifdef __x86_64__
#define SYS_prctl 157
#else
#define SYS_prctl 167
#endif
#endif

typedef struct { uint64_t handled_access_fs; uint64_t handled_access_net; } leanswe_ll_ruleset_attr_t;
typedef struct __attribute__((packed)) { uint64_t allowed_access; int32_t parent_fd; } leanswe_ll_path_beneath_attr_t;
typedef struct { uint64_t allowed_access; uint64_t port; } leanswe_ll_net_port_attr_t;

_Static_assert(sizeof(leanswe_ll_ruleset_attr_t) == 16, "landlock_ruleset_attr must be 16 bytes");
_Static_assert(sizeof(leanswe_ll_path_beneath_attr_t) == 12, "landlock_path_beneath_attr must be 12 bytes");
_Static_assert(sizeof(leanswe_ll_net_port_attr_t) == 16, "landlock_net_port_attr must be 16 bytes");
_Static_assert(sizeof(struct sock_filter) == 8, "sock_filter must be 8 bytes");

static int sbx_ba_to_cstr(b_lean_obj_arg ba, char *stack_buf, size_t cap,
                          const char **out_ptr, char **out_heap) {
  size_t len = lean_sarray_size(ba);
  const uint8_t *src = lean_sarray_cptr(ba);
  if (len > 0 && memchr(src, 0, len) != NULL) {
    return EINVAL;
  }
  if (len < cap) {
    if (len > 0) { memcpy(stack_buf, src, len); }
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

LEAN_EXPORT lean_obj_res leanswe_sys_landlock_query(uint32_t flags) {
  long rc = syscall(SYS_landlock_create_ruleset, NULL, (unsigned long)0, (unsigned long)flags);
  if (rc < 0) {
    return leanswe_mk_errno(errno);
  }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)rc));
}

LEAN_EXPORT lean_obj_res leanswe_sys_landlock_create(uint64_t fs, uint64_t net) {
  leanswe_ll_ruleset_attr_t attr;
  memset(&attr, 0, sizeof(attr));
  attr.handled_access_fs = fs;
  attr.handled_access_net = net;
  int fd = (int)syscall(SYS_landlock_create_ruleset, &attr, (unsigned long)sizeof(attr), 0UL);
  if (fd < 0) {
    return leanswe_mk_errno(errno);
  }
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) {
    return leanswe_mk_errno(ENOMEM);
  }
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_sys_landlock_add_path_beneath(
    b_lean_obj_arg ruleset, b_lean_obj_arg parent, uint64_t access) {
  LeanFdBox *rbox = (LeanFdBox *)lean_get_external_data(ruleset);
  LeanFdBox *pbox = (LeanFdBox *)lean_get_external_data(parent);
  int rfd = -1, pfd = -1;
  int rpinned = (leanswe_fd_box_pin(rbox, &rfd) == 0);
  int ppinned = (leanswe_fd_box_pin(pbox, &pfd) == 0);
  leanswe_ll_path_beneath_attr_t attr;
  memset(&attr, 0, sizeof(attr));
  attr.allowed_access = access;
  attr.parent_fd = ppinned ? pfd : -1;
  long rc = syscall(SYS_landlock_add_rule, (long)(rpinned ? rfd : -1), 1UL, &attr, 0UL);
  int saved = errno;
  if (ppinned) { leanswe_fd_box_unpin(pbox); }
  if (rpinned) { leanswe_fd_box_unpin(rbox); }
  if (rc < 0) {
    return leanswe_mk_errno(saved);
  }
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_landlock_add_net_port(
    b_lean_obj_arg ruleset, uint64_t port, uint64_t access) {
  LeanFdBox *rbox = (LeanFdBox *)lean_get_external_data(ruleset);
  int rfd = -1;
  int rpinned = (leanswe_fd_box_pin(rbox, &rfd) == 0);
  leanswe_ll_net_port_attr_t attr;
  memset(&attr, 0, sizeof(attr));
  attr.allowed_access = access;
  attr.port = port;
  long rc = syscall(SYS_landlock_add_rule, (long)(rpinned ? rfd : -1), 2UL, &attr, 0UL);
  int saved = errno;
  if (rpinned) { leanswe_fd_box_unpin(rbox); }
  if (rc < 0) {
    return leanswe_mk_errno(saved);
  }
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_landlock_restrict_self(b_lean_obj_arg ruleset) {
  LeanFdBox *rbox = (LeanFdBox *)lean_get_external_data(ruleset);
  int rfd = -1;
  int rpinned = (leanswe_fd_box_pin(rbox, &rfd) == 0);
  long rc = syscall(SYS_landlock_restrict_self, (long)(rpinned ? rfd : -1), 0UL);
  int saved = errno;
  if (rpinned) { leanswe_fd_box_unpin(rbox); }
  if (rc < 0) {
    return leanswe_mk_errno(saved);
  }
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_seccomp_get_action_avail(uint32_t action) {
  uint32_t act = action;
  long rc = syscall(SYS_seccomp, 2UL, 0UL, &act);
  if (rc < 0) {
    return leanswe_mk_errno(errno);
  }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)rc));
}

LEAN_EXPORT lean_obj_res leanswe_sys_seccomp_set_filter(
    uint32_t flags, b_lean_obj_arg filter_ba) {
  size_t byte_len = lean_sarray_size(filter_ba);
  if (byte_len == 0 || (byte_len % 8) != 0 || (byte_len / 8) > 0xFFFFu) {
    return leanswe_mk_errno(EINVAL);
  }
  struct sock_filter stack_insns[160];
  size_t ninsns = byte_len / 8;
  struct sock_filter *heap_insns = NULL;
  struct sock_filter *ptr = stack_insns;
  if (ninsns > 160) {
    heap_insns = (struct sock_filter *)malloc(byte_len);
    if (heap_insns == NULL) {
      return leanswe_mk_errno(ENOMEM);
    }
    ptr = heap_insns;
  }
  memcpy(ptr, lean_sarray_cptr(filter_ba), byte_len);
  struct sock_fprog prog = { (unsigned short)ninsns, ptr };
  long rc = syscall(SYS_seccomp, 1UL, (unsigned long)flags, &prog);
  int saved = errno;
  if (heap_insns != NULL) { free(heap_insns); }
  if (rc < 0) {
    return leanswe_mk_errno(saved);
  }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)rc));
}

LEAN_EXPORT lean_obj_res leanswe_sys_prctl(uint32_t tag, uint32_t arg) {
  static const int k_prctl_cmds[4] = { 38, 39, 36, 1 };
  if (tag >= 4u) {
    return leanswe_mk_errno(EINVAL);
  }
  int cmd = k_prctl_cmds[tag];
  long rc = syscall(SYS_prctl, (unsigned long)cmd, (unsigned long)arg, 0UL, 0UL, 0UL);
  if (rc < 0) {
    return leanswe_mk_errno(errno);
  }
  return leanswe_mk_ok(lean_box_uint32((uint32_t)rc));
}

LEAN_EXPORT lean_obj_res leanswe_sys_setrlimit(
    uint32_t tag, uint64_t cur, uint64_t max_lim) {
  static const int k_rlimit_resources[3] = { RLIMIT_CORE, RLIMIT_FSIZE, RLIMIT_NOFILE };
  if (tag >= 3u) {
    return leanswe_mk_errno(EINVAL);
  }
  struct rlimit rl;
  rl.rlim_cur = (rlim_t)cur;
  rl.rlim_max = (rlim_t)max_lim;
  if (setrlimit(k_rlimit_resources[tag], &rl) < 0) {
    return leanswe_mk_errno(errno);
  }
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_memfd_create(
    b_lean_obj_arg name_ba, uint32_t flags) {
  char sbuf[512];
  const char *cname = NULL;
  char *heap = NULL;
  int perr = sbx_ba_to_cstr(name_ba, sbuf, sizeof(sbuf), &cname, &heap);
  if (perr != 0) {
    return leanswe_mk_errno(perr);
  }
  int fd = (int)syscall(SYS_memfd_create, cname, (unsigned long)flags);
  int saved = errno;
  if (heap != NULL) { free(heap); }
  if (fd < 0) {
    return leanswe_mk_errno(saved);
  }
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) {
    return leanswe_mk_errno(ENOMEM);
  }
  return leanswe_mk_ok(obj);
}
