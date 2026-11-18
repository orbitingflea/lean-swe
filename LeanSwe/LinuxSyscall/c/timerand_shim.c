#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe LinuxSyscall requires Linux on x86_64 or aarch64"
#endif

#define _POSIX_C_SOURCE 200809L
#define _GNU_SOURCE
#include <errno.h>
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/random.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

#define LEANSWE_MAX_READ_BYTES 16777216u

static inline lean_obj_res mk_except_ok(lean_obj_res v) {
  lean_obj_res r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, v);
  return r;
}

static inline lean_obj_res mk_except_err(int err) {
  if (err == EFAULT) {
    abort();
  }
  lean_obj_res r = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(r, 0, lean_box_uint32((uint32_t)err));
  return r;
}

static inline lean_obj_res mk_pair(lean_obj_res a, lean_obj_res b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

static inline clockid_t decode_clock(uint32_t clk) {
  return clk == 0 ? CLOCK_REALTIME : CLOCK_MONOTONIC;
}

static inline unsigned int decode_grnd_flags(uint32_t flags) {
  return ((flags & 1u) ? GRND_NONBLOCK : 0u)
       | ((flags & 2u) ? GRND_RANDOM : 0u)
       | ((flags & 4u) ? GRND_INSECURE : 0u)
       | (flags & ~7u);
}

/** Raw Linux `clock_gettime(2)` wrapper returning `BaseIO (Except Errno (Int64 × UInt32))`. */
lean_obj_res leanswe_sys_clock_gettime(uint32_t clk) {
  struct timespec ts = {0};
  long rc = syscall(SYS_clock_gettime, decode_clock(clk), &ts);
  if (rc < 0) {
    return mk_except_err(errno);
  }
  return mk_except_ok(mk_pair(lean_box_uint64((uint64_t)(int64_t)ts.tv_sec),
                              lean_box_uint32((uint32_t)ts.tv_nsec)));
}

/** Raw Linux `clock_nanosleep(2)` wrapper returning `BaseIO (Except Errno Unit)` without retrying `EINTR`. */
lean_obj_res leanswe_sys_clock_nanosleep(uint32_t clk, uint8_t abstime, uint64_t sec,
                                         uint32_t nsec) {
  struct timespec ts;
  ts.tv_sec = (time_t)(int64_t)sec;
  ts.tv_nsec = (long)(uint64_t)nsec;
  int flags = abstime ? TIMER_ABSTIME : 0;
  long rc = syscall(SYS_clock_nanosleep, decode_clock(clk), flags, &ts, NULL);
  if (rc < 0) {
    return mk_except_err(errno);
  }
  return mk_except_ok(lean_box(0));
}

/** Raw Linux `getrandom(2)` wrapper clamping allocation to `LEANSWE_MAX_READ_BYTES` (`16 MiB`). */
lean_obj_res leanswe_sys_getrandom(uint32_t len, uint32_t flags) {
  size_t cap = len > LEANSWE_MAX_READ_BYTES ? LEANSWE_MAX_READ_BYTES : (size_t)len;
  lean_obj_res ba = lean_alloc_sarray(1, 0, cap);
  ssize_t n = syscall(SYS_getrandom, lean_sarray_cptr(ba), cap, decode_grnd_flags(flags));
  if (n < 0) {
    int err = errno;
    lean_dec_ref(ba);
    return mk_except_err(err);
  }
  lean_sarray_set_size(ba, (size_t)n);
  return mk_except_ok(ba);
}
