#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__)) || !defined(__LP64__)
#error "LeanSwe LinuxSyscall requires LP64 Linux on x86_64 or aarch64"
#endif
#define _POSIX_C_SOURCE 200809L
#define _GNU_SOURCE
#include <errno.h>
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/random.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>
#define LEANSWE_MAX_READ_BYTES 16777216u
_Static_assert(sizeof(struct timespec) == 16 && sizeof(time_t) == 8, "64-bit timespec ABI required");
static inline lean_obj_res mk_except_ok(lean_obj_res v) {
  lean_obj_res r = lean_alloc_ctor(1, 1, 0); lean_ctor_set(r, 0, v); return r;
}
static inline lean_obj_res mk_except_err(int err) {
  if (err == EFAULT) {
    abort();
  }
  lean_obj_res r = lean_alloc_ctor(0, 1, 0); lean_ctor_set(r, 0, lean_box_uint32((uint32_t)err)); return r;
}
static inline lean_obj_res mk_pair(lean_obj_res a, lean_obj_res b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0); lean_ctor_set(p, 0, a); lean_ctor_set(p, 1, b); return p;
}
static inline clockid_t decode_clock(uint32_t clk) {
  return clk == 0u ? CLOCK_REALTIME : (clk == 1u ? CLOCK_MONOTONIC : (clockid_t)-1);
}
static inline unsigned int decode_grnd_flags(uint32_t flags) {
  return ((flags & 1u) ? GRND_NONBLOCK : 0u) | ((flags & 2u) ? GRND_RANDOM : 0u)
       | ((flags & 4u) ? GRND_INSECURE : 0u) | (flags & ~7u);
}
static inline lean_obj_res alloc_byte_array_copy(const uint8_t *src, size_t n) {
  lean_obj_res ba = lean_alloc_sarray(1, n, n);
  if (n > 0u) { memcpy(lean_sarray_cptr(ba), src, n); }
  return ba;
}
/** Raw Linux `clock_gettime(2)` wrapper returning `BaseIO (Except Errno (Int64 × UInt32))`. */
LEAN_EXPORT lean_obj_res leanswe_sys_clock_gettime(uint32_t clk) {
  clockid_t clock_id = decode_clock(clk);
  if (clock_id == (clockid_t)-1) {
    return mk_except_err(EINVAL);
  }
  struct timespec ts = {0};
  if (syscall(SYS_clock_gettime, (long)clock_id, &ts) < 0) {
    return mk_except_err(errno);
  }
  return mk_except_ok(mk_pair(lean_box_uint64((uint64_t)(int64_t)ts.tv_sec), lean_box_uint32((uint32_t)ts.tv_nsec)));
}
/** Raw Linux `clock_nanosleep(2)` wrapper returning `BaseIO (Except Errno Unit)` without retrying `EINTR`. */
LEAN_EXPORT lean_obj_res leanswe_sys_clock_nanosleep(uint32_t clk, uint8_t abstime, uint64_t sec, uint32_t nsec) {
  clockid_t clock_id = decode_clock(clk);
  if (clock_id == (clockid_t)-1 || abstime > 1u) {
    return mk_except_err(EINVAL);
  }
  struct timespec ts = {0};
  ts.tv_sec = (time_t)(int64_t)sec; ts.tv_nsec = (long)(uint64_t)nsec;
  if (syscall(SYS_clock_nanosleep, (long)clock_id, (long)(abstime ? TIMER_ABSTIME : 0), &ts, NULL) < 0) {
    return mk_except_err(errno);
  }
  return mk_except_ok(lean_box(0));
}
/** Raw Linux `getrandom(2)` wrapper clamping allocation to `LEANSWE_MAX_READ_BYTES` (`16 MiB`). */
LEAN_EXPORT lean_obj_res leanswe_sys_getrandom(uint32_t len, uint32_t flags) {
  size_t cap = len > LEANSWE_MAX_READ_BYTES ? LEANSWE_MAX_READ_BYTES : (size_t)len;
  unsigned long raw_flags = (unsigned long)decode_grnd_flags(flags);
  lean_obj_res ba = lean_alloc_sarray(1, 0, cap);
  long n = syscall(SYS_getrandom, lean_sarray_cptr(ba), cap, raw_flags);
  if (n < 0) {
    int err = errno;
    lean_dec_ref(ba);
    return mk_except_err(err);
  }
  if ((size_t)n > cap) { lean_dec_ref(ba); abort(); }
  if ((size_t)n == cap) { lean_sarray_set_size(ba, (size_t)n); return mk_except_ok(ba); }
  lean_obj_res exact = alloc_byte_array_copy(lean_sarray_cptr(ba), (size_t)n);
  lean_dec_ref(ba);
  return mk_except_ok(exact);
}
