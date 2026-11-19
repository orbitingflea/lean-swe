#define _POSIX_C_SOURCE 200809L
#define _GNU_SOURCE

#include <errno.h>
#include <fenv.h>
#include <lean/lean.h>
#include <locale.h>
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static pthread_once_t g_c_locale_once = PTHREAD_ONCE_INIT;
static locale_t g_c_locale = (locale_t)0;

static void init_c_locale(void) {
  g_c_locale = newlocale(LC_NUMERIC_MASK, "C", (locale_t)0);
  if (g_c_locale == (locale_t)0) {
    abort();
  }
}

typedef struct {
  int saved_errno;
  fenv_t saved_env;
} leanswe_saved_fenv_t;

static leanswe_saved_fenv_t save_fenv_and_guard_nearest(void) {
  if (fegetround() != FE_TONEAREST) {
    abort();
  }
  leanswe_saved_fenv_t st;
  st.saved_errno = errno;
  if (fegetenv(&st.saved_env) != 0) {
    abort();
  }
  return st;
}

static void restore_fenv(leanswe_saved_fenv_t st) {
  if (fesetenv(&st.saved_env) != 0) {
    abort();
  }
  errno = st.saved_errno;
}

LEAN_EXPORT lean_obj_res leanswe_float_oracle_is_tonearest(void) {
  uint8_t ok = (fegetround() == FE_TONEAREST) ? 1 : 0;
  return lean_io_result_mk_ok(lean_box(ok));
}

LEAN_EXPORT lean_obj_res leanswe_float_oracle_strtod(b_lean_obj_arg s_obj) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  pthread_once(&g_c_locale_once, init_c_locale);
  if (g_c_locale == (locale_t)0) {
    abort();
  }
  const char *s = lean_string_cstr(s_obj);
  char *end = NULL;
  double d = strtod_l(s, &end, g_c_locale);
  uint64_t bits = 0;
  memcpy(&bits, &d, sizeof(bits));
  size_t consumed = (end != NULL && end >= s) ? (size_t)(end - s) : 0;
  restore_fenv(st);
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_box_usize(consumed));
  lean_ctor_set(p, 1, lean_box_uint64(bits));
  return p;
}

LEAN_EXPORT lean_obj_res leanswe_float_oracle_snprintf17g(uint64_t raw_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double d = 0.0;
  char buf[64];
  memcpy(&d, &raw_bits, sizeof(d));
  pthread_once(&g_c_locale_once, init_c_locale);
  if (g_c_locale == (locale_t)0) {
    abort();
  }
  locale_t prev = uselocale(g_c_locale);
  if (prev == (locale_t)0) {
    abort();
  }
  buf[sizeof(buf) - 1] = '\0';
  volatile int vn = snprintf(buf, sizeof(buf), "%.17g", d);
  int n = vn;
  if (uselocale(prev) == (locale_t)0) {
    abort();
  }
  restore_fenv(st);
  if (n < 0 || (size_t)n >= sizeof(buf)) {
    return lean_mk_string("");
  }
  return lean_mk_string_from_bytes(buf, (size_t)n);
}

LEAN_EXPORT double leanswe_float_oracle_raw_double_from_bits(uint64_t raw_bits) {
  double d = 0.0;
  memcpy(&d, &raw_bits, sizeof(d));
  return d;
}

LEAN_EXPORT float leanswe_float_oracle_raw_f32_from_bits(uint32_t raw_bits) {
  float f = 0.0f;
  memcpy(&f, &raw_bits, sizeof(f));
  return f;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_raw_bits_from_double(double d) {
  uint64_t bits = 0;
  memcpy(&bits, &d, sizeof(bits));
  return bits;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_raw_bits_from_f32(float f) {
  uint32_t bits = 0;
  memcpy(&bits, &f, sizeof(bits));
  return bits;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_unop(uint8_t op, uint64_t a_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0, r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (op == 0) r = -a;
  else if (op == 1) r = fabs(a);
  else if (op == 2) r = sqrt(a);
  else if (op == 3) r = ceil(a);
  else if (op == 4) r = floor(a);
  else if (op == 5) r = round(a);
  else abort();
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_trans1(uint8_t op, uint64_t a_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0, r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (op == 0) r = sin(a);
  else if (op == 1) r = cos(a);
  else if (op == 2) r = tan(a);
  else if (op == 3) r = asin(a);
  else if (op == 4) r = acos(a);
  else if (op == 5) r = atan(a);
  else if (op == 6) r = sinh(a);
  else abort();
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_trans2(uint8_t op, uint64_t a_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0, r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (op == 0) r = cosh(a);
  else if (op == 1) r = tanh(a);
  else if (op == 2) r = asinh(a);
  else if (op == 3) r = acosh(a);
  else if (op == 4) r = atanh(a);
  else if (op == 5) r = exp(a);
  else if (op == 6) r = exp2(a);
  else abort();
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_trans3(uint8_t op, uint64_t a_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0, r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (op == 0) r = log(a);
  else if (op == 1) r = log2(a);
  else if (op == 2) r = log10(a);
  else if (op == 3) r = cbrt(a);
  else abort();
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_binop(uint8_t op, uint64_t a_bits, uint64_t b_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0, b = 0.0, r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (op == 0) r = a + b;
  else if (op == 1) r = a - b;
  else if (op == 2) r = a * b;
  else if (op == 3) r = a / b;
  else if (op == 4) r = pow(a, b);
  else if (op == 5) r = atan2(a, b);
  else abort();
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_fma(uint64_t a_bits, uint64_t b_bits, uint64_t c_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0, b = 0.0, c = 0.0, r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  memcpy(&c, &c_bits, sizeof(c));
  r = fma(a, b, c);
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint8_t leanswe_float_oracle_cmp(uint64_t a_bits, uint64_t b_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0, b = 0.0;
  uint8_t mask = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (a == b) mask |= 1u;
  if (a < b) mask |= 2u;
  if (a <= b) mask |= 4u;
  if (isnan(a)) mask |= 8u;
  if (isfinite(a)) mask |= 16u;
  if (isinf(a)) mask |= 32u;
  restore_fenv(st);
  return mask;
}

LEAN_EXPORT lean_obj_res leanswe_float_oracle_frexp(uint64_t a_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0;
  int exp = 0;
  uint64_t sig_bits = 0;
  memcpy(&a, &a_bits, sizeof(a));
  double sig = frexp(a, &exp);
  memcpy(&sig_bits, &sig, sizeof(sig_bits));
  restore_fenv(st);
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_box_uint64(sig_bits));
  lean_ctor_set(p, 1, lean_box_uint32((uint32_t)(int32_t)exp));
  return p;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_ldexp(uint64_t a_bits, uint32_t exp_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0;
  int32_t exp = (int32_t)exp_bits;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  double r = ldexp(a, (int)exp);
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f64_to_f32(uint64_t a_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0;
  float r = 0.0f;
  uint32_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  r = (float)a;
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_f32_to_f64(uint32_t a_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f;
  double r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  r = (double)a;
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_minmax(uint8_t is_max, uint64_t a_bits, uint64_t b_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0, b = 0.0;
  uint64_t res = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (isnan(a) || isnan(b)) res = 0x7ff8000000000000ULL;
  else if (a == 0.0 && b == 0.0) res = is_max ? (a_bits & b_bits) : (a_bits | b_bits);
  else if (is_max) res = (a > b) ? a_bits : b_bits;
  else res = (a < b) ? a_bits : b_bits;
  restore_fenv(st);
  return res;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_minmax_num(uint8_t is_max, uint64_t a_bits, uint64_t b_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0, b = 0.0;
  uint64_t res = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (isnan(a) && isnan(b)) res = 0x7ff8000000000000ULL;
  else if (isnan(a)) res = b_bits;
  else if (isnan(b)) res = a_bits;
  else if (a == 0.0 && b == 0.0) res = is_max ? (a_bits & b_bits) : (a_bits | b_bits);
  else if (is_max) res = (a > b) ? a_bits : b_bits;
  else res = (a < b) ? a_bits : b_bits;
  restore_fenv(st);
  return res;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_to_uint64(uint64_t a_bits, uint64_t max_val) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0;
  uint64_t res = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (isnan(a) || a < 0.0) res = 0;
  else if (a >= 18446744073709551616.0) res = max_val;
  else {
    uint64_t v = (uint64_t)a;
    res = (v > max_val) ? max_val : v;
  }
  restore_fenv(st);
  return res;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_to_int64(uint64_t a_bits, uint64_t min_bits, uint64_t max_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double a = 0.0;
  int64_t min_val = (int64_t)min_bits;
  int64_t max_val = (int64_t)max_bits;
  uint64_t res = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (isnan(a)) res = 0;
  else if (a <= -9223372036854775808.0) res = (uint64_t)min_val;
  else if (a >= 9223372036854775808.0) res = (uint64_t)max_val;
  else {
    int64_t v = (int64_t)a;
    if (v < min_val) res = (uint64_t)min_val;
    else if (v > max_val) res = (uint64_t)max_val;
    else res = (uint64_t)v;
  }
  restore_fenv(st);
  return res;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_of_uint64(uint64_t u) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  double d = (double)u;
  uint64_t out = 0;
  memcpy(&out, &d, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_of_int64(uint64_t i_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  int64_t i = (int64_t)i_bits;
  double d = (double)i;
  uint64_t out = 0;
  memcpy(&out, &d, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f32_unop(uint8_t op, uint32_t a_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f, r = 0.0f;
  uint32_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (op == 0) r = -a;
  else if (op == 1) r = fabsf(a);
  else if (op == 2) r = sqrtf(a);
  else if (op == 3) r = ceilf(a);
  else if (op == 4) r = floorf(a);
  else if (op == 5) r = roundf(a);
  else abort();
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f32_binop(uint8_t op, uint32_t a_bits, uint32_t b_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f, b = 0.0f, r = 0.0f;
  uint32_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (op == 0) r = a + b;
  else if (op == 1) r = a - b;
  else if (op == 2) r = a * b;
  else if (op == 3) r = a / b;
  else if (op == 4) r = powf(a, b);
  else abort();
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f32_fma(uint32_t a_bits, uint32_t b_bits, uint32_t c_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f, b = 0.0f, c = 0.0f, r = 0.0f;
  uint32_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  memcpy(&c, &c_bits, sizeof(c));
  r = fmaf(a, b, c);
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint8_t leanswe_float_oracle_f32_cmp(uint32_t a_bits, uint32_t b_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f, b = 0.0f;
  uint8_t mask = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (a == b) mask |= 1u;
  if (a < b) mask |= 2u;
  if (a <= b) mask |= 4u;
  if (isnan(a)) mask |= 8u;
  if (isfinite(a)) mask |= 16u;
  if (isinf(a)) mask |= 32u;
  restore_fenv(st);
  return mask;
}

LEAN_EXPORT lean_obj_res leanswe_float_oracle_f32_frexp(uint32_t a_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f;
  int exp = 0;
  uint32_t sig_bits = 0;
  memcpy(&a, &a_bits, sizeof(a));
  float sig = frexpf(a, &exp);
  memcpy(&sig_bits, &sig, sizeof(sig_bits));
  restore_fenv(st);
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_box_uint32(sig_bits));
  lean_ctor_set(p, 1, lean_box_uint32((uint32_t)(int32_t)exp));
  return p;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f32_ldexp(uint32_t a_bits, uint32_t exp_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f;
  int32_t exp = (int32_t)exp_bits;
  uint32_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  float r = ldexpf(a, (int)exp);
  memcpy(&out, &r, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f32_minmax(uint8_t is_max, uint32_t a_bits, uint32_t b_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f, b = 0.0f;
  uint32_t res = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (isnan(a) || isnan(b)) res = 0x7fc00000U;
  else if (a == 0.0f && b == 0.0f) res = is_max ? (a_bits & b_bits) : (a_bits | b_bits);
  else if (is_max) res = (a > b) ? a_bits : b_bits;
  else res = (a < b) ? a_bits : b_bits;
  restore_fenv(st);
  return res;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f32_minmax_num(uint8_t is_max, uint32_t a_bits, uint32_t b_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f, b = 0.0f;
  uint32_t res = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (isnan(a) && isnan(b)) res = 0x7fc00000U;
  else if (isnan(a)) res = b_bits;
  else if (isnan(b)) res = a_bits;
  else if (a == 0.0f && b == 0.0f) res = is_max ? (a_bits & b_bits) : (a_bits | b_bits);
  else if (is_max) res = (a > b) ? a_bits : b_bits;
  else res = (a < b) ? a_bits : b_bits;
  restore_fenv(st);
  return res;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_f32_to_uint64(uint32_t a_bits, uint64_t max_val) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f;
  uint64_t res = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (isnan(a) || a < 0.0f) res = 0;
  else if (a >= 18446744073709551616.0f) res = max_val;
  else {
    uint64_t v = (uint64_t)a;
    res = (v > max_val) ? max_val : v;
  }
  restore_fenv(st);
  return res;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_f32_to_int64(uint32_t a_bits, uint64_t min_bits, uint64_t max_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float a = 0.0f;
  int64_t min_val = (int64_t)min_bits;
  int64_t max_val = (int64_t)max_bits;
  uint64_t res = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (isnan(a)) res = 0;
  else if (a <= -9223372036854775808.0f) res = (uint64_t)min_val;
  else if (a >= 9223372036854775808.0f) res = (uint64_t)max_val;
  else {
    int64_t v = (int64_t)a;
    if (v < min_val) res = (uint64_t)min_val;
    else if (v > max_val) res = (uint64_t)max_val;
    else res = (uint64_t)v;
  }
  restore_fenv(st);
  return res;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f32_of_uint64(uint64_t u) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  float f = (float)u;
  uint32_t out = 0;
  memcpy(&out, &f, sizeof(out));
  restore_fenv(st);
  return out;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f32_of_int64(uint64_t i_bits) {
  leanswe_saved_fenv_t st = save_fenv_and_guard_nearest();
  int64_t i = (int64_t)i_bits;
  float f = (float)i;
  uint32_t out = 0;
  memcpy(&out, &f, sizeof(out));
  restore_fenv(st);
  return out;
}
