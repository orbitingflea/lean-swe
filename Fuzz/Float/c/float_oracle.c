#define _POSIX_C_SOURCE 200809L
#define _GNU_SOURCE

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
}

LEAN_EXPORT lean_obj_res leanswe_float_oracle_strtod(b_lean_obj_arg s_obj) {
  pthread_once(&g_c_locale_once, init_c_locale);
  const char *s = lean_string_cstr(s_obj);
  char *end = NULL;
  double d = (g_c_locale != (locale_t)0) ? strtod_l(s, &end, g_c_locale) : strtod(s, &end);
  uint64_t bits = 0;
  memcpy(&bits, &d, sizeof(bits));
  size_t consumed = (end != NULL && end >= s) ? (size_t)(end - s) : 0;
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_box_usize(consumed));
  lean_ctor_set(p, 1, lean_box_uint64(bits));
  return p;
}

LEAN_EXPORT lean_obj_res leanswe_float_oracle_snprintf17g(uint64_t raw_bits) {
  double d = 0.0;
  char buf[64];
  memcpy(&d, &raw_bits, sizeof(d));
  pthread_once(&g_c_locale_once, init_c_locale);
  locale_t prev = (g_c_locale != (locale_t)0) ? uselocale(g_c_locale) : (locale_t)0;
  int n = snprintf(buf, sizeof(buf), "%.17g", d);
  if (prev != (locale_t)0) {
    uselocale(prev);
  }
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

LEAN_EXPORT uint64_t leanswe_float_oracle_unop(uint8_t op, uint64_t a_bits) {
  double a = 0.0;
  double r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  if (op == 0) {
    r = -a;
  } else if (op == 1) {
    r = fabs(a);
  } else if (op == 2) {
    r = sqrt(a);
  } else if (op == 3) {
    r = ceil(a);
  } else if (op == 4) {
    r = floor(a);
  } else {
    r = round(a);
  }
  memcpy(&out, &r, sizeof(out));
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_binop(uint8_t op, uint64_t a_bits, uint64_t b_bits) {
  double a = 0.0;
  double b = 0.0;
  double r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (op == 0) {
    r = a + b;
  } else if (op == 1) {
    r = a - b;
  } else if (op == 2) {
    r = a * b;
  } else {
    r = a / b;
  }
  memcpy(&out, &r, sizeof(out));
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_fma(uint64_t a_bits, uint64_t b_bits, uint64_t c_bits) {
  double a = 0.0;
  double b = 0.0;
  double c = 0.0;
  double r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  memcpy(&c, &c_bits, sizeof(c));
  r = fma(a, b, c);
  memcpy(&out, &r, sizeof(out));
  return out;
}

LEAN_EXPORT uint8_t leanswe_float_oracle_cmp(uint64_t a_bits, uint64_t b_bits) {
  double a = 0.0;
  double b = 0.0;
  uint8_t mask = 0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (a == b) mask |= 1u;
  if (a < b) mask |= 2u;
  if (a <= b) mask |= 4u;
  if (isnan(a)) mask |= 8u;
  if (isfinite(a)) mask |= 16u;
  if (isinf(a)) mask |= 32u;
  return mask;
}

LEAN_EXPORT lean_obj_res leanswe_float_oracle_frexp(uint64_t a_bits) {
  double a = 0.0;
  int exp = 0;
  uint64_t sig_bits = 0;
  memcpy(&a, &a_bits, sizeof(a));
  double sig = frexp(a, &exp);
  memcpy(&sig_bits, &sig, sizeof(sig_bits));
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_box_uint64(sig_bits));
  lean_ctor_set(p, 1, lean_box_uint32((uint32_t)(int32_t)exp));
  return p;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_ldexp(uint64_t a_bits, uint32_t exp_bits) {
  double a = 0.0;
  int32_t exp = (int32_t)exp_bits;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  double r = ldexp(a, (int)exp);
  memcpy(&out, &r, sizeof(out));
  return out;
}

LEAN_EXPORT uint32_t leanswe_float_oracle_f64_to_f32(uint64_t a_bits) {
  double a = 0.0;
  float r = 0.0f;
  uint32_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  r = (float)a;
  memcpy(&out, &r, sizeof(out));
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_f32_to_f64(uint32_t a_bits) {
  float a = 0.0f;
  double r = 0.0;
  uint64_t out = 0;
  memcpy(&a, &a_bits, sizeof(a));
  r = (double)a;
  memcpy(&out, &r, sizeof(out));
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_minmax(uint8_t is_max, uint64_t a_bits, uint64_t b_bits) {
  double a = 0.0;
  double b = 0.0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (isnan(a) || isnan(b)) {
    return 0x7ff8000000000000ULL;
  }
  if (a == 0.0 && b == 0.0) {
    return is_max ? (a_bits & b_bits) : (a_bits | b_bits);
  }
  if (is_max) {
    return (a > b) ? a_bits : b_bits;
  }
  return (a < b) ? a_bits : b_bits;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_minmax_num(uint8_t is_max, uint64_t a_bits, uint64_t b_bits) {
  double a = 0.0;
  double b = 0.0;
  memcpy(&a, &a_bits, sizeof(a));
  memcpy(&b, &b_bits, sizeof(b));
  if (isnan(a) && isnan(b)) {
    return 0x7ff8000000000000ULL;
  }
  if (isnan(a)) {
    return b_bits;
  }
  if (isnan(b)) {
    return a_bits;
  }
  if (a == 0.0 && b == 0.0) {
    return is_max ? (a_bits & b_bits) : (a_bits | b_bits);
  }
  if (is_max) {
    return (a > b) ? a_bits : b_bits;
  }
  return (a < b) ? a_bits : b_bits;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_to_uint64(uint64_t a_bits, uint64_t max_val) {
  double a = 0.0;
  memcpy(&a, &a_bits, sizeof(a));
  if (isnan(a) || a < 0.0) {
    return 0;
  }
  if (a >= 18446744073709551616.0) {
    return max_val;
  }
  uint64_t v = (uint64_t)a;
  return (v > max_val) ? max_val : v;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_to_int64(uint64_t a_bits, uint64_t min_bits, uint64_t max_bits) {
  double a = 0.0;
  int64_t min_val = (int64_t)min_bits;
  int64_t max_val = (int64_t)max_bits;
  memcpy(&a, &a_bits, sizeof(a));
  if (isnan(a)) {
    return 0;
  }
  if (a <= -9223372036854775808.0) {
    return (uint64_t)min_val;
  }
  if (a >= 9223372036854775808.0) {
    return (uint64_t)max_val;
  }
  int64_t v = (int64_t)a;
  if (v < min_val) {
    return (uint64_t)min_val;
  }
  if (v > max_val) {
    return (uint64_t)max_val;
  }
  return (uint64_t)v;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_of_uint64(uint64_t u) {
  double d = (double)u;
  uint64_t out = 0;
  memcpy(&out, &d, sizeof(out));
  return out;
}

LEAN_EXPORT uint64_t leanswe_float_oracle_of_int64(uint64_t i_bits) {
  int64_t i = (int64_t)i_bits;
  double d = (double)i;
  uint64_t out = 0;
  memcpy(&out, &d, sizeof(out));
  return out;
}
