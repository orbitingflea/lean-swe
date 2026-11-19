#define _POSIX_C_SOURCE 200809L
#include <lean/lean.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/opensslv.h>
#include <openssl/provider.h>
#include <pthread.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#if OPENSSL_VERSION_NUMBER >= 0x30200000L && !defined(LEANSWE_SIM_OSSL_30)
#define LEANSWE_HAVE_ERR_STATE_SAVE 1
#else
#define LEANSWE_HAVE_ERR_STATE_SAVE 0
#endif
#if !defined(LEANSWE_SIM_OSSL_30) && defined(__GNUC__)
#if OPENSSL_VERSION_NUMBER < 0x30200000L
__attribute__((weak)) ERR_STATE *OSSL_ERR_STATE_new(void);
__attribute__((weak)) void OSSL_ERR_STATE_save_to_mark(ERR_STATE *es);
__attribute__((weak)) void OSSL_ERR_STATE_restore(const ERR_STATE *es);
__attribute__((weak)) void OSSL_ERR_STATE_free(ERR_STATE *es);
__attribute__((weak)) int ERR_count_to_mark(void);
#endif
#if OPENSSL_VERSION_NUMBER < 0x30300000L
__attribute__((weak)) int ERR_pop(void);
#endif
#define LEANSWE_CAN_WEAK_PROBE 1
#else
#define LEANSWE_CAN_WEAK_PROBE 0
#endif
static const uint8_t g_empty_byte = 0;
static pthread_mutex_t g_ctx_mu = PTHREAD_MUTEX_INITIALIZER;
static OSSL_LIB_CTX *g_ossl_ctx = NULL;
typedef struct {
  int saved_errno, using_mark, num_segs, prior_line, prior_flags, seg_marks[16];
  unsigned long prior_last_err;
  const char *prior_file, *prior_func, *prior_data;
#if LEANSWE_HAVE_ERR_STATE_SAVE || LEANSWE_CAN_WEAK_PROBE
  ERR_STATE *segs[16];
#endif
} ossl_iso_t;
#if LEANSWE_HAVE_ERR_STATE_SAVE || LEANSWE_CAN_WEAK_PROBE
static int ossl_has_count_mark(void) {
#if LEANSWE_HAVE_ERR_STATE_SAVE
  return 1;
#else
  return ERR_count_to_mark != NULL;
#endif
}
static int ossl_has_err_pop(void) {
#if OPENSSL_VERSION_NUMBER >= 0x30300000L && !defined(LEANSWE_SIM_OSSL_30)
  return 1;
#else
  return ossl_has_count_mark() && ERR_pop != NULL;
#endif
}
static int ossl_has_state_save(void) {
#if LEANSWE_HAVE_ERR_STATE_SAVE
  return 1;
#else
  return OSSL_ERR_STATE_new != NULL && OSSL_ERR_STATE_save_to_mark != NULL && OSSL_ERR_STATE_restore != NULL && OSSL_ERR_STATE_free != NULL && ERR_count_to_mark != NULL;
#endif
}
static void ossl_iso_restore_segs(ossl_iso_t *iso) {
  for (int k = iso->num_segs - 1; k >= 0; k--) {
    OSSL_ERR_STATE_restore(iso->segs[k]);
    for (int m = 0; m < iso->seg_marks[k]; m++) ERR_set_mark();
    OSSL_ERR_STATE_free(iso->segs[k]); iso->segs[k] = NULL; iso->seg_marks[k] = 0;
  }
  iso->num_segs = 0;
}
#endif
static ossl_iso_t ossl_iso_enter(void) {
  ossl_iso_t iso; memset(&iso, 0, sizeof(iso)); iso.saved_errno = errno;
  if (ERR_peek_error() == 0) return iso;
#if LEANSWE_HAVE_ERR_STATE_SAVE || LEANSWE_CAN_WEAK_PROBE
  if (ossl_has_state_save()) {
    int ok = 1;
    while (ERR_peek_error() != 0 && iso.num_segs < 16) {
      int k = iso.num_segs; ERR_STATE *es = OSSL_ERR_STATE_new();
      if (es == NULL) { ok = 0; break; }
      while (ERR_count_to_mark() == 0 && ERR_clear_last_mark() == 1) iso.seg_marks[k]++;
      OSSL_ERR_STATE_save_to_mark(es); iso.segs[k] = es; iso.num_segs++;
    }
    if (ok && ERR_peek_error() == 0) return iso;
    ossl_iso_restore_segs(&iso);
  }
#endif
  iso.prior_last_err = ERR_peek_last_error_all(&iso.prior_file, &iso.prior_line, &iso.prior_func, &iso.prior_data, &iso.prior_flags);
  iso.using_mark = (ERR_set_mark() == 1); return iso;
}
static void ossl_iso_leave(ossl_iso_t *iso) {
#if LEANSWE_HAVE_ERR_STATE_SAVE || LEANSWE_CAN_WEAK_PROBE
  if (iso->num_segs > 0) { ERR_clear_error(); ossl_iso_restore_segs(iso); errno = iso->saved_errno; return; }
#endif
  if (iso->using_mark) { ERR_pop_to_mark(); iso->using_mark = 0; } else { ERR_clear_error(); }
  errno = iso->saved_errno;
}
static void ossl_reset_init_err(int *had_mark) {
  if (*had_mark) { ERR_pop_to_mark(); *had_mark = (ERR_set_mark() == 1); } else { ERR_clear_error(); }
}
static OSSL_LIB_CTX *leanswe_ossl_ctx(void) {
  OSSL_LIB_CTX *ctx = __atomic_load_n(&g_ossl_ctx, __ATOMIC_ACQUIRE);
  if (ctx != NULL) return ctx;
  pthread_mutex_lock(&g_ctx_mu); ctx = g_ossl_ctx;
  if (ctx == NULL) {
    int had_mark = (ERR_set_mark() == 1);
    if (OPENSSL_init_crypto(OPENSSL_INIT_NO_LOAD_CONFIG, NULL) == 1) {
      ossl_reset_init_err(&had_mark); OSSL_LIB_CTX *fresh = OSSL_LIB_CTX_new();
      if (fresh != NULL) {
        if (OSSL_PROVIDER_load(fresh, "default") != NULL) { __atomic_store_n(&g_ossl_ctx, fresh, __ATOMIC_RELEASE); ctx = fresh; }
        else { OSSL_LIB_CTX_free(fresh); }
      }
    }
    if (ctx != NULL) { if (had_mark) ERR_pop_to_mark(); else ERR_clear_error(); }
    else if (had_mark) { ERR_clear_last_mark(); }
  }
  pthread_mutex_unlock(&g_ctx_mu); return ctx;
}
static const uint8_t *leanswe_ba_cptr(b_lean_obj_arg ba, size_t *out_len) {
  size_t len = lean_sarray_size(ba); *out_len = len; return len == 0 ? &g_empty_byte : lean_sarray_cptr(ba);
}
static lean_obj_res mk_bytes_result(uint32_t status, uint64_t code, const char *detail, lean_obj_res bytes) {
  lean_obj_res p3 = lean_alloc_ctor(0, 2, 0), p2 = lean_alloc_ctor(0, 2, 0), p1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p3, 0, lean_mk_string(detail != NULL ? detail : "")); lean_ctor_set(p3, 1, bytes);
  lean_ctor_set(p2, 0, lean_box_uint64(code)); lean_ctor_set(p2, 1, p3);
  lean_ctor_set(p1, 0, lean_box_uint32(status)); lean_ctor_set(p1, 1, p2); return p1;
}
static unsigned long ossl_prior_diff_err(const ossl_iso_t *iso) {
  const char *f = NULL, *fn = NULL, *d = NULL; int ln = 0, fl = 0;
  unsigned long last = ERR_peek_last_error_all(&f, &ln, &fn, &d, &fl);
  return (last == iso->prior_last_err && f == iso->prior_file && ln == iso->prior_line && fn == iso->prior_func && d == iso->prior_data && fl == iso->prior_flags) ? 0 : last;
}
static lean_obj_res mk_ossl_err_result(ossl_iso_t *iso, const char *fallback) {
  char buf[256] = {0}; int saved_errno = iso->saved_errno; unsigned long err = 0;
  if (iso->using_mark) {
#if LEANSWE_HAVE_ERR_STATE_SAVE || LEANSWE_CAN_WEAK_PROBE
    if (ossl_has_err_pop()) { while (ERR_count_to_mark() > 1) (void)ERR_pop(); err = ERR_count_to_mark() == 1 ? ERR_peek_last_error() : 0; }
    else if (ossl_has_count_mark()) { err = ERR_count_to_mark() > 0 ? ERR_peek_last_error() : 0; }
    else
#endif
    { err = ossl_prior_diff_err(iso); }
  } else { err = ERR_get_error(); }
  if (err != 0) { ERR_error_string_n(err, buf, sizeof(buf)); buf[sizeof(buf) - 1] = '\0'; }
  ossl_iso_leave(iso);
  if (buf[0] == '\0') snprintf(buf, sizeof(buf), "%s", fallback != NULL ? fallback : "openssl crypto error");
  lean_obj_res r = mk_bytes_result(3, (uint64_t)err, buf, lean_alloc_sarray(1, 0, 0)); errno = saved_errno; return r;
}
static lean_obj_res mk_ok_or_len_mismatch(uint8_t *out, size_t out_sz, size_t expected_len, size_t out_len, const char *label) {
  if (out_len != expected_len) {
    char msg[128]; OPENSSL_cleanse(out, out_sz); snprintf(msg, sizeof(msg), "%s length mismatch: expected %zu, got %zu", label, expected_len, out_len);
    return mk_bytes_result(2, 0, msg, lean_alloc_sarray(1, 0, 0));
  }
  lean_obj_res ba = lean_alloc_sarray(1, out_len, out_len);
  memcpy(lean_sarray_cptr(ba), out, out_len); OPENSSL_cleanse(out, out_sz); return mk_bytes_result(0, 0, "", ba);
}
LEAN_EXPORT lean_obj_res leanswe_cryptohash_digest(uint8_t alg_tag, b_lean_obj_arg data) {
  if (alg_tag > 1) { int se = errno; lean_obj_res r = mk_bytes_result(1, 0, "unknown digest algorithm tag", lean_alloc_sarray(1, 0, 0)); errno = se; return r; }
  ossl_iso_t iso = ossl_iso_enter(); OSSL_LIB_CTX *ctx = leanswe_ossl_ctx();
  if (ctx == NULL) return mk_ossl_err_result(&iso, "failed to initialize isolated OpenSSL context");
  size_t expected_len = alg_tag == 0 ? 32 : 64, data_len = 0, out_len = 0; const uint8_t *data_ptr = leanswe_ba_cptr(data, &data_len); uint8_t out[64] = {0};
  if (EVP_Q_digest(ctx, alg_tag == 0 ? "SHA256" : "SHA512", NULL, data_ptr, data_len, out, &out_len) != 1) { OPENSSL_cleanse(out, sizeof(out)); return mk_ossl_err_result(&iso, "EVP_Q_digest failed"); }
  ossl_iso_leave(&iso); lean_obj_res r = mk_ok_or_len_mismatch(out, sizeof(out), expected_len, out_len, "digest"); errno = iso.saved_errno; return r;
}
LEAN_EXPORT lean_obj_res leanswe_cryptohash_hmac_sha256(b_lean_obj_arg key, b_lean_obj_arg msg) {
  ossl_iso_t iso = ossl_iso_enter(); OSSL_LIB_CTX *ctx = leanswe_ossl_ctx();
  if (ctx == NULL) return mk_ossl_err_result(&iso, "failed to initialize isolated OpenSSL context");
  size_t key_len = 0, msg_len = 0, key_hash_len = 0, out_len = 0; const uint8_t *key_ptr = leanswe_ba_cptr(key, &key_len), *msg_ptr = leanswe_ba_cptr(msg, &msg_len);
  uint8_t key_hash[EVP_MAX_MD_SIZE] = {0}, out[64] = {0};
  if (key_len > 64) {
    if (EVP_Q_digest(ctx, "SHA256", NULL, key_ptr, key_len, key_hash, &key_hash_len) != 1 || key_hash_len != 32) { OPENSSL_cleanse(key_hash, sizeof(key_hash)); return mk_ossl_err_result(&iso, "EVP_Q_digest(HMAC key) failed"); }
    key_ptr = key_hash; key_len = 32;
  }
  if (EVP_Q_mac(ctx, "HMAC", NULL, "SHA256", NULL, key_ptr, key_len, msg_ptr, msg_len, out, sizeof(out), &out_len) == NULL) { OPENSSL_cleanse(key_hash, sizeof(key_hash)); OPENSSL_cleanse(out, sizeof(out)); return mk_ossl_err_result(&iso, "EVP_Q_mac(HMAC-SHA256) failed"); }
  ossl_iso_leave(&iso); OPENSSL_cleanse(key_hash, sizeof(key_hash));
  lean_obj_res r = mk_ok_or_len_mismatch(out, sizeof(out), 32, out_len, "HMAC-SHA256"); errno = iso.saved_errno; return r;
}
LEAN_EXPORT uint8_t leanswe_cryptohash_ct_equal(b_lean_obj_arg a, b_lean_obj_arg b) {
  size_t a_len = 0, b_len = 0; const uint8_t *a_ptr = leanswe_ba_cptr(a, &a_len), *b_ptr = leanswe_ba_cptr(b, &b_len);
  return a_len != b_len ? 0 : (CRYPTO_memcmp(a_ptr, b_ptr, a_len) == 0 ? 1 : 0);
}
