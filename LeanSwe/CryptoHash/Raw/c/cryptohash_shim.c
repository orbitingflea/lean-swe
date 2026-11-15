#define _POSIX_C_SOURCE 200809L

#include <lean/lean.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/params.h>

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static const uint8_t g_empty_byte = 0;

static const uint8_t *leanswe_ba_cptr(b_lean_obj_arg ba, size_t *out_len) {
  size_t len = lean_sarray_size(ba);
  *out_len = len;
  return len == 0 ? &g_empty_byte : lean_sarray_cptr(ba);
}

static lean_obj_res mk_bytes_result(uint32_t status, uint64_t code,
                                    const char *detail, lean_obj_res bytes) {
  lean_obj_res p3 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p3, 0, lean_mk_string(detail != NULL ? detail : ""));
  lean_ctor_set(p3, 1, bytes);
  lean_obj_res p2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p2, 0, lean_box_uint64(code));
  lean_ctor_set(p2, 1, p3);
  lean_obj_res p1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p1, 0, lean_box_uint32(status));
  lean_ctor_set(p1, 1, p2);
  return lean_io_result_mk_ok(p1);
}

static lean_obj_res mk_bool_result(uint32_t status, uint64_t code,
                                   const char *detail, uint8_t val) {
  lean_obj_res p3 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p3, 0, lean_mk_string(detail != NULL ? detail : ""));
  lean_ctor_set(p3, 1, lean_box(val ? 1 : 0));
  lean_obj_res p2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p2, 0, lean_box_uint64(code));
  lean_ctor_set(p2, 1, p3);
  lean_obj_res p1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p1, 0, lean_box_uint32(status));
  lean_ctor_set(p1, 1, p2);
  return lean_io_result_mk_ok(p1);
}

static void capture_openssl_error(const char *fallback, uint64_t *out_code,
                                  char *buf, size_t buf_sz) {
  unsigned long err = ERR_get_error();
  while (ERR_get_error() != 0) {
  }
  *out_code = (uint64_t)err;
  if (err != 0) {
    ERR_error_string_n(err, buf, buf_sz);
    buf[buf_sz - 1] = '\0';
    if (buf[0] != '\0') {
      return;
    }
  }
  snprintf(buf, buf_sz, "%s", fallback != NULL ? fallback : "openssl crypto error");
}

LEAN_EXPORT lean_obj_res leanswe_cryptohash_digest(uint8_t alg_tag,
                                                   b_lean_obj_arg data,
                                                   lean_obj_arg w) {
  (void)w;
  const char *alg_name = NULL;
  size_t expected_len = 0;
  if (alg_tag == 0) {
    alg_name = "SHA256";
    expected_len = 32;
  } else if (alg_tag == 1) {
    alg_name = "SHA512";
    expected_len = 64;
  } else {
    return mk_bytes_result(1, 0, "unknown hash algorithm tag",
                           lean_alloc_sarray(1, 0, 0));
  }

  size_t data_len = 0;
  const uint8_t *data_ptr = leanswe_ba_cptr(data, &data_len);
  uint8_t out[64];
  size_t out_len = 0;

  ERR_clear_error();
  int ok = EVP_Q_digest(NULL, alg_name, NULL, data_ptr, data_len, out, &out_len);
  if (ok != 1) {
    uint64_t code = 0;
    char msg[256];
    capture_openssl_error("EVP_Q_digest failed", &code, msg, sizeof(msg));
    return mk_bytes_result(3, code, msg, lean_alloc_sarray(1, 0, 0));
  }
  if (out_len != expected_len) {
    char msg[128];
    snprintf(msg, sizeof(msg), "digest length mismatch: expected %zu, got %zu",
             expected_len, out_len);
    return mk_bytes_result(2, 0, msg, lean_alloc_sarray(1, 0, 0));
  }

  lean_obj_res ba = lean_alloc_sarray(1, out_len, out_len);
  memcpy(lean_sarray_cptr(ba), out, out_len);
  return mk_bytes_result(0, 0, "", ba);
}

LEAN_EXPORT lean_obj_res leanswe_cryptohash_hmac_sha256(b_lean_obj_arg key,
                                                        b_lean_obj_arg msg,
                                                        lean_obj_arg w) {
  (void)w;
  size_t key_len = 0;
  size_t msg_len = 0;
  const uint8_t *key_ptr = leanswe_ba_cptr(key, &key_len);
  const uint8_t *msg_ptr = leanswe_ba_cptr(msg, &msg_len);

  ERR_clear_error();
  EVP_MAC *mac = EVP_MAC_fetch(NULL, "HMAC", NULL);
  if (mac == NULL) {
    uint64_t code = 0;
    char errbuf[256];
    capture_openssl_error("EVP_MAC_fetch(HMAC) failed", &code, errbuf, sizeof(errbuf));
    return mk_bytes_result(3, code, errbuf, lean_alloc_sarray(1, 0, 0));
  }

  EVP_MAC_CTX *ctx = EVP_MAC_CTX_new(mac);
  if (ctx == NULL) {
    uint64_t code = 0;
    char errbuf[256];
    capture_openssl_error("EVP_MAC_CTX_new failed", &code, errbuf, sizeof(errbuf));
    EVP_MAC_free(mac);
    return mk_bytes_result(3, code, errbuf, lean_alloc_sarray(1, 0, 0));
  }

  char alg_buf[] = "SHA256";
  OSSL_PARAM params[2] = {
      OSSL_PARAM_construct_utf8_string("digest", alg_buf, 0),
      OSSL_PARAM_construct_end(),
  };

  uint8_t out[64];
  size_t out_len = 0;

  if (EVP_MAC_init(ctx, key_ptr, key_len, params) != 1 ||
      EVP_MAC_update(ctx, msg_ptr, msg_len) != 1 ||
      EVP_MAC_final(ctx, out, &out_len, sizeof(out)) != 1) {
    uint64_t code = 0;
    char errbuf[256];
    capture_openssl_error("HMAC-SHA256 operation failed", &code, errbuf, sizeof(errbuf));
    EVP_MAC_CTX_free(ctx);
    EVP_MAC_free(mac);
    return mk_bytes_result(3, code, errbuf, lean_alloc_sarray(1, 0, 0));
  }

  EVP_MAC_CTX_free(ctx);
  EVP_MAC_free(mac);

  if (out_len != 32) {
    char errbuf[128];
    snprintf(errbuf, sizeof(errbuf), "HMAC-SHA256 length mismatch: expected 32, got %zu",
             out_len);
    return mk_bytes_result(2, 0, errbuf, lean_alloc_sarray(1, 0, 0));
  }

  lean_obj_res ba = lean_alloc_sarray(1, 32, 32);
  memcpy(lean_sarray_cptr(ba), out, 32);
  return mk_bytes_result(0, 0, "", ba);
}

LEAN_EXPORT lean_obj_res leanswe_cryptohash_ct_equal(b_lean_obj_arg a,
                                                     b_lean_obj_arg b,
                                                     lean_obj_arg w) {
  (void)w;
  size_t a_len = 0;
  size_t b_len = 0;
  const uint8_t *a_ptr = leanswe_ba_cptr(a, &a_len);
  const uint8_t *b_ptr = leanswe_ba_cptr(b, &b_len);

  if (a_len != b_len) {
    char errbuf[128];
    snprintf(errbuf, sizeof(errbuf), "length mismatch: expected %zu bytes, got %zu",
             a_len, b_len);
    return mk_bool_result(2, 0, errbuf, 0);
  }

  int rc = CRYPTO_memcmp(a_ptr, b_ptr, a_len);
  return mk_bool_result(0, 0, "", rc == 0 ? 1 : 0);
}
