#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe LinuxSyscall requires Linux on x86_64 or aarch64"
#endif

#include <errno.h>
#include <lean/lean.h>
#include <netdb.h>
#include <netinet/in.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>

#ifdef EAI_ADDRFAMILY
#define DNS_EAI_ADDRFAMILY EAI_ADDRFAMILY
#else
#define DNS_EAI_ADDRFAMILY (-9)
#endif

static const char *dns_resolve_err_msg(int rc, uint32_t eno, char *buf, size_t bsz) {
  const char *msg = NULL;
  if (rc == EAI_SYSTEM && eno != 0u) {
#if defined(__GLIBC__) && defined(__USE_GNU)
    const char *m = strerror_r((int)eno, buf, bsz);
    if (m != NULL && m[0] != '\0') {
      msg = m;
    }
#else
    int sr = strerror_r((int)eno, buf, bsz);
    buf[bsz - 1u] = '\0';
    if ((sr == 0 || sr == ERANGE || sr == EINVAL) && buf[0] != '\0') {
      msg = buf;
    }
#endif
  }
  if (msg == NULL) {
    msg = gai_strerror(rc);
  }
  if (msg == NULL) {
    msg = "getaddrinfo failed";
  }
  return msg;
}

static lean_obj_res dns_err_obj(int rc, int raw_eno) {
  if (rc == EAI_SYSTEM && raw_eno == EFAULT) {
    abort();
  }
  uint32_t eno = 0u;
  if (rc == EAI_SYSTEM && raw_eno > 0) {
    eno = (uint32_t)raw_eno;
  }
  char buf[256];
  memset(buf, 0, sizeof(buf));
  const char *msg = dns_resolve_err_msg(rc, eno, buf, sizeof(buf));
  size_t mlen = strlen(msg);
  lean_obj_res mb = lean_alloc_sarray(1, mlen, mlen);
  if (mlen > 0u) {
    memcpy(lean_sarray_cptr(mb), msg, mlen);
  }
  lean_obj_res p2 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p2, 0, lean_box_uint32(eno));
  lean_ctor_set(p2, 1, mb);
  lean_obj_res p1 = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p1, 0, lean_box_uint32((uint32_t)(int32_t)rc));
  lean_ctor_set(p1, 1, p2);
  lean_obj_res r = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(r, 0, p1);
  return r;
}

static size_t dns_count_addrs(const struct addrinfo *res) {
  size_t n = 0;
  for (const struct addrinfo *ai = res; ai != NULL; ai = ai->ai_next) {
    if (ai->ai_family == AF_INET && ai->ai_addr != NULL && ai->ai_addrlen >= sizeof(struct sockaddr_in)) {
      n++;
    } else if (ai->ai_family == AF_INET6 && ai->ai_addr != NULL && ai->ai_addrlen >= sizeof(struct sockaddr_in6)) {
      n++;
    }
  }
  return n;
}

static void dns_copy_addrs(const struct addrinfo *res, uint8_t *dst) {
  for (const struct addrinfo *ai = res; ai != NULL; ai = ai->ai_next) {
    if (ai->ai_family == AF_INET && ai->ai_addr != NULL && ai->ai_addrlen >= sizeof(struct sockaddr_in)) {
      struct sockaddr_in s4;
      memcpy(&s4, ai->ai_addr, sizeof(s4));
      memset(dst, 0, 21u);
      dst[0] = 4u;
      memcpy(dst + 1, &s4.sin_addr.s_addr, 4u);
      dst += 21u;
    } else if (ai->ai_family == AF_INET6 && ai->ai_addr != NULL && ai->ai_addrlen >= sizeof(struct sockaddr_in6)) {
      struct sockaddr_in6 s6;
      memcpy(&s6, ai->ai_addr, sizeof(s6));
      uint32_t sc = s6.sin6_scope_id;
      dst[0] = 6u;
      memcpy(dst + 1, &s6.sin6_addr.s6_addr, 16u);
      dst[17] = (uint8_t)(sc & 0xffu);
      dst[18] = (uint8_t)((sc >> 8) & 0xffu);
      dst[19] = (uint8_t)((sc >> 16) & 0xffu);
      dst[20] = (uint8_t)((sc >> 24) & 0xffu);
      dst += 21u;
    }
  }
}

static lean_obj_res dns_pack_addrs(struct addrinfo *res) {
  size_t n = dns_count_addrs(res);
  if (n == 0u) {
    if (res != NULL) {
      freeaddrinfo(res);
    }
    return dns_err_obj(DNS_EAI_ADDRFAMILY, 0);
  }
  if (n > 65536u || n > SIZE_MAX / 21u) {
    freeaddrinfo(res);
    return dns_err_obj(EAI_MEMORY, 0);
  }
  lean_obj_res out = lean_alloc_sarray(1, n * 21u, n * 21u);
  dns_copy_addrs(res, lean_sarray_cptr(out));
  freeaddrinfo(res);
  lean_obj_res ok = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(ok, 0, out);
  return ok;
}

/** Single-call `getaddrinfo(3)` wrapper returning 21-byte `(tag, addr16, scope_id_le32)` records in `BaseIO`. */
LEAN_EXPORT lean_obj_res leanswe_sys_getaddrinfo(b_lean_obj_arg host, uint8_t family_hint, uint8_t socktype_hint) {
  size_t sz = lean_string_size(host);
  const char *chost = lean_string_cstr(host);
  if (sz <= 1u || strlen(chost) != sz - 1u) {
    return dns_err_obj(EAI_NONAME, 0);
  }
  if (family_hint > 2u) {
    return dns_err_obj(EAI_FAMILY, 0);
  }
  if (socktype_hint > 2u) {
    return dns_err_obj(EAI_SOCKTYPE, 0);
  }
  static const int k_fam[3] = { AF_UNSPEC, AF_INET, AF_INET6 };
  static const int k_sock[3] = { 0, SOCK_STREAM, SOCK_DGRAM };
  struct addrinfo hints;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family = k_fam[family_hint];
  hints.ai_socktype = k_sock[socktype_hint];
  struct addrinfo *res = NULL;
  errno = 0;
  int rc = getaddrinfo(chost, NULL, &hints, &res);
  if (rc != 0) {
    int eno = (rc == EAI_SYSTEM) ? errno : 0;
    return dns_err_obj(rc, eno);
  }
  return dns_pack_addrs(res);
}
