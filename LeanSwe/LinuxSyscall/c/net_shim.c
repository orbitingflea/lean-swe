#define _GNU_SOURCE
#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe.LinuxSyscall.Net requires Linux x86_64 or aarch64"
#endif

#include <arpa/inet.h>
#include <endian.h>
#include <errno.h>
#include <net/if.h>
#include <netinet/in.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
#include "fd_box.h"

#define LEANSWE_MAX_READ_BYTES (16u * 1024u * 1024u)
#define LEANSWE_MAX_SCM_FDS 32u

static inline lean_obj_res net_mk_pair(lean_obj_res a, lean_obj_res b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

static int decode_domain(uint32_t tag) {
  if (tag == 0u) return AF_INET;
  if (tag == 1u) return AF_INET6;
  if (tag == 2u) return AF_UNIX;
  return -1;
}

static int decode_sock_type(uint32_t tag) {
  if (tag == 0u) return SOCK_STREAM;
  if (tag == 1u) return SOCK_DGRAM;
  if (tag == 2u) return SOCK_SEQPACKET;
  return -1;
}

static int decode_sock_flags(uint32_t bits) {
  int f = 0;
  if (bits & (1u << 0)) f |= SOCK_NONBLOCK;
  if (bits & (1u << 1)) f |= SOCK_CLOEXEC;
  return f;
}

static int decode_msg_flags(uint32_t bits) {
  int f = 0;
  if (bits & (1u << 0)) f |= MSG_NOSIGNAL;
  if (bits & (1u << 1)) f |= MSG_DONTWAIT;
  if (bits & (1u << 2)) f |= MSG_PEEK;
  return f;
}

static int decode_shut_how(uint32_t tag) {
  if (tag == 0u) return SHUT_RD;
  if (tag == 1u) return SHUT_WR;
  if (tag == 2u) return SHUT_RDWR;
  return -1;
}

static int encode_unix_sockaddr(b_lean_obj_arg path_ba, struct sockaddr_storage *ss, socklen_t *out_len) {
  size_t len = lean_sarray_size(path_ba);
  const uint8_t *src = lean_sarray_cptr(path_ba);
  struct sockaddr_un *sun = (struct sockaddr_un *)ss;
  if (len == 0 || len > sizeof(sun->sun_path)) {
    return EINVAL;
  }
  if (src[0] != 0 && memchr(src, 0, len) != NULL) {
    return EINVAL;
  }
  sun->sun_family = AF_UNIX;
  memcpy(sun->sun_path, src, len);
  if (src[0] != 0 && len < sizeof(sun->sun_path)) {
    sun->sun_path[len] = '\0';
    *out_len = (socklen_t)(offsetof(struct sockaddr_un, sun_path) + len + 1);
  } else {
    *out_len = (socklen_t)(offsetof(struct sockaddr_un, sun_path) + len);
  }
  return 0;
}

static int encode_inet6_sockaddr(
    uint64_t hi, uint64_t lo, uint16_t port, uint32_t flow, uint32_t scope,
    struct sockaddr_storage *ss, socklen_t *out_len) {
  struct sockaddr_in6 *sin6 = (struct sockaddr_in6 *)ss;
  sin6->sin6_family = AF_INET6;
  sin6->sin6_port = htons(port);
  sin6->sin6_flowinfo = htonl(flow);
  sin6->sin6_scope_id = scope;
  uint64_t be_hi = htobe64(hi);
  uint64_t be_lo = htobe64(lo);
  memcpy(sin6->sin6_addr.s6_addr, &be_hi, 8);
  memcpy(sin6->sin6_addr.s6_addr + 8, &be_lo, 8);
  *out_len = (socklen_t)sizeof(*sin6);
  return 0;
}

static int encode_sockaddr(b_lean_obj_arg tup, struct sockaddr_storage *ss, socklen_t *out_len) {
  memset(ss, 0, sizeof(*ss));
  uint8_t tag = (uint8_t)lean_unbox(lean_ctor_get(tup, 0));
  b_lean_obj_arg t1 = lean_ctor_get(tup, 1);
  uint32_t v4 = lean_unbox_uint32(lean_ctor_get(t1, 0));
  b_lean_obj_arg t2 = lean_ctor_get(t1, 1);
  uint64_t hi = lean_unbox_uint64(lean_ctor_get(t2, 0));
  b_lean_obj_arg t3 = lean_ctor_get(t2, 1);
  uint64_t lo = lean_unbox_uint64(lean_ctor_get(t3, 0));
  b_lean_obj_arg t4 = lean_ctor_get(t3, 1);
  uint16_t port = (uint16_t)lean_unbox(lean_ctor_get(t4, 0));
  b_lean_obj_arg t5 = lean_ctor_get(t4, 1);
  uint32_t flow = lean_unbox_uint32(lean_ctor_get(t5, 0));
  b_lean_obj_arg t6 = lean_ctor_get(t5, 1);
  uint32_t scope = lean_unbox_uint32(lean_ctor_get(t6, 0));
  b_lean_obj_arg path_ba = lean_ctor_get(t6, 1);
  if (tag == 0u) {
    struct sockaddr_in *sin = (struct sockaddr_in *)ss;
    sin->sin_family = AF_INET;
    sin->sin_port = htons(port);
    sin->sin_addr.s_addr = htonl(v4);
    *out_len = (socklen_t)sizeof(*sin);
    return 0;
  }
  if (tag == 1u) return encode_inet6_sockaddr(hi, lo, port, flow, scope, ss, out_len);
  if (tag == 2u) return encode_unix_sockaddr(path_ba, ss, out_len);
  return EINVAL;
}

static lean_obj_res mk_raw_sockaddr_vals(
    uint8_t tag, uint32_t v4, uint64_t hi, uint64_t lo,
    uint16_t port, uint32_t flow, uint32_t scope, lean_obj_res path_ba) {
  return net_mk_pair(
      lean_box((unsigned)tag),
      net_mk_pair(
          lean_box_uint32(v4),
          net_mk_pair(
              lean_box_uint64(hi),
              net_mk_pair(
                  lean_box_uint64(lo),
                  net_mk_pair(
                      lean_box((unsigned)port),
                      net_mk_pair(
                          lean_box_uint32(flow),
                          net_mk_pair(lean_box_uint32(scope), path_ba)))))));
}

static lean_obj_res decode_unix_sockaddr(const struct sockaddr_storage *ss, socklen_t len) {
  const struct sockaddr_un *sun = (const struct sockaddr_un *)ss;
  socklen_t hdr = (socklen_t)offsetof(struct sockaddr_un, sun_path);
  size_t raw_len = 0u;
  if (ss->ss_family == AF_UNIX && len > hdr) {
    raw_len = (size_t)(len - hdr);
    if (raw_len > sizeof(sun->sun_path)) raw_len = sizeof(sun->sun_path);
  }
  size_t plen = (raw_len > 0u && sun->sun_path[0] != '\0') ? strnlen(sun->sun_path, raw_len) : raw_len;
  lean_obj_res ba = lean_alloc_sarray(1, plen, plen + 1);
  if (plen > 0) memcpy(lean_sarray_cptr(ba), sun->sun_path, plen);
  return mk_raw_sockaddr_vals(2u, 0u, 0u, 0u, 0u, 0u, 0u, ba);
}

static lean_obj_res decode_sockaddr(const struct sockaddr_storage *ss, socklen_t len) {
  if (ss->ss_family == AF_INET && len >= (socklen_t)sizeof(struct sockaddr_in)) {
    const struct sockaddr_in *sin = (const struct sockaddr_in *)ss;
    return mk_raw_sockaddr_vals(0u, ntohl(sin->sin_addr.s_addr), 0u, 0u,
                                ntohs(sin->sin_port), 0u, 0u, lean_alloc_sarray(1, 0, 1));
  }
  if (ss->ss_family == AF_INET6 && len >= (socklen_t)sizeof(struct sockaddr_in6)) {
    const struct sockaddr_in6 *sin6 = (const struct sockaddr_in6 *)ss;
    uint64_t be_hi = 0, be_lo = 0;
    memcpy(&be_hi, sin6->sin6_addr.s6_addr, 8);
    memcpy(&be_lo, sin6->sin6_addr.s6_addr + 8, 8);
    return mk_raw_sockaddr_vals(1u, 0u, be64toh(be_hi), be64toh(be_lo),
                                ntohs(sin6->sin6_port), ntohl(sin6->sin6_flowinfo),
                                sin6->sin6_scope_id, lean_alloc_sarray(1, 0, 1));
  }
  return decode_unix_sockaddr(ss, len);
}

static inline int net_pin_box(LeanFdBox *box, int *out_fd) {
  int err = leanswe_fd_box_pin(box, out_fd);
  return (err == EOVERFLOW) ? ENOMEM : err;
}

static int pin_scm_fds(b_lean_obj_arg fds_arr, int *raw_fds, size_t nfds, size_t *pinned_out) {
  for (size_t i = 0; i < nfds; i++) {
    LeanFdBox *box = (LeanFdBox *)lean_get_external_data(lean_array_get_core(fds_arr, i));
    int fd = -1;
    int perr = net_pin_box(box, &fd);
    if (perr != 0) {
      *pinned_out = i;
      return perr;
    }
    raw_fds[i] = fd;
  }
  *pinned_out = nfds;
  return 0;
}

static void unpin_scm_fds(b_lean_obj_arg fds_arr, size_t count) {
  for (size_t i = 0; i < count; i++) {
    LeanFdBox *box = (LeanFdBox *)lean_get_external_data(lean_array_get_core(fds_arr, i));
    leanswe_fd_box_unpin(box);
  }
}

static void close_raw_scm_fds(const uint8_t *raw_bytes, size_t start, size_t nfds) {
  for (size_t i = start; i < nfds; i++) {
    int rfd = -1;
    memcpy(&rfd, raw_bytes + i * sizeof(int), sizeof(int));
    if (rfd >= 0) close(rfd);
  }
}

static void close_all_scm_fds(struct msghdr *msg) {
  for (struct cmsghdr *cm = CMSG_FIRSTHDR(msg); cm != NULL; cm = CMSG_NXTHDR(msg, cm)) {
    if (cm->cmsg_level == SOL_SOCKET && cm->cmsg_type == SCM_RIGHTS) {
      size_t hdr_len = CMSG_LEN(0);
      size_t nfds = (cm->cmsg_len > hdr_len) ? (cm->cmsg_len - hdr_len) / sizeof(int) : 0u;
      close_raw_scm_fds((const uint8_t *)CMSG_DATA(cm), 0u, nfds);
    }
  }
}

static const struct cmsghdr *find_scm_rights_cmsg(struct msghdr *msg) {
  for (struct cmsghdr *cm = CMSG_FIRSTHDR(msg); cm != NULL; cm = CMSG_NXTHDR(msg, cm)) {
    if (cm->cmsg_level == SOL_SOCKET && cm->cmsg_type == SCM_RIGHTS) {
      return cm;
    }
  }
  return NULL;
}

static int box_scm_fds(const struct cmsghdr *cm, uint32_t max_fds, lean_obj_res *out_arr) {
  size_t hdr_len = CMSG_LEN(0);
  size_t nfds = (cm->cmsg_len > hdr_len) ? (cm->cmsg_len - hdr_len) / sizeof(int) : 0u;
  const uint8_t *raw_bytes = (const uint8_t *)CMSG_DATA(cm);
  if (nfds > (size_t)max_fds) {
    close_raw_scm_fds(raw_bytes, 0u, nfds);
    return EPROTO;
  }
  lean_obj_res arr = lean_mk_empty_array_with_capacity(lean_box(nfds));
  for (size_t i = 0; i < nfds; i++) {
    int rfd = -1;
    memcpy(&rfd, raw_bytes + i * sizeof(int), sizeof(int));
    lean_obj_res obj = leanswe_mk_fd_obj(rfd);
    if (obj == NULL) {
      lean_dec_ref(arr);
      close_raw_scm_fds(raw_bytes, i + 1u, nfds);
      return ENOMEM;
    }
    arr = lean_array_push(arr, obj);
  }
  *out_arr = arr;
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_sys_socket(
    uint32_t dom_tag, uint32_t type_tag, uint32_t flags_bits, uint32_t proto) {
  int dom = decode_domain(dom_tag);
  int stype = decode_sock_type(type_tag);
  if (dom < 0 || stype < 0) return leanswe_mk_errno(EINVAL);
  int fd = socket(dom, stype | decode_sock_flags(flags_bits), (int)proto);
  if (fd < 0) return leanswe_mk_errno(errno);
  lean_obj_res obj = leanswe_mk_fd_obj(fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}

LEAN_EXPORT lean_obj_res leanswe_sys_socketpair(
    uint32_t dom_tag, uint32_t type_tag, uint32_t flags_bits) {
  int dom = decode_domain(dom_tag);
  int stype = decode_sock_type(type_tag);
  if (dom < 0 || stype < 0) return leanswe_mk_errno(EINVAL);
  int fds[2] = {-1, -1};
  if (socketpair(dom, stype | decode_sock_flags(flags_bits), 0, fds) < 0) {
    return leanswe_mk_errno(errno);
  }
  lean_obj_res o0 = leanswe_mk_fd_obj(fds[0]);
  if (o0 == NULL) {
    close(fds[1]);
    return leanswe_mk_errno(ENOMEM);
  }
  lean_obj_res o1 = leanswe_mk_fd_obj(fds[1]);
  if (o1 == NULL) {
    lean_dec_ref(o0);
    return leanswe_mk_errno(ENOMEM);
  }
  return leanswe_mk_ok(net_mk_pair(o0, o1));
}

LEAN_EXPORT lean_obj_res leanswe_sys_bind(b_lean_obj_arg fd_obj, b_lean_obj_arg addr_tup) {
  struct sockaddr_storage ss;
  socklen_t slen = 0;
  int aerr = encode_sockaddr(addr_tup, &ss, &slen);
  if (aerr != 0) return leanswe_mk_errno(aerr);
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int rc = bind(fd, (const struct sockaddr *)&ss, slen);
  int err = (rc < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_listen(b_lean_obj_arg fd_obj, uint32_t backlog) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int rc = listen(fd, (int)backlog);
  int err = (rc < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_accept4(b_lean_obj_arg fd_obj, uint32_t flags_bits) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  struct sockaddr_storage ss;
  memset(&ss, 0, sizeof(ss));
  socklen_t slen = (socklen_t)sizeof(ss);
  int cfd = accept4(fd, (struct sockaddr *)&ss, &slen, decode_sock_flags(flags_bits));
  int err = (cfd < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (cfd < 0) return leanswe_mk_errno(err);
  lean_obj_res obj = leanswe_mk_fd_obj(cfd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(net_mk_pair(obj, decode_sockaddr(&ss, slen)));
}

LEAN_EXPORT lean_obj_res leanswe_sys_connect(b_lean_obj_arg fd_obj, b_lean_obj_arg addr_tup) {
  struct sockaddr_storage ss;
  socklen_t slen = 0;
  int aerr = encode_sockaddr(addr_tup, &ss, &slen);
  if (aerr != 0) return leanswe_mk_errno(aerr);
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int rc = connect(fd, (const struct sockaddr *)&ss, slen);
  int err = (rc < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_getsockopt(b_lean_obj_arg fd_obj, uint32_t opt_tag) {
  if (opt_tag > 1u) return leanswe_mk_errno(EINVAL);
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int val = 0;
  socklen_t len = (socklen_t)sizeof(val);
  int rc = getsockopt(fd, SOL_SOCKET, (opt_tag == 0u) ? SO_ERROR : SO_REUSEADDR, &val, &len);
  int err = (rc < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box_uint32((uint32_t)val));
}

LEAN_EXPORT lean_obj_res leanswe_sys_setsockopt(
    b_lean_obj_arg fd_obj, uint32_t opt_tag, uint32_t val) {
  if (opt_tag != 0u) return leanswe_mk_errno(EINVAL);
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int v = (int)val;
  int rc = setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &v, (socklen_t)sizeof(v));
  int err = (rc < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_getsockname(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  struct sockaddr_storage ss;
  memset(&ss, 0, sizeof(ss));
  socklen_t slen = (socklen_t)sizeof(ss);
  int rc = getsockname(fd, (struct sockaddr *)&ss, &slen);
  int err = (rc < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(decode_sockaddr(&ss, slen));
}

LEAN_EXPORT lean_obj_res leanswe_sys_recvfrom(
    b_lean_obj_arg fd_obj, uint32_t max_bytes, uint32_t flags_bits) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  size_t cap = (max_bytes > LEANSWE_MAX_READ_BYTES) ? LEANSWE_MAX_READ_BYTES : (size_t)max_bytes;
  uint8_t sbuf[4096];
  uint8_t *heap_buf = NULL;
  uint8_t *buf = sbuf;
  if (cap > sizeof(sbuf)) {
    heap_buf = (uint8_t *)malloc(cap);
    if (heap_buf == NULL) {
      leanswe_fd_box_unpin(box);
      return leanswe_mk_errno(ENOMEM);
    }
    buf = heap_buf;
  }
  ssize_t n = recvfrom(fd, buf, cap, decode_msg_flags(flags_bits), NULL, NULL);
  int err = (n < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (n < 0) {
    free(heap_buf);
    return leanswe_mk_errno(err);
  }
  size_t got = (size_t)n;
  lean_obj_res ba = lean_alloc_sarray(1, got, got);
  if (got > 0) memcpy(lean_sarray_cptr(ba), buf, got);
  free(heap_buf);
  return leanswe_mk_ok(ba);
}

LEAN_EXPORT lean_obj_res leanswe_sys_sendto(
    b_lean_obj_arg fd_obj, b_lean_obj_arg data_ba, uint32_t flags_bits) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  size_t len = lean_sarray_size(data_ba);
  const void *ptr = (len == 0) ? (const void *)"" : (const void *)lean_sarray_cptr(data_ba);
  ssize_t n = sendto(fd, ptr, len, decode_msg_flags(flags_bits), NULL, 0);
  int err = (n < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (n < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box_uint32((uint32_t)n));
}

LEAN_EXPORT lean_obj_res leanswe_sys_shutdown(b_lean_obj_arg fd_obj, uint32_t how_tag) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int rc = shutdown(fd, decode_shut_how(how_tag));
  int err = (rc < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

static void init_scm_send_msg(
    struct msghdr *msg, struct iovec *iov, char *cbuf, size_t cbuf_sz,
    const int *raw_fds, size_t nfds) {
  memset(cbuf, 0, cbuf_sz);
  memset(msg, 0, sizeof(*msg));
  msg->msg_iov = iov;
  msg->msg_iovlen = 1;
  msg->msg_control = cbuf;
  msg->msg_controllen = CMSG_SPACE(nfds * sizeof(int));
  struct cmsghdr *cm = CMSG_FIRSTHDR(msg);
  cm->cmsg_level = SOL_SOCKET;
  cm->cmsg_type = SCM_RIGHTS;
  cm->cmsg_len = CMSG_LEN(nfds * sizeof(int));
  memcpy(CMSG_DATA(cm), raw_fds, nfds * sizeof(int));
}

static int check_unix_socket_domain(int sfd) {
  int dom = 0;
  socklen_t dlen = (socklen_t)sizeof(dom);
  if (getsockopt(sfd, SOL_SOCKET, SO_DOMAIN, &dom, &dlen) < 0) return errno;
  return (dom == AF_UNIX) ? 0 : EOPNOTSUPP;
}

LEAN_EXPORT lean_obj_res leanswe_sys_sendmsg_scm(b_lean_obj_arg fd_obj, b_lean_obj_arg fds_arr) {
  size_t nfds = lean_array_size(fds_arr);
  if (nfds == 0 || nfds > LEANSWE_MAX_SCM_FDS) return leanswe_mk_errno(EINVAL);
  LeanFdBox *sbox = (LeanFdBox *)lean_get_external_data(fd_obj);
  int sfd = -1;
  int serr = net_pin_box(sbox, &sfd);
  if (serr != 0) return leanswe_mk_errno(serr);
  int raw_fds[LEANSWE_MAX_SCM_FDS];
  size_t pinned = 0;
  int perr = pin_scm_fds(fds_arr, raw_fds, nfds, &pinned);
  if (perr != 0) {
    unpin_scm_fds(fds_arr, pinned);
    leanswe_fd_box_unpin(sbox);
    return leanswe_mk_errno(perr);
  }
  int uerr = check_unix_socket_domain(sfd);
  if (uerr != 0) {
    unpin_scm_fds(fds_arr, nfds);
    leanswe_fd_box_unpin(sbox);
    return leanswe_mk_errno(uerr);
  }
  char dummy = 0;
  struct iovec iov = { &dummy, 1 };
  union {
    struct cmsghdr align;
    char buf[CMSG_SPACE(LEANSWE_MAX_SCM_FDS * sizeof(int))];
  } cbuf;
  struct msghdr msg;
  init_scm_send_msg(&msg, &iov, cbuf.buf, sizeof(cbuf.buf), raw_fds, nfds);
  ssize_t n = sendmsg(sfd, &msg, MSG_NOSIGNAL);
  int err = (n < 0) ? errno : 0;
  unpin_scm_fds(fds_arr, nfds);
  leanswe_fd_box_unpin(sbox);
  if (n < 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_sys_recvmsg_scm(b_lean_obj_arg fd_obj, uint32_t max_fds) {
  if (max_fds == 0u || max_fds > LEANSWE_MAX_SCM_FDS) return leanswe_mk_errno(EINVAL);
  LeanFdBox *sbox = (LeanFdBox *)lean_get_external_data(fd_obj);
  int sfd = -1;
  int serr = net_pin_box(sbox, &sfd);
  if (serr != 0) return leanswe_mk_errno(serr);
  char dummy = 0;
  struct iovec iov = { &dummy, 1 };
  union {
    struct cmsghdr align;
    char buf[CMSG_SPACE(LEANSWE_MAX_SCM_FDS * sizeof(int))];
  } cbuf;
  memset(&cbuf, 0, sizeof(cbuf));
  struct msghdr msg;
  memset(&msg, 0, sizeof(msg));
  msg.msg_iov = &iov;
  msg.msg_iovlen = 1;
  msg.msg_control = cbuf.buf;
  msg.msg_controllen = CMSG_LEN((size_t)max_fds * sizeof(int));
  ssize_t n = recvmsg(sfd, &msg, MSG_CMSG_CLOEXEC);
  int err = (n < 0) ? errno : 0;
  leanswe_fd_box_unpin(sbox);
  if (n < 0) return leanswe_mk_errno(err);
  if (msg.msg_flags & MSG_CTRUNC) {
    close_all_scm_fds(&msg);
    return leanswe_mk_errno(EPROTO);
  }
  const struct cmsghdr *cm = find_scm_rights_cmsg(&msg);
  if (cm == NULL) return leanswe_mk_ok(lean_mk_empty_array());
  lean_obj_res arr = NULL;
  int berr = box_scm_fds(cm, max_fds, &arr);
  if (berr != 0) return leanswe_mk_errno(berr);
  return leanswe_mk_ok(arr);
}

static int init_net_ifreq(uint32_t op_tag, uint32_t flags_arg, b_lean_obj_arg ifname_ba, struct ifreq *ifr) {
  if (op_tag > 1u) return EINVAL;
  size_t len = lean_sarray_size(ifname_ba);
  const uint8_t *src = lean_sarray_cptr(ifname_ba);
  if (len >= IFNAMSIZ || (len > 0 && memchr(src, 0, len) != NULL)) return EINVAL;
  memset(ifr, 0, sizeof(*ifr));
  if (len > 0) memcpy(ifr->ifr_name, src, len);
  if (op_tag == 1u) ifr->ifr_flags = (short)(uint16_t)(flags_arg & 0xffffu);
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_sys_net_ioctl(
    b_lean_obj_arg fd_obj, uint32_t op_tag, uint32_t flags_arg, b_lean_obj_arg ifname_ba) {
  struct ifreq ifr;
  int ierr = init_net_ifreq(op_tag, flags_arg, ifname_ba, &ifr);
  if (ierr != 0) return leanswe_mk_errno(ierr);
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1;
  int perr = net_pin_box(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int rc = ioctl(fd, (op_tag == 0u) ? SIOCGIFFLAGS : SIOCSIFFLAGS, &ifr);
  int err = (rc < 0) ? errno : 0;
  leanswe_fd_box_unpin(box);
  if (rc < 0) return leanswe_mk_errno(err);
  uint32_t res = (op_tag == 0u) ? (uint32_t)(uint16_t)ifr.ifr_flags : 0u;
  return leanswe_mk_ok(lean_box_uint32(res));
}
