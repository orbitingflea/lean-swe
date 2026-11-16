#define _POSIX_C_SOURCE 200809L

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <limits.h>
#include <netdb.h>
#include <netinet/in.h>
#include <poll.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#define CPROXY_RING_CAP 16384u
#define CPROXY_INIT_HEAD_CAP 8192u
#define CPROXY_CLOSING_DRAIN_MAX 65536u
#define CPROXY_CLOSING_TIMEOUT_MAX_MS 250ULL
#define CPROXY_DNS_STACK_SIZE (256u * 1024u)
#define CPROXY_IP_REC_SIZE 17u

#define CPROXY_ERR_OK 0u
#define CPROXY_ERR_INVALID_ARG 1u
#define CPROXY_ERR_ADDR_IN_USE 2u
#define CPROXY_ERR_PERM_DENIED 3u
#define CPROXY_ERR_RES_EXHAUSTED 4u
#define CPROXY_ERR_OTHER 5u
#define CPROXY_ERR_USER 6u

#define CPROXY_OUTCOME_ALLOWED 0u
#define CPROXY_OUTCOME_DENIED 1u
#define CPROXY_OUTCOME_FAILED 2u

#ifdef MSG_NOSIGNAL
#define CPROXY_SEND_FLAGS MSG_NOSIGNAL
#else
#define CPROXY_SEND_FLAGS 0
#endif

static const char g_reply_200[] = "HTTP/1.1 200 Connection Established\r\n\r\n";
static const char g_reply_403[] = "HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\n\r\n";
static const char g_reply_502[] = "HTTP/1.1 502 Bad Gateway\r\nContent-Length: 0\r\n\r\n";

typedef enum SlotState {
  SLOT_HANDSHAKE = 0,
  SLOT_DNS = 1,
  SLOT_CONNECTING = 2,
  SLOT_RELAY = 3,
  SLOT_CLOSING_REPLY = 4
} SlotState;

typedef struct CEvent {
  uint8_t has_host;
  char *host;
  uint8_t has_port;
  uint16_t port;
  uint8_t outcome;
  uint8_t has_reason;
  char *reason;
} CEvent;

typedef struct DnsJob {
  pthread_mutex_t mu;
  int refs;
  int cancelled;
  int done;
  int notify_wfd;
  int gai_rc;
  int gai_errno;
  char *host;
  char err_msg[256];
  uint8_t *ips_buf;
  size_t ips_count;
} DnsJob;

typedef struct RingBuf {
  uint8_t data[CPROXY_RING_CAP];
  size_t head;
  size_t len;
} RingBuf;

typedef struct ClientSlot {
  int client_fd;
  int upstream_fd;
  SlotState state;
  uint8_t event_emitted;
  uint8_t has_target;
  char *host;
  uint16_t port;
  uint64_t deadline_ms;

  uint8_t *head_buf;
  size_t head_len;
  size_t head_cap;
  size_t head_off;

  DnsJob *job;

  uint8_t *candidates;
  size_t cand_count;
  size_t cand_idx;
  int last_connect_errno;

  RingBuf c2u;
  RingBuf u2c;
  uint8_t c_eof;
  uint8_t u_eof;
  uint8_t c_wr_closed;
  uint8_t u_wr_closed;

  const char *reply_ptr;
  size_t reply_len;
  size_t reply_off;
  uint8_t closing_shut_wr;
  size_t closing_drained;
} ClientSlot;

typedef struct ProxyInstance {
  uint64_t handle_id;
  int listen_fd;
  int notify_rfd;
  int notify_wfd;

  size_t max_header_bytes;
  uint64_t header_timeout_ms;
  uint64_t connect_timeout_ms;
  size_t max_tunnels;

  pthread_mutex_t mu;
  pthread_cond_t done_cv;
  int stop_requested;
  int stop_claimed;
  int loop_exited;

  ClientSlot **slots;
  size_t slots_len;
  size_t slots_cap;

  struct pollfd *pfds;
  size_t pfds_cap;

  CEvent *events;
  size_t events_len;
  size_t events_cap;

  struct ProxyInstance *next;
} ProxyInstance;

static pthread_mutex_t g_proxy_mu = PTHREAD_MUTEX_INITIALIZER;
static ProxyInstance *g_proxy_list = NULL;
static uint64_t g_next_handle_id = 1;
static size_t g_active_proxy_count = 0;

static uint64_t mono_now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000ULL + (uint64_t)(ts.tv_nsec / 1000000L);
}

static uint64_t deadline_after(uint64_t now, uint64_t delta) {
  return (delta > UINT64_MAX - now) ? UINT64_MAX : (now + delta);
}

static int set_nonblock(int fd) {
  int flags = fcntl(fd, F_GETFL, 0);
  if (flags < 0) {
    return -1;
  }
  return fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

static int set_cloexec(int fd) {
  int flags = fcntl(fd, F_GETFD, 0);
  if (flags < 0) {
    return -1;
  }
  return fcntl(fd, F_SETFD, flags | FD_CLOEXEC);
}

static void set_nosigpipe(int fd) {
#ifdef SO_NOSIGPIPE
  int one = 1;
  (void)setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof(one));
#else
  (void)fd;
#endif
}

static int create_nb_cloexec_socket(int family) {
  int fd = socket(family, SOCK_STREAM, 0);
  if (fd < 0) {
    return -1;
  }
  if (set_nonblock(fd) != 0 || set_cloexec(fd) != 0) {
    int err = errno;
    close(fd);
    errno = err;
    return -1;
  }
  set_nosigpipe(fd);
  return fd;
}

static void close_if_open(int *fd) {
  if (*fd >= 0) {
    close(*fd);
    *fd = -1;
  }
}

static uint32_t classify_errno_tag(int err) {
  if (err == EINVAL) {
    return CPROXY_ERR_INVALID_ARG;
  }
  if (err == EADDRINUSE) {
    return CPROXY_ERR_ADDR_IN_USE;
  }
  if (err == EACCES || err == EPERM) {
    return CPROXY_ERR_PERM_DENIED;
  }
  if (err == EMFILE || err == ENFILE || err == ENOMEM || err == ENOBUFS || err == EAGAIN) {
    return CPROXY_ERR_RES_EXHAUSTED;
  }
  return CPROXY_ERR_OTHER;
}

static lean_obj_res mk_pair(lean_obj_arg a, lean_obj_arg b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

static lean_obj_res mk_create_result(
    uint32_t tag, uint32_t code, const char *detail, uint64_t hid, uint16_t port) {
  lean_obj_res p4 = mk_pair(lean_box_uint64(hid), lean_box(port));
  lean_obj_res p3 = mk_pair(lean_mk_string(detail != NULL ? detail : ""), p4);
  lean_obj_res p2 = mk_pair(lean_box_uint32(code), p3);
  lean_obj_res p1 = mk_pair(lean_box_uint32(tag), p2);
  return lean_io_result_mk_ok(p1);
}

static lean_obj_res mk_event_tuple(const CEvent *ev) {
  lean_obj_res s_reason = lean_mk_string(ev->reason != NULL ? ev->reason : "");
  lean_obj_res p6 = mk_pair(lean_box(ev->has_reason), s_reason);
  lean_obj_res p5 = mk_pair(lean_box(ev->outcome), p6);
  lean_obj_res p4 = mk_pair(lean_box(ev->port), p5);
  lean_obj_res p3 = mk_pair(lean_box(ev->has_port), p4);
  lean_obj_res s_host = lean_mk_string(ev->host != NULL ? ev->host : "");
  lean_obj_res p2 = mk_pair(s_host, p3);
  return mk_pair(lean_box(ev->has_host), p2);
}

static lean_obj_res mk_stop_result(
    uint32_t tag, uint32_t code, const char *detail, lean_obj_arg events_arr) {
  lean_obj_res p3 = mk_pair(lean_mk_string(detail != NULL ? detail : ""), events_arr);
  lean_obj_res p2 = mk_pair(lean_box_uint32(code), p3);
  lean_obj_res p1 = mk_pair(lean_box_uint32(tag), p2);
  return lean_io_result_mk_ok(p1);
}

static ProxyInstance *find_proxy_locked(uint64_t hid) {
  ProxyInstance *cur = g_proxy_list;
  while (cur != NULL) {
    if (cur->handle_id == hid) {
      return cur;
    }
    cur = cur->next;
  }
  return NULL;
}

static void detach_proxy_locked(ProxyInstance *target) {
  ProxyInstance **prev = &g_proxy_list;
  while (*prev != NULL) {
    if (*prev == target) {
      *prev = target->next;
      target->next = NULL;
      if (g_active_proxy_count > 0) {
        g_active_proxy_count--;
      }
      return;
    }
    prev = &(*prev)->next;
  }
}

static void free_events(CEvent *events, size_t len) {
  if (events == NULL) {
    return;
  }
  for (size_t i = 0; i < len; i++) {
    free(events[i].host);
    free(events[i].reason);
  }
  free(events);
}

static void append_event(
    ProxyInstance *inst,
    uint8_t has_host,
    const char *host,
    uint8_t has_port,
    uint16_t port,
    uint8_t outcome,
    uint8_t has_reason,
    const char *reason) {
  if (inst->events_len == inst->events_cap) {
    size_t new_cap = (inst->events_cap == 0) ? 16u : inst->events_cap * 2u;
    if (new_cap <= inst->events_cap) {
      return;
    }
    CEvent *nb = (CEvent *)realloc(inst->events, new_cap * sizeof(CEvent));
    if (nb == NULL) {
      return;
    }
    inst->events = nb;
    inst->events_cap = new_cap;
  }
  CEvent *ev = &inst->events[inst->events_len++];
  ev->has_host = has_host;
  ev->host = (has_host && host != NULL) ? strdup(host) : NULL;
  ev->has_port = has_port;
  ev->port = port;
  ev->outcome = outcome;
  ev->has_reason = has_reason;
  ev->reason = (has_reason && reason != NULL) ? strdup(reason) : NULL;
}

static void emit_slot_event(
    ProxyInstance *inst,
    ClientSlot *slot,
    uint8_t has_host,
    const char *host,
    uint8_t has_port,
    uint16_t port,
    uint8_t outcome,
    uint8_t has_reason,
    const char *reason) {
  if (slot->event_emitted) {
    return;
  }
  slot->event_emitted = 1;
  append_event(inst, has_host, host, has_port, port, outcome, has_reason, reason);
}

static void dns_job_destroy(DnsJob *job) {
  pthread_mutex_destroy(&job->mu);
  free(job->host);
  free(job->ips_buf);
  free(job);
}

static void dns_job_release_server(DnsJob *job, int cancel) {
  if (job == NULL) {
    return;
  }
  pthread_mutex_lock(&job->mu);
  if (cancel) {
    job->cancelled = 1;
    job->notify_wfd = -1;
  }
  job->refs--;
  int should_free = (job->refs == 0);
  pthread_mutex_unlock(&job->mu);
  if (should_free) {
    dns_job_destroy(job);
  }
}

static void free_slot(ClientSlot *slot, int cancel_dns) {
  if (slot == NULL) {
    return;
  }
  if (slot->job != NULL) {
    dns_job_release_server(slot->job, cancel_dns);
    slot->job = NULL;
  }
  close_if_open(&slot->client_fd);
  close_if_open(&slot->upstream_fd);
  free(slot->host);
  free(slot->head_buf);
  free(slot->candidates);
  free(slot);
}

static void remove_slot_at(ProxyInstance *inst, size_t idx, int cancel_dns) {
  if (idx >= inst->slots_len) {
    return;
  }
  free_slot(inst->slots[idx], cancel_dns);
  if (idx + 1 < inst->slots_len) {
    memmove(&inst->slots[idx], &inst->slots[idx + 1],
            (inst->slots_len - idx - 1) * sizeof(ClientSlot *));
  }
  inst->slots_len--;
}

static int ensure_slot_capacity(ProxyInstance *inst) {
  if (inst->slots_len < inst->slots_cap) {
    return 0;
  }
  size_t new_cap = (inst->slots_cap == 0) ? 16u : inst->slots_cap * 2u;
  if (new_cap > inst->max_tunnels) {
    new_cap = inst->max_tunnels;
  }
  if (new_cap <= inst->slots_cap) {
    new_cap = inst->slots_len + 1u;
  }
  ClientSlot **ns = (ClientSlot **)realloc(inst->slots, new_cap * sizeof(ClientSlot *));
  if (ns == NULL) {
    return -1;
  }
  inst->slots = ns;
  inst->slots_cap = new_cap;
  return 0;
}

static int ensure_pfds_capacity(ProxyInstance *inst, size_t needed) {
  if (needed <= inst->pfds_cap) {
    return 0;
  }
  size_t new_cap = (inst->pfds_cap == 0) ? 32u : inst->pfds_cap * 2u;
  while (new_cap < needed) {
    new_cap *= 2u;
  }
  struct pollfd *np = (struct pollfd *)realloc(inst->pfds, new_cap * sizeof(struct pollfd));
  if (np == NULL) {
    return -1;
  }
  inst->pfds = np;
  inst->pfds_cap = new_cap;
  return 0;
}

static void ring_push(RingBuf *rb, const uint8_t *src, size_t n) {
  for (size_t i = 0; i < n; i++) {
    size_t pos = (rb->head + rb->len) % CPROXY_RING_CAP;
    rb->data[pos] = src[i];
    rb->len++;
  }
}

static size_t ring_write_avail(const RingBuf *rb) {
  return CPROXY_RING_CAP - rb->len;
}

static size_t ring_contig_read(const RingBuf *rb, const uint8_t **ptr_out) {
  *ptr_out = &rb->data[rb->head];
  size_t to_end = CPROXY_RING_CAP - rb->head;
  return (rb->len < to_end) ? rb->len : to_end;
}

static void ring_consume(RingBuf *rb, size_t n) {
  rb->head = (rb->head + n) % CPROXY_RING_CAP;
  rb->len -= n;
  if (rb->len == 0) {
    rb->head = 0;
  }
}

static void enter_closing_reply(ProxyInstance *inst, ClientSlot *slot, int status_code) {
  if (slot->job != NULL) {
    dns_job_release_server(slot->job, 1);
    slot->job = NULL;
  }
  close_if_open(&slot->upstream_fd);
  free(slot->head_buf);
  slot->head_buf = NULL;
  slot->head_len = 0;
  slot->head_cap = 0;
  free(slot->candidates);
  slot->candidates = NULL;
  slot->cand_count = 0;

  slot->state = SLOT_CLOSING_REPLY;
  if (status_code == 403) {
    slot->reply_ptr = g_reply_403;
    slot->reply_len = sizeof(g_reply_403) - 1u;
  } else {
    slot->reply_ptr = g_reply_502;
    slot->reply_len = sizeof(g_reply_502) - 1u;
  }
  slot->reply_off = 0;
  slot->closing_shut_wr = 0;
  slot->closing_drained = 0;

  uint64_t close_ms =
      (inst->header_timeout_ms < CPROXY_CLOSING_TIMEOUT_MAX_MS)
          ? inst->header_timeout_ms
          : CPROXY_CLOSING_TIMEOUT_MAX_MS;
  slot->deadline_ms = deadline_after(mono_now_ms(), close_ms);

  while (slot->reply_off < slot->reply_len) {
    ssize_t n = send(slot->client_fd, slot->reply_ptr + slot->reply_off,
                     slot->reply_len - slot->reply_off, CPROXY_SEND_FLAGS);
    if (n > 0) {
      slot->reply_off += (size_t)n;
    } else if (n < 0 && errno == EINTR) {
      continue;
    } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
      break;
    } else {
      close_if_open(&slot->client_fd);
      return;
    }
  }
  if (slot->reply_off >= slot->reply_len) {
    if (shutdown(slot->client_fd, SHUT_WR) != 0 && errno != ENOTCONN) {
      close_if_open(&slot->client_fd);
      return;
    }
    slot->closing_shut_wr = 1;
  }
}

static void enter_relay(ProxyInstance *inst, ClientSlot *slot) {
  emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                  CPROXY_OUTCOME_ALLOWED, 0, NULL);
  free(slot->candidates);
  slot->candidates = NULL;
  slot->cand_count = 0;

  slot->state = SLOT_RELAY;
  slot->c2u.head = 0;
  slot->c2u.len = 0;
  slot->u2c.head = 0;
  slot->u2c.len = 0;
  slot->c_eof = 0;
  slot->u_eof = 0;
  slot->c_wr_closed = 0;
  slot->u_wr_closed = 0;

  ring_push(&slot->u2c, (const uint8_t *)g_reply_200, sizeof(g_reply_200) - 1u);

  if (slot->head_off >= slot->head_len) {
    free(slot->head_buf);
    slot->head_buf = NULL;
    slot->head_len = 0;
    slot->head_cap = 0;
    slot->head_off = 0;
  }
}

static int is_ipv4_mapped_v6(const uint8_t *b16) {
  for (size_t i = 0; i < 10; i++) {
    if (b16[i] != 0) {
      return 0;
    }
  }
  return b16[10] == 0xff && b16[11] == 0xff;
}

static void start_next_connect(ProxyInstance *inst, ClientSlot *slot) {
  while (slot->cand_idx < slot->cand_count) {
    const uint8_t *rec = slot->candidates + (slot->cand_idx * CPROXY_IP_REC_SIZE);
    slot->cand_idx++;

    struct sockaddr_storage ss;
    socklen_t ss_len = 0;
    int family = 0;
    memset(&ss, 0, sizeof(ss));

    if (rec[0] == 4u) {
      struct sockaddr_in *sin = (struct sockaddr_in *)&ss;
      family = AF_INET;
      sin->sin_family = AF_INET;
      sin->sin_port = htons(slot->port);
      memcpy(&sin->sin_addr.s_addr, &rec[1], 4);
      ss_len = sizeof(*sin);
    } else if (rec[0] == 6u && is_ipv4_mapped_v6(&rec[1])) {
      struct sockaddr_in *sin = (struct sockaddr_in *)&ss;
      family = AF_INET;
      sin->sin_family = AF_INET;
      sin->sin_port = htons(slot->port);
      memcpy(&sin->sin_addr.s_addr, &rec[13], 4);
      ss_len = sizeof(*sin);
    } else if (rec[0] == 6u) {
      struct sockaddr_in6 *sin6 = (struct sockaddr_in6 *)&ss;
      family = AF_INET6;
      sin6->sin6_family = AF_INET6;
      sin6->sin6_port = htons(slot->port);
      memcpy(sin6->sin6_addr.s6_addr, &rec[1], 16);
      ss_len = sizeof(*sin6);
    } else {
      slot->last_connect_errno = EINVAL;
      continue;
    }

    int ufd = create_nb_cloexec_socket(family);
    if (ufd < 0) {
      slot->last_connect_errno = errno;
      continue;
    }

    int rc = connect(ufd, (struct sockaddr *)&ss, ss_len);
    if (rc == 0) {
      slot->upstream_fd = ufd;
      enter_relay(inst, slot);
      return;
    }
    if (errno == EINPROGRESS || errno == EINTR) {
      slot->upstream_fd = ufd;
      slot->state = SLOT_CONNECTING;
      slot->deadline_ms = deadline_after(mono_now_ms(), inst->connect_timeout_ms);
      return;
    }
    slot->last_connect_errno = errno;
    close(ufd);
  }

  const char *msg =
      slot->last_connect_errno != 0 ? strerror(slot->last_connect_errno) : "upstream connect failed";
  emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                  CPROXY_OUTCOME_FAILED, 1, msg);
  enter_closing_reply(inst, slot, 502);
}

static void handle_resolve_decision(
    ProxyInstance *inst,
    ClientSlot *slot,
    const uint8_t *ips_ptr,
    size_t ips_count,
    b_lean_obj_arg on_resolved_cb) {
  lean_obj_res host_obj = lean_mk_string(slot->host != NULL ? slot->host : "");
  size_t ips_bytes_len = ips_count * CPROXY_IP_REC_SIZE;
  lean_obj_res ips_ba = lean_alloc_sarray(1, ips_bytes_len, ips_bytes_len);
  if (ips_bytes_len > 0 && ips_ptr != NULL) {
    memcpy(lean_sarray_cptr(ips_ba), ips_ptr, ips_bytes_len);
  }

  lean_inc(on_resolved_cb);
  lean_obj_res res = lean_apply_3(on_resolved_cb, host_obj, lean_box(slot->port), ips_ba);

  uint8_t tag = (uint8_t)lean_unbox(lean_ctor_get(res, 0));
  b_lean_obj_arg p1 = lean_ctor_get(res, 1);
  b_lean_obj_arg reason_obj = lean_ctor_get(p1, 0);
  b_lean_obj_arg out_ba = lean_ctor_get(p1, 1);

  if (tag == 0u) {
    const char *reason = lean_string_cstr(reason_obj);
    emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                    CPROXY_OUTCOME_DENIED, 1,
                    (reason != NULL && reason[0] != '\0') ? reason : "resolved IP denied");
    lean_dec(res);
    enter_closing_reply(inst, slot, 403);
    return;
  }

  size_t out_len = lean_sarray_size(out_ba);
  size_t cand_count = out_len / CPROXY_IP_REC_SIZE;
  if (cand_count == 0) {
    lean_dec(res);
    emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                    CPROXY_OUTCOME_DENIED, 1, "no resolved IP address permitted by IpPolicy");
    enter_closing_reply(inst, slot, 403);
    return;
  }

  uint8_t *cands = (uint8_t *)malloc(cand_count * CPROXY_IP_REC_SIZE);
  if (cands == NULL) {
    lean_dec(res);
    emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                    CPROXY_OUTCOME_FAILED, 1, "out of memory");
    enter_closing_reply(inst, slot, 502);
    return;
  }
  memcpy(cands, lean_sarray_cptr(out_ba), cand_count * CPROXY_IP_REC_SIZE);
  lean_dec(res);

  slot->candidates = cands;
  slot->cand_count = cand_count;
  slot->cand_idx = 0;
  slot->last_connect_errno = 0;
  slot->state = SLOT_CONNECTING;
  start_next_connect(inst, slot);
}

static void *dns_worker_main(void *arg) {
  DnsJob *job = (DnsJob *)arg;
  struct addrinfo hints;
  struct addrinfo *res = NULL;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;

  int rc = getaddrinfo(job->host, NULL, &hints, &res);
  int saved_errno = errno;

  uint8_t *buf = NULL;
  size_t count = 0;
  if (rc == 0) {
    size_t total = 0;
    for (struct addrinfo *ai = res; ai != NULL; ai = ai->ai_next) {
      if (ai->ai_family == AF_INET && ai->ai_addrlen >= sizeof(struct sockaddr_in)) {
        total++;
      } else if (ai->ai_family == AF_INET6 && ai->ai_addrlen >= sizeof(struct sockaddr_in6)) {
        const struct sockaddr_in6 *sin6 = (const struct sockaddr_in6 *)ai->ai_addr;
        if (sin6->sin6_scope_id == 0) {
          total++;
        }
      }
    }
    if (total > 0) {
      buf = (uint8_t *)calloc(total, CPROXY_IP_REC_SIZE);
      if (buf == NULL) {
        rc = EAI_MEMORY;
        saved_errno = ENOMEM;
      } else {
        for (struct addrinfo *ai = res; ai != NULL; ai = ai->ai_next) {
          if (ai->ai_family == AF_INET && ai->ai_addrlen >= sizeof(struct sockaddr_in)) {
            const struct sockaddr_in *sin = (const struct sockaddr_in *)ai->ai_addr;
            uint8_t *dst = buf + (count * CPROXY_IP_REC_SIZE);
            dst[0] = 4u;
            memcpy(&dst[1], &sin->sin_addr.s_addr, 4);
            count++;
          } else if (ai->ai_family == AF_INET6 && ai->ai_addrlen >= sizeof(struct sockaddr_in6)) {
            const struct sockaddr_in6 *sin6 = (const struct sockaddr_in6 *)ai->ai_addr;
            if (sin6->sin6_scope_id == 0) {
              uint8_t *dst = buf + (count * CPROXY_IP_REC_SIZE);
              dst[0] = 6u;
              memcpy(&dst[1], sin6->sin6_addr.s6_addr, 16);
              count++;
            }
          }
        }
      }
    }
    if (res != NULL) {
      freeaddrinfo(res);
    }
  }

  pthread_mutex_lock(&job->mu);
  job->gai_rc = rc;
  job->gai_errno = saved_errno;
  if (rc != 0) {
    const char *msg = (rc == EAI_SYSTEM && saved_errno != 0)
                          ? strerror(saved_errno)
                          : gai_strerror(rc);
    snprintf(job->err_msg, sizeof(job->err_msg), "%s",
             (msg != NULL && msg[0] != '\0') ? msg : "dns resolution failed");
    free(buf);
    job->ips_buf = NULL;
    job->ips_count = 0;
  } else {
    job->err_msg[0] = '\0';
    job->ips_buf = buf;
    job->ips_count = count;
  }
  job->done = 1;
  if (!job->cancelled && job->notify_wfd >= 0) {
    uint8_t wake = 'x';
    ssize_t wr = write(job->notify_wfd, &wake, 1);
    (void)wr;
  }
  job->refs--;
  int should_free = (job->refs == 0);
  pthread_mutex_unlock(&job->mu);

  if (should_free) {
    dns_job_destroy(job);
  }
  return NULL;
}

static void start_dns_lookup(ProxyInstance *inst, ClientSlot *slot, b_lean_obj_arg on_resolved_cb) {
  (void)on_resolved_cb;
  DnsJob *job = (DnsJob *)calloc(1, sizeof(DnsJob));
  if (job == NULL) {
    emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                    CPROXY_OUTCOME_FAILED, 1, "out of memory");
    enter_closing_reply(inst, slot, 502);
    return;
  }
  if (pthread_mutex_init(&job->mu, NULL) != 0) {
    free(job);
    emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                    CPROXY_OUTCOME_FAILED, 1, "dns mutex init failed");
    enter_closing_reply(inst, slot, 502);
    return;
  }
  job->host = strdup(slot->host != NULL ? slot->host : "");
  if (job->host == NULL) {
    pthread_mutex_destroy(&job->mu);
    free(job);
    emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                    CPROXY_OUTCOME_FAILED, 1, "out of memory");
    enter_closing_reply(inst, slot, 502);
    return;
  }
  job->refs = 2;
  job->cancelled = 0;
  job->done = 0;
  job->notify_wfd = inst->notify_wfd;

  pthread_attr_t attr;
  int attr_rc = pthread_attr_init(&attr);
  if (attr_rc != 0) {
    dns_job_destroy(job);
    emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                    CPROXY_OUTCOME_FAILED, 1, strerror(attr_rc));
    enter_closing_reply(inst, slot, 502);
    return;
  }
  pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
  size_t stack_sz = CPROXY_DNS_STACK_SIZE;
#ifdef PTHREAD_STACK_MIN
  if ((size_t)PTHREAD_STACK_MIN > stack_sz) {
    stack_sz = (size_t)PTHREAD_STACK_MIN;
  }
#endif
  pthread_attr_setstacksize(&attr, stack_sz);

  pthread_t tid;
  int create_rc = pthread_create(&tid, &attr, dns_worker_main, job);
  pthread_attr_destroy(&attr);
  if (create_rc != 0) {
    dns_job_destroy(job);
    emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                    CPROXY_OUTCOME_FAILED, 1, strerror(create_rc));
    enter_closing_reply(inst, slot, 502);
    return;
  }

  slot->job = job;
  slot->state = SLOT_DNS;
}

static void handle_complete_head(
    ProxyInstance *inst,
    ClientSlot *slot,
    size_t head_end,
    b_lean_obj_arg on_head_cb,
    b_lean_obj_arg on_resolved_cb) {
  lean_obj_res head_ba = lean_alloc_sarray(1, head_end, head_end);
  memcpy(lean_sarray_cptr(head_ba), slot->head_buf, head_end);

  lean_inc(on_head_cb);
  lean_obj_res res = lean_apply_1(on_head_cb, head_ba);

  uint8_t tag = (uint8_t)lean_unbox(lean_ctor_get(res, 0));
  b_lean_obj_arg p1 = lean_ctor_get(res, 1);
  uint8_t has_host = (uint8_t)lean_unbox(lean_ctor_get(p1, 0));
  b_lean_obj_arg p2 = lean_ctor_get(p1, 1);
  const char *host = lean_string_cstr(lean_ctor_get(p2, 0));
  b_lean_obj_arg p3 = lean_ctor_get(p2, 1);
  uint8_t has_port = (uint8_t)lean_unbox(lean_ctor_get(p3, 0));
  b_lean_obj_arg p4 = lean_ctor_get(p3, 1);
  uint16_t port = (uint16_t)lean_unbox(lean_ctor_get(p4, 0));
  b_lean_obj_arg p5 = lean_ctor_get(p4, 1);
  const char *reason = lean_string_cstr(lean_ctor_get(p5, 0));
  b_lean_obj_arg lit_ba = lean_ctor_get(p5, 1);

  if (tag == 0u) {
    emit_slot_event(inst, slot,
                    has_host ? 1 : 0, has_host ? host : NULL,
                    has_port ? 1 : 0, has_port ? port : 0,
                    CPROXY_OUTCOME_DENIED, 1,
                    (reason != NULL && reason[0] != '\0') ? reason : "request denied");
    lean_dec(res);
    enter_closing_reply(inst, slot, 403);
    return;
  }

  slot->host = strdup(host != NULL ? host : "");
  if (slot->host == NULL) {
    lean_dec(res);
    emit_slot_event(inst, slot, 0, NULL, 1, port,
                    CPROXY_OUTCOME_FAILED, 1, "out of memory");
    enter_closing_reply(inst, slot, 502);
    return;
  }
  slot->has_target = 1;
  slot->port = port;

  size_t lit_size = lean_sarray_size(lit_ba);
  if (lit_size == CPROXY_IP_REC_SIZE) {
    uint8_t lit_rec[CPROXY_IP_REC_SIZE];
    memcpy(lit_rec, lean_sarray_cptr(lit_ba), CPROXY_IP_REC_SIZE);
    lean_dec(res);
    handle_resolve_decision(inst, slot, lit_rec, 1u, on_resolved_cb);
    return;
  }

  lean_dec(res);
  start_dns_lookup(inst, slot, on_resolved_cb);
}

static ssize_t find_crlfcrlf(const uint8_t *buf, size_t start, size_t len) {
  if (len < 4u) {
    return -1;
  }
  for (size_t i = start; i + 3u < len; i++) {
    if (buf[i] == 0x0du && buf[i + 1u] == 0x0au &&
        buf[i + 2u] == 0x0du && buf[i + 3u] == 0x0au) {
      return (ssize_t)i;
    }
  }
  return -1;
}

static void step_handshake_read(
    ProxyInstance *inst,
    ClientSlot *slot,
    b_lean_obj_arg on_head_cb,
    b_lean_obj_arg on_resolved_cb) {
  for (;;) {
    if (slot->head_len == slot->head_cap) {
      if (slot->head_len >= inst->max_header_bytes) {
        emit_slot_event(inst, slot, 0, NULL, 0, 0,
                        CPROXY_OUTCOME_DENIED, 1, "request head exceeds maxHeaderBytes");
        enter_closing_reply(inst, slot, 403);
        return;
      }
      size_t new_cap = 0;
      if (slot->head_cap == 0) {
        new_cap = (inst->max_header_bytes < CPROXY_INIT_HEAD_CAP)
                      ? inst->max_header_bytes
                      : CPROXY_INIT_HEAD_CAP;
      } else {
        new_cap = (slot->head_cap > SIZE_MAX / 2u) ? inst->max_header_bytes : slot->head_cap * 2u;
        if (new_cap > inst->max_header_bytes) {
          new_cap = inst->max_header_bytes;
        }
      }
      uint8_t *nb = (uint8_t *)realloc(slot->head_buf, new_cap);
      if (nb == NULL) {
        emit_slot_event(inst, slot, 0, NULL, 0, 0,
                        CPROXY_OUTCOME_FAILED, 1, "out of memory");
        enter_closing_reply(inst, slot, 502);
        return;
      }
      slot->head_buf = nb;
      slot->head_cap = new_cap;
    }

    ssize_t n = recv(slot->client_fd, slot->head_buf + slot->head_len,
                     slot->head_cap - slot->head_len, 0);
    if (n > 0) {
      size_t scan_from = (slot->head_len >= 3u) ? (slot->head_len - 3u) : 0u;
      slot->head_len += (size_t)n;
      ssize_t end_pos = find_crlfcrlf(slot->head_buf, scan_from, slot->head_len);
      if (end_pos >= 0) {
        size_t head_end = (size_t)end_pos + 4u;
        slot->head_off = head_end;
        handle_complete_head(inst, slot, head_end, on_head_cb, on_resolved_cb);
        return;
      }
      if (slot->head_len >= inst->max_header_bytes) {
        emit_slot_event(inst, slot, 0, NULL, 0, 0,
                        CPROXY_OUTCOME_DENIED, 1, "request head exceeds maxHeaderBytes");
        enter_closing_reply(inst, slot, 403);
        return;
      }
    } else if (n == 0) {
      emit_slot_event(inst, slot, 0, NULL, 0, 0,
                      CPROXY_OUTCOME_DENIED, 1, "client closed before completing CONNECT headers");
      enter_closing_reply(inst, slot, 403);
      return;
    } else {
      if (errno == EINTR) {
        continue;
      }
      if (errno == EAGAIN || errno == EWOULDBLOCK) {
        return;
      }
      emit_slot_event(inst, slot, 0, NULL, 0, 0,
                      CPROXY_OUTCOME_DENIED, 1, strerror(errno));
      enter_closing_reply(inst, slot, 403);
      return;
    }
  }
}

static void step_closing_reply(ProxyInstance *inst, ClientSlot *slot, short revents, uint64_t now) {
  (void)inst;
  if (slot->client_fd < 0) {
    return;
  }
  if (!slot->closing_shut_wr) {
    if (revents & (POLLERR | POLLHUP | POLLNVAL)) {
      close_if_open(&slot->client_fd);
      return;
    }
    if (revents & POLLOUT) {
      while (slot->reply_off < slot->reply_len) {
        ssize_t n = send(slot->client_fd, slot->reply_ptr + slot->reply_off,
                         slot->reply_len - slot->reply_off, CPROXY_SEND_FLAGS);
        if (n > 0) {
          slot->reply_off += (size_t)n;
        } else if (n < 0 && errno == EINTR) {
          continue;
        } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
          break;
        } else {
          close_if_open(&slot->client_fd);
          return;
        }
      }
      if (slot->reply_off >= slot->reply_len) {
        if (shutdown(slot->client_fd, SHUT_WR) != 0 && errno != ENOTCONN) {
          close_if_open(&slot->client_fd);
          return;
        }
        slot->closing_shut_wr = 1;
      }
    }
  }

  if (slot->closing_shut_wr && slot->client_fd >= 0 &&
      (revents & (POLLIN | POLLHUP | POLLERR | POLLNVAL))) {
    uint8_t drain[1024];
    for (;;) {
      ssize_t n = recv(slot->client_fd, drain, sizeof(drain), 0);
      if (n > 0) {
        slot->closing_drained += (size_t)n;
        if (slot->closing_drained >= CPROXY_CLOSING_DRAIN_MAX) {
          close_if_open(&slot->client_fd);
          return;
        }
      } else if (n == 0) {
        close_if_open(&slot->client_fd);
        return;
      } else {
        if (errno == EINTR) {
          continue;
        }
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
          break;
        }
        close_if_open(&slot->client_fd);
        return;
      }
    }
  }

  if (slot->client_fd >= 0 && now >= slot->deadline_ms) {
    close_if_open(&slot->client_fd);
  }
}

static int fd_has_so_error(int fd) {
  int err = 0;
  socklen_t len = sizeof(err);
  if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &len) != 0) {
    return 1;
  }
  return err != 0;
}

static void step_relay(ClientSlot *slot, short c_rev, short u_rev) {
  if ((c_rev & POLLNVAL) || (u_rev & POLLNVAL)) {
    close_if_open(&slot->client_fd);
    close_if_open(&slot->upstream_fd);
    return;
  }
  if (((c_rev & POLLERR) && fd_has_so_error(slot->client_fd)) ||
      ((u_rev & POLLERR) && fd_has_so_error(slot->upstream_fd))) {
    close_if_open(&slot->client_fd);
    close_if_open(&slot->upstream_fd);
    return;
  }

  if (slot->head_buf != NULL && (u_rev & (POLLOUT | POLLERR | POLLHUP))) {
    while (slot->head_off < slot->head_len) {
      ssize_t n = send(slot->upstream_fd, slot->head_buf + slot->head_off,
                       slot->head_len - slot->head_off, CPROXY_SEND_FLAGS);
      if (n > 0) {
        slot->head_off += (size_t)n;
      } else if (n < 0 && errno == EINTR) {
        continue;
      } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
        break;
      } else {
        close_if_open(&slot->client_fd);
        close_if_open(&slot->upstream_fd);
        return;
      }
    }
    if (slot->head_off >= slot->head_len) {
      free(slot->head_buf);
      slot->head_buf = NULL;
      slot->head_len = 0;
      slot->head_cap = 0;
      slot->head_off = 0;
    }
  }

  if (slot->head_buf == NULL && !slot->c_eof && ring_write_avail(&slot->c2u) > 0 &&
      (c_rev & (POLLIN | POLLHUP | POLLERR))) {
    for (;;) {
      size_t avail = ring_write_avail(&slot->c2u);
      if (avail == 0) {
        break;
      }
      uint8_t tmp[CPROXY_RING_CAP];
      size_t want = (avail < sizeof(tmp)) ? avail : sizeof(tmp);
      ssize_t n = recv(slot->client_fd, tmp, want, 0);
      if (n > 0) {
        ring_push(&slot->c2u, tmp, (size_t)n);
      } else if (n == 0) {
        slot->c_eof = 1;
        break;
      } else {
        if (errno == EINTR) {
          continue;
        }
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
          break;
        }
        close_if_open(&slot->client_fd);
        close_if_open(&slot->upstream_fd);
        return;
      }
    }
  }

  if (!slot->u_eof && ring_write_avail(&slot->u2c) > 0 &&
      (u_rev & (POLLIN | POLLHUP | POLLERR))) {
    for (;;) {
      size_t avail = ring_write_avail(&slot->u2c);
      if (avail == 0) {
        break;
      }
      uint8_t tmp[CPROXY_RING_CAP];
      size_t want = (avail < sizeof(tmp)) ? avail : sizeof(tmp);
      ssize_t n = recv(slot->upstream_fd, tmp, want, 0);
      if (n > 0) {
        ring_push(&slot->u2c, tmp, (size_t)n);
      } else if (n == 0) {
        slot->u_eof = 1;
        break;
      } else {
        if (errno == EINTR) {
          continue;
        }
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
          break;
        }
        close_if_open(&slot->client_fd);
        close_if_open(&slot->upstream_fd);
        return;
      }
    }
  }

  if (slot->head_buf == NULL && slot->c2u.len > 0 && !slot->u_wr_closed &&
      (u_rev & (POLLOUT | POLLERR | POLLHUP))) {
    while (slot->c2u.len > 0) {
      const uint8_t *ptr = NULL;
      size_t chunk = ring_contig_read(&slot->c2u, &ptr);
      ssize_t n = send(slot->upstream_fd, ptr, chunk, CPROXY_SEND_FLAGS);
      if (n > 0) {
        ring_consume(&slot->c2u, (size_t)n);
      } else if (n < 0 && errno == EINTR) {
        continue;
      } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
        break;
      } else {
        close_if_open(&slot->client_fd);
        close_if_open(&slot->upstream_fd);
        return;
      }
    }
  }

  if (slot->u2c.len > 0 && !slot->c_wr_closed &&
      (c_rev & (POLLOUT | POLLERR | POLLHUP))) {
    while (slot->u2c.len > 0) {
      const uint8_t *ptr = NULL;
      size_t chunk = ring_contig_read(&slot->u2c, &ptr);
      ssize_t n = send(slot->client_fd, ptr, chunk, CPROXY_SEND_FLAGS);
      if (n > 0) {
        ring_consume(&slot->u2c, (size_t)n);
      } else if (n < 0 && errno == EINTR) {
        continue;
      } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
        break;
      } else {
        close_if_open(&slot->client_fd);
        close_if_open(&slot->upstream_fd);
        return;
      }
    }
  }

  if (slot->c_eof && slot->head_buf == NULL && slot->c2u.len == 0 && !slot->u_wr_closed) {
    if (shutdown(slot->upstream_fd, SHUT_WR) != 0 && errno != ENOTCONN) {
      close_if_open(&slot->client_fd);
      close_if_open(&slot->upstream_fd);
      return;
    }
    slot->u_wr_closed = 1;
  }

  if (slot->u_eof && slot->u2c.len == 0 && !slot->c_wr_closed) {
    if (shutdown(slot->client_fd, SHUT_WR) != 0 && errno != ENOTCONN) {
      close_if_open(&slot->client_fd);
      close_if_open(&slot->upstream_fd);
      return;
    }
    slot->c_wr_closed = 1;
  }

  if (slot->client_fd >= 0 && slot->c_eof && slot->c_wr_closed) {
    close_if_open(&slot->client_fd);
  }
  if (slot->upstream_fd >= 0 && slot->u_eof && slot->u_wr_closed) {
    close_if_open(&slot->upstream_fd);
  }
}

static void accept_new_clients(ProxyInstance *inst, uint64_t now) {
  while (inst->slots_len < inst->max_tunnels) {
    int cfd = accept(inst->listen_fd, NULL, NULL);
    if (cfd < 0) {
      if (errno == EINTR) {
        continue;
      }
      break;
    }
    (void)set_nonblock(cfd);
    (void)set_cloexec(cfd);
    set_nosigpipe(cfd);

    if (ensure_slot_capacity(inst) != 0) {
      ssize_t wr = send(cfd, g_reply_502, sizeof(g_reply_502) - 1u, CPROXY_SEND_FLAGS);
      (void)wr;
      close(cfd);
      append_event(inst, 0, NULL, 0, 0, CPROXY_OUTCOME_FAILED, 1, "out of memory");
      break;
    }

    ClientSlot *slot = (ClientSlot *)calloc(1, sizeof(ClientSlot));
    if (slot == NULL) {
      ssize_t wr = send(cfd, g_reply_502, sizeof(g_reply_502) - 1u, CPROXY_SEND_FLAGS);
      (void)wr;
      close(cfd);
      append_event(inst, 0, NULL, 0, 0, CPROXY_OUTCOME_FAILED, 1, "out of memory");
      break;
    }

    slot->client_fd = cfd;
    slot->upstream_fd = -1;
    slot->state = SLOT_HANDSHAKE;
    slot->deadline_ms = deadline_after(now, inst->header_timeout_ms);
    inst->slots[inst->slots_len++] = slot;
  }
}

static void drain_notify_pipe(int rfd) {
  uint8_t buf[256];
  for (;;) {
    ssize_t n = read(rfd, buf, sizeof(buf));
    if (n > 0) {
      continue;
    }
    if (n < 0 && errno == EINTR) {
      continue;
    }
    break;
  }
}

LEAN_EXPORT lean_obj_res leanswe_cproxy_create(
    uint16_t listen_port,
    uint64_t max_header_bytes,
    uint64_t header_timeout_ms,
    uint64_t connect_timeout_ms,
    uint64_t max_concurrent_tunnels,
    lean_obj_arg w) {
  (void)w;
  if (max_header_bytes == 0 || header_timeout_ms == 0 ||
      connect_timeout_ms == 0 || max_concurrent_tunnels == 0) {
    return mk_create_result(CPROXY_ERR_INVALID_ARG, EINVAL,
                            "proxy limits must be positive", 0, 0);
  }

  int lfd = create_nb_cloexec_socket(AF_INET);
  if (lfd < 0) {
    int err = errno;
    return mk_create_result(classify_errno_tag(err), (uint32_t)err, strerror(err), 0, 0);
  }

  int one = 1;
  if (setsockopt(lfd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one)) != 0) {
    int err = errno;
    close(lfd);
    return mk_create_result(classify_errno_tag(err), (uint32_t)err, strerror(err), 0, 0);
  }

  struct sockaddr_in addr;
  memset(&addr, 0, sizeof(addr));
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = htons(listen_port);

  if (bind(lfd, (struct sockaddr *)&addr, sizeof(addr)) != 0) {
    int err = errno;
    close(lfd);
    return mk_create_result(classify_errno_tag(err), (uint32_t)err, strerror(err), 0, 0);
  }

  if (listen(lfd, 128) != 0) {
    int err = errno;
    close(lfd);
    return mk_create_result(classify_errno_tag(err), (uint32_t)err, strerror(err), 0, 0);
  }

  struct sockaddr_in bound_addr;
  socklen_t bound_len = sizeof(bound_addr);
  memset(&bound_addr, 0, sizeof(bound_addr));
  if (getsockname(lfd, (struct sockaddr *)&bound_addr, &bound_len) != 0) {
    int err = errno;
    close(lfd);
    return mk_create_result(classify_errno_tag(err), (uint32_t)err, strerror(err), 0, 0);
  }
  uint16_t bound_port = ntohs(bound_addr.sin_port);
  if (bound_port == 0) {
    close(lfd);
    return mk_create_result(CPROXY_ERR_OTHER, EINVAL, "getsockname returned port 0", 0, 0);
  }

  int pfd[2] = {-1, -1};
  if (pipe(pfd) != 0) {
    int err = errno;
    close(lfd);
    return mk_create_result(classify_errno_tag(err), (uint32_t)err, strerror(err), 0, 0);
  }
  (void)set_nonblock(pfd[0]);
  (void)set_nonblock(pfd[1]);
  (void)set_cloexec(pfd[0]);
  (void)set_cloexec(pfd[1]);

  ProxyInstance *inst = (ProxyInstance *)calloc(1, sizeof(ProxyInstance));
  if (inst == NULL) {
    close(pfd[0]);
    close(pfd[1]);
    close(lfd);
    return mk_create_result(CPROXY_ERR_RES_EXHAUSTED, ENOMEM, "out of memory", 0, 0);
  }

  if (pthread_mutex_init(&inst->mu, NULL) != 0) {
    free(inst);
    close(pfd[0]);
    close(pfd[1]);
    close(lfd);
    return mk_create_result(CPROXY_ERR_RES_EXHAUSTED, ENOMEM, "mutex init failed", 0, 0);
  }
  if (pthread_cond_init(&inst->done_cv, NULL) != 0) {
    pthread_mutex_destroy(&inst->mu);
    free(inst);
    close(pfd[0]);
    close(pfd[1]);
    close(lfd);
    return mk_create_result(CPROXY_ERR_RES_EXHAUSTED, ENOMEM, "cond init failed", 0, 0);
  }

  inst->listen_fd = lfd;
  inst->notify_rfd = pfd[0];
  inst->notify_wfd = pfd[1];
  inst->max_header_bytes =
      (max_header_bytes > (uint64_t)SIZE_MAX) ? SIZE_MAX : (size_t)max_header_bytes;
  inst->header_timeout_ms = header_timeout_ms;
  inst->connect_timeout_ms = connect_timeout_ms;
  inst->max_tunnels =
      (max_concurrent_tunnels > (uint64_t)SIZE_MAX) ? SIZE_MAX : (size_t)max_concurrent_tunnels;

  pthread_mutex_lock(&g_proxy_mu);
  uint64_t hid = g_next_handle_id++;
  inst->handle_id = hid;
  inst->next = g_proxy_list;
  g_proxy_list = inst;
  g_active_proxy_count++;
  pthread_mutex_unlock(&g_proxy_mu);

  return mk_create_result(CPROXY_ERR_OK, 0, "", hid, bound_port);
}

LEAN_EXPORT lean_obj_res leanswe_cproxy_run_loop(
    uint64_t handle_id,
    b_lean_obj_arg on_head_cb,
    b_lean_obj_arg on_resolved_cb,
    lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proxy_mu);
  ProxyInstance *inst = find_proxy_locked(handle_id);
  pthread_mutex_unlock(&g_proxy_mu);
  if (inst == NULL) {
    return lean_io_result_mk_ok(lean_box(0));
  }

  for (;;) {
    pthread_mutex_lock(&inst->mu);
    int stop = inst->stop_requested;
    pthread_mutex_unlock(&inst->mu);
    if (stop) {
      break;
    }

    size_t max_pfds = 2u + 2u * inst->slots_len;
    if (ensure_pfds_capacity(inst, max_pfds) != 0) {
      break;
    }

    nfds_t nfds = 0;
    size_t idx_notify = (size_t)nfds;
    inst->pfds[nfds].fd = inst->notify_rfd;
    inst->pfds[nfds].events = POLLIN;
    inst->pfds[nfds].revents = 0;
    nfds++;

    size_t idx_listen = (size_t)nfds;
    inst->pfds[nfds].fd = inst->listen_fd;
    inst->pfds[nfds].events = (inst->slots_len < inst->max_tunnels) ? POLLIN : 0;
    inst->pfds[nfds].revents = 0;
    nfds++;

    uint64_t now = mono_now_ms();
    uint64_t min_rem = UINT64_MAX;

    size_t *c_pfd_idx = (size_t *)calloc(inst->slots_len > 0 ? inst->slots_len : 1u, sizeof(size_t));
    size_t *u_pfd_idx = (size_t *)calloc(inst->slots_len > 0 ? inst->slots_len : 1u, sizeof(size_t));
    if (c_pfd_idx == NULL || u_pfd_idx == NULL) {
      free(c_pfd_idx);
      free(u_pfd_idx);
      break;
    }

    for (size_t i = 0; i < inst->slots_len; i++) {
      ClientSlot *slot = inst->slots[i];
      c_pfd_idx[i] = SIZE_MAX;
      u_pfd_idx[i] = SIZE_MAX;

      if (slot->client_fd >= 0) {
        short cev = 0;
        if (slot->state == SLOT_HANDSHAKE) {
          cev = POLLIN;
        } else if (slot->state == SLOT_RELAY) {
          if (slot->head_buf == NULL && !slot->c_eof && ring_write_avail(&slot->c2u) > 0) {
            cev |= POLLIN;
          }
          if (slot->u2c.len > 0 && !slot->c_wr_closed) {
            cev |= POLLOUT;
          }
        } else if (slot->state == SLOT_CLOSING_REPLY) {
          cev = slot->closing_shut_wr ? POLLIN : POLLOUT;
        }
        if (slot->state != SLOT_RELAY || cev != 0) {
          c_pfd_idx[i] = (size_t)nfds;
          inst->pfds[nfds].fd = slot->client_fd;
          inst->pfds[nfds].events = cev;
          inst->pfds[nfds].revents = 0;
          nfds++;
        }
      }

      if (slot->upstream_fd >= 0) {
        short uev = 0;
        if (slot->state == SLOT_CONNECTING) {
          uev = POLLOUT;
        } else if (slot->state == SLOT_RELAY) {
          if (!slot->u_eof && ring_write_avail(&slot->u2c) > 0) {
            uev |= POLLIN;
          }
          if ((slot->head_buf != NULL || slot->c2u.len > 0) && !slot->u_wr_closed) {
            uev |= POLLOUT;
          }
        }
        if (slot->state != SLOT_RELAY || uev != 0) {
          u_pfd_idx[i] = (size_t)nfds;
          inst->pfds[nfds].fd = slot->upstream_fd;
          inst->pfds[nfds].events = uev;
          inst->pfds[nfds].revents = 0;
          nfds++;
        }
      }

      if (slot->state == SLOT_HANDSHAKE || slot->state == SLOT_CONNECTING ||
          slot->state == SLOT_CLOSING_REPLY) {
        uint64_t rem = (slot->deadline_ms > now) ? (slot->deadline_ms - now) : 0ULL;
        if (rem < min_rem) {
          min_rem = rem;
        }
      }
    }

    int poll_to = -1;
    if (min_rem != UINT64_MAX) {
      poll_to = (min_rem > (uint64_t)INT_MAX) ? INT_MAX : (int)min_rem;
    }

    int prc = poll(inst->pfds, nfds, poll_to);
    if (prc < 0) {
      int err = errno;
      free(c_pfd_idx);
      free(u_pfd_idx);
      if (err == EINTR) {
        continue;
      }
      break;
    }

    if (inst->pfds[idx_notify].revents & POLLIN) {
      drain_notify_pipe(inst->notify_rfd);
    }

    pthread_mutex_lock(&inst->mu);
    stop = inst->stop_requested;
    pthread_mutex_unlock(&inst->mu);
    if (stop) {
      free(c_pfd_idx);
      free(u_pfd_idx);
      break;
    }

    now = mono_now_ms();
    size_t existing_len = inst->slots_len;

    for (size_t i = 0; i < existing_len; i++) {
      ClientSlot *slot = inst->slots[i];
      short c_rev = (c_pfd_idx[i] != SIZE_MAX) ? inst->pfds[c_pfd_idx[i]].revents : 0;
      short u_rev = (u_pfd_idx[i] != SIZE_MAX) ? inst->pfds[u_pfd_idx[i]].revents : 0;

      if (slot->state == SLOT_HANDSHAKE) {
        if (c_rev & (POLLIN | POLLHUP | POLLERR | POLLNVAL)) {
          step_handshake_read(inst, slot, on_head_cb, on_resolved_cb);
        }
        if (slot->state == SLOT_HANDSHAKE && slot->client_fd >= 0 && now >= slot->deadline_ms) {
          emit_slot_event(inst, slot, 0, NULL, 0, 0,
                          CPROXY_OUTCOME_DENIED, 1, "header timeout");
          enter_closing_reply(inst, slot, 403);
        }
      } else if (slot->state == SLOT_DNS) {
        if (c_rev & (POLLERR | POLLHUP | POLLNVAL)) {
          emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                          CPROXY_OUTCOME_FAILED, 1, "client disconnected");
          close_if_open(&slot->client_fd);
          dns_job_release_server(slot->job, 1);
          slot->job = NULL;
        } else if (slot->job != NULL) {
          pthread_mutex_lock(&slot->job->mu);
          int is_done = slot->job->done;
          pthread_mutex_unlock(&slot->job->mu);
          if (is_done) {
            DnsJob *job = slot->job;
            slot->job = NULL;
            if (job->gai_rc != 0) {
              emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                              CPROXY_OUTCOME_FAILED, 1, job->err_msg);
              dns_job_release_server(job, 0);
              enter_closing_reply(inst, slot, 502);
            } else {
              uint8_t *ips = job->ips_buf;
              size_t cnt = job->ips_count;
              handle_resolve_decision(inst, slot, ips, cnt, on_resolved_cb);
              dns_job_release_server(job, 0);
            }
          }
        }
      } else if (slot->state == SLOT_CONNECTING) {
        if (c_rev & (POLLERR | POLLHUP | POLLNVAL)) {
          emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                          CPROXY_OUTCOME_FAILED, 1, "client disconnected");
          close_if_open(&slot->upstream_fd);
          close_if_open(&slot->client_fd);
        } else if (u_rev & (POLLOUT | POLLERR | POLLHUP | POLLNVAL)) {
          int so_err = 0;
          socklen_t slen = sizeof(so_err);
          if (getsockopt(slot->upstream_fd, SOL_SOCKET, SO_ERROR, &so_err, &slen) != 0) {
            so_err = errno;
          }
          if (so_err == 0 && (u_rev & POLLOUT) && !(u_rev & (POLLERR | POLLNVAL))) {
            enter_relay(inst, slot);
          } else {
            slot->last_connect_errno = (so_err != 0) ? so_err : ECONNREFUSED;
            close_if_open(&slot->upstream_fd);
            start_next_connect(inst, slot);
          }
        } else if (now >= slot->deadline_ms) {
          slot->last_connect_errno = ETIMEDOUT;
          close_if_open(&slot->upstream_fd);
          start_next_connect(inst, slot);
        }
      } else if (slot->state == SLOT_RELAY) {
        step_relay(slot, c_rev, u_rev);
      } else if (slot->state == SLOT_CLOSING_REPLY) {
        step_closing_reply(inst, slot, c_rev, now);
      }
    }

    free(c_pfd_idx);
    free(u_pfd_idx);

    for (size_t i = 0; i < inst->slots_len;) {
      ClientSlot *slot = inst->slots[i];
      if (slot->client_fd < 0 && slot->upstream_fd < 0 && slot->job == NULL) {
        remove_slot_at(inst, i, 0);
      } else {
        i++;
      }
    }

    if (inst->pfds[idx_listen].revents & POLLIN) {
      accept_new_clients(inst, now);
    }
  }

  for (size_t i = 0; i < inst->slots_len; i++) {
    ClientSlot *slot = inst->slots[i];
    if (!slot->event_emitted) {
      if (slot->has_target) {
        emit_slot_event(inst, slot, 1, slot->host, 1, slot->port,
                        CPROXY_OUTCOME_FAILED, 1, "proxy stopped");
      } else {
        emit_slot_event(inst, slot, 0, NULL, 0, 0,
                        CPROXY_OUTCOME_FAILED, 1, "proxy stopped");
      }
    }
    free_slot(slot, 1);
  }
  free(inst->slots);
  inst->slots = NULL;
  inst->slots_len = 0;
  inst->slots_cap = 0;
  free(inst->pfds);
  inst->pfds = NULL;
  inst->pfds_cap = 0;

  close_if_open(&inst->listen_fd);

  pthread_mutex_lock(&inst->mu);
  close_if_open(&inst->notify_rfd);
  close_if_open(&inst->notify_wfd);
  inst->loop_exited = 1;
  pthread_cond_broadcast(&inst->done_cv);
  pthread_mutex_unlock(&inst->mu);

  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_cproxy_stop(uint64_t handle_id, lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proxy_mu);
  ProxyInstance *inst = find_proxy_locked(handle_id);
  if (inst == NULL || inst->stop_claimed) {
    pthread_mutex_unlock(&g_proxy_mu);
    return mk_stop_result(CPROXY_ERR_INVALID_ARG, EINVAL,
                          "proxy handle is not active", lean_alloc_array(0, 0));
  }
  inst->stop_claimed = 1;
  pthread_mutex_unlock(&g_proxy_mu);

  pthread_mutex_lock(&inst->mu);
  inst->stop_requested = 1;
  if (!inst->loop_exited && inst->notify_wfd >= 0) {
    uint8_t wake = 's';
    ssize_t wr = write(inst->notify_wfd, &wake, 1);
    (void)wr;
  }
  while (!inst->loop_exited) {
    pthread_cond_wait(&inst->done_cv, &inst->mu);
  }
  pthread_mutex_unlock(&inst->mu);

  lean_obj_res arr = lean_alloc_array(inst->events_len, inst->events_len);
  for (size_t i = 0; i < inst->events_len; i++) {
    lean_array_set_core(arr, i, mk_event_tuple(&inst->events[i]));
  }

  pthread_mutex_lock(&g_proxy_mu);
  detach_proxy_locked(inst);
  pthread_mutex_unlock(&g_proxy_mu);

  free_events(inst->events, inst->events_len);
  pthread_cond_destroy(&inst->done_cv);
  pthread_mutex_destroy(&inst->mu);
  free(inst);

  return mk_stop_result(CPROXY_ERR_OK, 0, "", arr);
}

LEAN_EXPORT lean_obj_res leanswe_cproxy_active_count(lean_obj_arg w) {
  (void)w;
  pthread_mutex_lock(&g_proxy_mu);
  size_t count = g_active_proxy_count;
  pthread_mutex_unlock(&g_proxy_mu);
  return lean_io_result_mk_ok(lean_usize_to_nat(count));
}
