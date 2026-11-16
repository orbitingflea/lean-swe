#define _GNU_SOURCE

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#ifdef __linux__

#include <arpa/inet.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/landlock.h>
#include <linux/seccomp.h>
#include <net/if.h>
#include <netinet/in.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>

extern char **environ;

#ifndef __NR_clone3
#define __NR_clone3 435
#endif
#ifndef __NR_close_range
#define __NR_close_range 436
#endif
#ifndef __NR_getdents64
#if defined(__x86_64__)
#define __NR_getdents64 217
#elif defined(__aarch64__)
#define __NR_getdents64 61
#endif
#endif

#ifndef __NR_landlock_create_ruleset
#define __NR_landlock_create_ruleset 444
#endif
#ifndef __NR_landlock_add_rule
#define __NR_landlock_add_rule 445
#endif
#ifndef __NR_landlock_restrict_self
#define __NR_landlock_restrict_self 446
#endif

#ifndef __NR_seccomp
#define __NR_seccomp 317
#endif

#ifndef AF_SMC
#define AF_SMC 43
#endif

#ifndef MSG_FASTOPEN
#define MSG_FASTOPEN 0x20000000U
#endif

#ifndef __X32_SYSCALL_BIT
#define __X32_SYSCALL_BIT 0x40000000U
#endif

#define PS_LL_FS_EXECUTE (1ULL << 0)
#define PS_LL_FS_WRITE_FILE (1ULL << 1)
#define PS_LL_FS_READ_FILE (1ULL << 2)
#define PS_LL_FS_READ_DIR (1ULL << 3)
#define PS_LL_FS_TRUNCATE (1ULL << 14)
#define PS_LL_FS_V4_ALL ((1ULL << 15) - 1ULL)
#define PS_LL_FS_FILE_ONLY (PS_LL_FS_EXECUTE | PS_LL_FS_WRITE_FILE | PS_LL_FS_READ_FILE | PS_LL_FS_TRUNCATE)
#define PS_LL_NET_BIND_TCP (1ULL << 0)
#define PS_LL_NET_CONNECT_TCP (1ULL << 1)

#define PS_STATUS_READY 1
#define PS_STATUS_INIT_ERR 2
#define PS_STATUS_EXEC_ERR 3
#define PS_STATUS_EXITED 4
#define PS_STATUS_SIGNALED 5

#define PS_INIT_MAX_PLAN_BYTES (16U * 1024U * 1024U)
#define PS_CLONE_NEW_NS_MASK 0x7e020000U

struct psandbox_ll_ruleset_attr {
  uint64_t handled_access_fs;
  uint64_t handled_access_net;
};

struct psandbox_ll_net_port_attr {
  uint64_t allowed_access;
  uint64_t port;
};

typedef struct InitStatusMsg {
  uint8_t kind;
  uint8_t flag;
  uint8_t pad[2];
  int32_t value;
} InitStatusMsg;

typedef struct ParsedMount {
  uint8_t tag;
  char *host_path;
  char *box_path;
} ParsedMount;

typedef struct ParsedSysEntry {
  uint8_t tag;
  char *path;
  char *target;
} ParsedSysEntry;

typedef struct ParsedPortForward {
  uint16_t box_port;
  uint16_t host_port;
} ParsedPortForward;

typedef struct ParsedPlan {
  uint8_t allow_box_localhost;
  uint8_t has_file_size_max;
  uint64_t file_size_max_bytes;
  uint32_t landlock_min_abi;
  char *program;
  char *cwd;
  uint32_t argc;
  char **args;
  uint32_t envc;
  char **envp;
  uint32_t n_sys;
  ParsedSysEntry *sys;
  uint32_t n_etc;
  char **etc_paths;
  uint32_t n_masks;
  char **masks;
  uint32_t n_mounts;
  ParsedMount *mounts;
  uint32_t n_fwds;
  ParsedPortForward *fwds;
} ParsedPlan;

typedef struct BufReader {
  const uint8_t *data;
  size_t len;
  size_t pos;
} BufReader;

static int set_cloexec(int fd) {
  if (fd < 0) {
    return 0;
  }
  int flags = fcntl(fd, F_GETFD, 0);
  if (flags < 0) {
    return -1;
  }
  return fcntl(fd, F_SETFD, flags | FD_CLOEXEC);
}

static int write_all_fd(int fd, const void *buf, size_t len) {
  const uint8_t *p = (const uint8_t *)buf;
  size_t off = 0;
  while (off < len) {
    ssize_t n = write(fd, p + off, len - off);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

typedef struct InitDirent64 {
  uint64_t d_ino;
  int64_t d_off;
  uint16_t d_reclen;
  uint8_t d_type;
  char d_name[];
} InitDirent64;

static void close_guest_extra_fds(int keep_fd) {
  if (keep_fd <= STDERR_FILENO) {
    (void)syscall(__NR_close_range, 3U, ~0U, 0U);
    return;
  }
  unsigned int k = (unsigned int)keep_fd;
  int ok1 = (k > 3U) ? (syscall(__NR_close_range, 3U, k - 1U, 0U) == 0) : 1;
  int ok2 = (syscall(__NR_close_range, k + 1U, ~0U, 0U) == 0);
  if (ok1 && ok2) {
    return;
  }
  int dirfd = open("/proc/self/fd", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  if (dirfd >= 0) {
    char buf[2048];
    for (;;) {
      long nread = syscall(__NR_getdents64, dirfd, buf, (long)sizeof(buf));
      if (nread <= 0) {
        break;
      }
      long pos = 0;
      while (pos < nread) {
        const InitDirent64 *d = (const InitDirent64 *)(buf + pos);
        if (d->d_reclen == 0) {
          pos = nread;
          break;
        }
        if (d->d_name[0] >= '0' && d->d_name[0] <= '9') {
          int fd = 0;
          int valid = 1;
          for (const char *p = d->d_name; *p != '\0'; p++) {
            if (*p < '0' || *p > '9' || fd > 100000000) {
              valid = 0;
              break;
            }
            fd = fd * 10 + (*p - '0');
          }
          if (valid && fd > STDERR_FILENO && fd != dirfd && fd != keep_fd) {
            close(fd);
          }
        }
        pos += d->d_reclen;
      }
    }
    close(dirfd);
    return;
  }
  long max_fd = sysconf(_SC_OPEN_MAX);
  if (max_fd <= 0 || max_fd > 65536L) {
    max_fd = 65536L;
  }
  for (int fd = 3; fd < (int)max_fd; fd++) {
    if (fd != keep_fd) {
      close(fd);
    }
  }
}

static void send_status(int fd, uint8_t kind, uint8_t flag, int32_t value) {
  if (fd < 0) {
    return;
  }
  InitStatusMsg msg;
  memset(&msg, 0, sizeof(msg));
  msg.kind = kind;
  msg.flag = flag;
  msg.value = value;
  (void)write_all_fd(fd, &msg, sizeof(msg));
}

static int read_u8(BufReader *r, uint8_t *out) {
  if (r->pos + 1 > r->len) {
    return -1;
  }
  *out = r->data[r->pos++];
  return 0;
}

static int read_u16(BufReader *r, uint16_t *out) {
  if (r->pos + 2 > r->len) {
    return -1;
  }
  *out = (uint16_t)r->data[r->pos] | ((uint16_t)r->data[r->pos + 1] << 8);
  r->pos += 2;
  return 0;
}

static int read_u32(BufReader *r, uint32_t *out) {
  if (r->pos + 4 > r->len) {
    return -1;
  }
  *out = (uint32_t)r->data[r->pos] |
         ((uint32_t)r->data[r->pos + 1] << 8) |
         ((uint32_t)r->data[r->pos + 2] << 16) |
         ((uint32_t)r->data[r->pos + 3] << 24);
  r->pos += 4;
  return 0;
}

static int read_u64(BufReader *r, uint64_t *out) {
  if (r->pos + 8 > r->len) {
    return -1;
  }
  uint64_t v = 0;
  for (int i = 0; i < 8; i++) {
    v |= ((uint64_t)r->data[r->pos + (size_t)i]) << (8 * i);
  }
  r->pos += 8;
  *out = v;
  return 0;
}

static int read_str(BufReader *r, char **out) {
  uint32_t slen = 0;
  if (read_u32(r, &slen) != 0) {
    return -1;
  }
  if (slen > r->len - r->pos) {
    return -1;
  }
  const uint8_t *src = r->data + r->pos;
  for (uint32_t i = 0; i < slen; i++) {
    if (src[i] == 0) {
      return -1;
    }
  }
  char *s = (char *)malloc((size_t)slen + 1);
  if (s == NULL) {
    return -1;
  }
  if (slen > 0) {
    memcpy(s, src, slen);
  }
  s[slen] = '\0';
  r->pos += slen;
  *out = s;
  return 0;
}

static int read_plan_fd(int plan_fd, uint8_t **buf_out, size_t *len_out) {
  size_t cap = 4096;
  size_t len = 0;
  uint8_t *buf = (uint8_t *)malloc(cap);
  if (buf == NULL) {
    return -1;
  }
  for (;;) {
    if (len == cap) {
      if (cap >= PS_INIT_MAX_PLAN_BYTES) {
        free(buf);
        errno = E2BIG;
        return -1;
      }
      size_t ncap = cap * 2;
      if (ncap > PS_INIT_MAX_PLAN_BYTES) {
        ncap = PS_INIT_MAX_PLAN_BYTES;
      }
      uint8_t *nb = (uint8_t *)realloc(buf, ncap);
      if (nb == NULL) {
        free(buf);
        return -1;
      }
      buf = nb;
      cap = ncap;
    }
    ssize_t n = read(plan_fd, buf + len, cap - len);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      free(buf);
      return -1;
    }
    if (n == 0) {
      break;
    }
    len += (size_t)n;
  }
  *buf_out = buf;
  *len_out = len;
  return 0;
}

static int parse_plan(const uint8_t *data, size_t len, ParsedPlan *p) {
  memset(p, 0, sizeof(*p));
  if (len < 8 || memcmp(data, "LSWP0001", 8) != 0) {
    errno = EINVAL;
    return -1;
  }
  BufReader r = {data, len, 8};

  uint8_t empty_root = 0, unshare_all = 0, mount_proc = 0, mount_dev = 0;
  uint8_t direct_cg = 0, block_unix = 0, allow_pair = 0, clone3_enosys = 0;
  uint8_t seccomp_deny = 0, no_new_privs = 0, rlimit_core0 = 0, subreaper = 0, clean_env = 0;
  uint64_t timeout_ms = 0, mem_max = 0, pids_max = 0, max_out = 0;
  uint8_t has_mem = 0, has_pids = 0, has_out = 0;

  if (read_u8(&r, &empty_root) != 0 ||
      read_u8(&r, &unshare_all) != 0 ||
      read_u8(&r, &mount_proc) != 0 ||
      read_u8(&r, &mount_dev) != 0 ||
      read_u8(&r, &direct_cg) != 0 ||
      read_u32(&r, &p->landlock_min_abi) != 0 ||
      read_u8(&r, &p->allow_box_localhost) != 0 ||
      read_u8(&r, &block_unix) != 0 ||
      read_u8(&r, &allow_pair) != 0 ||
      read_u8(&r, &clone3_enosys) != 0 ||
      read_u8(&r, &seccomp_deny) != 0 ||
      read_u8(&r, &no_new_privs) != 0 ||
      read_u8(&r, &rlimit_core0) != 0 ||
      read_u8(&r, &subreaper) != 0 ||
      read_u8(&r, &clean_env) != 0 ||
      read_u64(&r, &timeout_ms) != 0 ||
      read_u8(&r, &has_mem) != 0 || read_u64(&r, &mem_max) != 0 ||
      read_u8(&r, &has_pids) != 0 || read_u64(&r, &pids_max) != 0 ||
      read_u8(&r, &p->has_file_size_max) != 0 || read_u64(&r, &p->file_size_max_bytes) != 0 ||
      read_u8(&r, &has_out) != 0 || read_u64(&r, &max_out) != 0) {
    errno = EINVAL;
    return -1;
  }

  (void)timeout_ms;
  (void)has_mem;
  (void)mem_max;
  (void)has_pids;
  (void)pids_max;
  (void)has_out;
  (void)max_out;

  if (!empty_root || !unshare_all || !mount_proc || !mount_dev || !direct_cg ||
      p->landlock_min_abi < 4 || !block_unix || !allow_pair || !clone3_enosys ||
      !seccomp_deny || !no_new_privs || !rlimit_core0 || !subreaper || !clean_env) {
    errno = EINVAL;
    return -1;
  }

  if (read_str(&r, &p->program) != 0 || read_str(&r, &p->cwd) != 0) {
    errno = EINVAL;
    return -1;
  }

  if (read_u32(&r, &p->argc) != 0 || p->argc > 65536U) {
    errno = EINVAL;
    return -1;
  }
  p->args = (char **)calloc((size_t)p->argc, sizeof(char *));
  if (p->args == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->argc; i++) {
    if (read_str(&r, &p->args[i]) != 0) {
      errno = EINVAL;
      return -1;
    }
  }

  if (read_u32(&r, &p->envc) != 0 || p->envc > 65536U) {
    errno = EINVAL;
    return -1;
  }
  p->envp = (char **)calloc((size_t)p->envc + 1U, sizeof(char *));
  if (p->envp == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->envc; i++) {
    char *k = NULL, *v = NULL;
    if (read_str(&r, &k) != 0 || read_str(&r, &v) != 0) {
      free(k);
      free(v);
      errno = EINVAL;
      return -1;
    }
    size_t kl = strlen(k), vl = strlen(v);
    char *kv = (char *)malloc(kl + 1 + vl + 1);
    if (kv == NULL) {
      free(k);
      free(v);
      return -1;
    }
    memcpy(kv, k, kl);
    kv[kl] = '=';
    memcpy(kv + kl + 1, v, vl + 1);
    free(k);
    free(v);
    p->envp[i] = kv;
  }
  p->envp[p->envc] = NULL;

  if (read_u32(&r, &p->n_sys) != 0 || p->n_sys > 1024U) {
    errno = EINVAL;
    return -1;
  }
  p->sys = (ParsedSysEntry *)calloc((size_t)p->n_sys + 1U, sizeof(ParsedSysEntry));
  if (p->sys == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_sys; i++) {
    if (read_u8(&r, &p->sys[i].tag) != 0 || read_str(&r, &p->sys[i].path) != 0) {
      errno = EINVAL;
      return -1;
    }
    if (p->sys[i].tag == 1) {
      if (read_str(&r, &p->sys[i].target) != 0) {
        errno = EINVAL;
        return -1;
      }
    }
  }

  if (read_u32(&r, &p->n_etc) != 0 || p->n_etc > 1024U) {
    errno = EINVAL;
    return -1;
  }
  p->etc_paths = (char **)calloc((size_t)p->n_etc + 1U, sizeof(char *));
  if (p->etc_paths == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_etc; i++) {
    if (read_str(&r, &p->etc_paths[i]) != 0) {
      errno = EINVAL;
      return -1;
    }
  }

  if (read_u32(&r, &p->n_masks) != 0 || p->n_masks > 1024U) {
    errno = EINVAL;
    return -1;
  }
  p->masks = (char **)calloc((size_t)p->n_masks + 1U, sizeof(char *));
  if (p->masks == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_masks; i++) {
    if (read_str(&r, &p->masks[i]) != 0) {
      errno = EINVAL;
      return -1;
    }
  }

  if (read_u32(&r, &p->n_mounts) != 0 || p->n_mounts > 4096U) {
    errno = EINVAL;
    return -1;
  }
  p->mounts = (ParsedMount *)calloc((size_t)p->n_mounts + 1U, sizeof(ParsedMount));
  if (p->mounts == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_mounts; i++) {
    if (read_u8(&r, &p->mounts[i].tag) != 0) {
      errno = EINVAL;
      return -1;
    }
    if (p->mounts[i].tag == 0 || p->mounts[i].tag == 1) {
      if (read_str(&r, &p->mounts[i].host_path) != 0 ||
          read_str(&r, &p->mounts[i].box_path) != 0) {
        errno = EINVAL;
        return -1;
      }
    } else if (p->mounts[i].tag == 2) {
      if (read_str(&r, &p->mounts[i].box_path) != 0) {
        errno = EINVAL;
        return -1;
      }
    } else {
      errno = EINVAL;
      return -1;
    }
  }

  if (read_u32(&r, &p->n_fwds) != 0 || p->n_fwds > 1024U) {
    errno = EINVAL;
    return -1;
  }
  p->fwds = (ParsedPortForward *)calloc((size_t)p->n_fwds + 1U, sizeof(ParsedPortForward));
  if (p->fwds == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_fwds; i++) {
    if (read_u16(&r, &p->fwds[i].box_port) != 0 ||
        read_u16(&r, &p->fwds[i].host_port) != 0) {
      errno = EINVAL;
      return -1;
    }
  }

  if (r.pos != r.len) {
    errno = EINVAL;
    return -1;
  }
  return 0;
}

static int ensure_loopback_up(void) {
  int s = socket(AF_INET, SOCK_DGRAM | SOCK_CLOEXEC, 0);
  if (s < 0) {
    return -1;
  }
  struct ifreq ifr;
  memset(&ifr, 0, sizeof(ifr));
  strncpy(ifr.ifr_name, "lo", IFNAMSIZ - 1);
  if (ioctl(s, SIOCGIFFLAGS, &ifr) != 0) {
    int err = errno;
    close(s);
    errno = err;
    return -1;
  }
  if ((ifr.ifr_flags & IFF_UP) == 0) {
    ifr.ifr_flags |= IFF_UP | IFF_RUNNING;
    if (ioctl(s, SIOCSIFFLAGS, &ifr) != 0) {
      int err = errno;
      close(s);
      errno = err;
      return -1;
    }
  }
  close(s);
  return 0;
}

static int send_fds_scm(int ctrl_fd, const int *fds, uint32_t count) {
  uint32_t off = 0;
  while (off < count) {
    uint32_t batch = count - off;
    if (batch > 32U) {
      batch = 32U;
    }
    uint8_t dummy = 1;
    struct iovec iov;
    iov.iov_base = &dummy;
    iov.iov_len = 1;

    size_t cmsg_space = CMSG_SPACE((size_t)batch * sizeof(int));
    uint8_t *cbuf = (uint8_t *)calloc(1, cmsg_space);
    if (cbuf == NULL) {
      return -1;
    }

    struct msghdr msg;
    memset(&msg, 0, sizeof(msg));
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;
    msg.msg_control = cbuf;
    msg.msg_controllen = cmsg_space;

    struct cmsghdr *cmsg = CMSG_FIRSTHDR(&msg);
    cmsg->cmsg_level = SOL_SOCKET;
    cmsg->cmsg_type = SCM_RIGHTS;
    cmsg->cmsg_len = CMSG_LEN((size_t)batch * sizeof(int));
    memcpy(CMSG_DATA(cmsg), fds + off, (size_t)batch * sizeof(int));

    ssize_t sent = -1;
    for (;;) {
      sent = sendmsg(ctrl_fd, &msg, MSG_NOSIGNAL);
      if (sent < 0 && errno == EINTR) {
        continue;
      }
      break;
    }
    int err = errno;
    free(cbuf);
    if (sent <= 0) {
      errno = err ? err : EIO;
      return -1;
    }
    off += batch;
  }
  return 0;
}

static int setup_port_forwards(int ctrl_fd, const ParsedPlan *p) {
  if (p->n_fwds == 0) {
    return 0;
  }
  int *lfds = (int *)calloc((size_t)p->n_fwds, sizeof(int));
  if (lfds == NULL) {
    return -1;
  }
  for (uint32_t i = 0; i < p->n_fwds; i++) {
    lfds[i] = -1;
  }
  int rc = 0;
  for (uint32_t i = 0; i < p->n_fwds; i++) {
    int fd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
    if (fd < 0) {
      rc = -1;
      break;
    }
    int one = 1;
    (void)setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
    struct sockaddr_in sa;
    memset(&sa, 0, sizeof(sa));
    sa.sin_family = AF_INET;
    sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    sa.sin_port = htons(p->fwds[i].box_port);
    if (bind(fd, (struct sockaddr *)&sa, sizeof(sa)) != 0 || listen(fd, 128) != 0) {
      int err = errno;
      close(fd);
      errno = err;
      rc = -1;
      break;
    }
    lfds[i] = fd;
  }
  if (rc == 0) {
    rc = send_fds_scm(ctrl_fd, lfds, p->n_fwds);
  }
  int saved_err = errno;
  for (uint32_t i = 0; i < p->n_fwds; i++) {
    if (lfds[i] >= 0) {
      close(lfds[i]);
    }
  }
  free(lfds);
  errno = saved_err;
  return rc;
}

static int add_ll_path(int rs, const char *path, uint64_t access) {
  int fd = open(path, O_PATH | O_CLOEXEC);
  if (fd < 0) {
    return -1;
  }
  struct stat st;
  if (fstat(fd, &st) != 0) {
    int err = errno;
    close(fd);
    errno = err;
    return -1;
  }
  uint64_t eff = access;
  if (!S_ISDIR(st.st_mode)) {
    eff &= PS_LL_FS_FILE_ONLY;
  }
  if (eff != 0) {
    struct landlock_path_beneath_attr pb;
    memset(&pb, 0, sizeof(pb));
    pb.allowed_access = eff;
    pb.parent_fd = fd;
    if (syscall(__NR_landlock_add_rule, rs, LANDLOCK_RULE_PATH_BENEATH, &pb, 0) != 0) {
      int err = errno;
      close(fd);
      errno = err;
      return -1;
    }
  }
  close(fd);
  return 0;
}

static int install_landlock(const ParsedPlan *p) {
  long abi = syscall(__NR_landlock_create_ruleset, NULL, 0, LANDLOCK_CREATE_RULESET_VERSION);
  if (abi < 4) {
    if (abi >= 0) {
      errno = ENOSYS;
    }
    return -1;
  }
  struct psandbox_ll_ruleset_attr attr;
  memset(&attr, 0, sizeof(attr));
  attr.handled_access_fs = PS_LL_FS_V4_ALL;
  attr.handled_access_net = p->allow_box_localhost
                                ? 0ULL
                                : (PS_LL_NET_BIND_TCP | PS_LL_NET_CONNECT_TCP);
  int rs = (int)syscall(__NR_landlock_create_ruleset, &attr, sizeof(attr), 0);
  if (rs < 0) {
    return -1;
  }

  if (add_ll_path(rs, "/", PS_LL_FS_READ_DIR) != 0 ||
      add_ll_path(rs, "/proc", PS_LL_FS_READ_FILE | PS_LL_FS_READ_DIR) != 0 ||
      add_ll_path(rs, "/etc/hosts", PS_LL_FS_READ_FILE) != 0) {
    int err = errno;
    close(rs);
    errno = err;
    return -1;
  }

  if (add_ll_path(rs, "/dev", PS_LL_FS_READ_DIR) != 0) {
    int err = errno;
    close(rs);
    errno = err;
    return -1;
  }
  static const char *const k_safe_devs[] = {
    "/dev/null", "/dev/zero", "/dev/urandom", "/dev/tty", "/dev/ptmx", "/dev/pts"
  };
  for (size_t i = 0; i < sizeof(k_safe_devs) / sizeof(k_safe_devs[0]); i++) {
    if (add_ll_path(rs, k_safe_devs[i],
                    PS_LL_FS_READ_FILE | PS_LL_FS_WRITE_FILE | PS_LL_FS_TRUNCATE | PS_LL_FS_READ_DIR) != 0) {
      int err = errno;
      close(rs);
      errno = err;
      return -1;
    }
  }

  for (uint32_t i = 0; i < p->n_sys; i++) {
    if (p->sys[i].tag == 0) {
      if (add_ll_path(rs, p->sys[i].path,
                      PS_LL_FS_READ_FILE | PS_LL_FS_READ_DIR | PS_LL_FS_EXECUTE) != 0) {
        int err = errno;
        close(rs);
        errno = err;
        return -1;
      }
    }
  }

  for (uint32_t i = 0; i < p->n_etc; i++) {
    if (add_ll_path(rs, p->etc_paths[i],
                    PS_LL_FS_READ_FILE | PS_LL_FS_READ_DIR | PS_LL_FS_EXECUTE) != 0) {
      int err = errno;
      close(rs);
      errno = err;
      return -1;
    }
  }

  for (uint32_t i = 0; i < p->n_mounts; i++) {
    uint64_t acc = (p->mounts[i].tag == 0)
                       ? (PS_LL_FS_READ_FILE | PS_LL_FS_READ_DIR | PS_LL_FS_EXECUTE)
                       : PS_LL_FS_V4_ALL;
    if (add_ll_path(rs, p->mounts[i].box_path, acc) != 0) {
      int err = errno;
      close(rs);
      errno = err;
      return -1;
    }
  }

  if (!p->allow_box_localhost) {
    for (uint32_t i = 0; i < p->n_fwds; i++) {
      struct psandbox_ll_net_port_attr np;
      memset(&np, 0, sizeof(np));
      np.allowed_access = PS_LL_NET_CONNECT_TCP;
      np.port = (uint64_t)p->fwds[i].box_port;
      if (syscall(__NR_landlock_add_rule, rs, LANDLOCK_RULE_NET_PORT, &np, 0) != 0) {
        int err = errno;
        close(rs);
        errno = err;
        return -1;
      }
    }
  }

  if (syscall(__NR_landlock_restrict_self, rs, 0) != 0) {
    int err = errno;
    close(rs);
    errno = err;
    return -1;
  }
  close(rs);
  return 0;
}

static int install_seccomp(void) {
#if defined(__x86_64__)
  const uint32_t expected_arch = AUDIT_ARCH_X86_64;
#elif defined(__aarch64__)
  const uint32_t expected_arch = AUDIT_ARCH_AARCH64;
#else
#error "Unsupported Linux architecture for seccomp"
#endif

  struct sock_filter f[160];
  size_t n = 0;

  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, arch));
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, expected_arch, 1, 0);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM);

  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, nr));

#if defined(__x86_64__)
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JGE | BPF_K, __X32_SYSCALL_BIT, 0, 1);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM);
#endif

  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_clone3, 0, 1);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | ENOSYS);

  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_clone, 0, 5);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, args[0]));
  f[n++] = (struct sock_filter)BPF_STMT(BPF_ALU | BPF_AND | BPF_K, PS_CLONE_NEW_NS_MASK);
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, 0);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW);

#ifdef __NR_socket
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_socket, 0, 5);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, args[0]));
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AF_UNIX, 1, 0);
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AF_SMC, 0, 1);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW);
#endif

#ifdef __NR_socketpair
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_socketpair, 0, 10);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, args[0]));
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AF_UNIX, 0, 6);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, args[2]));
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 0, 4);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, args[1]));
  f[n++] = (struct sock_filter)BPF_STMT(BPF_ALU | BPF_AND | BPF_K, (uint32_t)(~(SOCK_CLOEXEC | SOCK_NONBLOCK)));
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SOCK_STREAM, 2, 0);
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SOCK_SEQPACKET, 1, 0);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW);
#endif

#ifdef __NR_sendto
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_sendto, 0, 5);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, args[3]));
  f[n++] = (struct sock_filter)BPF_STMT(BPF_ALU | BPF_AND | BPF_K, MSG_FASTOPEN);
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, 0);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW);
#endif

#ifdef __NR_sendmsg
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_sendmsg, 0, 5);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, args[2]));
  f[n++] = (struct sock_filter)BPF_STMT(BPF_ALU | BPF_AND | BPF_K, MSG_FASTOPEN);
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, 0);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW);
#endif

#ifdef __NR_sendmmsg
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_sendmmsg, 0, 5);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (uint32_t)offsetof(struct seccomp_data, args[3]));
  f[n++] = (struct sock_filter)BPF_STMT(BPF_ALU | BPF_AND | BPF_K, MSG_FASTOPEN);
  f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, 0);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM);
  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW);
#endif

  static const uint32_t k_deny_nrs[] = {
#ifdef __NR_reboot
    __NR_reboot,
#endif
#ifdef __NR_kexec_load
    __NR_kexec_load,
#endif
#ifdef __NR_kexec_file_load
    __NR_kexec_file_load,
#endif
#ifdef __NR_mount
    __NR_mount,
#endif
#ifdef __NR_umount2
    __NR_umount2,
#endif
#ifdef __NR_pivot_root
    __NR_pivot_root,
#endif
#ifdef __NR_swapon
    __NR_swapon,
#endif
#ifdef __NR_swapoff
    __NR_swapoff,
#endif
#ifdef __NR_fsmount
    __NR_fsmount,
#endif
#ifdef __NR_fsopen
    __NR_fsopen,
#endif
#ifdef __NR_fspick
    __NR_fspick,
#endif
#ifdef __NR_move_mount
    __NR_move_mount,
#endif
#ifdef __NR_open_tree
    __NR_open_tree,
#endif
#ifdef __NR_mount_setattr
    __NR_mount_setattr,
#endif
#ifdef __NR_init_module
    __NR_init_module,
#endif
#ifdef __NR_finit_module
    __NR_finit_module,
#endif
#ifdef __NR_delete_module
    __NR_delete_module,
#endif
#ifdef __NR_acct
    __NR_acct,
#endif
#ifdef __NR_settimeofday
    __NR_settimeofday,
#endif
#ifdef __NR_clock_settime
    __NR_clock_settime,
#endif
#ifdef __NR_clock_adjtime
    __NR_clock_adjtime,
#endif
#ifdef __NR_adjtimex
    __NR_adjtimex,
#endif
#ifdef __NR_bpf
    __NR_bpf,
#endif
#ifdef __NR_io_uring_setup
    __NR_io_uring_setup,
#endif
#ifdef __NR_io_uring_enter
    __NR_io_uring_enter,
#endif
#ifdef __NR_io_uring_register
    __NR_io_uring_register,
#endif
#ifdef __NR_keyctl
    __NR_keyctl,
#endif
#ifdef __NR_add_key
    __NR_add_key,
#endif
#ifdef __NR_request_key
    __NR_request_key,
#endif
#ifdef __NR_perf_event_open
    __NR_perf_event_open,
#endif
#ifdef __NR_userfaultfd
    __NR_userfaultfd,
#endif
#ifdef __NR_unshare
    __NR_unshare,
#endif
#ifdef __NR_setns
    __NR_setns,
#endif
  };

  for (size_t i = 0; i < sizeof(k_deny_nrs) / sizeof(k_deny_nrs[0]); i++) {
    f[n++] = (struct sock_filter)BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, k_deny_nrs[i], 0, 1);
    f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM);
  }

  f[n++] = (struct sock_filter)BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW);

  struct sock_fprog prog;
  prog.len = (unsigned short)n;
  prog.filter = f;
  if (syscall(__NR_seccomp, SECCOMP_SET_MODE_FILTER, 0, &prog) != 0) {
    if (errno != ENOSYS || prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog) != 0) {
      return -1;
    }
  }
  return 0;
}

static int parse_int_arg(const char *s) {
  char *end = NULL;
  long v = strtol(s, &end, 10);
  if (s[0] == '\0' || end == NULL || *end != '\0' || v < 0 || v > 1048576L) {
    return -1;
  }
  return (int)v;
}

int main(int argc, char **argv) {
  if (argc == 2 && strcmp(argv[1], "--probe") == 0) {
    return 0;
  }

  int plan_fd = -1, status_fd = -1, go_fd = -1, ctrl_fd = -1;
  for (int i = 1; i + 1 < argc; i += 2) {
    if (strcmp(argv[i], "--plan-fd") == 0) {
      plan_fd = parse_int_arg(argv[i + 1]);
    } else if (strcmp(argv[i], "--status-fd") == 0) {
      status_fd = parse_int_arg(argv[i + 1]);
    } else if (strcmp(argv[i], "--go-fd") == 0) {
      go_fd = parse_int_arg(argv[i + 1]);
    } else if (strcmp(argv[i], "--ctrl-fd") == 0) {
      ctrl_fd = parse_int_arg(argv[i + 1]);
    }
  }

  (void)set_cloexec(plan_fd);
  (void)set_cloexec(status_fd);
  (void)set_cloexec(go_fd);
  (void)set_cloexec(ctrl_fd);

  if (plan_fd < 0 || status_fd < 0 || go_fd < 0) {
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, EINVAL);
    return 1;
  }

  uint8_t *raw_plan = NULL;
  size_t raw_plan_len = 0;
  if (read_plan_fd(plan_fd, &raw_plan, &raw_plan_len) != 0) {
    int err = errno ? errno : EIO;
    close(plan_fd);
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }
  close(plan_fd);

  ParsedPlan plan;
  if (parse_plan(raw_plan, raw_plan_len, &plan) != 0) {
    int err = errno ? errno : EINVAL;
    free(raw_plan);
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }
  free(raw_plan);

  if (prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 ||
      prctl(PR_SET_CHILD_SUBREAPER, 1) != 0) {
    int err = errno ? errno : EPERM;
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }

  struct rlimit rcore;
  rcore.rlim_cur = 0;
  rcore.rlim_max = 0;
  if (setrlimit(RLIMIT_CORE, &rcore) != 0) {
    int err = errno ? errno : EPERM;
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }

  if (plan.has_file_size_max) {
    struct rlimit rf;
    rf.rlim_cur = (rlim_t)plan.file_size_max_bytes;
    rf.rlim_max = (rlim_t)plan.file_size_max_bytes;
    if (setrlimit(RLIMIT_FSIZE, &rf) != 0) {
      int err = errno ? errno : EPERM;
      send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
      return 1;
    }
  }

  if (ensure_loopback_up() != 0) {
    int err = errno ? errno : EIO;
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }

  if (plan.n_fwds > 0) {
    if (ctrl_fd < 0 || setup_port_forwards(ctrl_fd, &plan) != 0) {
      int err = errno ? errno : EIO;
      if (ctrl_fd >= 0) {
        close(ctrl_fd);
      }
      send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
      return 1;
    }
  }
  if (ctrl_fd >= 0) {
    close(ctrl_fd);
    ctrl_fd = -1;
  }

  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) {
    int err = errno ? errno : EPERM;
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }

  if (install_landlock(&plan) != 0) {
    int err = errno ? errno : EPERM;
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }

  if (install_seccomp() != 0) {
    int err = errno ? errno : EPERM;
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }

  char **guest_argv = (char **)calloc((size_t)plan.argc + 2U, sizeof(char *));
  if (guest_argv == NULL) {
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, ENOMEM);
    return 1;
  }
  guest_argv[0] = plan.program;
  for (uint32_t i = 0; i < plan.argc; i++) {
    guest_argv[i + 1] = plan.args[i];
  }
  guest_argv[plan.argc + 1] = NULL;

  send_status(status_fd, PS_STATUS_READY, 0, 0);

  uint8_t go_byte = 0;
  for (;;) {
    ssize_t gr = read(go_fd, &go_byte, 1);
    if (gr < 0 && errno == EINTR) {
      continue;
    }
    if (gr <= 0) {
      close(go_fd);
      close(status_fd);
      return 0;
    }
    break;
  }
  close(go_fd);

  int exec_err_pipe[2] = {-1, -1};
  if (pipe2(exec_err_pipe, O_CLOEXEC) != 0) {
    int err = errno ? errno : EIO;
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }

  pid_t child = fork();
  if (child < 0) {
    int err = errno ? errno : EAGAIN;
    close(exec_err_pipe[0]);
    close(exec_err_pipe[1]);
    send_status(status_fd, PS_STATUS_INIT_ERR, 0, err);
    return 1;
  }

  if (child == 0) {
    close(exec_err_pipe[0]);
    close(status_fd);
    close_guest_extra_fds(exec_err_pipe[1]);
    signal(SIGPIPE, SIG_DFL);

    if (clearenv() != 0) {
      int err = errno ? errno : ENOMEM;
      InitStatusMsg msg = {PS_STATUS_EXEC_ERR, 0, {0, 0}, err};
      (void)write_all_fd(exec_err_pipe[1], &msg, sizeof(msg));
      _exit(127);
    }
    environ = plan.envp;

    if (chdir(plan.cwd) != 0) {
      int err = errno ? errno : EIO;
      InitStatusMsg msg = {PS_STATUS_EXEC_ERR, 1, {0, 0}, err};
      (void)write_all_fd(exec_err_pipe[1], &msg, sizeof(msg));
      _exit(127);
    }

    execvp(plan.program, guest_argv);
    int err = errno ? errno : EIO;
    InitStatusMsg msg = {PS_STATUS_EXEC_ERR, 0, {0, 0}, err};
    (void)write_all_fd(exec_err_pipe[1], &msg, sizeof(msg));
    _exit(127);
  }

  close(exec_err_pipe[1]);
  close(STDIN_FILENO);
  close(STDOUT_FILENO);
  close(STDERR_FILENO);

  InitStatusMsg exec_msg;
  memset(&exec_msg, 0, sizeof(exec_msg));
  size_t got = 0;
  uint8_t *ep = (uint8_t *)&exec_msg;
  while (got < sizeof(exec_msg)) {
    ssize_t n = read(exec_err_pipe[0], ep + got, sizeof(exec_msg) - got);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      break;
    }
    if (n == 0) {
      break;
    }
    got += (size_t)n;
  }
  close(exec_err_pipe[0]);

  if (got > 0) {
    int st = 0;
    while (waitpid(child, &st, 0) < 0 && errno == EINTR) {
    }
    if (got == sizeof(exec_msg) && exec_msg.kind == PS_STATUS_EXEC_ERR) {
      send_status(status_fd, PS_STATUS_EXEC_ERR, exec_msg.flag, exec_msg.value);
    } else {
      send_status(status_fd, PS_STATUS_EXEC_ERR, 0, EIO);
    }
    close(status_fd);
    return 0;
  }

  int st = 0;
  while (waitpid(child, &st, 0) < 0) {
    if (errno == EINTR) {
      continue;
    }
    break;
  }

  (void)kill(-1, SIGKILL);
  for (;;) {
    int s2 = 0;
    pid_t r = waitpid(-1, &s2, 0);
    if (r > 0) {
      continue;
    }
    if (errno == EINTR) {
      continue;
    }
    if (errno == ECHILD) {
      break;
    }
    break;
  }

  if (WIFEXITED(st)) {
    send_status(status_fd, PS_STATUS_EXITED, 0, (int32_t)WEXITSTATUS(st));
  } else if (WIFSIGNALED(st)) {
    send_status(status_fd, PS_STATUS_SIGNALED, 0, (int32_t)WTERMSIG(st));
  } else {
    send_status(status_fd, PS_STATUS_EXITED, 0, 1);
  }
  close(status_fd);
  return 0;
}

#else

int main(void) {
  return 1;
}

#endif
