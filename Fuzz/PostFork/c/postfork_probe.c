#define _GNU_SOURCE

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <unistd.h>

extern char **environ;

static off_t g_out_off = 0;

static void write_exact(int fd, const void *buf, size_t n) {
  size_t off = 0u;
  const uint8_t *p = (const uint8_t *)buf;
  while (off < n) {
    ssize_t w = pwrite(fd, p + off, n - off, g_out_off + (off_t)off);
    if (w < 0) {
      if (errno == EINTR) continue;
      _exit(78);
    }
    if (w == 0) _exit(78);
    off += (size_t)w;
  }
  g_out_off += (off_t)n;
}
static void write_u32(int fd, uint32_t v) { write_exact(fd, &v, sizeof(v)); }
static void write_u64(int fd, uint64_t v) { write_exact(fd, &v, sizeof(v)); }
static void write_str(int fd, const char *s) {
  uint32_t n = s ? (uint32_t)strlen(s) : 0u;
  write_u32(fd, n);
  if (n > 0u) write_exact(fd, s, n);
}
static void maybe_probe_action(int argc, char **argv) {
  if (argc < 2) return;
  if (strcmp(argv[1], "--self-kill") == 0) (void)raise(SIGKILL);
  if (strcmp(argv[1], "--emit-stdio") == 0) {
    ssize_t r1 = write(1, "PF-STDOUT\n", 10), r2 = write(2, "PF-STDERR\n", 10);
    (void)r1; (void)r2;
  }
}

static int32_t sig_disp_code(int sig) {
  struct sigaction sa;
  if (sigaction(sig, NULL, &sa) != 0) return -1;
  if (sa.sa_handler == SIG_DFL) return 0;
  if (sa.sa_handler == SIG_IGN) return 1;
  return 2;
}

static uint32_t probe_sig_blk_bits(void) {
  sigset_t b;
  if (sigprocmask(SIG_SETMASK, NULL, &b) != 0) return 0xffffffffu;
  uint32_t m = 0u;
  if (sigismember(&b, SIGHUP) == 1) m |= (1u << 0);
  if (sigismember(&b, SIGINT) == 1) m |= (1u << 1);
  if (sigismember(&b, SIGUSR1) == 1) m |= (1u << 9);
  if (sigismember(&b, SIGUSR2) == 1) m |= (1u << 11);
  if (sigismember(&b, SIGPIPE) == 1) m |= (1u << 12);
  if (sigismember(&b, SIGTERM) == 1) m |= (1u << 14);
  return m;
}

static uint32_t count_str_vec(char *const *vec, int limit) {
  uint32_t cnt = 0u;
  if (vec == NULL) return 0u;
  for (int i = 0; i < limit && vec[i] != NULL; i++) cnt++;
  return cnt;
}

static void dump_str_vec(int out, char *const *vec, int limit) {
  uint32_t cnt = count_str_vec(vec, limit);
  write_u32(out, cnt);
  if (vec == NULL) return;
  for (uint32_t i = 0u; i < cnt; i++) write_str(out, vec[i]);
}

static void dump_argv(int out, int argc, char **argv) {
  write_u32(out, (uint32_t)argc);
  for (int i = 0; i < argc; i++) write_str(out, argv[i]);
}

typedef struct OpenFdInfo { uint32_t fd, flags; uint64_t dev, ino; } OpenFdInfo;
static int probe_fd_flags(int fd) {
  int flags = fcntl(fd, F_GETFD, 0);
  if (flags != -1) return flags;
  struct stat st;
  return (errno != EBADF && fstat(fd, &st) == 0) ? 0 : -1;
}
static uint32_t count_open_fds_proc(OpenFdInfo *dst, uint32_t cap) {
  DIR *d = opendir("/proc/self/fd");
  if (d == NULL) return UINT32_MAX;
  int dfd = dirfd(d);
  uint32_t cnt = 0u;
  struct dirent *ent;
  errno = 0;
  while (cnt < cap && (errno = 0, (ent = readdir(d)) != NULL)) {
    if (ent->d_name[0] < '0' || ent->d_name[0] > '9') continue;
    char *end = NULL;
    long v = strtol(ent->d_name, &end, 10);
    if (end == ent->d_name || *end != '\0' || v < 0 || v > INT_MAX || (int)v == dfd) continue;
    int fd = (int)v;
    int fl = probe_fd_flags(fd);
    if (fl != -1) {
      struct stat st;
      memset(&st, 0, sizeof(st));
      (void)fstat(fd, &st);
      dst[cnt++] = (OpenFdInfo){ (uint32_t)fd, (uint32_t)fl, (uint64_t)st.st_dev, (uint64_t)st.st_ino };
    }
  }
  int saved_errno = errno;
  closedir(d);
  if (saved_errno != 0) return UINT32_MAX;
  return cnt;
}
static uint32_t count_open_fds(OpenFdInfo *dst, int max_fd) {
  uint32_t cnt = 0u;
  for (int fd = 0; fd <= max_fd; fd++) {
    int flags = probe_fd_flags(fd);
    if (flags != -1) {
      struct stat st;
      memset(&st, 0, sizeof(st));
      (void)fstat(fd, &st);
      dst[cnt++] = (OpenFdInfo){ (uint32_t)fd, (uint32_t)flags, (uint64_t)st.st_dev, (uint64_t)st.st_ino };
    }
  }
  return cnt;
}

static void dump_open_fds(int out, const OpenFdInfo *fds, uint32_t cnt) {
  write_u32(out, cnt);
  for (uint32_t i = 0u; i < cnt; i++) {
    write_u32(out, fds[i].fd); write_u32(out, fds[i].flags);
    write_u64(out, fds[i].dev); write_u64(out, fds[i].ino);
  }
}
static void free_fd0(void) { if (close(0) != 0) (void)syscall(436L, 0u, 0u, 0u); }
static int open_probe_out(const char *target) {
  int out = open(target, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0600);
  if (out < 0 && (errno == EMFILE || errno == ENFILE)) {
    free_fd0();
    out = open(target, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0600);
  }
  return out;
}
static const char *probe_out_env(void) {
  const char *p = getenv("_PF_PROBE_OUT");
  return (p != NULL && p[0] != '\0') ? p : NULL;
}

int main(int argc, char **argv) {
  maybe_probe_action(argc, argv);
  char cwd[PATH_MAX], inbuf[256];
  int32_t pgid = (int32_t)getpgid(0), sp = sig_disp_code(SIGPIPE);
  int32_t su1 = sig_disp_code(SIGUSR1), su2 = sig_disp_code(SIGUSR2);
  const char *cwd_str = getcwd(cwd, sizeof(cwd)) != NULL ? cwd : "";
  struct iovec iov = { inbuf, sizeof(inbuf) };
  ssize_t in_len = readv(0, &iov, 1);
  uint32_t stdin_n = in_len > 0 ? (uint32_t)in_len : 0u;
  const char *target = probe_out_env();
  if (target == NULL) return 0;
  OpenFdInfo open_fds[1024];
  uint32_t open_cnt = count_open_fds_proc(open_fds, 1024u);
  if (open_cnt == UINT32_MAX) open_cnt = count_open_fds(open_fds, 1023);
  int out = open_probe_out(target);
  if (out < 0) return 77;
  write_u32(out, 0x50465052u); write_u32(out, (uint32_t)pgid);
  write_u32(out, (uint32_t)sp); write_u32(out, (uint32_t)su1);
  write_u32(out, (uint32_t)su2); write_u32(out, probe_sig_blk_bits());
  write_str(out, cwd_str); dump_argv(out, argc, argv); dump_str_vec(out, environ, 4096);
  write_u32(out, stdin_n); if (stdin_n > 0u) write_exact(out, inbuf, stdin_n);
  dump_open_fds(out, open_fds, open_cnt); close(out); return 0;
}
