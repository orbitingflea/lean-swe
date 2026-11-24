#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe.LinuxSyscall.Process fuzz env requires Linux x86_64 or aarch64"
#endif

#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/audit.h>
#include <linux/capability.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include "fd_box.h"

#if defined(__x86_64__)
#define LEANSWE_AUDIT_ARCH AUDIT_ARCH_X86_64
#elif defined(__aarch64__)
#define LEANSWE_AUDIT_ARCH AUDIT_ARCH_AARCH64
#endif

#ifndef SYS_pidfd_open
#define SYS_pidfd_open 434
#endif

typedef lean_obj_res (*leanswe_pidfd_open_fn_t)(uint32_t, uint64_t);
__attribute__((weak)) extern lean_obj_res leanswe_sys_pidfd_open(uint32_t pid_u32, uint64_t bits);
extern char **environ;

static unsigned int fuzz_decode_pidfd_open_flags(uint64_t bits) {
  unsigned int f = (bits & 1ull) ? (unsigned int)O_NONBLOCK : 0u;
  return f | ((bits & 2ull) ? (unsigned int)O_EXCL : 0u) | (((bits >> 2) != 0ull) ? 0x80000000u : 0u);
}

static lean_obj_res call_sys_pidfd_open(uint32_t pid_u32, uint64_t bits) {
  leanswe_pidfd_open_fn_t fn = leanswe_sys_pidfd_open;
  if (fn == NULL) { void *sym = dlsym(RTLD_DEFAULT, "leanswe_sys_pidfd_open"); memcpy(&fn, &sym, sizeof(fn)); }
  if (fn != NULL) return fn(pid_u32, bits);
  long fd = syscall(SYS_pidfd_open, (long)(int32_t)pid_u32, (unsigned long)fuzz_decode_pidfd_open_flags(bits));
  if (fd < 0) return leanswe_mk_errno(errno);
  lean_obj_res obj = leanswe_mk_fd_obj((int)fd);
  if (obj == NULL) return leanswe_mk_errno(ENOMEM);
  return leanswe_mk_ok(obj);
}
static rlim_t g_saved_nofile_cur = 0;
static pthread_mutex_t g_nofile_mu = PTHREAD_MUTEX_INITIALIZER;

static inline lean_obj_res mk_pair(lean_obj_res a, lean_obj_res b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a); lean_ctor_set(p, 1, b); return p;
}

static int open_sync_pair(int sv[2]) { return socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sv); }
static pid_t fuzz_raw_fork(void) { return (pid_t)syscall(SYS_clone, (unsigned long)SIGCHLD, 0UL, 0UL, 0UL, 0UL); }

static void write_text_file(const char *path, const char *txt) {
  int fd = open(path, O_WRONLY | O_CLOEXEC);
  if (fd >= 0) { ssize_t r = write(fd, txt, strlen(txt)); (void)r; close(fd); }
}

static void map_self_uid_gid(uid_t uid, gid_t gid) {
  char buf[64]; write_text_file("/proc/self/setgroups", "deny\n");
  snprintf(buf, sizeof(buf), "0 %u 1\n", (unsigned)uid); write_text_file("/proc/self/uid_map", buf);
  snprintf(buf, sizeof(buf), "0 %u 1\n", (unsigned)gid); write_text_file("/proc/self/gid_map", buf);
}

static int drop_cap_kill_perm(void) {
  prctl(PR_CAPBSET_DROP, 5, 0, 0, 0);
  struct __user_cap_header_struct hdr;
  struct __user_cap_data_struct data[2];
  memset(&hdr, 0, sizeof(hdr)); memset(data, 0, sizeof(data));
  hdr.version = _LINUX_CAPABILITY_VERSION_3; hdr.pid = 0;
  if (syscall(SYS_capget, &hdr, data) < 0) return errno;
  uint32_t mask = ~(1u << 5);
  data[0].effective &= mask; data[0].permitted &= mask; data[0].inheritable &= mask;
  if (syscall(SYS_capset, &hdr, data) < 0) return errno;
  return 0;
}

static void reset_rt_sig_if_caught(int sig) {
  uint64_t old_ksa[4] = {0, 0, 0, 0}, dfl_ksa[4] = {0, 0, 0, 0};
  if (syscall(SYS_rt_sigaction, (long)sig, (void *)NULL, old_ksa, (size_t)8) == 0 && old_ksa[0] != 0 && old_ksa[0] != 1) {
    syscall(SYS_rt_sigaction, (long)sig, dfl_ksa, (void *)NULL, (size_t)8);
  }
}

static void setup_child_pgid(int32_t pgid_req, pid_t parent_pid) {
  if (parent_pid > 0) { prctl(PR_SET_PDEATHSIG, SIGKILL, 0, 0, 0); if (getppid() != parent_pid) _exit(0); }
  reset_rt_sig_if_caught(SIGSEGV); reset_rt_sig_if_caught(SIGBUS);
  reset_rt_sig_if_caught(32); reset_rt_sig_if_caught(33);
  if (pgid_req >= 0) setpgid(0, (pgid_req == 0) ? 0 : (pid_t)pgid_req);
}

static ssize_t read_nointr(int fd, void *buf, size_t n) {
  sigset_t all, old; sigfillset(&all); pthread_sigmask(SIG_BLOCK, &all, &old);
  ssize_t rd = read(fd, buf, n);
  pthread_sigmask(SIG_SETMASK, &old, NULL);
  return rd;
}

static uint32_t read_ready_pgid(int rfd) {
  uint32_t pg = 0u; ssize_t rd = read_nointr(rfd, &pg, sizeof(pg)); close(rfd);
  return (rd == (ssize_t)sizeof(pg)) ? pg : 0u;
}

LEAN_EXPORT lean_obj_res leanswe_proc_close_fd(b_lean_obj_arg fd_obj) {
  int rc = leanswe_fd_box_close((LeanFdBox *)lean_get_external_data(fd_obj));
  return (rc != 0) ? leanswe_mk_errno(rc) : leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_get_fd_flags(b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  int fd = -1, perr = leanswe_fd_box_pin(box, &fd);
  if (perr != 0) return leanswe_mk_errno(perr);
  int fdf = fcntl(fd, F_GETFD), e1 = errno;
  int flf = (fdf >= 0) ? fcntl(fd, F_GETFL) : -1, e2 = errno;
  leanswe_fd_box_unpin(box);
  if (fdf < 0) return leanswe_mk_errno(e1);
  if (flf < 0) return leanswe_mk_errno(e2);
  return leanswe_mk_ok(mk_pair(lean_box_uint32((uint32_t)fdf), lean_box_uint32((uint32_t)flf)));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_controlled(uint32_t pgid_req, uint8_t reset_sigchld) {
  int p[2] = {-1, -1}; pid_t ppid = getpid();
  if (open_sync_pair(p) < 0) return leanswe_mk_errno(errno);
  pid_t pid = fuzz_raw_fork();
  if (pid < 0) { int err = errno; close(p[0]); close(p[1]); return leanswe_mk_errno(err); }
  if (pid == 0) {
    close(p[0]);
    if (reset_sigchld) signal(SIGCHLD, SIG_DFL);
    setup_child_pgid((int32_t)pgid_req, ppid);
    uint32_t pg = (uint32_t)getpgrp(); ssize_t wr = write(p[1], &pg, sizeof(pg)); (void)wr; close(p[1]);
    pause(); _exit(0);
  }
  close(p[1]);
  return leanswe_mk_ok(mk_pair(lean_box_uint32((uint32_t)pid), lean_box_uint32(read_ready_pgid(p[0]))));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_autonomous(uint32_t pgid_req, uint32_t delay_us, uint8_t exit_code) {
  int p[2] = {-1, -1}; pid_t ppid = getpid();
  if (open_sync_pair(p) < 0) return leanswe_mk_errno(errno);
  pid_t pid = fuzz_raw_fork();
  if (pid < 0) { int err = errno; close(p[0]); close(p[1]); return leanswe_mk_errno(err); }
  if (pid == 0) {
    close(p[0]); setup_child_pgid((int32_t)pgid_req, ppid);
    uint32_t pg = (uint32_t)getpgrp(); ssize_t wr = write(p[1], &pg, sizeof(pg)); (void)wr; close(p[1]);
    if (delay_us > 0u) { struct timespec ts = {(time_t)(delay_us / 1000000u), (long)(delay_us % 1000000u) * 1000L}; nanosleep(&ts, NULL); }
    _exit((int)exit_code);
  }
  close(p[1]);
  return leanswe_mk_ok(mk_pair(lean_box_uint32((uint32_t)pid), lean_box_uint32(read_ready_pgid(p[0]))));
}

static void unblock_and_reset_sig(uint32_t sig) {
  uint64_t dfl_ksa[4] = {0, 0, 0, 0};
  uint64_t mask = (sig >= 1u && sig <= 64u) ? (1ULL << (sig - 1u)) : 0ULL;
  syscall(SYS_rt_sigaction, (long)sig, dfl_ksa, (void *)NULL, (size_t)8);
  if (mask) syscall(SYS_rt_sigprocmask, (long)SIG_UNBLOCK, &mask, (void *)NULL, (size_t)8);
}

static int force_kill_child(pid_t pid) {
  if (kill(pid, SIGKILL) == 0) return 1;
  int pfd = (int)syscall(SYS_pidfd_open, (long)pid, 0UL);
  if (pfd >= 0) { long rc = syscall(SYS_pidfd_send_signal, (long)pfd, (long)SIGKILL, (void *)NULL, 0UL); close(pfd); if (rc == 0) return 1; }
  if (syscall(SYS_tgkill, (long)pid, (long)pid, (long)SIGKILL) == 0) return 1;
  return 0;
}

static int waitid_nointr(id_t id, siginfo_t *si, int opts) {
  sigset_t all, old; sigfillset(&all);
  pthread_sigmask(SIG_BLOCK, &all, &old);
  int rc = waitid(P_PID, id, si, opts);
  pthread_sigmask(SIG_SETMASK, &old, NULL);
  return rc;
}

static pid_t waitpid_nointr(pid_t p, int *st) {
  sigset_t all, old; sigfillset(&all);
  pthread_sigmask(SIG_BLOCK, &all, &old);
  pid_t rc = waitpid(p, st, 0);
  if (rc < 0 && errno == EINTR) rc = waitpid(p, st, 0);
  pthread_sigmask(SIG_SETMASK, &old, NULL);
  return rc;
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_is_self_pgid_orphaned(void) {
  pid_t pg = getpgrp(), sid = getsid(0);
  if (pg < 0) return lean_io_result_mk_ok(lean_box(0u));
  if (pg > 0 && pg == sid) return lean_io_result_mk_ok(lean_box(1u));
  pid_t p = fuzz_raw_fork();
  if (p < 0) return lean_io_result_mk_ok(lean_box(0u));
  if (p == 0) { unblock_and_reset_sig(21u); pid_t me = (pid_t)syscall(SYS_gettid); syscall(SYS_tgkill, (long)me, (long)me, (long)SIGTTIN); _exit(1); }
  siginfo_t si; memset(&si, 0, sizeof(si));
  int rc = waitid_nointr((id_t)p, &si, WEXITED | WSTOPPED);
  if (rc == 0 && si.si_code == CLD_STOPPED) {
    if (force_kill_child(p)) waitid_nointr((id_t)p, &si, WEXITED);
    else waitid_nointr((id_t)p, &si, WEXITED | WNOHANG);
    return lean_io_result_mk_ok(lean_box(0u));
  }
  return lean_io_result_mk_ok(lean_box(1u));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_stopped(uint32_t pgid_req, uint32_t stop_sig) {
  uint8_t self_orph = 0u;
  pid_t parent_pg = getpgrp(), ppid = getpid();
  if (stop_sig != 19u) {
    lean_obj_res r = leanswe_proc_fuzz_is_self_pgid_orphaned();
    self_orph = (uint8_t)lean_unbox(lean_ctor_get(r, 0));
    lean_dec(r);
  }
  int p[2] = {-1, -1};
  if (open_sync_pair(p) < 0) return leanswe_mk_errno(errno);
  pid_t pid = fuzz_raw_fork();
  if (pid < 0) { int err = errno; close(p[0]); close(p[1]); return leanswe_mk_errno(err); }
  if (pid == 0) {
    close(p[0]); setup_child_pgid((int32_t)pgid_req, ppid);
    pid_t pg_now = getpgrp();
    if (stop_sig != 19u && ((int32_t)pgid_req < 0 || (self_orph && pg_now == parent_pg) || (pg_now > 0 && pg_now == getsid(0)))) setpgid(0, 0);
    uint32_t pg = (uint32_t)getpgrp(); ssize_t wr = write(p[1], &pg, sizeof(pg)); (void)wr; close(p[1]);
    unblock_and_reset_sig(stop_sig);
    pid_t self_tid = (pid_t)syscall(SYS_gettid);
    syscall(SYS_tgkill, (long)self_tid, (long)self_tid, (long)stop_sig);
    pause(); _exit(0);
  }
  close(p[1]);
  uint32_t pg = read_ready_pgid(p[0]);
  siginfo_t si; memset(&si, 0, sizeof(si));
  int wrc = waitid_nointr((id_t)pid, &si, WSTOPPED | WEXITED | WNOWAIT);
  if (wrc != 0 || si.si_code != CLD_STOPPED) {
    force_kill_child(pid); waitid_nointr((id_t)pid, &si, WEXITED);
    return leanswe_mk_errno(EAGAIN);
  }
  return leanswe_mk_ok(mk_pair(lean_box_uint32((uint32_t)pid), lean_box_uint32(pg)));
}

static void child_terminate_zombie(uint8_t is_sig, uint32_t code_or_sig, uint8_t allow_core) {
  if (is_sig) {
    write_text_file("/proc/self/coredump_filter", "0");
    struct rlimit rl;
    if (allow_core && getrlimit(RLIMIT_CORE, &rl) == 0) {
      rl.rlim_cur = (rl.rlim_max > 65536u) ? 65536u : rl.rlim_max;
      setrlimit(RLIMIT_CORE, &rl);
    } else if (!allow_core) {
      rl.rlim_cur = 1; rl.rlim_max = 1; setrlimit(RLIMIT_CORE, &rl);
    }
    unblock_and_reset_sig(code_or_sig);
    pid_t self_tid = (pid_t)syscall(SYS_gettid);
    syscall(SYS_tgkill, (long)self_tid, (long)self_tid, (long)code_or_sig);
    _exit(128);
  }
  _exit((int)(code_or_sig & 0xffu));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_zombie(
    uint32_t pgid_req, uint8_t is_sig, uint32_t code_or_sig, uint8_t allow_core) {
  int p[2] = {-1, -1}; pid_t ppid = getpid();
  if (open_sync_pair(p) < 0) return leanswe_mk_errno(errno);
  pid_t pid = fuzz_raw_fork();
  if (pid < 0) { int err = errno; close(p[0]); close(p[1]); return leanswe_mk_errno(err); }
  if (pid == 0) {
    close(p[0]); setup_child_pgid((int32_t)pgid_req, ppid);
    uint32_t pg = (uint32_t)getpgrp(); ssize_t wr = write(p[1], &pg, sizeof(pg)); (void)wr; close(p[1]);
    child_terminate_zombie(is_sig, code_or_sig, allow_core);
  }
  close(p[1]);
  uint32_t pg = read_ready_pgid(p[0]);
  siginfo_t si; memset(&si, 0, sizeof(si));
  waitid_nointr((id_t)pid, &si, WEXITED | WNOWAIT);
  uint8_t dumped = (si.si_code == CLD_DUMPED) ? 1u : 0u;
  lean_obj_res ids = mk_pair(lean_box_uint32((uint32_t)pid), lean_box_uint32(pg));
  return leanswe_mk_ok(mk_pair(ids, lean_box(dumped)));
}

typedef struct { int ready_wr; int32_t pgid_req; pthread_barrier_t bar; pthread_t th; } ThreadStartArg;

static void join_and_free_thread(ThreadStartArg *arg) {
  pthread_barrier_wait(&arg->bar);
  pthread_join(arg->th, NULL);
  pthread_barrier_destroy(&arg->bar);
  free(arg);
}

static void *thread_wait_worker(void *raw) {
  ThreadStartArg *arg = (ThreadStartArg *)raw;
  uint32_t tid = (uint32_t)syscall(SYS_gettid);
  ssize_t wr = write(arg->ready_wr, &tid, sizeof(tid)); (void)wr; close(arg->ready_wr);
  pthread_barrier_wait(&arg->bar);
  return NULL;
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_thread(void) {
  int sv[2] = {-1, -1};
  if (open_sync_pair(sv) < 0) return leanswe_mk_errno(errno);
  ThreadStartArg *arg = (ThreadStartArg *)malloc(sizeof(ThreadStartArg));
  if (arg == NULL) { close(sv[0]); close(sv[1]); return leanswe_mk_errno(ENOMEM); }
  arg->ready_wr = sv[1]; arg->pgid_req = -1;
  pthread_barrier_init(&arg->bar, NULL, 2);
  int rc = pthread_create(&arg->th, NULL, thread_wait_worker, arg);
  if (rc != 0) { pthread_barrier_destroy(&arg->bar); free(arg); close(sv[0]); close(sv[1]); return leanswe_mk_errno(rc); }
  uint32_t tid = 0; ssize_t rd = read_nointr(sv[0], &tid, sizeof(tid)); close(sv[0]);
  if (rd != (ssize_t)sizeof(tid) || tid == 0u) { join_and_free_thread(arg); return leanswe_mk_errno(EIO); }
  return leanswe_mk_ok(mk_pair(lean_box_uint32(tid), lean_box_uint64((uint64_t)(uintptr_t)arg)));
}

typedef struct { uint32_t tid; uint32_t child_pid; uint32_t child_pgid; } SiblingChildMsg;

static void *sibling_fork_worker(void *raw) {
  ThreadStartArg *arg = (ThreadStartArg *)raw;
  SiblingChildMsg msg; memset(&msg, 0, sizeof(msg));
  msg.tid = (uint32_t)syscall(SYS_gettid);
  pid_t ppid = getpid();
  int p[2] = {-1, -1};
  if (open_sync_pair(p) == 0) {
    pid_t c = fuzz_raw_fork();
    if (c == 0) {
      close(p[0]); close(arg->ready_wr);
      setup_child_pgid(arg->pgid_req, ppid);
      uint32_t pg = (uint32_t)getpgrp(); ssize_t wr = write(p[1], &pg, sizeof(pg)); (void)wr; close(p[1]);
      pause(); _exit(0);
    }
    close(p[1]);
    if (c > 0) { msg.child_pid = (uint32_t)c; msg.child_pgid = read_ready_pgid(p[0]); }
    else { close(p[0]); }
  }
  ssize_t wr = write(arg->ready_wr, &msg, sizeof(msg)); (void)wr; close(arg->ready_wr);
  pthread_barrier_wait(&arg->bar);
  return NULL;
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_sibling_child(uint32_t pgid_req) {
  int sv[2] = {-1, -1};
  if (open_sync_pair(sv) < 0) return leanswe_mk_errno(errno);
  ThreadStartArg *arg = (ThreadStartArg *)malloc(sizeof(ThreadStartArg));
  if (arg == NULL) { close(sv[0]); close(sv[1]); return leanswe_mk_errno(ENOMEM); }
  arg->ready_wr = sv[1]; arg->pgid_req = (int32_t)pgid_req;
  pthread_barrier_init(&arg->bar, NULL, 2);
  int rc = pthread_create(&arg->th, NULL, sibling_fork_worker, arg);
  if (rc != 0) { pthread_barrier_destroy(&arg->bar); free(arg); close(sv[0]); close(sv[1]); return leanswe_mk_errno(rc); }
  SiblingChildMsg msg; memset(&msg, 0, sizeof(msg));
  ssize_t rd = read_nointr(sv[0], &msg, sizeof(msg)); close(sv[0]);
  if (rd != (ssize_t)sizeof(msg) || msg.tid == 0u || msg.child_pid == 0u) { join_and_free_thread(arg); return leanswe_mk_errno(EAGAIN); }
  lean_obj_res tail = mk_pair(lean_box_uint32(msg.tid), lean_box_uint64((uint64_t)(uintptr_t)arg));
  return leanswe_mk_ok(mk_pair(mk_pair(lean_box_uint32(msg.child_pid), lean_box_uint32(msg.child_pgid)), tail));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_join_thread(uint64_t handle) {
  join_and_free_thread((ThreadStartArg *)(uintptr_t)handle);
  return lean_io_result_mk_ok(lean_box(0));
}

typedef struct { int ready_wr; int32_t pgid_req; pid_t ppid; uint8_t immediate_exit; uint8_t exit_code; } CloneChildArg;

static int clone_child_entry(void *raw) {
  CloneChildArg *arg = (CloneChildArg *)raw;
  setup_child_pgid(arg->pgid_req, arg->ppid);
  uint32_t pg = (uint32_t)getpgrp();
  ssize_t wr = write(arg->ready_wr, &pg, sizeof(pg)); (void)wr; close(arg->ready_wr);
  if (arg->immediate_exit) _exit((int)arg->exit_code);
  pause(); _exit(0);
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_clone_child(
    uint32_t pgid_req, uint8_t immediate_exit, uint8_t exit_code) {
  int p[2] = {-1, -1};
  if (open_sync_pair(p) < 0) return leanswe_mk_errno(errno);
  void *stk = mmap(NULL, 16384, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (stk == MAP_FAILED) { int err = errno; close(p[0]); close(p[1]); return leanswe_mk_errno(err); }
  CloneChildArg arg = { p[1], (int32_t)pgid_req, getpid(), immediate_exit, exit_code };
  int cpid = clone(clone_child_entry, (char *)stk + 16384, 0, &arg), saved = errno;
  munmap(stk, 16384); close(p[1]);
  if (cpid < 0) { close(p[0]); return leanswe_mk_errno(saved); }
  uint32_t pg = read_ready_pgid(p[0]);
  if (immediate_exit) { siginfo_t si; memset(&si, 0, sizeof(si)); waitid_nointr((id_t)cpid, &si, WEXITED | WNOWAIT | __WALL); }
  return leanswe_mk_ok(mk_pair(lean_box_uint32((uint32_t)cpid), lean_box_uint32(pg)));
}

typedef struct { int wr; uint32_t delay_us; uint8_t sub_code; } WorkerThreadArg;

static int child_worker_thread_entry(void *raw) {
  WorkerThreadArg wa = *(WorkerThreadArg *)raw;
  uint32_t tid = (uint32_t)syscall(SYS_gettid);
  ssize_t r = write(wa.wr, &tid, sizeof(tid)); (void)r; close(wa.wr);
  if (wa.delay_us == 0u) pause();
  else { struct timespec ts = {(time_t)(wa.delay_us / 1000000u), (long)(wa.delay_us % 1000000u) * 1000L}; nanosleep(&ts, NULL); }
  syscall(SYS_exit, (long)(int)wa.sub_code);
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_threaded_child(uint32_t pgid_req) {
  int sv[2] = {-1, -1}; pid_t ppid = getpid();
  if (open_sync_pair(sv) < 0) return leanswe_mk_errno(errno);
  pid_t pid = fuzz_raw_fork();
  if (pid < 0) { int err = errno; close(sv[0]); close(sv[1]); return leanswe_mk_errno(err); }
  if (pid == 0) {
    close(sv[0]); setup_child_pgid((int32_t)pgid_req, ppid);
    void *stk = mmap(NULL, 16384, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (stk != MAP_FAILED) {
      WorkerThreadArg *wa = (WorkerThreadArg *)stk; wa->wr = sv[1]; wa->delay_us = 0u; wa->sub_code = 0u;
      int tid = clone(child_worker_thread_entry, (char *)stk + 16384,
            CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND | CLONE_THREAD, wa);
      if (tid >= 0) { pause(); _exit(0); }
    }
    close(sv[1]); _exit(1);
  }
  close(sv[1]);
  uint32_t tid = 0; ssize_t rd = read_nointr(sv[0], &tid, sizeof(tid)); close(sv[0]);
  if (rd != (ssize_t)sizeof(tid) || tid == 0u) {
    siginfo_t si; memset(&si, 0, sizeof(si));
    force_kill_child(pid); waitid_nointr((id_t)pid, &si, WEXITED | __WALL);
    return leanswe_mk_errno(EAGAIN);
  }
  pid_t pg = getpgid(pid);
  lean_obj_res tail = mk_pair(lean_box_uint32((uint32_t)(pg >= 0 ? pg : 0)), lean_box_uint32(tid));
  return leanswe_mk_ok(mk_pair(lean_box_uint32((uint32_t)pid), tail));
}

static void resolve_self_stat_path(char out[32], pid_t fallback) {
  char lnk[16]; ssize_t n = readlink("/proc/self", lnk, sizeof(lnk) - 1);
  if (n > 0 && lnk[0] >= '1' && lnk[0] <= '9') { lnk[n] = '\0'; snprintf(out, 32, "/proc/%s/stat", lnk); }
  else snprintf(out, 32, "/proc/%d/stat", (int)fallback);
}

static int wait_leader_zombie(const char *path) {
  char buf[512];
  for (int i = 0; i < 200; i++) {
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    ssize_t n = (fd >= 0) ? read(fd, buf, sizeof(buf) - 1) : -1;
    if (fd >= 0) close(fd);
    if (n > 0) {
      buf[n] = '\0';
      char *rp = strrchr(buf, ')');
      if (rp != NULL && rp[1] == ' ' && rp[2] == 'Z') return 0;
    }
    struct timespec ts = {0, 1000000L}; nanosleep(&ts, NULL);
  }
  return -1;
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_delayed_zombie(
    uint32_t pgid_req, uint8_t exit_code, uint32_t sub_delay_us, uint8_t sub_exit_code) {
  int sv[2] = {-1, -1}; pid_t ppid = getpid();
  if (open_sync_pair(sv) < 0) return leanswe_mk_errno(errno);
  pid_t pid = fuzz_raw_fork();
  if (pid < 0) { int err = errno; close(sv[0]); close(sv[1]); return leanswe_mk_errno(err); }
  if (pid == 0) {
    char spath[32]; memset(spath, 0, sizeof(spath));
    close(sv[0]); setup_child_pgid((int32_t)pgid_req, ppid);
    resolve_self_stat_path(spath, (pid_t)syscall(SYS_gettid));
    void *stk = mmap(NULL, 16384, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (stk != MAP_FAILED) {
      WorkerThreadArg *wa = (WorkerThreadArg *)stk; wa->wr = sv[1]; wa->delay_us = sub_delay_us; wa->sub_code = sub_exit_code;
      ssize_t w0 = write(sv[1], spath, sizeof(spath)); (void)w0;
      int tid = clone(child_worker_thread_entry, (char *)stk + 16384,
            CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND | CLONE_THREAD, wa);
      if (tid >= 0) syscall(SYS_exit, (long)(int)exit_code);
    }
    close(sv[1]); _exit(1);
  }
  close(sv[1]);
  char spath[32]; uint32_t tid = 0u;
  ssize_t r0 = read_nointr(sv[0], spath, sizeof(spath)); spath[31] = '\0';
  ssize_t rd = (r0 == (ssize_t)sizeof(spath)) ? read_nointr(sv[0], &tid, sizeof(tid)) : -1;
  close(sv[0]);
  if (rd != (ssize_t)sizeof(tid) || spath[0] != '/' || tid == 0u || wait_leader_zombie(spath) != 0) {
    siginfo_t si; memset(&si, 0, sizeof(si));
    force_kill_child(pid); waitid_nointr((id_t)pid, &si, WEXITED | __WALL);
    return leanswe_mk_errno(EAGAIN);
  }
  pid_t pg = getpgid(pid);
  lean_obj_res tail = mk_pair(lean_box_uint32((uint32_t)(pg >= 0 ? pg : 0)), lean_box_uint32(tid));
  return leanswe_mk_ok(mk_pair(lean_box_uint32((uint32_t)pid), tail));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_probe_pidfd_thread_raw(void) {
  long fd = syscall(SYS_pidfd_open, (long)getpid(), (long)O_EXCL);
  if (fd >= 0) { close((int)fd); return lean_io_result_mk_ok(lean_box(1u)); }
  return lean_io_result_mk_ok(lean_box(0u));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_probe_watch_queue_raw(void) {
  int fds[2] = {-1, -1};
  if (syscall(SYS_pipe2, fds, (long)(O_CLOEXEC | O_EXCL)) == 0) { close(fds[0]); close(fds[1]); return lean_io_result_mk_ok(lean_box(1u)); }
  return lean_io_result_mk_ok(lean_box(0u));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_reparented_grandchild(uint32_t pgid_req) {
  int sv[2] = {-1, -1};
  if (open_sync_pair(sv) < 0) return leanswe_mk_errno(errno);
  pid_t mid = fuzz_raw_fork();
  if (mid < 0) { int err = errno; close(sv[0]); close(sv[1]); return leanswe_mk_errno(err); }
  if (mid == 0) {
    close(sv[0]);
    pid_t gc = fuzz_raw_fork();
    if (gc == 0) {
      setup_child_pgid((int32_t)pgid_req, 0);
      unblock_and_reset_sig(14u); alarm(60u);
      uint32_t pair[2] = {(uint32_t)syscall(SYS_gettid), (uint32_t)getpgrp()};
      ssize_t wr = write(sv[1], pair, sizeof(pair)); (void)wr; close(sv[1]);
      pause(); _exit(0);
    }
    close(sv[1]); _exit(0);
  }
  close(sv[1]);
  siginfo_t si; memset(&si, 0, sizeof(si));
  waitid_nointr((id_t)mid, &si, WEXITED);
  uint32_t pair[2] = {0u, 0u};
  ssize_t rd = read_nointr(sv[0], pair, sizeof(pair)); close(sv[0]);
  if (rd != (ssize_t)sizeof(pair) || pair[0] == 0u) return leanswe_mk_errno(EAGAIN);
  return leanswe_mk_ok(mk_pair(lean_box_uint32(pair[0]), lean_box_uint32(pair[1])));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_set_subreaper(uint8_t enable) {
  if (prctl(PR_SET_CHILD_SUBREAPER, enable ? 1 : 0, 0, 0, 0) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_set_sigchld_autoreap(uint8_t mode) {
  struct sigaction sa; memset(&sa, 0, sizeof(sa));
  sa.sa_handler = (mode == 1u) ? SIG_IGN : SIG_DFL;
  if (mode == 2u) sa.sa_flags = SA_NOCLDWAIT;
  else if (mode == 3u) sa.sa_flags = SA_NOCLDSTOP;
  else if (mode == 4u) sa.sa_flags = SA_NOCLDWAIT | SA_NOCLDSTOP;
  if (sigaction(SIGCHLD, &sa, NULL) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_set_sig_ign(uint32_t sig, uint8_t ign) {
  struct sigaction sa; memset(&sa, 0, sizeof(sa)); sa.sa_handler = ign ? SIG_IGN : SIG_DFL;
  if (sigaction((int)sig, &sa, NULL) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_set_sig_block(uint32_t sig, uint8_t blocked) {
  sigset_t set; sigemptyset(&set);
  if (sigaddset(&set, (int)sig) < 0) return leanswe_mk_errno(errno);
  int rc = pthread_sigmask(blocked ? SIG_BLOCK : SIG_UNBLOCK, &set, NULL);
  if (rc != 0) return leanswe_mk_errno(rc);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_clear_sig_mask(void) {
  sigset_t set; sigemptyset(&set); pthread_sigmask(SIG_SETMASK, &set, NULL);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_set_nofile_mode(uint8_t mode) {
  struct rlimit rl;
  if (getrlimit(RLIMIT_NOFILE, &rl) < 0) return leanswe_mk_errno(errno);
  pthread_mutex_lock(&g_nofile_mu);
  if (g_saved_nofile_cur == 0u) g_saved_nofile_cur = rl.rlim_cur;
  rl.rlim_cur = g_saved_nofile_cur;
  pthread_mutex_unlock(&g_nofile_mu);
  if (setrlimit(RLIMIT_NOFILE, &rl) < 0) return leanswe_mk_errno(errno);
  if (mode == 0u) return leanswe_mk_ok(lean_box(0));
  int f0 = open("/dev/null", O_RDONLY | O_CLOEXEC);
  if (f0 < 0) return leanswe_mk_errno(errno);
  int f1 = dup(f0); close(f0);
  if (f1 < 0) return leanswe_mk_errno(errno);
  close(f1); rl.rlim_cur = (mode == 1u) ? (rlim_t)f0 : (rlim_t)f1;
  if (setrlimit(RLIMIT_NOFILE, &rl) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_set_core_limit(uint8_t enable) {
  write_text_file("/proc/self/coredump_filter", "0");
  struct rlimit rl;
  if (getrlimit(RLIMIT_CORE, &rl) < 0) return leanswe_mk_errno(errno);
  rlim_t cap = (rl.rlim_max > 65536u) ? 65536u : rl.rlim_max;
  rl.rlim_cur = enable ? cap : (rl.rlim_max > 0 ? 1 : 0);
  if (setrlimit(RLIMIT_CORE, &rl) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_getpgrp(void) {
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)getpgrp()));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_getsid(void) {
  pid_t sid = getsid(0); return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(sid >= 0 ? sid : 0)));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_setpgid(uint32_t pid, uint32_t pgid) {
  if (setpgid((pid_t)(int32_t)pid, (pid_t)(int32_t)pgid) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_drop_cap_kill(void) {
  int err = drop_cap_kill_perm(); return (err != 0) ? leanswe_mk_errno(err) : leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_drop_to_nobody(void) {
  int err = drop_cap_kill_perm();
  if (err != 0) return leanswe_mk_errno(err);
  if (setresgid(65534, 65534, 65534) < 0 || setresuid(65534, 65534, 65534) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_cleanup_child(uint32_t pid) {
  siginfo_t si; memset(&si, 0, sizeof(si)); pid_t target = (pid_t)(int32_t)pid;
  if (target <= 0) return lean_io_result_mk_ok(lean_box(0));
  if (force_kill_child(target)) waitid_nointr((id_t)target, &si, WEXITED | __WALL);
  else waitid_nointr((id_t)target, &si, WEXITED | WNOHANG | __WALL);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_probe_zombie(uint32_t pid) {
  siginfo_t si; memset(&si, 0, sizeof(si));
  int rc = waitid_nointr((id_t)pid, &si, WEXITED | WNOHANG | WNOWAIT | __WALL);
  if (rc < 0) return lean_io_result_mk_ok(mk_pair(lean_box_uint32(3u), lean_box_uint32(0u)));
  if ((uint32_t)si.si_pid != pid) return lean_io_result_mk_ok(mk_pair(lean_box_uint32(0u), lean_box_uint32(0u)));
  if (si.si_code == CLD_EXITED) return lean_io_result_mk_ok(mk_pair(lean_box_uint32(1u), lean_box_uint32((uint32_t)(si.si_status & 0xff))));
  uint32_t dumped = (si.si_code == CLD_DUMPED) ? 0x100u : 0u;
  return lean_io_result_mk_ok(mk_pair(lean_box_uint32(2u), lean_box_uint32((uint32_t)si.si_status | dumped)));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_probe_unshare(void) {
  pid_t p = fork();
  if (p < 0) return lean_io_result_mk_ok(lean_box(0));
  if (p == 0) _exit(unshare(CLONE_NEWUSER | CLONE_NEWPID) == 0 ? 0 : 1);
  int st = 0; pid_t wr = waitpid_nointr(p, &st);
  return lean_io_result_mk_ok(lean_box((wr == p && WIFEXITED(st) && WEXITSTATUS(st) == 0) ? 1u : 0u));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_spawn_sig_probe(void) {
  int sv[2] = {-1, -1};
  if (open_sync_pair(sv) < 0) return leanswe_mk_errno(errno);
  pid_t pid = fuzz_raw_fork();
  if (pid < 0) { int err = errno; close(sv[0]); close(sv[1]); return leanswe_mk_errno(err); }
  if (pid == 0) {
    close(sv[0]); uint64_t all = ~0ULL, pnd = 0ULL; char ch = 'R';
    syscall(SYS_rt_sigprocmask, (long)SIG_SETMASK, &all, (void *)NULL, (size_t)8);
    ssize_t w1 = write(sv[1], &ch, 1), r1 = read(sv[1], &ch, 1); (void)w1; (void)r1;
    syscall(SYS_rt_sigpending, &pnd, (size_t)8);
    ssize_t w2 = write(sv[1], &pnd, sizeof(pnd)); (void)w2; close(sv[1]); _exit(0);
  }
  close(sv[1]); char rdy = 0;
  if (read_nointr(sv[0], &rdy, 1) != 1) {
    siginfo_t si; memset(&si, 0, sizeof(si)); close(sv[0]);
    force_kill_child(pid); waitid_nointr((id_t)pid, &si, WEXITED); return leanswe_mk_errno(EAGAIN);
  }
  lean_obj_res fd_obj = leanswe_mk_fd_obj(sv[0]);
  if (fd_obj == NULL) {
    siginfo_t si; memset(&si, 0, sizeof(si));
    force_kill_child(pid); waitid_nointr((id_t)pid, &si, WEXITED); return leanswe_mk_errno(ENOMEM);
  }
  return leanswe_mk_ok(mk_pair(lean_box_uint32((uint32_t)pid), fd_obj));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_finish_sig_probe(uint32_t pid_u32, b_lean_obj_arg fd_obj) {
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(fd_obj);
  pid_t pid = (pid_t)(int32_t)pid_u32; int sock = -1;
  if (leanswe_fd_box_pin(box, &sock) != 0) return lean_io_result_mk_ok(lean_box_uint64(~0ULL));
  char q = 'Q'; ssize_t s1 = send(sock, &q, 1, MSG_NOSIGNAL); (void)s1;
  siginfo_t si; memset(&si, 0, sizeof(si));
  int wrc = waitid_nointr((id_t)pid, &si, WEXITED | WSTOPPED);
  uint64_t pnd = ~0ULL;
  if (wrc == 0 && si.si_code == CLD_EXITED) {
    if (read_nointr(sock, &pnd, sizeof(pnd)) != (ssize_t)sizeof(pnd)) pnd = ~0ULL;
  } else {
    if (force_kill_child(pid)) waitid_nointr((id_t)pid, &si, WEXITED);
    pnd = (wrc == 0 && si.si_code == CLD_STOPPED) ? (1ULL << 18) : (1ULL << 8);
  }
  leanswe_fd_box_unpin(box); leanswe_fd_box_close(box);
  return lean_io_result_mk_ok(lean_box_uint64(pnd));
}

static void pin_stdio_fd(int target_fd, int open_flags, int replace_cloexec) {
  int flags = fcntl(target_fd, F_GETFD);
  if ((flags < 0 && errno == EBADF) || (replace_cloexec && flags >= 0 && (flags & FD_CLOEXEC) != 0)) {
    int dn = open("/dev/null", open_flags);
    if (dn >= 0 && dn != target_fd) { dup2(dn, target_fd); close(dn); }
  }
}
LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_ensure_stdio(void) {
  pin_stdio_fd(0, O_RDONLY, 0); pin_stdio_fd(1, O_WRONLY, 0); pin_stdio_fd(2, O_WRONLY, 0);
  return lean_io_result_mk_ok(lean_box(0));
}
static void exec_self_ns_worker(uint8_t do_setsid, const char *mode_str, const char *arg_str) {
  pin_stdio_fd(0, O_RDONLY, 1); pin_stdio_fd(1, O_WRONLY, 1); pin_stdio_fd(2, O_WRONLY, 1);
  if (do_setsid) setsid();
  char *argv[7] = {"/proc/self/exe", "--suite", "process", "--ns-worker", (char *)mode_str, (char *)arg_str, NULL};
  execve("/proc/self/exe", argv, environ); _exit(127);
}

static void spawn_host_via_reaper(const char *mode_str, const char *arg_str) {
  prctl(PR_SET_PDEATHSIG, SIGKILL, 0, 0, 0); prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0);
  setsid(); setenv("UV_USE_IO_URING", "0", 1); setenv("LEAN_NUM_THREADS", "1", 1);
  pid_t w = fork();
  if (w < 0) _exit(124);
  if (w == 0) exec_self_ns_worker(0u, mode_str, arg_str);
  signal(SIGHUP, SIG_IGN);
  int st = 0; pid_t r = waitpid_nointr(w, &st); kill(-w, SIGKILL);
  if (r < 0) _exit(123);
  if (WIFEXITED(st)) _exit(WEXITSTATUS(st));
  if (WIFSIGNALED(st)) _exit(128 + WTERMSIG(st));
  _exit(123);
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_run_host_worker(b_lean_obj_arg mode_obj, b_lean_obj_arg arg_obj) {
  const char *mode_str = lean_string_cstr(mode_obj), *arg_str = lean_string_cstr(arg_obj);
  pid_t p1 = fork();
  if (p1 < 0) return leanswe_mk_errno(errno);
  if (p1 == 0) spawn_host_via_reaper(mode_str, arg_str);
  int st1 = 0;
  if (waitpid_nointr(p1, &st1) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box_uint32(WIFEXITED(st1) ? (uint32_t)WEXITSTATUS(st1) : 122u));
}

static void reset_pid1_rt_sigs(void) {
  unblock_and_reset_sig(4u); unblock_and_reset_sig(6u); unblock_and_reset_sig(7u);
  unblock_and_reset_sig(8u); unblock_and_reset_sig(11u); unblock_and_reset_sig(13u);
  unblock_and_reset_sig(14u); unblock_and_reset_sig(24u); unblock_and_reset_sig(30u);
}

static void run_ns_pid1(uint8_t do_setsid, uint8_t as_pid2, const char *mode_str, const char *arg_str) {
  unblock_and_reset_sig(15u);
  setenv("UV_USE_IO_URING", "0", 1); setenv("LEAN_NUM_THREADS", "1", 1);
  if (!as_pid2) exec_self_ns_worker(do_setsid, mode_str, arg_str);
  reset_pid1_rt_sigs();
  pid_t p3 = fork();
  if (p3 < 0) _exit(124);
  if (p3 == 0) exec_self_ns_worker(do_setsid, mode_str, arg_str);
  int st3 = 0; pid_t r = waitpid_nointr(p3, &st3);
  if (r < 0) _exit(123);
  if (WIFEXITED(st3)) _exit(WEXITSTATUS(st3));
  if (WIFSIGNALED(st3)) _exit(128 + WTERMSIG(st3));
  _exit(123);
}

static int exec_idmap(const char *bin, pid_t target, unsigned long orig, const char *sub) {
  if (!sub || sub[0] == '\0') return -1;
  pid_t p = fork();
  if (p < 0) return -1;
  if (p == 0) {
    char pids[24], origs[24];
    snprintf(pids, sizeof(pids), "%d", (int)target); snprintf(origs, sizeof(origs), "%lu", orig);
    char *argv[9] = {(char *)bin, pids, "0", origs, "1", "65534", (char *)sub, "1", NULL};
    execv(bin, argv); _exit(127);
  }
  int st = 0;
  return (waitpid_nointr(p, &st) >= 0 && WIFEXITED(st) && WEXITSTATUS(st) == 0) ? 0 : -1;
}

static void sync_and_map_subid(pid_t p_mid, int sv0, uint8_t ns_flags, uid_t u, gid_t g) {
  char ch = 0; ssize_t r1 = read(sv0, &ch, 1); (void)r1; int id_ok = 1;
  if ((ns_flags & 4u) != 0u) {
    if (exec_idmap("/usr/bin/newgidmap", p_mid, (unsigned long)g, getenv("LEANSWE_SUBGID")) != 0 ||
        exec_idmap("/usr/bin/newuidmap", p_mid, (unsigned long)u, getenv("LEANSWE_SUBUID")) != 0) id_ok = 0;
  }
  ssize_t w1 = write(sv0, id_ok ? "1" : "0", 1); (void)w1;
}

static void run_ns_mid(int sv1, uint8_t ns_flags, uid_t u, gid_t g, const char *mode_str, const char *arg_str) {
  setpgid(0, 0);
  if (unshare(CLONE_NEWUSER | CLONE_NEWPID) < 0) { close(sv1); _exit(125); }
  ssize_t w0 = write(sv1, "1", 1); char ack = '0'; ssize_t r0 = read(sv1, &ack, 1);
  (void)w0; (void)r0;
  if (ack != '1') {
    if ((ns_flags & 8u) != 0u) { close(sv1); _exit(126); }
    map_self_uid_gid(u, g);
  }
  pid_t p2 = fork();
  if (p2 < 0) { close(sv1); _exit(124); }
  if (p2 == 0) { close(sv1); run_ns_pid1((ns_flags & 1u) != 0u, (ns_flags & 2u) != 0u, mode_str, arg_str); }
  ssize_t w2 = write(sv1, &p2, sizeof(p2)); (void)w2; close(sv1);
  _exit(0);
}

static void finish_ns_reap(
    uint8_t ns_flags, const char *mode_str, const char *arg_str,
    pid_t p_mid, pid_t p2, pid_t r2, int st2, int err) {
  if (r2 < 0 || !WIFEXITED(st2) || WEXITSTATUS(st2) != 0) {
    fprintf(stderr, "ns-worker-fail mode=%s arg=%s flags=%u p1=%d p_mid=%d p2=%d reaped=%d st2=0x%x exited=%d code=%d signaled=%d sig=%d errno=%d\n",
            mode_str, arg_str, (unsigned)ns_flags, (int)getpid(), (int)p_mid, (int)p2, (int)r2, (unsigned)st2,
            WIFEXITED(st2) ? 1 : 0, WIFEXITED(st2) ? WEXITSTATUS(st2) : -1, WIFSIGNALED(st2) ? 1 : 0, WIFSIGNALED(st2) ? WTERMSIG(st2) : 0, err);
    fflush(stderr);
  }
  if (r2 < 0) _exit(123);
  if (WIFEXITED(st2)) _exit(WEXITSTATUS(st2));
  if (WIFSIGNALED(st2)) _exit(128 + WTERMSIG(st2));
  _exit(123);
}

static void spawn_ns_via_reaper(uint8_t ns_flags, const char *mode_str, const char *arg_str) {
  int sv[2];
  if (open_sync_pair(sv) < 0) _exit(124);
  prctl(PR_SET_PDEATHSIG, SIGKILL, 0, 0, 0); prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0); setpgid(0, 0);
  uid_t u = geteuid(); gid_t g = getegid(); pid_t p_mid = fork();
  if (p_mid < 0) _exit(124);
  if (p_mid == 0) { close(sv[0]); run_ns_mid(sv[1], ns_flags, u, g, mode_str, arg_str); }
  close(sv[1]); sync_and_map_subid(p_mid, sv[0], ns_flags, u, g);
  int stm = 0, st2 = 0; pid_t p2 = -1;
  if (waitpid_nointr(p_mid, &stm) < 0 || !WIFEXITED(stm) || WEXITSTATUS(stm) != 0) { close(sv[0]); _exit(125); }
  ssize_t rd = read_nointr(sv[0], &p2, sizeof(p2)); close(sv[0]);
  if (rd != (ssize_t)sizeof(p2) || p2 <= 0) finish_ns_reap(ns_flags, mode_str, arg_str, p_mid, p2, -1, 0, EIO);
  pid_t r2 = waitpid_nointr(p2, &st2);
  finish_ns_reap(ns_flags, mode_str, arg_str, p_mid, p2, r2, st2, (r2 < 0) ? errno : 0);
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_run_ns_worker(
    uint8_t do_setsid, uint32_t ns_flags, b_lean_obj_arg mode_obj, b_lean_obj_arg arg_obj) {
  const char *mode_str = lean_string_cstr(mode_obj), *arg_str = lean_string_cstr(arg_obj);
  uint8_t flags = (uint8_t)((do_setsid ? 1u : 0u) | (ns_flags & 14u));
  pid_t p1 = fork();
  if (p1 < 0) return leanswe_mk_errno(errno);
  if (p1 == 0) spawn_ns_via_reaper(flags, mode_str, arg_str);
  int st1 = 0;
  if (waitpid_nointr(p1, &st1) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box_uint32(WIFEXITED(st1) ? (uint32_t)WEXITSTATUS(st1) : 122u));
}

static int resolve_proc_sys_nr(uint8_t op_kind) {
  switch (op_kind) {
    case 0: return SYS_pipe2; case 1: return SYS_wait4; case 2: return SYS_kill;
    case 3: return SYS_pidfd_open; case 4: return SYS_pidfd_send_signal; case 5: return SYS_getpid;
    default: return SYS_getuid;
  }
}

static int install_seccomp_prog(struct sock_filter *filter, unsigned short len) {
  struct sock_fprog prog = { len, filter };
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) < 0) return errno;
  if (prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog) < 0) return errno;
  return 0;
}

static int install_seccomp_errno_nr(int sys_nr, uint32_t err_num) {
  struct sock_filter filter[7] = {
    { (uint16_t)(BPF_LD | BPF_W | BPF_ABS), 0u, 0u, (uint32_t)offsetof(struct seccomp_data, arch) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 1u, 0u, (uint32_t)LEANSWE_AUDIT_ARCH },
    { (uint16_t)(BPF_RET | BPF_K), 0u, 0u, (uint32_t)SECCOMP_RET_ALLOW },
    { (uint16_t)(BPF_LD | BPF_W | BPF_ABS), 0u, 0u, (uint32_t)offsetof(struct seccomp_data, nr) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 0u, 1u, (uint32_t)sys_nr },
    { (uint16_t)(BPF_RET | BPF_K), 0u, 0u, (uint32_t)(SECCOMP_RET_ERRNO | (err_num & 0x0000ffffu)) },
    { (uint16_t)(BPF_RET | BPF_K), 0u, 0u, (uint32_t)SECCOMP_RET_ALLOW },
  };
  return install_seccomp_prog(filter, (unsigned short)7);
}

static int install_seccomp_wait4_neg1(uint32_t err_num) {
  struct sock_filter filter[9] = {
    { (uint16_t)(BPF_LD | BPF_W | BPF_ABS), 0u, 0u, (uint32_t)offsetof(struct seccomp_data, arch) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 1u, 0u, (uint32_t)LEANSWE_AUDIT_ARCH },
    { (uint16_t)(BPF_RET | BPF_K), 0u, 0u, (uint32_t)SECCOMP_RET_ALLOW },
    { (uint16_t)(BPF_LD | BPF_W | BPF_ABS), 0u, 0u, (uint32_t)offsetof(struct seccomp_data, nr) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 0u, 3u, (uint32_t)SYS_wait4 },
    { (uint16_t)(BPF_LD | BPF_W | BPF_ABS), 0u, 0u, (uint32_t)offsetof(struct seccomp_data, args[0]) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 0u, 1u, 0xffffffffu },
    { (uint16_t)(BPF_RET | BPF_K), 0u, 0u, (uint32_t)(SECCOMP_RET_ERRNO | (err_num & 0x0000ffffu)) },
    { (uint16_t)(BPF_RET | BPF_K), 0u, 0u, (uint32_t)SECCOMP_RET_ALLOW },
  };
  return install_seccomp_prog(filter, (unsigned short)9);
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_install_seccomp_errno(uint8_t op_kind, uint32_t err_num) {
  if (err_num == 0u || err_num > 4095u || err_num == (uint32_t)EFAULT) return leanswe_mk_errno(EINVAL);
  int err = (op_kind == 7u) ? install_seccomp_wait4_neg1(err_num) : install_seccomp_errno_nr(resolve_proc_sys_nr(op_kind), err_num);
  if (err != 0) return leanswe_mk_errno(err);
  return leanswe_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_check_seccomp_efault_abort(void) {
  pid_t p = fork();
  if (p < 0) return leanswe_mk_errno(errno);
  if (p == 0) {
    struct rlimit rl = {0, 0}; setrlimit(RLIMIT_CORE, &rl);
    if (install_seccomp_errno_nr(SYS_pidfd_open, (uint32_t)EFAULT) != 0) _exit(125);
    (void)call_sys_pidfd_open((uint32_t)getpid(), 0ull);
    _exit(124);
  }
  int st = 0;
  if (waitpid_nointr(p, &st) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box((WIFSIGNALED(st) && WTERMSIG(st) == SIGABRT) ? 1u : 0u));
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_check_pidfd_fd0(void) {
  pid_t p = fork();
  if (p < 0) return leanswe_mk_errno(errno);
  if (p == 0) {
    close(0);
    lean_obj_res r0 = call_sys_pidfd_open((uint32_t)getpid(), 0ull);
    lean_obj_res r1 = call_sys_pidfd_open((uint32_t)getpid(), 1ull);
    lean_object *e0 = lean_ctor_get(r0, 0), *e1 = lean_ctor_get(r1, 0);
    int f1 = (lean_obj_tag(e1) == 1u) ? ((LeanFdBox *)lean_get_external_data(lean_ctor_get(e1, 0)))->fd : -1;
    uint8_t ok = (lean_obj_tag(e0) == 1u && f1 >= 0 && (fcntl(f1, F_GETFL) & O_NONBLOCK) != 0) ? 1u : 0u;
    lean_dec(r1); lean_dec(r0);
    _exit(ok ? 0 : 1);
  }
  int st = 0;
  if (waitpid_nointr(p, &st) < 0) return leanswe_mk_errno(errno);
  return leanswe_mk_ok(lean_box((WIFEXITED(st) && WEXITSTATUS(st) == 0) ? 1u : 0u));
}

typedef struct { LeanFdBox *box; int expected_fd; uint32_t err_num; int ok; } SeccompCloseArg;

static int is_expected_close_detach(uint32_t e) {
  return e == (uint32_t)EBADF || e == (uint32_t)EINTR || e == (uint32_t)EIO || e == (uint32_t)ENOSPC ||
         e == (uint32_t)EDQUOT || e == (uint32_t)ENOMEM || e == (uint32_t)ESTALE || e == (uint32_t)ECONNRESET;
}

static int verify_post_seccomp_close(LeanFdBox *box, int expected_fd, int detach) {
  int pfd = -1, pin_rc = leanswe_fd_box_pin(box, &pfd);
  if (detach) return (pin_rc == EBADF && leanswe_fd_box_close(box) == EBADF) ? 1 : 0;
  ssize_t wr = (pin_rc == 0) ? write(pfd, "K", 1) : -1;
  if (pin_rc == 0) leanswe_fd_box_unpin(box);
  return (pin_rc == 0 && pfd == expected_fd && wr == 1) ? 1 : 0;
}

static void *seccomp_close_thread_entry(void *raw) {
  SeccompCloseArg *a = (SeccompCloseArg *)raw;
  int sc = install_seccomp_errno_nr(SYS_close, a->err_num);
  int c1 = (sc == 0) ? leanswe_fd_box_close(a->box) : -1;
  int det = is_expected_close_detach(a->err_num);
  a->ok = (sc == 0 && c1 == (int)a->err_num && verify_post_seccomp_close(a->box, a->expected_fd, det)) ? 1 : 0;
  return NULL;
}

LEAN_EXPORT lean_obj_res leanswe_proc_fuzz_check_fd_close_seccomp(uint32_t err_num) {
  int fds[2] = {-1, -1};
  if (pipe2(fds, O_CLOEXEC | O_NONBLOCK) < 0) return leanswe_mk_errno(errno);
  int wfd = fds[1], bfd = -1;
  lean_obj_res box_obj = leanswe_mk_fd_obj(wfd);
  if (box_obj == NULL) { close(fds[0]); return leanswe_mk_errno(ENOMEM); }
  lean_mark_mt(box_obj);
  LeanFdBox *box = (LeanFdBox *)lean_get_external_data(box_obj);
  int bp = leanswe_fd_box_pin(box, &bfd);
  int busy_ok = (bp == 0 && bfd == wfd && leanswe_fd_box_close(box) == EBUSY);
  if (bp == 0) leanswe_fd_box_unpin(box);
  SeccompCloseArg arg = { box, wfd, err_num, 0 };
  pthread_t th; int prc = pthread_create(&th, NULL, seccomp_close_thread_entry, &arg);
  if (prc != 0) { lean_dec(box_obj); close(fds[0]); return leanswe_mk_errno(prc); }
  pthread_join(th, NULL);
  if (is_expected_close_detach(err_num)) {
    lean_dec(box_obj); if (busy_ok) close(wfd); close(fds[0]);
    return leanswe_mk_ok(lean_box((uint8_t)(busy_ok && arg.ok)));
  }
  char ch = 0;
  int pre_open = (read(fds[0], &ch, 1) == 1 && ch == 'K' && read(fds[0], &ch, 1) < 0 && errno == EAGAIN);
  lean_dec(box_obj);
  int finalized = (read(fds[0], &ch, 1) == 0);
  close(fds[0]);
  return leanswe_mk_ok(lean_box((uint8_t)(busy_ok && arg.ok && pre_open && finalized)));
}
