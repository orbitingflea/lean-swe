#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__))
#error "LeanSwe LinuxSyscall requires Linux on x86_64 or aarch64"
#endif

#define _GNU_SOURCE
#include <errno.h>
#include <lean/lean.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

#if defined(__x86_64__)
#define LEANSWE_AUDIT_ARCH AUDIT_ARCH_X86_64
#else
#define LEANSWE_AUDIT_ARCH AUDIT_ARCH_AARCH64
#endif

static int g_sigalrm_armed = 0;
static int g_timer_active = 0;
static timer_t g_timer_id;
static struct sigaction g_prev_sigalrm;

static void fuzz_sigalrm_handler(int signo) {
  (void)signo;
}

/** Install a `SIGALRM` handler (`SA_RESTART` optional) and arm a periodic thread-directed `CLOCK_MONOTONIC` timer in microseconds. */
lean_obj_res leanswe_fuzz_arm_sigalrm(uint32_t usec, uint8_t sa_restart) {
  struct sigaction sa;
  memset(&sa, 0, sizeof(sa));
  sa.sa_handler = fuzz_sigalrm_handler;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = sa_restart ? SA_RESTART : 0;
  if (sigaction(SIGALRM, &sa, g_sigalrm_armed ? NULL : &g_prev_sigalrm) < 0) {
    abort();
  }
  g_sigalrm_armed = 1;
  struct sigevent sev;
  memset(&sev, 0, sizeof(sev));
  sev.sigev_notify = SIGEV_THREAD_ID;
  sev.sigev_signo = SIGALRM;
  sev._sigev_un._tid = (pid_t)syscall(SYS_gettid);
  if (!g_timer_active) {
    if (timer_create(CLOCK_MONOTONIC, &sev, &g_timer_id) < 0) {
      abort();
    }
    g_timer_active = 1;
  }
  struct itimerspec its;
  memset(&its, 0, sizeof(its));
  its.it_value.tv_sec = (time_t)(usec / 1000000u);
  its.it_value.tv_nsec = (long)((usec % 1000000u) * 1000u);
  its.it_interval = its.it_value;
  if (usec > 0 && timer_settime(g_timer_id, 0, &its, NULL) < 0) {
    abort();
  }
  return lean_box(0);
}

/** Delete the thread-directed timer and flush any pending `SIGALRM` before restoring the previous handler. */
lean_obj_res leanswe_fuzz_disarm_sigalrm(uint32_t unused) {
  (void)unused;
  if (g_timer_active) {
    if (timer_delete(g_timer_id) < 0) {
      abort();
    }
    g_timer_active = 0;
  }
  if (g_sigalrm_armed) {
    struct sigaction ign;
    memset(&ign, 0, sizeof(ign));
    ign.sa_handler = SIG_IGN;
    sigemptyset(&ign.sa_mask);
    if (sigaction(SIGALRM, &ign, NULL) < 0 || sigaction(SIGALRM, &g_prev_sigalrm, NULL) < 0) {
      abort();
    }
    g_sigalrm_armed = 0;
  }
  return lean_box(0);
}

/** Install a process-wide `SECCOMP_RET_ERRNO` filter returning `eno` (`1..4095`) on the masked `TimeRand` syscalls (`bit0=clock_gettime`, `bit1=clock_nanosleep`, `bit2=getrandom`). */
uint32_t leanswe_fuzz_install_seccomp_errno(uint32_t eno, uint32_t syscall_mask) {
  if (eno == 0u || eno > 4095u) {
    return (uint32_t)EINVAL;
  }
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) < 0) {
    return (uint32_t)errno;
  }
  uint32_t nr0 = (syscall_mask & 1u) ? (uint32_t)__NR_clock_gettime : 0x7FFFFFFFu;
  uint32_t nr1 = (syscall_mask & 2u) ? (uint32_t)__NR_clock_nanosleep : 0x7FFFFFFFu;
  uint32_t nr2 = (syscall_mask & 4u) ? (uint32_t)__NR_getrandom : 0x7FFFFFFFu;
  struct sock_filter filter[] = {
    { (uint16_t)(BPF_LD | BPF_W | BPF_ABS), 0, 0, (uint32_t)offsetof(struct seccomp_data, arch) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 0, 5, (uint32_t)LEANSWE_AUDIT_ARCH },
    { (uint16_t)(BPF_LD | BPF_W | BPF_ABS), 0, 0, (uint32_t)offsetof(struct seccomp_data, nr) },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 2, 0, nr0 },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 1, 0, nr1 },
    { (uint16_t)(BPF_JMP | BPF_JEQ | BPF_K), 0, 1, nr2 },
    { (uint16_t)(BPF_RET | BPF_K), 0, 0, SECCOMP_RET_ERRNO | (eno & 0x0000FFFFu) },
    { (uint16_t)(BPF_RET | BPF_K), 0, 0, SECCOMP_RET_ALLOW },
  };
  struct sock_fprog prog = {
    (unsigned short)(sizeof(filter) / sizeof(filter[0])),
    filter,
  };
  if (syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, 0, &prog) < 0) {
    return (uint32_t)errno;
  }
  return 0u;
}
