#if !defined(__linux__) || (!defined(__x86_64__) && !defined(__aarch64__)) || !defined(__LP64__)
#error "LeanSwe LinuxSyscall requires LP64 Linux on x86_64 or aarch64"
#endif
#define _GNU_SOURCE
#include <lean/lean.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

static pthread_mutex_t g_sig_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_once_t g_atfork_once = PTHREAD_ONCE_INIT;
static pid_t g_sig_pid = 0; static int g_sigalrm_refs = 0, g_prev_saved = 0;
static struct sigaction g_prev_sigalrm;
static __thread pid_t t_timer_pid = 0; static __thread int t_armed = 0, t_timer_active = 0;
static __thread timer_t t_timer_id; static __thread sigset_t t_prev_mask;
static void atfork_prepare(void) { pthread_mutex_lock(&g_sig_mu); }
static void atfork_unlock(void) { pthread_mutex_unlock(&g_sig_mu); }
static void register_atfork(void) { pthread_atfork(atfork_prepare, atfork_unlock, atfork_unlock); }
static void sync_sig_pid(pid_t cur_pid) {
  if (g_sig_pid != cur_pid) {
    g_sig_pid = cur_pid; g_sigalrm_refs = t_armed;
    if (!t_armed) { g_prev_saved = 0; }
  }
}
static void fuzz_sigalrm_handler(int signo) { (void)signo; }
static void arm_thread_timer(pid_t cur_pid, uint32_t usec) {
  if (t_timer_active && t_timer_pid != cur_pid) { t_timer_active = 0; }
  if (usec > 0u && !t_timer_active) {
    struct sigevent sev; memset(&sev, 0, sizeof(sev));
    sev.sigev_notify = SIGEV_THREAD_ID; sev.sigev_signo = SIGALRM; sev._sigev_un._tid = (pid_t)syscall(SYS_gettid);
    if (timer_create(CLOCK_MONOTONIC, &sev, &t_timer_id) < 0) { abort(); }
    t_timer_active = 1; t_timer_pid = cur_pid;
  }
  if (t_timer_active) {
    struct itimerspec its; memset(&its, 0, sizeof(its));
    its.it_value.tv_sec = (time_t)(usec / 1000000u); its.it_value.tv_nsec = (long)((usec % 1000000u) * 1000u);
    its.it_interval = its.it_value;
    if (timer_settime(t_timer_id, 0, &its, NULL) < 0) { abort(); }
  }
}
/** Unblock `SIGALRM`, install the signal handler (`SA_RESTART` optional), and arm or disarm (`usec = 0`) the thread-directed `CLOCK_MONOTONIC` timer. */
LEAN_EXPORT lean_obj_res leanswe_fuzz_arm_sigalrm(uint32_t usec, uint8_t sa_restart) {
  pthread_once(&g_atfork_once, register_atfork);
  pid_t cur_pid = getpid();
  struct sigaction sa; memset(&sa, 0, sizeof(sa));
  sa.sa_handler = fuzz_sigalrm_handler; sigemptyset(&sa.sa_mask); sa.sa_flags = sa_restart ? SA_RESTART : 0;
  pthread_mutex_lock(&g_sig_mu);
  sync_sig_pid(cur_pid);
  if (sigaction(SIGALRM, &sa, g_prev_saved ? NULL : &g_prev_sigalrm) < 0) { abort(); }
  g_prev_saved = 1;
  if (!t_armed) { g_sigalrm_refs++; }
  pthread_mutex_unlock(&g_sig_mu);
  if (!t_armed) {
    sigset_t unblock; sigemptyset(&unblock); sigaddset(&unblock, SIGALRM);
    if (pthread_sigmask(SIG_UNBLOCK, &unblock, &t_prev_mask) != 0) { abort(); } t_armed = 1;
  }
  arm_thread_timer(cur_pid, usec); return lean_box(0);
}
static void disarm_global_sigalrm(pid_t cur_pid) {
  pthread_mutex_lock(&g_sig_mu);
  sync_sig_pid(cur_pid);
  if (g_sigalrm_refs > 0) { g_sigalrm_refs--; }
  if (g_sigalrm_refs == 0 && g_prev_saved) {
    struct sigaction ign; memset(&ign, 0, sizeof(ign));
    ign.sa_handler = SIG_IGN; sigemptyset(&ign.sa_mask);
    if (sigaction(SIGALRM, &ign, NULL) < 0 || sigaction(SIGALRM, &g_prev_sigalrm, NULL) < 0) { abort(); }
    g_prev_saved = 0;
  }
  pthread_mutex_unlock(&g_sig_mu);
}
/** Delete the thread-directed timer and flush any pending `SIGALRM` before restoring the previous handler and signal mask. */
LEAN_EXPORT lean_obj_res leanswe_fuzz_disarm_sigalrm(uint32_t unused) {
  (void)unused; pthread_once(&g_atfork_once, register_atfork);
  pid_t cur_pid = getpid();
  if (t_timer_active && t_timer_pid != cur_pid) { t_timer_active = 0; }
  if (t_timer_active) { if (timer_delete(t_timer_id) < 0) { abort(); } t_timer_active = 0; }
  if (t_armed) {
    disarm_global_sigalrm(cur_pid);
    if (pthread_sigmask(SIG_SETMASK, &t_prev_mask, NULL) != 0) { abort(); } t_armed = 0;
  }
  return lean_box(0);
}
