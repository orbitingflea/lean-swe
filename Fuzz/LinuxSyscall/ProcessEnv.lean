import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types

namespace Fuzz.LinuxSyscall.ProcessEnv

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Process

/-- Close a `RawFd` boxed via `LeanFdBox` using `leanswe_fd_box_close`. -/
@[extern "leanswe_proc_close_fd"]
opaque closeFd (fd : @& RawFd) : IO (Except Errno Unit)

/-- Spawn a controlled sleeping child in requested `pgidReq` (`0` = own pgid, `-1` = inherit, `> 0` = join pgid), optionally resetting `SIGCHLD` to `SIG_DFL`. -/
@[extern "leanswe_proc_fuzz_spawn_controlled"]
opaque spawnControlled (pgidReq : Int32) (resetSigchld : Bool) : IO (Except Errno (UInt32 × UInt32))

/-- Spawn an autonomous child that sleeps `delayUs` microseconds and exits with `exitCode`. -/
@[extern "leanswe_proc_fuzz_spawn_autonomous"]
opaque spawnAutonomous (pgidReq : Int32) (delayUs : UInt32) (exitCode : UInt8) : IO (Except Errno (UInt32 × UInt32))

/-- Spawn a child that immediately stops itself via `stopSig` (`waitid WSTOPPED|WNOWAIT` synchronized). -/
@[extern "leanswe_proc_fuzz_spawn_stopped"]
opaque spawnStopped (pgidReq : Int32) (stopSig : UInt32) : IO (Except Errno (UInt32 × UInt32))

/-- Spawn a child that immediately terminates (`isSig = true` sends `codeOrSig`, `false` calls `_exit`), returning `((pid, pgid), dumpedCore)`. -/
@[extern "leanswe_proc_fuzz_spawn_zombie"]
opaque spawnZombie (pgidReq : Int32) (isSig : Bool) (codeOrSig : UInt32) (allowCore : Bool) :
    IO (Except Errno ((UInt32 × UInt32) × Bool))

/-- Spawn an in-process non-leader thread returning `(tid, (ctlWriteFd, pthreadHandle))`. -/
@[extern "leanswe_proc_fuzz_spawn_thread"]
opaque spawnThread : IO (Except Errno (UInt32 × (UInt32 × UInt64)))

/-- Spawn a persistent sibling thread that forks a controlled child, returning `((childPid, childPgid), (siblingTid, threadHandle))`. -/
@[extern "leanswe_proc_fuzz_spawn_sibling_child"]
opaque spawnSiblingChild (pgidReq : Int32) : IO (Except Errno ((UInt32 × UInt32) × (UInt32 × UInt64)))

/-- Signal and join a spawned helper thread. -/
@[extern "leanswe_proc_fuzz_join_thread"]
opaque joinThread (ctlWr : UInt32) (handle : UInt64) : IO Unit

/-- Spawn a `clone(..., 0)` child (`__WCLONE`, non-`SIGCHLD` exit signal), optionally exiting immediately with `exitCode`. -/
@[extern "leanswe_proc_fuzz_spawn_clone_child"]
opaque spawnCloneChild (pgidReq : Int32) (immediateExit : Bool) (exitCode : UInt8) :
    IO (Except Errno (UInt32 × UInt32))

/-- Spawn a controlled child containing a live non-leader kernel thread, returning `(childPid, (childPgid, workerTid))`. -/
@[extern "leanswe_proc_fuzz_spawn_threaded_child"]
opaque spawnThreadedChild (pgidReq : Int32) : IO (Except Errno (UInt32 × (UInt32 × UInt32)))

/-- Spawn a delayed-zombie child whose leader exited via `SYS_exit(exitCode)` while a non-leader worker thread sleeps (`subDelayUs = 0` pauses indefinitely; `> 0` calls `SYS_exit(subExitCode)` after `subDelayUs` microseconds), returning `(childPid, (childPgid, workerTid))`. -/
@[extern "leanswe_proc_fuzz_spawn_delayed_zombie"]
opaque spawnDelayedZombie (pgidReq : Int32) (exitCode : UInt8) (subDelayUs : UInt32 := 0)
    (subExitCode : UInt8 := exitCode) : IO (Except Errno (UInt32 × (UInt32 × UInt32)))

/-- Probe whether the host kernel supports `pidfd_open(..., PIDFD_THREAD)` directly via raw `syscall`, bypassing `process_shim.c`. -/
@[extern "leanswe_proc_fuzz_probe_pidfd_thread_raw"]
opaque probeKernelPidfdThread : IO Bool

/-- Probe whether the host kernel supports `pipe2(..., O_NOTIFICATION_PIPE)` directly in C, bypassing `process_shim.c`. -/
@[extern "leanswe_proc_fuzz_probe_watch_queue_raw"]
opaque probeKernelWatchQueue : IO Bool

/-- Spawn a grandchild whose immediate parent exits immediately so it reparents to the caller (under `PR_SET_CHILD_SUBREAPER` or `PID 1`). -/
@[extern "leanswe_proc_fuzz_spawn_reparented_grandchild"]
opaque spawnReparentedGrandchild (pgidReq : Int32) : IO (Except Errno (UInt32 × UInt32))

/-- Configure `PR_SET_CHILD_SUBREAPER` (`1` = enable, `0` = disable) for the calling process. -/
@[extern "leanswe_proc_fuzz_set_subreaper"]
opaque setSubreaper (enable : Bool) : IO (Except Errno Unit)

/-- Configure `SIGCHLD` disposition (`0 = SIG_DFL`, `1 = SIG_IGN`, `2 = SA_NOCLDWAIT`, `3 = SA_NOCLDSTOP`, `4 = SA_NOCLDWAIT|SA_NOCLDSTOP`). -/
@[extern "leanswe_proc_fuzz_set_sigchld_autoreap"]
opaque setSigchldAutoreap (mode : UInt8) : IO (Except Errno Unit)

/-- Set disposition of `sig` to `SIG_IGN` (`ign = true`) or `SIG_DFL` (`ign = false`). -/
@[extern "leanswe_proc_fuzz_set_sig_ign"]
opaque setSigIgn (sig : UInt32) (ign : Bool) : IO (Except Errno Unit)

/-- Block (`blocked = true`) or unblock (`blocked = false`) `sig` in the calling thread signal mask via `pthread_sigmask`. -/
@[extern "leanswe_proc_fuzz_set_sig_block"]
opaque setSigBlock (sig : UInt32) (blocked : Bool) : IO (Except Errno Unit)

/-- Reset the calling process signal mask to empty via `sigprocmask(SIG_SETMASK, empty)`. -/
@[extern "leanswe_proc_fuzz_clear_sig_mask"]
opaque clearSigMask : IO Unit

/-- Temporarily tighten `RLIMIT_NOFILE` (`0 = restore`, `1 = 0 free FDs`, `2 = 1 free FD`) to exercise `EMFILE`. -/
@[extern "leanswe_proc_fuzz_set_nofile_mode"]
opaque setNofileMode (mode : UInt8) : IO (Except Errno Unit)

/-- Set `RLIMIT_CORE` soft limit to `rlim_max` (`true`) or `0`/`1` (`false`). -/
@[extern "leanswe_proc_fuzz_set_core_limit"]
opaque setCoreLimit (enable : Bool) : IO (Except Errno Unit)

/-- Query the calling process's process group ID via `getpgrp()`. -/
@[extern "leanswe_proc_fuzz_getpgrp"]
opaque getpgrp : IO UInt32

/-- Query the calling process's session ID via `getsid(0)`. -/
@[extern "leanswe_proc_fuzz_getsid"]
opaque getsid : IO UInt32

/-- Probe whether the calling process is currently in an orphaned process group (`SIGTTIN` dropped). -/
@[extern "leanswe_proc_fuzz_is_self_pgid_orphaned"]
opaque isSelfPgidOrphaned : IO Bool

/-- Query `(F_GETFD, F_GETFL)` flags on a `RawFd` handle using `fcntl(2)`. -/
@[extern "leanswe_proc_fuzz_get_fd_flags"]
opaque getFdFlags (fd : @& RawFd) : IO (Except Errno (UInt32 × UInt32))

/-- Move `pid` into process group `pgid` via `setpgid(2)`. -/
@[extern "leanswe_proc_fuzz_setpgid"]
opaque setpgid (pid : UInt32) (pgid : UInt32) : IO (Except Errno Unit)

/-- Drop `CAP_KILL` from effective, permitted, and bounding capability sets. -/
@[extern "leanswe_proc_fuzz_drop_cap_kill"]
opaque dropCapKill : IO (Except Errno Unit)

/-- Drop `CAP_KILL` and switch real/effective/saved UID/GID to `65534`. -/
@[extern "leanswe_proc_fuzz_drop_to_nobody"]
opaque dropToNobody : IO (Except Errno Unit)

/-- Forcefully kill and reap a helper child PID if still present (`kill` with `pidfd_send_signal` seccomp fallback). -/
@[extern "leanswe_proc_fuzz_cleanup_child"]
opaque cleanupChild (pid : UInt32) : IO Unit

/-- Non-destructively probe whether child `pid` is live (`0`), a confirmed zombie (`1` exited / `2` signaled), or reaped (`3`). -/
@[extern "leanswe_proc_fuzz_probe_zombie"]
opaque probeZombie (pid : UInt32) : IO (UInt32 × UInt32)

/-- Probe whether unprivileged `unshare(CLONE_NEWUSER | CLONE_NEWPID)` succeeds in a forked helper. -/
@[extern "leanswe_proc_fuzz_probe_unshare"]
opaque probeUnshare : IO Bool

/-- Reopen closed file descriptors `0`, `1`, and `2` (`EBADF`) on `/dev/null` without replacing live descriptors. -/
@[extern "leanswe_proc_fuzz_ensure_stdio"]
opaque ensureStdio : IO Unit

/-- Execute `/proc/self/exe --suite process --ns-worker <mode> <arg>` inside an isolated `setsid` subreaper session on the host. -/
@[extern "leanswe_proc_fuzz_run_host_worker"]
opaque runHostWorker (mode : @& String) (arg : @& String) : IO (Except Errno UInt32)

/-- Execute `/proc/self/exe --suite process --ns-worker <mode> <arg>` inside an isolated `CLONE_NEWUSER | CLONE_NEWPID` namespace (`nsFlags`: bit1=`asPid2`, bit2=`mapUid0`, bit3=`strictSubid`). -/
@[extern "leanswe_proc_fuzz_run_ns_worker"]
opaque runNsWorker (doSetsid : Bool) (nsFlags : UInt32) (mode : @& String) (arg : @& String) :
    IO (Except Errno UInt32)

/-- Install a cBPF `seccomp` `SECCOMP_RET_ERRNO` filter in the calling process for syscall index `opKind` (`0..6`, `7 = wait4(pid == -1)`) returning `errNum` (`1..4095`, `!= EFAULT`). -/
@[extern "leanswe_proc_fuzz_install_seccomp_errno"]
opaque installSeccompErrno (opKind : UInt8) (errNum : UInt32) : IO (Except Errno Unit)

/-- Fork a child with `SECCOMP_RET_ERRNO | EFAULT` on `pidfd_open` and verify `fd_box.h` calls `abort()` (`SIGABRT`). -/
@[extern "leanswe_proc_fuzz_check_seccomp_efault_abort"]
opaque checkSeccompEfaultAbort : IO (Except Errno Bool)

/-- Fork a child with FD `0` closed and verify `leanswe_sys_pidfd_open` succeeds returning `ok` even when `fd == 0`. -/
@[extern "leanswe_proc_fuzz_check_pidfd_fd0"]
opaque checkPidfdFd0 : IO (Except Errno Bool)

/-- Install `SECCOMP_RET_ERRNO | errNum` on `SYS_close` in a temporary thread of the calling process, verify `fd_box.h` close-detach vs keep-open semantics, and verify unsandboxed finalization closes kept FDs. -/
@[extern "leanswe_proc_fuzz_check_fd_close_seccomp"]
opaque checkFdCloseSeccomp (errNum : UInt32) : IO (Except Errno Bool)

/-- Spawn a non-`PID 1` helper child with all blockable signals masked (`SYS_rt_sigprocmask`), returning `(childPid, syncSock)` for `/proc`-independent `SYS_rt_sigpending` probing. -/
@[extern "leanswe_proc_fuzz_spawn_sig_probe"]
opaque spawnSigPendingProbe : IO (Except Errno (UInt32 × RawFd))

/-- Query the `SYS_rt_sigpending` bitmask (`0` iff no signal `1..64` was delivered/queued) and reap the helper child from `spawnSigPendingProbe`. -/
@[extern "leanswe_proc_fuzz_finish_sig_probe"]
opaque finishSigPendingProbe (pid : UInt32) (sock : @& RawFd) : IO UInt64

end Fuzz.LinuxSyscall.ProcessEnv
