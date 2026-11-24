import Aeneas

open Aeneas Aeneas.Std Result

set_option linter.dupNamespace false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanSwe.PostFork.Aeneas.Internal.World

/-- Raw byte sequence representing a NUL-free path, argument, environment entry, or pipe payload. -/
abbrev Bytes := List Std.U8

/-- Kernel open-file-description identifier shared across duplicated file descriptors. -/
abbrev Desc := Nat

/-- One open slot in the child process's file descriptor table. -/
structure FdEntry where
  /-- Underlying kernel open file description. -/
  desc : Desc
  /-- Close-on-exec descriptor flag (`FD_CLOEXEC`, bit `0`). -/
  cloexec : Bool
  /-- Non-`FD_CLOEXEC` descriptor flag bits (`bits 1..30`) for POSIX flag-preservation checks. -/
  extraFdFlags : Std.I32 := 0#i32
  deriving DecidableEq, Repr, Inhabited

/-- Kernel state of an open file description referenced by one or more descriptors. -/
inductive DescState where
  /-- Stream, pipe end, device, or regular file with explicit read/write/broken-pipe capabilities. -/
  | stream (readable : Bool) (writable : Bool) (brokenPipe : Bool) (readBytes : Bytes)
  /-- Generic open directory descriptor (`O_DIRECTORY`) with cursor (`0` = `"."`, `1` = `".."`, `≥ 2` = EOF). -/
  | directory (cursor : Int := 0)
  /-- Open `/proc/self/fd` directory descriptor with `getdents64` cursor (`-2` = `"."`, `-1` = `".."`, `≥ 0` = `fd`). -/
  | procSelfFd (cursor : Int)
  deriving DecidableEq, Repr, Inhabited

/-- Per-signal disposition in the child process. -/
inductive Disp where
  /-- Default kernel signal action (`SIG_DFL`). -/
  | default
  /-- Ignored signal (`SIG_IGN`, preserved across `execve`). -/
  | ignore
  /-- Userspace signal handler installed before `fork` (reset to `SIG_DFL` on `execve`). -/
  | handler
  deriving DecidableEq, Repr, Inhabited

/-- Syscall request issued by `postfork::sys` while the child is running. -/
inductive Req where
  /-- `setpgid(0, 0)`. -/
  | setpgidSelf
  /-- `rt_sigaction(sig, SIG_DFL, NULL)`. -/
  | sigDfl (sig : Std.I32)
  /-- `rt_sigaction(sig, SIG_IGN, NULL)`. -/
  | sigIgn (sig : Std.I32)
  /-- `rt_sigprocmask(SIG_UNBLOCK, {sig}, NULL, 8)`. -/
  | sigUnblock (sig : Std.I32)
  /-- `close(fd)`. -/
  | close (fd : Std.I32)
  /-- `dup2(oldfd, newfd)`. -/
  | dup2 (oldfd newfd : Std.I32)
  /-- `fcntl(fd, F_GETFD)`. -/
  | fcntlGetfd (fd : Std.I32)
  /-- `fcntl(fd, F_SETFD, flags)`. -/
  | fcntlSetfd (fd flags : Std.I32)
  /-- `fcntl(fd, F_DUPFD_CLOEXEC, minFd)`. -/
  | fcntlDupfdCloexec (fd minFd : Std.I32)
  /-- `close_range(first, last, flags)`. -/
  | closeRange (first last flags : Std.U32)
  /-- `open("/proc/self/fd", O_RDONLY | O_DIRECTORY | O_CLOEXEC)`. -/
  | openProcSelfFd
  /-- `getdents64(dirfd, buf, 256)`. -/
  | getdents64 (dirfd : Std.I32)
  /-- `read(fd, buf, 1)`. -/
  | read1 (fd : Std.I32)
  /-- `write(fd, buf, len)`. -/
  | write (fd : Std.I32) (bytes : Bytes)
  /-- `chdir(path)`. -/
  | chdir (path : Bytes)
  /-- `execve(path, argv, envp)`. -/
  | execve (path : Bytes) (argv envp : List Bytes)
  /-- `_exit(code)`. -/
  | exit (code : Std.I32)
  deriving DecidableEq, Repr

/-- Recorded syscall outcome in `ChildState.trace`. -/
inductive EventOutcome where
  /-- Syscall succeeded with scalar return value (`0` for unit calls). -/
  | okVal (ret : Int)
  /-- Syscall failed with Linux `errno` (`1..4095`). -/
  | err (errno : Std.I32)
  /-- Syscall triggered fatal synchronous signal delivery (`SIGPIPE` on broken pipe with `SIG_DFL`). -/
  | fatalSig (sig : Std.I32)
  deriving DecidableEq, Repr

/-- One trace entry pairing a `Req` with its `EventOutcome`. -/
structure Event where
  /-- Syscall request sent to Linux. -/
  req : Req
  /-- Observed outcome of `req`. -/
  out : EventOutcome
  deriving DecidableEq, Repr

/-- Resulting process image immediately after a successful `execve`. -/
structure ExecImage where
  /-- Executable path passed to `execve`. -/
  path : Bytes
  /-- Argument vector passed to `execve`. -/
  argv : List Bytes
  /-- Environment vector passed to `execve`. -/
  envp : List Bytes
  /-- Surviving non-`FD_CLOEXEC` descriptor table (deduplicated by `fd`). -/
  fds : List (Int × FdEntry)
  /-- Working directory at `execve`. -/
  cwd : Bytes
  /-- Process group ID at `execve`. -/
  pgid : Int
  /-- Signal dispositions after `execve` (`.handler` reset to `.default`, `.ignore` preserved). -/
  sig : List (Int × Disp)
  /-- Blocked signal mask inherited across `execve` (`SigBlk`). -/
  blockedSigs : List Int := []
  deriving DecidableEq, Repr

/-- Execution status of the forked child process. -/
inductive Status where
  /-- Still executing post-`fork` setup code. -/
  | running
  /-- Terminated via `_exit(code)`. -/
  | exited (code : Std.I32)
  /-- Terminated by fatal signal `sig` (e.g., `SIGPIPE = 13` on broken-pipe `write` under `SIG_DFL`). -/
  | signaled (sig : Std.I32)
  /-- Replaced process image via successful `execve`. -/
  | execd (img : ExecImage)
  deriving DecidableEq, Repr

/-- Environment/fault directive for the `k`-th syscall in `ChildState.oracle`. -/
inductive StepFault where
  /-- Execute normal Linux kernel transition with full write/batch size. -/
  | normal
  /-- Inject kernel-side syscall failure with `errno` (clamped to valid Linux `1..4095`). -/
  | fail (errno : Std.I32)
  /-- Inject seccomp-bpf `SECCOMP_RET_ERRNO` failure BEFORE kernel entry with `errno`. -/
  | seccomp (errno : Std.I32)
  /-- Cap a succeeding `write` to at most `maxBytes + 1` bytes to exercise partial-write loops. -/
  | partialWrite (maxBytesMinusOne : Nat)
  /-- Cap a succeeding `getdents64` call to at most `maxEntries + 1` directory entries to exercise multi-batch loops. -/
  | dentsBatch (maxEntriesMinusOne : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Complete physical-Linux single-process state of the child between `fork` and `execve`/`_exit`. -/
structure ChildState where
  /-- Child PID (`> 0` in Linux). -/
  pid : Int := 2
  /-- Session ID (`sid == pid ∧ pid > 0` iff session leader; `sid == 0` inside `CLONE_NEWPID` before `setsid`). -/
  sid : Int := 1
  /-- Current process group ID. -/
  pgid : Int := 1
  /-- Open file descriptor table (`fd ↦ FdEntry`; first matching key wins, maintained deduplicated). -/
  fds : List (Int × FdEntry) := []
  /-- Kernel open-file-description table (`desc ↦ DescState`; unlisted `Desc` defaults to readable+writable stream). -/
  descs : List (Desc × DescState) := []
  /-- Current `RLIMIT_NOFILE.rlim_cur` ceiling for new descriptor allocation (`open`, `dup2` when `oldfd ≠ newfd`, `F_DUPFD_CLOEXEC`). -/
  fdLimit : Int := 1024
  /-- Whether `F_SETFD` masks descriptor flags to `FD_CLOEXEC` (`true` on Linux `7.1`, `false` for future/POSIX flag preservation). -/
  kernelMasksSetfd : Bool := true
  /-- Whether `close_range(2)` is permitted and supported (`false` models `ENOSYS` or container `seccomp` `EPERM`). -/
  closeRangeSupported : Bool := true
  /-- Forced `errno` when `closeRangeSupported = false` (`38` `ENOSYS` by default, or `1` `EPERM`). -/
  closeRangeErrno : Std.I32 := 38#i32
  /-- Whether `/proc/self/fd` can be opened (`false` inside unmounted-`/proc` empty roots). -/
  procSelfFdAvailable : Bool := true
  /-- Forced `errno` when `procSelfFdAvailable = false` (`2` `ENOENT` by default, or `13` `EACCES`). -/
  procOpenErrno : Std.I32 := 2#i32
  /-- Current working directory bytes. -/
  cwd : Bytes := [47#u8]
  /-- Optional kernel-resolved targets for `chdir` paths `(rawPath, resolvedCwd)` (used when symlinked or relative paths differ from lexical `chdirTarget`). -/
  chdirResolved : List (Bytes × Bytes) := []
  /-- Non-default signal dispositions (`sig ↦ Disp`; unlisted signals have `.default`). -/
  sig : List (Int × Disp) := []
  /-- Blocked signals in the process signal mask (`SigBlk` via `sigprocmask`). -/
  blockedSigs : List Int := []
  /-- Underlying kernel `fdtable.max_fds` baseline (`1024` default on Linux) for `/proc/self/fd` `d_off`/EOF cursor. -/
  procMaxFds : Nat := 1024
  /-- Chronological log of bytes written per open file description `(desc, bytes)`. -/
  writeLog : List (Desc × Bytes) := []
  /-- Chronological trace of syscalls issued while `status == .running`. -/
  trace : List Event := []
  /-- Finite per-step environment/fault schedule indexed by `trace.length` (steps beyond `oracle.length` execute `.normal`). -/
  oracle : List StepFault := []
  /-- Current lifecycle status of the child process. -/
  status : Status := .running
  deriving DecidableEq, Repr

end LeanSwe.PostFork.Aeneas.Internal.World

/-- `postfork::sys::Sys`: physical-Linux child process state. -/
abbrev sys.Sys : Type := LeanSwe.PostFork.Aeneas.Internal.World.ChildState

/-- `postfork::sys::CStr`: NUL-free byte content of a borrowed C string. -/
abbrev sys.CStr : Type := LeanSwe.PostFork.Aeneas.Internal.World.Bytes

/-- `postfork::sys::CStrArray`: list of NUL-free C strings in a `NULL`-terminated array. -/
abbrev sys.CStrArray : Type := List LeanSwe.PostFork.Aeneas.Internal.World.Bytes
