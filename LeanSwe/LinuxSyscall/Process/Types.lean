import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.Process

open LeanSwe.LinuxSyscall

/-- Maximum valid positive signed 32-bit Linux `pid_t` (`0x7fffffff`). -/
def MAX_LINUX_PID : UInt32 := 0x7fffffff

/-- Portable symbolic flags for Linux `pipe2(2)` (`O_CLOEXEC`, `O_NONBLOCK`, `O_DIRECT`, `O_NOTIFICATION_PIPE`), plus `extraBits` for unsupported flag validation (`extraBits != 0` triggers `EINVAL`). -/
structure PipeFlags where
  /-- Atomically set close-on-exec (`FD_CLOEXEC`) on both pipe descriptors (`O_CLOEXEC`). -/
  cloexec : Bool := true
  /-- Atomically set non-blocking mode (`O_NONBLOCK`) on both pipe descriptors. -/
  nonblock : Bool := false
  /-- Request packet-mode pipe (`O_DIRECT`). -/
  direct : Bool := false
  /-- Request watch-queue notification pipe (`O_NOTIFICATION_PIPE` / `O_EXCL`, returning `ENOPKG` if kernel `CONFIG_WATCH_QUEUE` is disabled). -/
  notificationPipe : Bool := false
  /-- Unsupported raw flag bits (`0` for valid portable calls; non-zero triggers `EINVAL`). -/
  extraBits : UInt32 := 0
  deriving Repr, DecidableEq

/-- Returns `true` iff `f` carries no unsupported raw flag bits (`f.extraBits == 0`). -/
def PipeFlags.isValid (f : PipeFlags) : Bool :=
  f.extraBits == 0

/-- Injectively encode `PipeFlags` into a portable 64-bit wire mask decoded by `process_shim.c` (bit `0` = `O_CLOEXEC`, bit `1` = `O_NONBLOCK`, bit `2` = `O_DIRECT`, bit `3` = `O_NOTIFICATION_PIPE`, `bits >> 4` = `extraBits`; `process_shim.c` maps any non-zero `extraBits` to canonical invalid kernel flag bit `0x80000000u`). -/
def PipeFlags.toBits (f : PipeFlags) : UInt64 :=
  let bit (b : Bool) (shift : UInt64) : UInt64 := if b then (1 <<< shift) else 0
  bit f.cloexec 0 ||| bit f.nonblock 1 ||| bit f.direct 2 |||
    bit f.notificationPipe 3 ||| (f.extraBits.toUInt64 <<< 4)

/-- Portable symbolic option flags for Linux `wait4(2)` / `waitpid(2)` (`WNOHANG`, `WUNTRACED`, `WCONTINUED`, `__WALL`, `__WCLONE`, `__WNOTHREAD`), plus `extraBits` for unsupported option validation (`extraBits != 0` triggers `EINVAL`). -/
structure WaitFlags where
  /-- Return `WaitResult.stillRunning` (`0`) immediately if matching child(ren) exist with no waitable state change (`WNOHANG`). -/
  nohang : Bool := false
  /-- Report children stopped by a signal (`WUNTRACED`). -/
  untraced : Bool := false
  /-- Report stopped children resumed by `SIGCONT` (`WCONTINUED`). -/
  continued : Bool := false
  /-- Wait for all children regardless of clone exit signal (`__WALL`; overrides `__WCLONE`). -/
  wall : Bool := false
  /-- Wait only for clone children (`exit_signal != SIGCHLD`, `__WCLONE`). -/
  wclone : Bool := false
  /-- Do not wait for children created by sibling threads (`__WNOTHREAD`). -/
  wnothread : Bool := false
  /-- Unsupported raw option bits (`0` for valid portable calls; non-zero triggers `EINVAL`). -/
  extraBits : UInt32 := 0
  deriving Repr, DecidableEq

/-- Returns `true` iff `f` carries no unsupported raw option bits (`f.extraBits == 0`). -/
def WaitFlags.isValid (f : WaitFlags) : Bool :=
  f.extraBits == 0

/-- Injectively encode `WaitFlags` into a portable 64-bit wire mask decoded by `process_shim.c` (bit `0` = `WNOHANG`, bit `1` = `WUNTRACED`, bit `2` = `WCONTINUED`, bit `3` = `__WALL`, bit `4` = `__WCLONE`, bit `5` = `__WNOTHREAD`, `bits >> 6` = `extraBits`; `process_shim.c` maps any non-zero `extraBits` to canonical invalid `wait4` option bit `0x10`). -/
def WaitFlags.toBits (f : WaitFlags) : UInt64 :=
  let bit (b : Bool) (shift : UInt64) : UInt64 := if b then (1 <<< shift) else 0
  bit f.nohang 0 ||| bit f.untraced 1 ||| bit f.continued 2 |||
    bit f.wall 3 ||| bit f.wclone 4 ||| bit f.wnothread 5 |||
    (f.extraBits.toUInt64 <<< 6)

/-- Decoded child state-change outcome returned by `waitpid(2)` wrapping Linux `wait4(2)`. -/
inductive WaitResult where
  /-- `WNOHANG` was set and at least one matching child exists with no waitable state change (`rc == 0`). -/
  | stillRunning
  /-- Child `pid` terminated normally via `_exit` (`WIFEXITED`, `WEXITSTATUS` in `0..255`). -/
  | exited (pid : UInt32) (exitCode : UInt8)
  /-- Child `pid` was terminated by signal `termSignal` (`WIFSIGNALED`, `WTERMSIG` in `1..126`, `WCOREDUMP`). -/
  | signaled (pid : UInt32) (termSignal : UInt32) (coreDumped : Bool := false)
  /-- Child `pid` was stopped by signal `stopSignal` (`WIFSTOPPED`, `WSTOPSIG`, reported under `WUNTRACED`). -/
  | stopped (pid : UInt32) (stopSignal : UInt32)
  /-- Stopped child `pid` was resumed by `SIGCONT` (`WIFCONTINUED`, reported under `WCONTINUED`). -/
  | continued (pid : UInt32)
  deriving Repr, DecidableEq

/-- Raw C-ABI tuple `(rcPid, rawStatus)` returned by `leanswe_sys_waitpid` when `wait4(2)` returns `>= 0`. -/
abbrev RawWaitTuple := Int32 × UInt32

/-- Decode `(rcPid, rawStatus)` from Linux `wait4(2)` into `WaitResult` using standard `<bits/waitstatus.h>` bit masks (`x86_64` and `aarch64`). -/
def WaitResult.ofRawWait4 (t : RawWaitTuple) : WaitResult :=
  let (rcPid, rawStatus) := t
  if rcPid <= 0 then
    .stillRunning
  else
    let pid : UInt32 := rcPid.toUInt32
    let low7 : UInt32 := rawStatus &&& 0x7f
    if low7 == 0 then
      .exited pid (((rawStatus >>> 8) &&& 0xff).toUInt8)
    else if low7 == 0x7f then
      if (rawStatus &&& 0xff) == 0x7f then
        .stopped pid ((rawStatus >>> 8) &&& 0xff)
      else
        .continued pid
    else
      .signaled pid low7 ((rawStatus &&& 0x80) != 0)

/-- Portable symbolic signal for Linux `kill(2)` and `pidfd_send_signal(2)`, translated via host `<signal.h>`. -/
inductive Signal where
  /-- Null signal `0`: performs process existence and permission checks without delivering a signal. -/
  | sigzero
  /-- Hangup (`SIGHUP`, 1). -/
  | sighup
  /-- Terminal interrupt (`SIGINT`, 2). -/
  | sigint
  /-- Uncatchable termination (`SIGKILL`, 9). -/
  | sigkill
  /-- User-defined signal 1 (`SIGUSR1`, 10). -/
  | sigusr1
  /-- User-defined signal 2 (`SIGUSR2`, 12). -/
  | sigusr2
  /-- Graceful termination request (`SIGTERM`, 15). -/
  | sigterm
  /-- Continue if stopped (`SIGCONT`, 18). -/
  | sigcont
  /-- Uncatchable stop (`SIGSTOP`, 19). -/
  | sigstop
  /-- Explicit numeric signal for real-time or out-of-range signal testing (`< 0` or `> 64` triggers `EINVAL`). -/
  | raw (sig : Int32)
  deriving Repr, DecidableEq

/-- Injectively encode `Signal` into `(tag, rawArg)` for `process_shim.c`. -/
def Signal.toRaw : Signal → UInt8 × Int32
  | .sigzero => (0, 0)
  | .sighup => (1, 0)
  | .sigint => (2, 0)
  | .sigkill => (3, 0)
  | .sigusr1 => (4, 0)
  | .sigusr2 => (5, 0)
  | .sigterm => (6, 0)
  | .sigcont => (7, 0)
  | .sigstop => (8, 0)
  | .raw n => (9, n)

/-- Effective Linux signal number on `x86_64` and `aarch64` (`include/uapi/asm-generic/signal.h`). -/
def Signal.toLinuxNum : Signal → Int
  | .sigzero => 0
  | .sighup => 1
  | .sigint => 2
  | .sigkill => 9
  | .sigusr1 => 10
  | .sigusr2 => 12
  | .sigterm => 15
  | .sigcont => 18
  | .sigstop => 19
  | .raw n => n.toInt

/-- Returns `true` iff `s` resolves to a valid Linux `kill` / `pidfd_send_signal` number (`0 <= n <= _NSIG`, `_NSIG = 64`). -/
def Signal.isValid (s : Signal) : Bool :=
  let n := s.toLinuxNum
  decide (0 ≤ n ∧ n ≤ 64)

/-- Returns `true` iff `s` resolves to glibc/NPTL-reserved internal signal `32` (`SIGCANCEL`) or `33` (`SIGSETXID`), which safe Lean bindings reject with `EINVAL` before calling C to avoid `pthread`/NPTL runtime undefined behavior. -/
def Signal.isNptlReserved (s : Signal) : Bool :=
  let n := s.toLinuxNum
  n == 32 || n == 33

/-- Portable symbolic flags for Linux `pidfd_open(2)` (`__NR_pidfd_open = 434`). -/
structure PidfdOpenFlags where
  /-- Set `O_NONBLOCK` (`PIDFD_NONBLOCK`) on the returned descriptor (`FD_CLOEXEC` is always set unconditionally by the kernel). -/
  nonblock : Bool := false
  /-- Open a thread-level pidfd (`PIDFD_THREAD = O_EXCL` on Linux 6.9+) permitting non-leader thread targets. -/
  thread : Bool := false
  /-- Unsupported raw flag bits (`0` for valid portable calls; non-zero triggers `EINVAL`). -/
  extraBits : UInt32 := 0
  deriving Repr, DecidableEq

/-- Returns `true` iff `f` carries no unsupported raw flag bits (`f.extraBits == 0`). -/
def PidfdOpenFlags.isValid (f : PidfdOpenFlags) : Bool :=
  f.extraBits == 0

/-- Injectively encode `PidfdOpenFlags` into a portable 64-bit wire mask decoded by `process_shim.c` (bit `0` = `PIDFD_NONBLOCK`, bit `1` = `PIDFD_THREAD`, `bits >> 2` = `extraBits`; `process_shim.c` maps any non-zero `extraBits` to canonical invalid kernel flag bit `0x80000000u`). -/
def PidfdOpenFlags.toBits (f : PidfdOpenFlags) : UInt64 :=
  let bit (b : Bool) (shift : UInt64) : UInt64 := if b then (1 <<< shift) else 0
  bit f.nonblock 0 ||| bit f.thread 1 ||| (f.extraBits.toUInt64 <<< 2)

/-- Portable symbolic flags for Linux `pidfd_send_signal(2)` (`__NR_pidfd_send_signal = 424`). -/
structure PidfdSignalFlags where
  /-- Target the specific thread (`PIDFD_SIGNAL_THREAD`). -/
  thread : Bool := false
  /-- Target the thread group (`PIDFD_SIGNAL_THREAD_GROUP`). -/
  threadGroup : Bool := false
  /-- Target the process group (`PIDFD_SIGNAL_PROCESS_GROUP`; dispatches via `PIDTYPE_PGID` on the `pidfd`'s `PID`, else `ESRCH` if no active process belongs to that PGID). -/
  processGroup : Bool := false
  /-- Unsupported raw flag bits (`0` for valid portable calls; non-zero triggers `EINVAL`). -/
  extraBits : UInt32 := 0
  deriving Repr, DecidableEq

/-- Returns `true` iff `f` sets no unsupported bits and at most one mutually exclusive `PIDFD_SIGNAL_*` scope flag. -/
def PidfdSignalFlags.isValid (f : PidfdSignalFlags) : Bool :=
  let scopes : Nat :=
    (if f.thread then 1 else 0) +
    (if f.threadGroup then 1 else 0) +
    (if f.processGroup then 1 else 0)
  f.extraBits == 0 && decide (scopes ≤ 1)

/-- Injectively encode `PidfdSignalFlags` into a portable 64-bit wire mask decoded by `process_shim.c` (bit `0` = `PIDFD_SIGNAL_THREAD`, bit `1` = `PIDFD_SIGNAL_THREAD_GROUP`, bit `2` = `PIDFD_SIGNAL_PROCESS_GROUP`, `bits >> 3` = `extraBits`; `process_shim.c` must map any non-zero `extraBits` to canonical invalid kernel flag bit `0x80000000u` rather than forwarding raw shifted bits). -/
def PidfdSignalFlags.toBits (f : PidfdSignalFlags) : UInt64 :=
  let bit (b : Bool) (shift : UInt64) : UInt64 := if b then (1 <<< shift) else 0
  bit f.thread 0 ||| bit f.threadGroup 1 ||| bit f.processGroup 2 ||| (f.extraBits.toUInt64 <<< 3)

/-- Semantic classification of Linux process-syscall `Errno` outcomes for error-coverage auditing. -/
inductive ProcessErrorKind where
  /-- Target process, process group, or thread-group leader does not exist or has already been reaped (`ESRCH`, plus `ENOENT` on non-leader thread `pidfd_open` in Linux `>= 6.9`). -/
  | noSuchProcess
  /-- Calling process has no matching unwaited child processes (`ECHILD`). -/
  | noChild
  /-- Closed, invalid, or non-pidfd file descriptor (`EBADF`). -/
  | badFd
  /-- Invalid flag/option bits, invalid signal number, or non-positive `pid` in `pidfd_open` (`EINVAL`, `ENOSYS`, `EOPNOTSUPP`). -/
  | invalidArg
  /-- Insufficient permissions to signal target process (`EPERM`, `EACCES`). -/
  | permissionDenied
  /-- Interrupted syscall or kernel/descriptor resource exhaustion (`EINTR`, `ENOMEM`, `ENFILE`, `EMFILE`, `EAGAIN`, `EBUSY`, `EIO`, `ENOSPC`, or other OS errno). -/
  | transientOrResource
  deriving Repr, DecidableEq

/-- Classify any Linux `Errno` into a `ProcessErrorKind`. -/
def ProcessErrorKind.ofErrno (e : Errno) : ProcessErrorKind :=
  if e == Errno.ESRCH || e == Errno.ENOENT then .noSuchProcess
  else if e == Errno.ECHILD then .noChild
  else if e == Errno.EBADF then .badFd
  else if e == Errno.EINVAL || e == Errno.ENOSYS || e == Errno.EOPNOTSUPP then .invalidArg
  else if e == Errno.EPERM || e == Errno.EACCES then .permissionDenied
  else .transientOrResource

/-- Low-level C-ABI syscall hook bundle parameterized over monad `m` and descriptor type `fd`, consumed by `Internal.mkProcessOps` and backed in `IO` by `process_shim.c`. -/
structure PosixProcessOpsM (m : Type → Type) (fd : Type := RawFd) where
  /-- Raw `pipe2(2)` hook accepting portable `PipeFlags.toBits`. -/
  pipe2 : UInt64 → m (Except Errno (fd × fd))
  /-- Raw `wait4(2)` hook accepting `(pid, WaitFlags.toBits)` and returning `(rcPid, rawStatus)`. -/
  waitpid : Int32 → UInt64 → m (Except Errno RawWaitTuple)
  /-- Raw `kill(2)` hook accepting `(pidOrNegPgid, sigTag, sigArg)`. -/
  kill : Int32 → UInt8 → Int32 → m (Except Errno Unit)
  /-- Raw `pidfd_open(2)` (`__NR_pidfd_open = 434`) hook accepting `(pid, PidfdOpenFlags.toBits)`. -/
  pidfd_open : UInt32 → UInt64 → m (Except Errno fd)
  /-- Raw `pidfd_send_signal(2)` (`__NR_pidfd_send_signal = 424`) hook accepting `(pidfd, sigTag, sigArg, PidfdSignalFlags.toBits)`. -/
  pidfd_send_signal : fd → UInt8 → Int32 → UInt64 → m (Except Errno Unit)
  /-- Raw `getpid(2)` hook returning the calling thread-group ID (or seccomp `Errno`). -/
  getpid : m (Except Errno UInt32)
  /-- Raw `getuid(2)` hook returning the calling real user ID (or seccomp `Errno`). -/
  getuid : m (Except Errno UInt32)

/-- Real-world `IO` specialization of `PosixProcessOpsM` using ABA-safe `RawFd` handles. -/
abbrev PosixProcessOps := PosixProcessOpsM IO RawFd

/-- Monadic capability bundle for all 7 curated Linux `Process` syscalls, parameterized over monad `m` and descriptor type `fd`. -/
structure ProcessOpsM (m : Type → Type) (fd : Type := RawFd) where
  /-- Create a unidirectional pipe pair `(readFd, writeFd)` with atomic flags via `pipe2(2)`. -/
  pipe2 : PipeFlags → m (Except Errno (fd × fd))
  /-- Wait for child process state changes via `wait4(pid, &status, opts, NULL)`. -/
  waitpid : Int32 → WaitFlags → m (Except Errno WaitResult)
  /-- Send `sig` (`SIGZERO` for existence/permission probe) to a process or process group (`pidOrNegPgid`) via `kill(2)`. -/
  kill : Int32 → Signal → m (Except Errno Unit)
  /-- Open a race-free process file descriptor (`FD_CLOEXEC` always set) for thread-group leader `pid` via `pidfd_open(2)` (`__NR = 434`). -/
  pidfd_open : UInt32 → PidfdOpenFlags → m (Except Errno fd)
  /-- Send `sig` to the process referenced by `pidfd` via `pidfd_send_signal(2)` (`__NR = 424`). -/
  pidfd_send_signal : fd → Signal → PidfdSignalFlags → m (Except Errno Unit)
  /-- Return the calling process's thread-group ID (`PID > 0`, or seccomp `Errno`) via `getpid(2)`. -/
  getpid : m (Except Errno UInt32)
  /-- Return the calling process's real user ID (or seccomp `Errno`) via `getuid(2)`. -/
  getuid : m (Except Errno UInt32)

/-- Real-world `IO` specialization of `ProcessOpsM` using ABA-safe `RawFd` handles. -/
abbrev ProcessOps := ProcessOpsM IO RawFd

/-- Logical handle identifier used by the `Process` relational world model and fuzzer traces. -/
abbrev HandleId := Nat

/-- One syscall request in a `Process` world-model trace (covers all 7 curated syscalls). -/
inductive ProcessReq where
  /-- `pipe2(flags)`. -/
  | pipe2 (flags : PipeFlags)
  /-- `waitpid(pid, flags)` wrapping `wait4`. -/
  | waitpid (pid : Int32) (flags : WaitFlags)
  /-- `kill(pidOrNegPgid, sig)`. -/
  | kill (pidOrNegPgid : Int32) (sig : Signal)
  /-- `pidfd_open(pid, flags)`. -/
  | pidfd_open (pid : UInt32) (flags : PidfdOpenFlags)
  /-- `pidfd_send_signal(hid, sig, flags)`. -/
  | pidfd_send_signal (hid : HandleId) (sig : Signal) (flags : PidfdSignalFlags)
  /-- `getpid()`. -/
  | getpid
  /-- `getuid()`. -/
  | getuid
  deriving Repr, DecidableEq

/-- Raw kernel outcome observed for one `ProcessReq`. -/
inductive ProcessOutcome where
  /-- `pipe2` succeeded and allocated `(readHid, writeHid)`. -/
  | piped (readHid : HandleId) (writeHid : HandleId)
  /-- `pidfd_open` succeeded and allocated `hid`. -/
  | opened (hid : HandleId)
  /-- `waitpid` succeeded with decoded `WaitResult`. -/
  | waited (res : WaitResult)
  /-- Unit-returning syscall succeeded (`kill`, `pidfd_send_signal`). -/
  | unit
  /-- `UInt32`-returning syscall succeeded (`getpid`, `getuid`). -/
  | u32 (val : UInt32)
  /-- Syscall failed with Linux `Errno`. -/
  | err (code : Errno)
  deriving Repr, DecidableEq

end LeanSwe.LinuxSyscall.Process
