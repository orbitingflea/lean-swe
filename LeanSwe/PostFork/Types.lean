import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.PostFork

open LeanSwe.LinuxSyscall

/-- Positive Linux process ID (`1 ≤ pid ≤ 2147483647`). -/
abbrev Pid := UInt32

/-- Descriptor reference passed across `fork()`: either an ABA-safe handle `fd`
    or a raw non-negative OS descriptor number (e.g. inherited `0..2`). -/
inductive FdRef (fd : Type) where
  /-- Managed descriptor handle (for `IO`, an ABA-safe `RawFd` pinned across `fork()`). -/
  | handle (h : fd)
  /-- Raw non-negative OS descriptor number (for inherited descriptors). -/
  | raw (num : Int32)
  deriving Repr, BEq, DecidableEq

/-- Argument token passed in `ChildSpecM.argv`, resolved atomically inside C while
    managed `RawFd` handles remain pinned across `fork()`. -/
inductive ArgToken (fd : Type) where
  /-- Literal NUL-free argument string. -/
  | lit (text : String)
  /-- Decimal ASCII rendering of `fd` (e.g. `"5"`). -/
  | fdDecimal (fd : FdRef fd)
  /-- Decimal ASCII rendering of `fd` wrapped with NUL-free `prefixText` and `suffixText`
      (e.g. `"/proc/self/fd/5"` or `"--plan-fd=5"`). -/
  | prefixedFd (prefixText : String) (fd : FdRef fd) (suffixText : String := "")
  deriving Repr, BEq, DecidableEq

/-- Construct a literal `ArgToken`. -/
@[inline] def ArgToken.ofLiteral {fd : Type} (s : String) : ArgToken fd :=
  .lit s

/-- Construct a decimal-FD `ArgToken` from a managed handle. -/
@[inline] def ArgToken.ofHandle {fd : Type} (h : fd) : ArgToken fd :=
  .fdDecimal (.handle h)

/-- Construct a `"/proc/self/fd/<N>"` `ArgToken` from a managed handle. -/
@[inline] def ArgToken.procSelfFd {fd : Type} (h : fd) : ArgToken fd :=
  .prefixedFd "/proc/self/fd/" (.handle h) ""

/-- Reaped `waitpid` termination status of a forked child process. -/
inductive ChildWaitStatus where
  /-- Child terminated normally via `_exit(code)` or `return` from `main`. -/
  | exited (code : UInt32)
  /-- Child was terminated by uncaught signal `sig`. -/
  | signaled (sig : UInt32)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Stage at which post-`fork` child setup failed prior to replacing the process image. -/
inductive FailureStage where
  /-- Pre-execution flag or descriptor validation failed (`EINVAL` or `EBADF`, wire tag `1`). -/
  | validate
  /-- `setpgid(0, 0)` failed (wire tag `2`). -/
  | processGroup
  /-- `rt_sigaction(SIGPIPE, SIG_DFL, NULL)` or `SIG_UNBLOCK` failed (wire tag `3`). -/
  | signalReset
  /-- Open-FD probe, `rep_w` relocation, `setup_stdio`, or `FD_CLOEXEC` toggle failed (wire tag `4`). -/
  | fdSetup
  /-- `close_fds_above2_except` (`close_range` + `/proc/self/fd` fallback) failed (wire tag `5`). -/
  | closeUnkept
  /-- `chdir(cwd)` failed (wire tag `6`). -/
  | chdir
  /-- `execve(path, argv, envp)` failed (wire tag `7`). -/
  | execve
  /-- Host read a truncated, overlong, or malformed frame on the failure report pipe. -/
  | wireTruncated
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Decoded post-`fork` child failure report written by `libpostfork.a` before `_exit(127)`. -/
structure ChildFailure where
  /-- Exact post-`fork` phase that failed. -/
  stage : FailureStage
  /-- Strictly positive Linux `errno` (`1..4095`; `EIO` on truncated/malformed wire payload). -/
  errno : Errno
  /-- Reaped child `waitpid` status (normally `some (.exited 127)`). -/
  waitStatus : Option ChildWaitStatus := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Coarse error classification returned by `LeanSwe.PostFork` host operations. -/
inductive PostForkErrorKind where
  /-- Pre-`fork` caller input error (empty `path`, embedded NUL, bad `env` key, negative raw FD, or overlapping descriptors). -/
  | invalidInput
  /-- Host OS failure during handle pinning, probing, `pipe2`, `fork`, `write`, `read`, or `waitpid`. -/
  | sysError
  /-- Child forked successfully but failed post-`fork` before `execve` (already reaped). -/
  | childFailed
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Structured error value returned by `LeanSwe.PostFork` host operations. -/
structure PostForkError where
  /-- Coarse error classification covered by `errorCoverage`. -/
  kind : PostForkErrorKind
  /-- Optional positive Linux `errno` associated with this error. -/
  errno : Option Errno := none
  /-- Populated iff `kind == .childFailed`. -/
  childFailure : Option ChildFailure := none
  /-- Non-empty diagnostic description. -/
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How standard descriptors `0`, `1`, and `2` are configured in the child. -/
inductive StdioPlan (fd : Type) where
  /-- Leave inherited `0`, `1`, `2` untouched (no `dup2`, no `relocate_rep_above2`). -/
  | inherit
  /-- Atomically route `(stdin, stdout, stderr)` onto `(0, 1, 2)` without clobbering swaps or 3-cycles,
      clearing `FD_CLOEXEC` on `0..2`. When `closeSourcesAbove2 = true` and `fdPolicy` is `.inheritNonCloexec`,
      source descriptors `> 2` are closed after `dup2`. -/
  | redirect (stdin stdout stderr : FdRef fd) (closeSourcesAbove2 : Bool := true)
  deriving Repr, BEq, DecidableEq

/-- Policy for descriptors `> 2` across `execve`. -/
inductive FdPolicy (fd : Type) where
  /-- Preserve open non-`O_CLOEXEC` descriptors (close only explicit `closeFds` and redirected stdio sources `> 2` if requested).
      Any `keepFds` listed are verified open via `F_GETFD` and have `FD_CLOEXEC` cleared. -/
  | inheritNonCloexec (keepFds : Array (FdRef fd) := #[])
  /-- Verify every descriptor in `keepFds` is open, clear `FD_CLOEXEC` on `keepFds`, and close all other
      descriptors `> 2` via gap-wise `close_range` with `/proc/self/fd` `getdents64` fallback. -/
  | closeAllAbove2Except (keepFds : Array (FdRef fd) := #[])
  deriving Repr, BEq, DecidableEq

/-- Process-group setup policy in child and parent. -/
inductive ProcessGroupPolicy where
  /-- Inherit the parent's process group (no `setpgid`). -/
  | inherit
  /-- Place child in its own process group (`setpgid(0, 0)` in child plus best-effort `setpgid(pid, pid)` in parent). -/
  | newGroup
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `SIGPIPE` disposition policy in the child prior to `execve`. -/
inductive SigpipePolicy where
  /-- Preserve inherited `SIGPIPE` disposition and mask. -/
  | inherit
  /-- Reset `SIGPIPE` (`13`) to `SIG_DFL` and unblock `SIGPIPE` before `execve`. -/
  | resetDefault
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Host `fork()` execution thread policy supporting `PR_SET_PDEATHSIG`-safe children. -/
inductive ForkMode where
  /-- Invoke `fork()` directly on the caller's OS thread. -/
  | direct
  /-- Invoke `fork()` from a dedicated immortal spawner pthread so transient Lean worker-thread exit
      cannot prematurely trigger `PR_SET_PDEATHSIG` in the child. -/
  | immortalThread
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Caller-agnostic post-`fork` child specification parameterized over descriptor handle type `fd`. -/
structure ChildSpecM (fd : Type) where
  /-- Resolved executable path passed to `execve` (non-empty, NUL-free). -/
  path : String
  /-- Argument vector passed to `execve` (`argv[0]` may differ from `path`; all tokens NUL-free). -/
  argv : Array (ArgToken fd)
  /-- Optional working directory passed to `chdir` prior to `execve` (NUL-free). -/
  cwd : Option String := none
  /-- Explicit `(key, value)` environment bindings formatted as `KEY=VALUE`. -/
  env : Array (String × String) := #[]
  /-- Standard descriptor (`0`, `1`, `2`) setup policy. -/
  stdio : StdioPlan fd := .inherit
  /-- Unkept descriptor (`> 2`) handling and kept-FD `FD_CLOEXEC` clearing policy. -/
  fdPolicy : FdPolicy fd := .inheritNonCloexec #[]
  /-- Descriptors to close unconditionally in the child before probing or waiting on the sync barrier. -/
  closeFds : Array (FdRef fd) := #[]
  /-- Process group policy (`setpgid`). -/
  processGroup : ProcessGroupPolicy := .inherit
  /-- `SIGPIPE` disposition policy prior to `execve`. -/
  sigpipe : SigpipePolicy := .resetDefault
  /-- Host `fork()` thread policy (`.immortalThread` for `PR_SET_PDEATHSIG` children). -/
  forkMode : ForkMode := .direct
  deriving Repr, BEq, DecidableEq

/-- Real-world `IO` specialization of `ChildSpecM` using ABA-safe `RawFd` handles. -/
abbrev ChildSpec := ChildSpecM RawFd

/-- Convenience builder setting `argv := #[.lit path] ++ args.map .lit`. -/
def ChildSpecM.ofCommand {fd : Type} (path : String) (args : Array String := #[]) : ChildSpecM fd :=
  { path := path, argv := (#[ArgToken.lit path] ++ args.map ArgToken.lit) }

/-- Live running child returned after `execve` has succeeded (failure report pipe observed EOF). -/
structure SpawnedChild where
  /-- Positive child PID. -/
  pid : Pid
  /-- `some pid` when `processGroup == .newGroup`, else `none`. -/
  pgid : Option Pid := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Child paused at the pre-`execve` sync barrier (returned by `spawnWithBarrier`).
    Caller must consume via `releaseBarrier` or `abortBarrier` exactly once. -/
structure PendingChildM (fd : Type) where
  /-- Positive child PID (already placed in its own pgid when `processGroup == .newGroup`). -/
  pid : Pid
  /-- `some pid` when `processGroup == .newGroup`, else `none`. -/
  pgid : Option Pid := none
  /-- Internal parent write end of the 1-byte sync barrier pipe (`O_CLOEXEC`). -/
  syncWrite : fd
  /-- Internal parent read end of the 8-byte failure report pipe (`O_CLOEXEC`). -/
  errRead : fd
  deriving Repr, BEq, DecidableEq

/-- Real-world `IO` specialization of `PendingChildM` backed by ABA-safe `RawFd` pipe handles. -/
abbrev PendingChild := PendingChildM RawFd

/-- Outcome returned by `abortBarrier` after closing the sync barrier without releasing. -/
inductive AbortOutcome where
  /-- Child observed EOF on the sync barrier and terminated (normally `.exited 125`). -/
  | aborted (wait : ChildWaitStatus)
  /-- Child failed before reaching the sync barrier and wrote a failure report. -/
  | failedBeforeBarrier (failure : ChildFailure) (wait : ChildWaitStatus)
  deriving Repr, BEq, DecidableEq

/-- Public caller-agnostic monadic capability bundle for `LeanSwe.PostFork` (zero Aeneas or Mathlib types). -/
structure PostForkOpsM (m : Type → Type) (fd : Type) where
  /-- Validate `spec`, fork, run post-`fork` child setup without a sync barrier, verify `execve` via EOF,
      and return the live `SpawnedChild` (reaping automatically on failure). -/
  spawn : ChildSpecM fd → m (Except PostForkError SpawnedChild)
  /-- Validate `spec`, fork, pause child at the 1-byte sync barrier after `setpgid`, `closeFds`, and FD probing,
      and return `PendingChildM fd` for parent-side setup (e.g. `cgroup.procs` and `pidfd_open`). -/
  spawnWithBarrier : ChildSpecM fd → m (Except PostForkError (PendingChildM fd))
  /-- Write the 1-byte release token (`EPIPE`-safe if child failed early), close barrier/report pipes,
      verify `execve` via EOF, and return `SpawnedChild` (reaping automatically on failure). -/
  releaseBarrier : PendingChildM fd → m (Except PostForkError SpawnedChild)
  /-- Close the sync barrier without writing a token, drain any pre-barrier failure report,
      reap the child (`_exit(125)` on clean abort), and return `AbortOutcome`. -/
  abortBarrier : PendingChildM fd → m (Except PostForkError AbortOutcome)

/-- Real-world `IO` specialization of `PostForkOpsM`. -/
abbrev PostForkOps := PostForkOpsM IO RawFd

end LeanSwe.PostFork
