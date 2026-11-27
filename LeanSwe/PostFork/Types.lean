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

/-- Literal NUL-free argument token passed in `ChildSpecM.argv`. -/
inductive ArgToken (fd : Type) where
  /-- Literal NUL-free argument string. -/
  | lit (text : String)
  deriving Repr, BEq, DecidableEq

/-- Construct a literal `ArgToken`. -/
@[inline] def ArgToken.ofLiteral {fd : Type} (s : String) : ArgToken fd :=
  .lit s

/-- Reaped `waitpid` termination status of a forked child process. -/
inductive ChildWaitStatus where
  /-- Child terminated normally via `_exit(code)` or `return` from `main`. -/
  | exited (code : UInt32)
  /-- Child was terminated by uncaught signal `sig`. -/
  | signaled (sig : UInt32)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Stage at which post-`fork` child setup failed prior to replacing the process image. -/
inductive FailureStage where
  /-- Pre-execution flag or descriptor validation failed (`EINVAL` or `EBADF`, tag `1`). -/
  | validate
  /-- `setpgid(0, 0)` failed (tag `2`). -/
  | processGroup
  /-- `sigaction(SIGPIPE, SIG_DFL)` or `SIG_UNBLOCK` failed (tag `3`). -/
  | signalReset
  /-- Stdio redirection or `FD_CLOEXEC` clearing failed (tag `4`). -/
  | fdSetup
  /-- Closing inherited descriptors `>= 3` failed (tag `5`). -/
  | closeUnkept
  /-- `chdir(cwd)` failed (tag `6`). -/
  | chdir
  /-- `execve(path, argv, envp)` failed (tag `7`). -/
  | execve
  /-- Host read a truncated, overlong, or malformed packet on the error pipe. -/
  | wireTruncated
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Decoded post-`fork` child failure report written by `postfork_shim.c` before `_exit(127)`. -/
structure ChildFailure where
  /-- Exact post-`fork` phase that failed. -/
  stage : FailureStage
  /-- Strictly positive Linux `errno` (`1..4095`; `EIO` on malformed wire payload). -/
  errno : Errno
  /-- Reaped child `waitpid` status (normally `some (.exited 127)`). -/
  waitStatus : Option ChildWaitStatus := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Coarse error classification returned by `LeanSwe.PostFork` host operations. -/
inductive PostForkErrorKind where
  /-- Pre-`fork` caller input error (empty `path`, embedded NUL, bad `env` key, negative raw FD, non-empty `keepFds`, or overlapping descriptors). -/
  | invalidInput
  /-- Host OS failure during handle pinning, probing, `pipe2`, `fork`, `read`, or `waitpid`. -/
  | sysError
  /-- Child forked successfully but failed post-`fork` before `execve` (already reaped). -/
  | childFailed
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Structured error value returned by `LeanSwe.PostFork` host operations. -/
structure PostForkError where
  /-- Coarse error classification covered by central error-coverage checks. -/
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
  /-- Leave inherited `0`, `1`, `2` untouched. -/
  | inherit
  /-- Atomically route `(stdin, stdout, stderr)` onto `(0, 1, 2)` without clobbering swaps or 3-cycles,
      clearing `FD_CLOEXEC` on `0..2`. All descriptors `>= 3` are closed before `execve`. -/
  | redirect (stdin stdout stderr : FdRef fd) (closeSourcesAbove2 : Bool := true)
  deriving Repr, BEq, DecidableEq

/-- Policy for descriptors `> 2` across `execve` (all descriptors `>= 3` are closed by the shim; `keepFds` must be empty). -/
inductive FdPolicy (fd : Type) where
  /-- Close all descriptors `>= 3` across `execve` (`keepFds` must be `#[]`). -/
  | inheritNonCloexec (keepFds : Array (FdRef fd) := #[])
  /-- Close all descriptors `>= 3` across `execve` (`keepFds` must be `#[]`). -/
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

/-- Host `fork()` execution policy (direct single-shot `fork()` on the caller's thread). -/
inductive ForkMode where
  /-- Invoke `fork()` directly on the caller's OS thread. -/
  | direct
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
  /-- Optional raw NUL-free byte-level `KEY=VALUE` entries prepended verbatim to `envp`
      without UTF-8 decoding (used for raw inherited POSIX `environ(7)` slices). Any entry whose
      key bytes before `'='` match a binding in `env` is omitted so explicit `env` values always
      take precedence over `rawEnv` under first-match `getenv(3)`. -/
  rawEnv : Array ByteArray := #[]
  /-- Standard descriptor (`0`, `1`, `2`) setup policy. -/
  stdio : StdioPlan fd := .inherit
  /-- Unkept descriptor (`> 2`) policy (`keepFds` must be empty; all fds `>= 3` are closed). -/
  fdPolicy : FdPolicy fd := .inheritNonCloexec #[]
  /-- Descriptors `>= 3` closed before `execve` (all descriptors `>= 3` are closed unconditionally). -/
  closeFds : Array (FdRef fd) := #[]
  /-- Process group policy (`setpgid`). -/
  processGroup : ProcessGroupPolicy := .inherit
  /-- `SIGPIPE` disposition policy prior to `execve`. -/
  sigpipe : SigpipePolicy := .resetDefault
  /-- Host `fork()` execution policy. -/
  forkMode : ForkMode := .direct
  deriving BEq, DecidableEq

instance {fd : Type} [Repr fd] : Repr (ChildSpecM fd) where
  reprPrec s _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "path := " ++ repr s.path,
        "argv := " ++ repr s.argv,
        "cwd := " ++ repr s.cwd,
        "env := " ++ repr s.env,
        "rawEnv := " ++ repr (s.rawEnv.map (·.toList)),
        "stdio := " ++ repr s.stdio,
        "fdPolicy := " ++ repr s.fdPolicy,
        "closeFds := " ++ repr s.closeFds,
        "processGroup := " ++ repr s.processGroup,
        "sigpipe := " ++ repr s.sigpipe,
        "forkMode := " ++ repr s.forkMode
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Real-world `IO` specialization of `ChildSpecM` using ABA-safe `RawFd` handles. -/
abbrev ChildSpec := ChildSpecM RawFd

/-- Convenience builder setting `argv := #[.lit path] ++ args.map .lit`. -/
def ChildSpecM.ofCommand {fd : Type} (path : String) (args : Array String := #[]) : ChildSpecM fd :=
  { path := path, argv := (#[ArgToken.lit path] ++ args.map ArgToken.lit) }

/-- Live running child returned after `execve` has succeeded (error pipe observed EOF). -/
structure SpawnedChild where
  /-- Positive child PID. -/
  pid : Pid
  /-- `some pid` when `processGroup == .newGroup`, else `none`. -/
  pgid : Option Pid := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Raw failure returned by the trusted single-shot C spawn shim (`leanswe_postfork_spawn`). -/
inductive RawSpawnErr where
  /-- Host-side OS error during pinning, probing, `pipe2`, `fork`, `read`, or `waitpid`. -/
  | sys (errno : Errno)
  /-- Child failed post-`fork` and was already reaped with `wait`. -/
  | child (wait : ChildWaitStatus) (stageTag : UInt32) (errno : Errno)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Low-level single-shot spawn capability bundle backed by `leanswe_postfork_spawn`. -/
structure RawSpawnOpsM (m : Type → Type) (fd : Type) where
  /-- Pin stdio handles, create an `O_CLOEXEC` error pipe, `fork`, wire stdio, close all fds `>= 3`,
      optionally `setpgid`/`SIGPIPE`/`chdir`, call `execve`, and either return the live PID or reap and return `RawSpawnErr`. -/
  spawnRaw :
    UInt32 →
    FdRef fd → FdRef fd → FdRef fd →
    Option String → String → Array String → Array ByteArray →
    m (Except RawSpawnErr Pid)

/-- Public caller-agnostic monadic capability bundle for `LeanSwe.PostFork`. -/
structure PostForkOpsM (m : Type → Type) (fd : Type) where
  /-- Validate `spec`, fork, run post-`fork` child setup, verify `execve` via EOF,
      and return the live `SpawnedChild` (reaping automatically on failure). -/
  spawn : ChildSpecM fd → m (Except PostForkError SpawnedChild)

/-- Real-world `IO` specialization of `PostForkOpsM`. -/
abbrev PostForkOps := PostForkOpsM IO RawFd

end LeanSwe.PostFork
