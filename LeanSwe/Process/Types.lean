namespace LeanSwe.Process

private def reprByteArray (bs : ByteArray) : Std.Format :=
  repr bs.toList

/-- Classification of process execution errors modeled after POSIX `errno` and subprocess failures. -/
inductive ProcessErrorKind where
  /-- Executable program or working directory does not exist (`ENOENT`). -/
  | notFound
  /-- Insufficient permissions to execute program or enter directory (`EACCES` / `EPERM`). -/
  | permissionDenied
  /-- Invalid command options, empty program, NUL byte, invalid env key, or invalid limit (`EINVAL`). -/
  | invalidInput
  /-- Child process exceeded its timeout; child and its process group were terminated and reaped. -/
  | timedOut
  /-- Captured stdout/stderr exceeded the configured maximum byte limit. -/
  | outputLimitExceeded
  /-- Child process was terminated by an OS signal (`WIFSIGNALED`). -/
  | terminatedBySignal
  /-- Child process exited with a non-zero exit code (reported by `runChecked`). -/
  | nonZeroExit
  /-- Other OS-level `fork`, `pipe`, `poll`, `execvp`, or `waitpid` failure (`OSError`). -/
  | ioError
  deriving Repr, BEq, DecidableEq

/-- Typed process error returned by `LeanSwe.Process` operations. -/
structure ProcessError where
  /-- Machine-checkable error category. -/
  kind : ProcessErrorKind
  /-- Program executable name or path associated with the error, when available. -/
  program : Option String := none
  /-- Child exit status code, when available (e.g., for `nonZeroExit`). -/
  exitCode : Option Int := none
  /-- Terminating OS signal number, when available (e.g., for `terminatedBySignal`). -/
  signal : Option Int := none
  /-- Underlying OS `errno` code, when available. -/
  errnoCode : Option UInt32 := none
  /-- Captured stdout bytes prior to failure, when available. -/
  stdout : Option ByteArray := none
  /-- Captured stderr bytes prior to failure, when available. -/
  stderr : Option ByteArray := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving BEq, DecidableEq

instance : Repr ProcessError where
  reprPrec e _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "kind := " ++ repr e.kind,
        "program := " ++ repr e.program,
        "exitCode := " ++ repr e.exitCode,
        "signal := " ++ repr e.signal,
        "errnoCode := " ++ repr e.errnoCode,
        "stdout := " ++ (match e.stdout with | none => "none" | some b => "some " ++ reprByteArray b),
        "stderr := " ++ (match e.stderr with | none => "none" | some b => "some " ++ reprByteArray b),
        "message := " ++ repr e.message
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Pure representation of raw OS process error inputs for total error-mapping specs. -/
inductive ProcessRawError where
  /-- Executable or working directory missing (`ENOENT`). -/
  | executableNotFound (program : String) (errno : UInt32) (detail : String)
  /-- Permission denied (`EACCES` / `EPERM`). -/
  | permissionDenied (program? : Option String) (errno : UInt32) (detail : String)
  /-- Invalid argument or option (`EINVAL`). -/
  | invalidArgument (program? : Option String) (errno : UInt32) (detail : String)
  /-- Child exceeded its timeout limit. -/
  | timedOut (program : String) (timeoutMs : Nat) (detail : String)
  /-- Output exceeded configured byte cap. -/
  | outputLimitExceeded (program : String) (limitBytes : Nat) (detail : String)
  /-- Child process was terminated by a signal. -/
  | signaled (program : String) (signal : Int) (detail : String)
  /-- Generic numeric OS error. -/
  | otherError (errno : UInt32) (detail : String)
  /-- Generic fallback error string. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq

/-- One-shot command execution request (`PATH`-searching `execve`, never executed via a shell).
    When `program` contains no `'/'`, searches valid UTF-8 `PATH` directory segments treating
    empty segments (e.g. `""`, `:/usr/bin`, `/usr/bin:`, `a::b`) as `"."` per POSIX `execvp(3)`;
    any individual non-UTF-8 `PATH` directory segment is skipped without failing the search (and
    the raw `PATH` value and all other raw `environ(7)` entries are still passed unmodified to the
    child `execve(2)`). Unlike glibc `execvp(3)`, executable scripts lacking a `#!` shebang are
    never retried via `/bin/sh`: `execve(2)` `ENOEXEC` fails with `kind = .invalidInput` and
    `errnoCode = some 8`. -/
structure ExecRequest where
  /-- Executable name or path (`argv[0]`); `PATH`-resolved when containing no `'/'`. -/
  program : String
  /-- Explicit argument array (`argv[1..]`), passed verbatim without shell interpretation. -/
  args : Array String := #[]
  /-- Optional working directory (`chdir` before `execve`). -/
  cwd : Option String := none
  /-- Environment variable overrides (`some val`) or removals (`none`). -/
  env : Array (String × Option String) := #[]
  /-- Whether to inherit the parent process's raw `environ(7)` bytes before applying `env`. -/
  inheritEnv : Bool := true
  /-- Standard input bytes written to the child's stdin pipe before closing it. -/
  stdin : ByteArray := ByteArray.empty
  /-- Optional timeout in milliseconds (`some 0` is rejected as invalid input). -/
  timeoutMs : Option Nat := none
  /-- Optional maximum combined captured bytes across `stdout` and `stderr`. -/
  maxOutputBytes : Option Nat := none
  deriving BEq, DecidableEq

instance : Repr ExecRequest where
  reprPrec r _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "program := " ++ repr r.program,
        "args := " ++ repr r.args,
        "cwd := " ++ repr r.cwd,
        "env := " ++ repr r.env,
        "inheritEnv := " ++ repr r.inheritEnv,
        "stdin := " ++ reprByteArray r.stdin,
        "timeoutMs := " ++ repr r.timeoutMs,
        "maxOutputBytes := " ++ repr r.maxOutputBytes
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Captured output and exit status from a completed child process. -/
structure ExecResult where
  /-- Normal exit status code (`0` indicates success). -/
  exitCode : Int
  /-- Captured standard output bytes. -/
  stdout : ByteArray
  /-- Captured standard error bytes. -/
  stderr : ByteArray
  deriving BEq, DecidableEq

instance : Repr ExecResult where
  reprPrec r _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "exitCode := " ++ repr r.exitCode,
        "stdout := " ++ reprByteArray r.stdout,
        "stderr := " ++ reprByteArray r.stderr
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Handle to a spawned child process isolated in its own process group. -/
structure ProcessHandle where
  /-- Opaque handle slot identifier assigned by `RawProcessOpsM`. -/
  handleId : Nat
  /-- Child process ID (`pid`). -/
  pid : Int
  /-- Isolated process group ID (`pgid`) covering the child and all descendants. -/
  pgid : Int
  deriving Repr, BEq, DecidableEq

/-- Result of waiting for and streaming I/O with a spawned child process before reaping. -/
inductive ExecOutcome where
  /-- Child closed output pipes and exited normally (`WIFEXITED`). -/
  | exited (result : ExecResult)
  /-- Child was terminated by an OS signal (`WIFSIGNALED`). -/
  | signaled (signal : Int) (stdout stderr : ByteArray)
  /-- Child exceeded `timeoutMs`; process group remains to be killed and reaped. -/
  | timedOut (stdout stderr : ByteArray)
  /-- Output exceeded `maxOutputBytes`; process group remains to be killed and reaped. -/
  | outputLimitExceeded (stdout stderr : ByteArray)
  deriving BEq, DecidableEq

instance : Repr ExecOutcome where
  reprPrec
    | .exited r, _ => "ExecOutcome.exited (" ++ repr r ++ ")"
    | .signaled sig out err, _ =>
      "ExecOutcome.signaled " ++ repr sig ++ " " ++ reprByteArray out ++ " " ++ reprByteArray err
    | .timedOut out err, _ =>
      "ExecOutcome.timedOut " ++ reprByteArray out ++ " " ++ reprByteArray err
    | .outputLimitExceeded out err, _ =>
      "ExecOutcome.outputLimitExceeded " ++ reprByteArray out ++ " " ++ reprByteArray err

/-- Minimal single-step process primitives parameterized over effect monad `m`. -/
structure RawProcessOpsM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `ProcessError` with non-empty message. -/
  mapRawError : ProcessRawError → ProcessError
  /-- Spawn a child process directly in its own process group (`setpgid`). When `program` lacks `'/'`,
      searches `PATH` (treating empty segments as `"."`); does not fall back to `/bin/sh` on `ENOEXEC`
      (returns `.error` with `kind := .invalidInput` and `errnoCode := some 8`). -/
  spawn : ExecRequest → m (Except ProcessError ProcessHandle)
  /-- Feed `stdin`, stream `stdout`/`stderr` up to `timeoutMs` and `maxOutputBytes`. -/
  awaitOutput :
    ProcessHandle → ByteArray → Option Nat → Option Nat → m (Except ProcessError ExecOutcome)
  /-- Send `SIGKILL` to the entire process group (`-pgid`) to stop child and grandchildren. -/
  killProcessGroup : ProcessHandle → m (Except ProcessError Unit)
  /-- Wait/reap child handle and release associated OS/table resources (no zombies/leaks). -/
  reap : ProcessHandle → m (Except ProcessError Unit)
  /-- Return count of currently active (un-reaped) spawned process handles. -/
  activeProcessCount : m Nat

/-- Concrete `IO` process primitive bundle exported by `LeanSwe.Process`. -/
abbrev RawProcessOps := RawProcessOpsM IO

/-- Public command-execution operations exported by `LeanSwe.Process`, parameterized over effect monad `m`. -/
structure ProcessApiM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `ProcessError` with non-empty message. -/
  mapRawError : ProcessRawError → ProcessError
  /-- Validate and normalize an `ExecRequest` (rejecting empty program, NUL bytes, bad env keys, and zero timeout). -/
  validateRequest : ExecRequest → Except ProcessError ExecRequest
  /-- Construct a direct `execvp`-style `ExecRequest` with explicit argument array (no shell). -/
  mkCommandRequest : String → Array String → ExecRequest
  /-- Return a copy of `req` with UTF-8 encoded `stdin` text. -/
  withTextInput : ExecRequest → String → ExecRequest
  /-- Validate `req` and spawn a child process directly in its own process group (`setpgid`). -/
  spawn : ExecRequest → m (Except ProcessError ProcessHandle)
  /-- Feed `stdin`, stream `stdout`/`stderr`, and wait for completion, timeout, or output cap. -/
  awaitOutput :
    ProcessHandle → ByteArray → Option Nat → Option Nat → m (Except ProcessError ExecOutcome)
  /-- Send `SIGTERM` followed by `SIGKILL` to the child process group (`-pgid`) to stop child and descendants. -/
  killProcessGroup : ProcessHandle → m (Except ProcessError Unit)
  /-- Wait/reap child handle and release associated OS/table resources (no zombies/leaks). -/
  reap : ProcessHandle → m (Except ProcessError Unit)
  /-- Execute a command directly in its own process group, returning `ExecResult` even for non-zero exit codes. -/
  run : ExecRequest → m (Except ProcessError ExecResult)
  /-- Execute a command like `run`, mapping any non-zero exit code to `.error` with `kind := .nonZeroExit`. -/
  runChecked : ExecRequest → m (Except ProcessError ExecResult)
  /-- Convenience wrapper executing `program` with explicit `args` via `run`. -/
  runCommand : String → Array String → m (Except ProcessError ExecResult)
  /-- Convenience wrapper executing `program` with explicit `args` via `runChecked`. -/
  runCommandChecked : String → Array String → m (Except ProcessError ExecResult)
  /-- Return count of currently active (un-reaped) spawned child process handles. -/
  activeProcessCount : m Nat

/-- Concrete `IO` process execution API bundle for `LeanSwe.Process`. -/
abbrev ProcessApi := ProcessApiM IO

end LeanSwe.Process
