import Core.ConcOps
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.PostFork.Interface
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSwe.Process.Impl
import LeanSwe.Process.SysBridge

namespace LeanSwe.Process

private initialize gProcTable : IO.Ref (Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd) ← IO.mkRef {}

/-- Default `ProcessApi` wired directly over `LinuxSyscall.{Process,Files,Poll,TimeRand}.defaultOps`, `PostFork.defaultOps`, `EnvVars.Raw.defaultOpsBase`, `Core.ioConcOps`, and `Core.ioStateCell`. -/
def defaultApi : ProcessApi :=
  Internal.mkFullApiM
    { proc := LeanSwe.LinuxSyscall.Process.defaultOps
      files := LeanSwe.LinuxSyscall.Files.defaultOps
      poll := LeanSwe.LinuxSyscall.Poll.defaultOps
      timeRand := LeanSwe.LinuxSyscall.TimeRand.defaultOps
      postFork := LeanSwe.PostFork.defaultOps
      envRaw := LeanSwe.EnvVars.Raw.defaultOpsBase }
    Core.ioConcOps
    (Core.ioStateCell gProcTable)

/-- Convert a raw OS error record into a normalized `ProcessError` with non-empty message. -/
@[inline] def mapRawError (err : ProcessRawError) : ProcessError :=
  defaultApi.mapRawError err

/-- Validate and normalize an `ExecRequest`. -/
@[inline] def validateRequest (req : ExecRequest) : Except ProcessError ExecRequest :=
  defaultApi.validateRequest req

/-- Construct a direct `execvp`-style `ExecRequest` with explicit argument array (no shell). -/
@[inline] def mkCommandRequest (program : String) (args : Array String := #[]) : ExecRequest :=
  defaultApi.mkCommandRequest program args

/-- Return a copy of `req` with UTF-8 encoded `stdin` text. -/
@[inline] def withTextInput (req : ExecRequest) (text : String) : ExecRequest :=
  defaultApi.withTextInput req text

/-- Validate `req` and spawn a child process directly in its own process group. -/
@[inline] def spawn (req : SpawnRequest) : IO (Except ProcessError ProcessHandle) :=
  defaultApi.spawn req

/-- Feed `stdin`, stream `stdout`/`stderr`, and wait for completion, timeout, or output cap. -/
@[inline] def awaitOutput
    (h : ProcessHandle)
    (stdin : ByteArray := ByteArray.empty)
    (timeoutMs : Option Nat := none)
    (maxOutputBytes : Option Nat := none) : IO (Except ProcessError ExecOutcome) :=
  defaultApi.awaitOutput h stdin timeoutMs maxOutputBytes

/-- Terminate the child process group (`SIGTERM` followed by `SIGKILL`). -/
@[inline] def killProcessGroup (h : ProcessHandle) : IO (Except ProcessError Unit) :=
  defaultApi.killProcessGroup h

/-- Wait for and release a spawned child handle. -/
@[inline] def reap (h : ProcessHandle) : IO (Except ProcessError Unit) :=
  defaultApi.reap h

/-- Execute a command directly in its own process group, returning `ExecResult` even for non-zero exit codes. -/
@[inline] def run (req : ExecRequest) : IO (Except ProcessError ExecResult) :=
  defaultApi.run req

/-- Execute a command like `run`, mapping any non-zero exit code to `.error` with `kind := .nonZeroExit`. -/
@[inline] def runChecked (req : ExecRequest) : IO (Except ProcessError ExecResult) :=
  defaultApi.runChecked req

/-- Execute `program` with explicit `args` via `run`. -/
@[inline] def runCommand (program : String) (args : Array String := #[]) :
    IO (Except ProcessError ExecResult) :=
  defaultApi.runCommand program args

/-- Execute `program` with explicit `args` via `runChecked`. -/
@[inline] def runCommandChecked (program : String) (args : Array String := #[]) :
    IO (Except ProcessError ExecResult) :=
  defaultApi.runCommandChecked program args

/-- Return count of currently active (un-reaped) spawned child process handles. -/
@[inline] def activeProcessCount : IO Nat :=
  defaultApi.activeProcessCount

end LeanSwe.Process
