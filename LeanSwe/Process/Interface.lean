import LeanSwe.Process.Types
import LeanSwe.Process.Impl
import LeanSwe.Process.SysBridge

namespace LeanSwe.Process

/-- Default `ProcessApi` backed by `LeanSwe.Process.SysBridge.defaultOps`. -/
def defaultApi : ProcessApi :=
  Internal.mkApiM SysBridge.defaultOps

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
