import LeanSwe.Process.Raw.Types
import LeanSwe.Process.Raw.Impl

namespace LeanSwe.Process.Raw

@[extern "leanswe_process_spawn"]
private opaque rawSpawn :
  @& String → @& Array String → Bool → @& String → Bool →
  @& Array String → @& ByteArray → @& Array String → IO UInt64

@[extern "leanswe_process_pid"]
private opaque rawPid : UInt64 → IO UInt32

@[extern "leanswe_process_await_output"]
private opaque rawAwaitOutput :
  UInt64 → @& ByteArray → Bool → UInt64 → Bool → UInt64 → IO UInt8

@[extern "leanswe_process_take_stdout"]
private opaque rawTakeStdout : UInt64 → IO ByteArray

@[extern "leanswe_process_take_stderr"]
private opaque rawTakeStderr : UInt64 → IO ByteArray

@[extern "leanswe_process_exit_code"]
private opaque rawExitCode : UInt64 → IO UInt32

@[extern "leanswe_process_term_signal"]
private opaque rawTermSignal : UInt64 → IO UInt32

@[extern "leanswe_process_kill_group"]
private opaque rawKillGroup : UInt64 → IO Unit

@[extern "leanswe_process_reap"]
private opaque rawReap : UInt64 → IO Unit

@[extern "leanswe_process_active_count"]
private opaque rawActiveCount : IO Nat

private def posixRawOps : Internal.PosixRawOps :=
  { spawn := rawSpawn
    pid := rawPid
    awaitOutput := rawAwaitOutput
    takeStdout := rawTakeStdout
    takeStderr := rawTakeStderr
    exitCode := rawExitCode
    termSignal := rawTermSignal
    killGroup := rawKillGroup
    reap := rawReap
    activeCount := rawActiveCount }

/-- Default OS process primitive operations backed by `c/process_shim.c`. -/
def defaultOps : RawProcessOps :=
  Internal.mkRawOps posixRawOps

/-- Convert a raw OS error record into a normalized `ProcessError` with non-empty message. -/
@[inline] def mapRawError (err : ProcessRawError) : ProcessError :=
  defaultOps.mapRawError err

/-- Spawn a child process directly (`execvp`) in its own process group. -/
@[inline] def spawn (req : ExecRequest) : IO (Except ProcessError ProcessHandle) :=
  defaultOps.spawn req

/-- Feed `stdin`, stream `stdout`/`stderr`, and wait for completion, timeout, or output cap. -/
@[inline] def awaitOutput
    (h : ProcessHandle)
    (stdin : ByteArray := ByteArray.empty)
    (timeoutMs : Option Nat := none)
    (maxOutputBytes : Option Nat := none) : IO (Except ProcessError ExecOutcome) :=
  defaultOps.awaitOutput h stdin timeoutMs maxOutputBytes

/-- Terminate the child process group (`SIGTERM` followed by `SIGKILL`). -/
@[inline] def killProcessGroup (h : ProcessHandle) : IO (Except ProcessError Unit) :=
  defaultOps.killProcessGroup h

/-- Wait for and release a spawned child handle. -/
@[inline] def reap (h : ProcessHandle) : IO (Except ProcessError Unit) :=
  defaultOps.reap h

/-- Return the count of currently active unreaped process handles. -/
@[inline] def activeProcessCount : IO Nat :=
  defaultOps.activeProcessCount

end LeanSwe.Process.Raw
