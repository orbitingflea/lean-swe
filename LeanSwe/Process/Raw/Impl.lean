import LeanSwe.Process.Raw.Types

namespace LeanSwe.Process.Raw.Internal

open LeanSwe.Process.Raw
  (ProcessErrorKind ProcessError ProcessRawError ExecRequest ExecResult
   ProcessHandle ExecOutcome RawProcessOpsM RawProcessOps)

/-- FFI hooks injected by `LeanSwe.Process.Raw.Interface`. -/
structure PosixRawOps where
  /-- Spawn a child process in its own process group, returning its handle ID. -/
  spawn :
    String → Array String → Bool → String → Bool →
    Array String → ByteArray → Array String → IO UInt64
  /-- Return the child OS PID for an active handle ID. -/
  pid : UInt64 → IO UInt32
  /-- Run non-blocking I/O poll loop until EOF, timeout, or output cap; returns outcome tag. -/
  awaitOutput : UInt64 → ByteArray → Bool → UInt64 → Bool → UInt64 → IO UInt8
  /-- Take captured stdout bytes stored on the handle slot. -/
  takeStdout : UInt64 → IO ByteArray
  /-- Take captured stderr bytes stored on the handle slot. -/
  takeStderr : UInt64 → IO ByteArray
  /-- Read normal exit code stored on the handle slot. -/
  exitCode : UInt64 → IO UInt32
  /-- Read terminating signal number stored on the handle slot. -/
  termSignal : UInt64 → IO UInt32
  /-- Send `SIGTERM` then `SIGKILL` to the process group of `handleId`. -/
  killGroup : UInt64 → IO Unit
  /-- Wait for child process and free the handle slot. -/
  reap : UInt64 → IO Unit
  /-- Return number of active unreaped handles. -/
  activeCount : IO Nat

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Clamp a `Nat` to `UInt64` without modulo wraparound. -/
def natToUInt64Sat (n : Nat) : UInt64 :=
  UInt64.ofNat (Nat.min n (UInt64.size - 1))

/-- Convert a pure `ProcessRawError` into a normalized `ProcessError` with a non-empty message. -/
def mapRawError : ProcessRawError → ProcessError
  | .executableNotFound prog code detail =>
    { kind := .notFound
      program := some prog
      errnoCode := some code
      message := nonEmptyMsg s!"executable not found: {prog}" detail }
  | .permissionDenied prog? code detail =>
    { kind := .permissionDenied
      program := prog?
      errnoCode := some code
      message := nonEmptyMsg "permission denied" detail }
  | .invalidArgument prog? code detail =>
    { kind := .invalidInput
      program := prog?
      errnoCode := some code
      message := nonEmptyMsg "invalid process argument" detail }
  | .timedOut prog timeoutMs detail =>
    { kind := .timedOut
      program := some prog
      message := nonEmptyMsg s!"process '{prog}' timed out after {timeoutMs}ms" detail }
  | .outputLimitExceeded prog limitBytes detail =>
    { kind := .outputLimitExceeded
      program := some prog
      message := nonEmptyMsg s!"process '{prog}' exceeded output limit ({limitBytes} bytes)" detail }
  | .signaled prog sig detail =>
    { kind := .terminatedBySignal
      program := some prog
      signal := some sig
      message := nonEmptyMsg s!"process '{prog}' terminated by signal {sig}" detail }
  | .otherError code detail =>
    { kind := .ioError
      errnoCode := some code
      message := nonEmptyMsg s!"os error {code}" detail }
  | .userError detail =>
    { kind := .ioError
      message := nonEmptyMsg "process error" detail }

/-- Convert a Lean `IO.Error` into `ProcessRawError`. -/
def ioErrorToRaw (fallbackProg : Option String) : IO.Error → ProcessRawError
  | .noFileOrDirectory p code detail =>
    .executableNotFound (if p.isEmpty then fallbackProg.getD "" else p) code detail
  | .permissionDenied p? code detail =>
    .permissionDenied (p? <|> fallbackProg) code detail
  | .invalidArgument p? code detail =>
    .invalidArgument (p? <|> fallbackProg) code detail
  | .otherError code detail =>
    .otherError code detail
  | .userError detail =>
    .userError detail
  | .interrupted p code detail =>
    .otherError code s!"{p}: {detail}"
  | .timeExpired code detail =>
    .otherError code detail
  | .resourceExhausted p? code detail =>
    .invalidArgument (p? <|> fallbackProg) code detail
  | .noSuchThing p? code detail =>
    .executableNotFound (p?.or fallbackProg |>.getD "") code detail
  | .alreadyExists _ code detail => .otherError code detail
  | .inappropriateType _ code detail => .otherError code detail
  | .unsupportedOperation code detail => .otherError code detail
  | .unsatisfiedConstraints code detail => .otherError code detail
  | .illegalOperation code detail => .otherError code detail
  | .resourceBusy code detail => .otherError code detail
  | .resourceVanished code detail => .otherError code detail
  | .hardwareFault code detail => .otherError code detail
  | .protocolError code detail => .otherError code detail
  | .unexpectedEof => .userError "unexpected end of file"

/-- Normalize an `IO.Error` into a `ProcessError`, preserving `fallbackProg` if absent. -/
def mapIoError (fallbackProg : Option String) (err : IO.Error) : ProcessError :=
  let mapped := mapRawError (ioErrorToRaw fallbackProg err)
  { mapped with program := mapped.program <|> fallbackProg }

/-- Run an `IO` action and capture thrown `IO.Error` values into `Except ProcessError`. -/
def catchProc {α : Type} (prog? : Option String) (act : IO α) : IO (Except ProcessError α) := do
  try
    return .ok (← act)
  catch err =>
    return .error (mapIoError prog? err)

/-- Build the concrete `RawProcessOps` bundle from injected POSIX FFI hooks. -/
def mkRawOps (posix : PosixRawOps) : RawProcessOps :=
  { mapRawError := mapRawError
    spawn := fun req => do
      if req.program.isEmpty then
        return .error (mapRawError (.invalidArgument (some req.program) 22 "empty program"))
      let hasCwd := req.cwd.isSome
      let cwd := req.cwd.getD ""
      let keys := req.env.map (·.1)
      let hasVals := ByteArray.mk (req.env.map (fun kv => if kv.2.isSome then 1 else 0))
      let vals := req.env.map (fun kv => kv.2.getD "")
      catchProc (some req.program) do
        let hid ← posix.spawn req.program req.args hasCwd cwd req.inheritEnv keys hasVals vals
        let pidU ← posix.pid hid
        let pidI := Int.ofNat pidU.toNat
        return { handleId := hid.toNat, pid := pidI, pgid := pidI }
    awaitOutput := fun h stdin timeoutMs? maxOutputBytes? =>
      catchProc none do
        let hid := UInt64.ofNat h.handleId
        let hasTimeout := timeoutMs?.isSome
        let timeoutVal := natToUInt64Sat (timeoutMs?.getD 0)
        let hasLimit := maxOutputBytes?.isSome
        let limitVal := natToUInt64Sat (maxOutputBytes?.getD 0)
        let tag ← posix.awaitOutput hid stdin hasTimeout timeoutVal hasLimit limitVal
        let out ← posix.takeStdout hid
        let err ← posix.takeStderr hid
        match tag.toNat with
        | 0 =>
          let code ← posix.exitCode hid
          return .exited { exitCode := Int.ofNat code.toNat, stdout := out, stderr := err }
        | 1 =>
          let sig ← posix.termSignal hid
          return .signaled (Int.ofNat sig.toNat) out err
        | 2 =>
          return .timedOut out err
        | _ =>
          return .outputLimitExceeded out err
    killProcessGroup := fun h =>
      catchProc none (posix.killGroup (UInt64.ofNat h.handleId))
    reap := fun h =>
      catchProc none (posix.reap (UInt64.ofNat h.handleId))
    activeProcessCount := posix.activeCount }

end LeanSwe.Process.Raw.Internal
