import Core.ConcOps
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSwe.Process.SysBridge

namespace LeanSwe.Process.Internal

open LeanSwe.Process
  (ProcessErrorKind ProcessError ProcessRawError SpawnRequest ExecRequest ExecResult
   ProcessHandle ExecOutcome RawProcessOpsM ProcessApiM)

/-- Return `err` with a non-empty fallback message if `err.message` is empty. -/
def ensureNonEmptyMsg (fallback : String) (err : ProcessError) : ProcessError :=
  if err.message.isEmpty then { err with message := fallback } else err

/-- Return `true` iff `s` contains a NUL character. -/
def hasNul (s : String) : Bool :=
  s.toList.contains '\x00'

/-- Return `true` iff an environment entry `(k, v?)` is invalid (empty key, `=`, or NUL byte). -/
def isInvalidEnvEntry (kv : String × Option String) : Bool :=
  kv.1.isEmpty || kv.1.toList.contains '=' || hasNul kv.1 ||
    match kv.2 with
    | some v => hasNul v
    | none => false

/-- Deduplicate environment entries keeping the last entry per key in order. -/
def dedupEnvList : List (String × Option String) → List (String × Option String)
  | [] => []
  | kv :: rest =>
    let tail := dedupEnvList rest
    if tail.any (fun p => p.1 == kv.1) then tail else kv :: tail

/-- Validate and normalize a `SpawnRequest` before spawning. -/
def validateSpawnRequest (req : SpawnRequest) : Except ProcessError SpawnRequest :=
  if req.program.isEmpty then
    .error { kind := .invalidInput, program := some req.program, message := "executable program must not be empty" }
  else if hasNul req.program then
    .error { kind := .invalidInput, program := some req.program, message := "executable program must not contain NUL bytes" }
  else if req.args.toList.any hasNul then
    .error { kind := .invalidInput, program := some req.program, message := "command arguments must not contain NUL bytes" }
  else if match req.cwd with | some d => hasNul d | none => false then
    .error { kind := .invalidInput, program := some req.program, message := "working directory must not contain NUL bytes" }
  else if req.env.toList.any isInvalidEnvEntry then
    .error { kind := .invalidInput, program := some req.program, message := "invalid environment variable entry" }
  else
    .ok { req with env := (dedupEnvList req.env.toList).toArray }

/-- Validate and normalize an `ExecRequest` before spawning. -/
def validateRequest (req : ExecRequest) : Except ProcessError ExecRequest :=
  match validateSpawnRequest req.toSpawnRequest with
  | .error err => .error err
  | .ok norm =>
    if req.timeoutMs == some 0 then
      .error { kind := .invalidInput, program := some req.program, message := "timeoutMs must be greater than zero" }
    else
      .ok { req with toSpawnRequest := norm }

/-- Construct a direct `execvp`-style `ExecRequest` from `program` and `args`. -/
def mkCommandRequest (program : String) (args : Array String) : ExecRequest :=
  { program := program, args := args }

/-- Return a copy of `req` with UTF-8 encoded `stdin` text. -/
def withTextInput (req : ExecRequest) (text : String) : ExecRequest :=
  { req with stdin := text.toUTF8 }

/-- Validate `req` and spawn a child process in its own process group via `raw`. -/
def spawn {m : Type → Type} [Monad m] (raw : RawProcessOpsM m) (req : SpawnRequest) :
    m (Except ProcessError ProcessHandle) := do
  match validateSpawnRequest req with
  | .error err => return .error err
  | .ok norm =>
    match ← raw.spawn { toSpawnRequest := norm } with
    | .error err => return .error (ensureNonEmptyMsg "process spawn failed" err)
    | .ok h => return .ok h

/-- Feed `stdin`, stream `stdout`/`stderr`, and wait for completion, timeout, or output cap via `raw`. -/
def awaitOutput {m : Type → Type} [Monad m] (raw : RawProcessOpsM m)
    (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs : Option Nat) (maxOutputBytes : Option Nat) :
    m (Except ProcessError ExecOutcome) := do
  if timeoutMs == some 0 then
    return .error { kind := .invalidInput, message := "timeoutMs must be greater than zero" }
  match ← raw.awaitOutput h stdin timeoutMs maxOutputBytes with
  | .error err => return .error (ensureNonEmptyMsg "process I/O failed" err)
  | .ok out => return .ok out

/-- Terminate the child process group (`SIGTERM` followed by `SIGKILL`) via `raw`. -/
def killProcessGroup {m : Type → Type} [Monad m] (raw : RawProcessOpsM m) (h : ProcessHandle) :
    m (Except ProcessError Unit) := do
  match ← raw.killProcessGroup h with
  | .error err => return .error (ensureNonEmptyMsg "process group termination failed" err)
  | .ok () => return .ok ()

/-- Wait for and release a spawned child handle via `raw`. -/
def reap {m : Type → Type} [Monad m] (raw : RawProcessOpsM m) (h : ProcessHandle) :
    m (Except ProcessError Unit) := do
  match ← raw.reap h with
  | .error err => return .error (ensureNonEmptyMsg "process reap failed" err)
  | .ok () => return .ok ()

/-- Execute a command via `raw`, isolating in a process group and cleaning up on every outcome. -/
def run {m : Type → Type} [Monad m] (raw : RawProcessOpsM m) (req : ExecRequest) :
    m (Except ProcessError ExecResult) := do
  match validateRequest req with
  | .error err => return .error err
  | .ok norm =>
    match ← raw.spawn norm with
    | .error err => return .error (ensureNonEmptyMsg "process spawn failed" err)
    | .ok h =>
      match ← raw.awaitOutput h norm.stdin norm.timeoutMs norm.maxOutputBytes with
      | .error err =>
        let _ ← raw.killProcessGroup h
        let _ ← raw.reap h
        return .error (ensureNonEmptyMsg "process I/O failed" err)
      | .ok (.exited res) =>
        match ← raw.reap h with
        | .error err => return .error (ensureNonEmptyMsg "process reap failed" err)
        | .ok () => return .ok res
      | .ok (.signaled sig out err) =>
        let _ ← raw.killProcessGroup h
        let _ ← raw.reap h
        return .error
          { kind := .terminatedBySignal
            program := some norm.program
            signal := some sig
            stdout := some out
            stderr := some err
            message := s!"process '{norm.program}' terminated by signal {sig}" }
      | .ok (.timedOut out err) =>
        let _ ← raw.killProcessGroup h
        let _ ← raw.reap h
        return .error
          { kind := .timedOut
            program := some norm.program
            stdout := some out
            stderr := some err
            message := s!"process '{norm.program}' timed out" }
      | .ok (.outputLimitExceeded out err) =>
        let _ ← raw.killProcessGroup h
        let _ ← raw.reap h
        return .error
          { kind := .outputLimitExceeded
            program := some norm.program
            stdout := some out
            stderr := some err
            message := s!"process '{norm.program}' exceeded output byte limit" }

/-- Execute a command like `run`, mapping any non-zero exit code to `.nonZeroExit`. -/
def runChecked {m : Type → Type} [Monad m] (raw : RawProcessOpsM m) (req : ExecRequest) :
    m (Except ProcessError ExecResult) := do
  match ← run raw req with
  | .error err => return .error err
  | .ok res =>
    if res.exitCode == 0 then
      return .ok res
    else
      return .error
        { kind := .nonZeroExit
          program := some req.program
          exitCode := some res.exitCode
          stdout := some res.stdout
          stderr := some res.stderr
          message := s!"process '{req.program}' exited with status {res.exitCode}" }

/-- Build a generic `ProcessApiM m` implementation backed by `raw : RawProcessOpsM m`. -/
def mkApiM {m : Type → Type} [Monad m] (raw : RawProcessOpsM m) : ProcessApiM m :=
  { mapRawError := raw.mapRawError
    validateRequest := validateRequest
    mkCommandRequest := mkCommandRequest
    withTextInput := withTextInput
    spawn := spawn raw
    awaitOutput := awaitOutput raw
    killProcessGroup := killProcessGroup raw
    reap := reap raw
    run := run raw
    runChecked := runChecked raw
    runCommand := fun program args => run raw (mkCommandRequest program args)
    runCommandChecked := fun program args => runChecked raw (mkCommandRequest program args)
    activeProcessCount := raw.activeProcessCount }

/-- Build the full `ProcessApiM m` implementation directly over `ProcessSysCapsM m`, `Core.ConcOpsM m`, and `Core.StateCellM m`. -/
def mkFullApiM {m : Type → Type} [Monad m] [MonadFinally m]
    (sys : ProcessSysCapsM m) (conc : Core.ConcOpsM m)
    (cell : Core.StateCellM m (ProcCellS conc.Ref conc.TaskHandle)) : ProcessApiM m :=
  { mapRawError := (SysBridge.mkFullRawOpsM sys conc cell).mapRawError
    validateRequest := validateRequest
    mkCommandRequest := mkCommandRequest
    withTextInput := withTextInput
    spawn := spawn (SysBridge.mkFullRawOpsM sys conc cell)
    awaitOutput := awaitOutput (SysBridge.mkFullRawOpsM sys conc cell)
    killProcessGroup := killProcessGroup (SysBridge.mkFullRawOpsM sys conc cell)
    reap := reap (SysBridge.mkFullRawOpsM sys conc cell)
    run := run (SysBridge.mkFullRawOpsM sys conc cell)
    runChecked := runChecked (SysBridge.mkFullRawOpsM sys conc cell)
    runCommand := fun program args => run (SysBridge.mkFullRawOpsM sys conc cell) (mkCommandRequest program args)
    runCommandChecked := fun program args => runChecked (SysBridge.mkFullRawOpsM sys conc cell) (mkCommandRequest program args)
    activeProcessCount := (SysBridge.mkFullRawOpsM sys conc cell).activeProcessCount }

/-- Construct a `ProcessApiM m` composing `Impl` and `SysBridge` over a `ProcessHostCapsM fd m` bundle. -/
def mkApiFromCapsM {m : Type → Type} [Monad m] {fd : Type}
    (cap : ProcessHostCapsM fd m) : ProcessApiM m :=
  let deps : SysDepsM m fd :=
    { proc := cap.proc
      files := cap.files
      poll := cap.poll
      timeRand := cap.timeRand
      postFork := cap.postFork
      listAmbientEnv := Except.ok <$> cap.listEnvironBytes }
  mkApiM (SysBridge.mkRawOpsM deps cap.table)

/-- Construct a `ProcessApiM m` composing `Impl` and `SysBridge` over `HealthyHostCapsM m` (`LinuxSyscall.{Process,Files,Poll,TimeRand}`, `PostFork`, `EnvVars`). -/
def mkApiFromHostCapsM {m : Type → Type} [Monad m]
    (cap : HealthyHostCapsM m) : ProcessApiM m :=
  mkApiFromCapsM cap

end LeanSwe.Process.Internal
