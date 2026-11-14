import LeanSwe.Process.Types

namespace LeanSwe.Process.Internal

open LeanSwe.Process
  (ProcessErrorKind ProcessError ProcessRawError ExecRequest ExecResult
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

/-- Validate and normalize an `ExecRequest` before spawning. -/
def validateRequest (req : ExecRequest) : Except ProcessError ExecRequest :=
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
  else if req.timeoutMs == some 0 then
    .error { kind := .invalidInput, program := some req.program, message := "timeoutMs must be greater than zero" }
  else
    .ok { req with env := (dedupEnvList req.env.toList).toArray }

/-- Construct a direct `execvp`-style `ExecRequest` from `program` and `args`. -/
def mkCommandRequest (program : String) (args : Array String) : ExecRequest :=
  { program := program, args := args }

/-- Return a copy of `req` with UTF-8 encoded `stdin` text. -/
def withTextInput (req : ExecRequest) (text : String) : ExecRequest :=
  { req with stdin := text.toUTF8 }

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
    run := run raw
    runChecked := runChecked raw
    runCommand := fun program args => run raw (mkCommandRequest program args)
    runCommandChecked := fun program args => runChecked raw (mkCommandRequest program args)
    activeProcessCount := raw.activeProcessCount }

end LeanSwe.Process.Internal
