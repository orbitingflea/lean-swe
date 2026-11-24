import LeanSwe.Process.Types

/-!
Pure top-level domain model and single-step capability-refinement specification for
`LeanSwe.Process`. Defines pure request-validation/error-mapping models alongside the
handle-lifecycle state `ProcessModelState`, `RawProcessOpsM` step contract (`allowedRawStep`),
and `ProcessApiM` step contract (`allowedPkgStep`) for `Core.RefinesStepFrom`.
-/

namespace LeanSwe.Process.Model

open LeanSwe.Process

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsgModel (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Pure model of `LeanSwe.Process.mapRawError`. -/
def mapRawErrorModel : ProcessRawError → ProcessError
  | .executableNotFound prog code detail =>
    { kind := .notFound
      program := some prog
      errnoCode := some code
      message := nonEmptyMsgModel s!"executable not found: {prog}" detail }
  | .permissionDenied prog? code detail =>
    { kind := .permissionDenied
      program := prog?
      errnoCode := some code
      message := nonEmptyMsgModel "permission denied" detail }
  | .invalidArgument prog? code detail =>
    { kind := .invalidInput
      program := prog?
      errnoCode := some code
      message := nonEmptyMsgModel "invalid process argument" detail }
  | .timedOut prog timeoutMs detail =>
    { kind := .timedOut
      program := some prog
      message := nonEmptyMsgModel s!"process '{prog}' timed out after {timeoutMs}ms" detail }
  | .outputLimitExceeded prog limitBytes detail =>
    { kind := .outputLimitExceeded
      program := some prog
      message := nonEmptyMsgModel s!"process '{prog}' exceeded output limit ({limitBytes} bytes)" detail }
  | .signaled prog sig detail =>
    { kind := .terminatedBySignal
      program := some prog
      signal := some sig
      message := nonEmptyMsgModel s!"process '{prog}' terminated by signal {sig}" detail }
  | .otherError code detail =>
    { kind := .ioError
      errnoCode := some code
      message := nonEmptyMsgModel s!"os error {code}" detail }
  | .userError detail =>
    { kind := .ioError
      message := nonEmptyMsgModel "process error" detail }

/-- Return `true` iff `s` contains a NUL character. -/
def hasNulModel (s : String) : Bool :=
  s.toList.contains '\x00'

/-- Return `true` iff an environment entry `(k, v?)` is invalid (empty key, `=`, or NUL byte). -/
def isInvalidEnvEntryModel (kv : String × Option String) : Bool :=
  kv.1.isEmpty || kv.1.toList.contains '=' || hasNulModel kv.1 ||
    match kv.2 with
    | some v => hasNulModel v
    | none => false

/-- Deduplicate environment entries keeping the last entry per key in order. -/
def dedupEnvListModel : List (String × Option String) → List (String × Option String)
  | [] => []
  | kv :: rest =>
    let tail := dedupEnvListModel rest
    if tail.any (fun p => p.1 == kv.1) then tail else kv :: tail

/-- Pure model of `SpawnRequest` validation and environment deduplication. -/
def validateSpawnRequestModel (req : SpawnRequest) : Except ProcessError SpawnRequest :=
  if req.program.isEmpty then
    .error { kind := .invalidInput, program := some req.program, message := "executable program must not be empty" }
  else if hasNulModel req.program then
    .error { kind := .invalidInput, program := some req.program, message := "executable program must not contain NUL bytes" }
  else if req.args.toList.any hasNulModel then
    .error { kind := .invalidInput, program := some req.program, message := "command arguments must not contain NUL bytes" }
  else if match req.cwd with | some d => hasNulModel d | none => false then
    .error { kind := .invalidInput, program := some req.program, message := "working directory must not contain NUL bytes" }
  else if req.env.toList.any isInvalidEnvEntryModel then
    .error { kind := .invalidInput, program := some req.program, message := "invalid environment variable entry" }
  else
    .ok { req with env := (dedupEnvListModel req.env.toList).toArray }

/-- Pure model of `LeanSwe.Process.validateRequest`. -/
def validateRequestModel (req : ExecRequest) : Except ProcessError ExecRequest :=
  match validateSpawnRequestModel req.toSpawnRequest with
  | .error err => .error err
  | .ok norm =>
    if req.timeoutMs == some 0 then
      .error { kind := .invalidInput, program := some req.program, message := "timeoutMs must be greater than zero" }
    else
      .ok { req with toSpawnRequest := norm }

/-- Pure model of `LeanSwe.Process.mkCommandRequest`. -/
def mkCommandRequestModel (program : String) (args : Array String) : ExecRequest :=
  { program := program, args := args }

/-- Pure model of `LeanSwe.Process.withTextInput`. -/
def withTextInputModel (req : ExecRequest) (text : String) : ExecRequest :=
  { req with stdin := text.toUTF8 }

/-- Abstract entry tracking one active (unreaped) spawned child process handle. -/
structure ProcessHandleEntry where
  /-- Unique handle identifier matching `ProcessHandle.handleId`. -/
  handleId : Nat
  /-- Positive child process ID (`pid > 0`). -/
  pid : Int
  /-- Positive isolated child process group ID (`pgid > 0`). -/
  pgid : Int
  /-- Whether `awaitOutput` has consumed the handle's child pipes. -/
  ioConsumed : Bool := false
  /-- Whether the child exit status has already been waited/reaped. -/
  waited : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure abstract state for `LeanSwe.Process` tracking active unreaped handles. -/
structure ProcessModelState where
  /-- Monotonically increasing next fresh handle identifier (`≥ 1`). -/
  nextHandleId : Nat := 1
  /-- Active (unreaped) spawned child process handles. -/
  activeHandles : List ProcessHandleEntry := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Return `true` iff a list of `Nat` handle identifiers contains no duplicates. -/
def hasNoDupHandleIds : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && hasNoDupHandleIds xs

/-- Total well-formedness guard on `ProcessModelState` for `Core.RefinesStepFrom`. -/
def processStateWf (s : ProcessModelState) : Bool :=
  decide (s.nextHandleId ≥ 1) &&
  hasNoDupHandleIds (s.activeHandles.map (·.handleId)) &&
  s.activeHandles.all fun e => decide (e.handleId < s.nextHandleId && e.pid > 0 && e.pgid > 0)

/-- Error invariant asserting a non-empty diagnostic message and excluding post-spawn outcome and non-zero-exit kinds. -/
def isNonOutcomeError (err : ProcessError) : Prop :=
  err.message ≠ "" ∧
  err.kind ≠ .timedOut ∧
  err.kind ≠ .outputLimitExceeded ∧
  err.kind ≠ .terminatedBySignal ∧
  err.kind ≠ .nonZeroExit

/-- Allowed post-step invariant on `RawProcessOpsM.spawn` over `ProcessModelState`. -/
def allowedRawSpawn (s : ProcessModelState) (res : Except ProcessError ProcessHandle)
    (s' : ProcessModelState) : Prop :=
  match res with
  | .error err => s' = s ∧ isNonOutcomeError err
  | .ok h =>
    h.handleId = s.nextHandleId ∧
    h.pid > 0 ∧
    h.pgid > 0 ∧
    s' = { nextHandleId := s.nextHandleId + 1
           activeHandles :=
             { handleId := h.handleId
               pid := h.pid
               pgid := h.pgid
               ioConsumed := false
               waited := false } :: s.activeHandles }

/-- Allowed outcome invariant on `ExecOutcome` returned by `awaitOutput`. -/
def allowedAwaitOutcome (timeoutMs? maxOutputBytes? : Option Nat) (outcome : ExecOutcome) : Prop :=
  match outcome with
  | .exited res =>
    ∀ lim, maxOutputBytes? = some lim → res.stdout.size + res.stderr.size ≤ lim
  | .signaled _ _ _ => True
  | .timedOut _ _ => timeoutMs?.isSome = true
  | .outputLimitExceeded out err =>
    maxOutputBytes?.isSome = true ∧
    ∀ lim, maxOutputBytes? = some lim → out.size + err.size ≤ lim

/-- Allowed post-step invariant on `awaitOutput` preserving handle IDs and other active entries. -/
def allowedAwaitCore (s : ProcessModelState) (h : ProcessHandle)
    (timeoutMs? maxOutputBytes? : Option Nat) (res : Except ProcessError ExecOutcome)
    (s' : ProcessModelState) : Prop :=
  processStateWf s' = true ∧
  s'.nextHandleId = s.nextHandleId ∧
  s'.activeHandles.map (·.handleId) = s.activeHandles.map (·.handleId) ∧
  s'.activeHandles.filter (·.handleId != h.handleId) =
    s.activeHandles.filter (·.handleId != h.handleId) ∧
  match res with
  | .error err => isNonOutcomeError err
  | .ok outcome =>
    h.handleId ∈ s.activeHandles.map (·.handleId) ∧
    allowedAwaitOutcome timeoutMs? maxOutputBytes? outcome

/-- Allowed post-step invariant on `killProcessGroup` preserving active handles. -/
def allowedKillGroup (s : ProcessModelState) (res : Except ProcessError Unit)
    (s' : ProcessModelState) : Prop :=
  s' = s ∧
  match res with
  | .ok () => True
  | .error err => isNonOutcomeError err

/-- Allowed post-step invariant on `reap` detaching `h.handleId` from `activeHandles`. -/
def allowedReap (s : ProcessModelState) (h : ProcessHandle) (res : Except ProcessError Unit)
    (s' : ProcessModelState) : Prop :=
  s'.nextHandleId = s.nextHandleId ∧
  s'.activeHandles = s.activeHandles.filter (·.handleId != h.handleId) ∧
  match res with
  | .ok () => True
  | .error err => isNonOutcomeError err

/-- Single-step request sum covering all 6 operations of `RawProcessOpsM`. -/
inductive RawStepReq where
  /-- Pure `raw.mapRawError err`. -/
  | mapRawError (err : ProcessRawError)
  /-- `raw.spawn req`. -/
  | spawn (req : ExecRequest)
  /-- `raw.awaitOutput h stdin timeoutMs maxOutputBytes`. -/
  | awaitOutput (h : ProcessHandle) (stdin : ByteArray) (timeoutMs maxOutputBytes : Option Nat)
  /-- `raw.killProcessGroup h`. -/
  | killProcessGroup (h : ProcessHandle)
  /-- `raw.reap h`. -/
  | reap (h : ProcessHandle)
  /-- `raw.activeProcessCount`. -/
  | activeProcessCount
  deriving BEq, DecidableEq, Inhabited

/-- Single-step output sum for `RawStepReq` transitions in `Core.RefinesStepFrom`. -/
inductive RawStepOut where
  /-- Normalized error returned by `RawProcessOpsM.mapRawError`. -/
  | mapped (err : ProcessError)
  /-- Spawn result returned by `RawProcessOpsM.spawn`. -/
  | spawned (res : Except ProcessError ProcessHandle)
  /-- Stream/wait outcome returned by `RawProcessOpsM.awaitOutput`. -/
  | awaited (res : Except ProcessError ExecOutcome)
  /-- Unit result returned by `RawProcessOpsM.killProcessGroup` or `RawProcessOpsM.reap`. -/
  | unit (res : Except ProcessError Unit)
  /-- Active handle count returned by `RawProcessOpsM.activeProcessCount`. -/
  | count (n : Nat)
  deriving Inhabited

/-- Execute one `RawStepReq` against an arbitrary `RawProcessOpsM (StateM W)`. -/
def execRawStep {W : Type} (raw : RawProcessOpsM (StateM W)) : RawStepReq → StateM W RawStepOut
  | .mapRawError err => pure (.mapped (raw.mapRawError err))
  | .spawn req => .spawned <$> raw.spawn req
  | .awaitOutput h stdin timeoutMs maxOutputBytes =>
    .awaited <$> raw.awaitOutput h stdin timeoutMs maxOutputBytes
  | .killProcessGroup h => .unit <$> raw.killProcessGroup h
  | .reap h => .unit <$> raw.reap h
  | .activeProcessCount => .count <$> raw.activeProcessCount

/-- Relational single-step contract for `RawProcessOpsM` over `ProcessModelState`. -/
def allowedRawStep (s : ProcessModelState) (req : RawStepReq) (out : RawStepOut)
    (s' : ProcessModelState) : Prop :=
  processStateWf s = true ∧
  processStateWf s' = true ∧
  match req, out with
  | .mapRawError err, .mapped res => s' = s ∧ res = mapRawErrorModel err
  | .spawn _, .spawned res => allowedRawSpawn s res s'
  | .awaitOutput h _ timeoutMs maxOutputBytes, .awaited res =>
    allowedAwaitCore s h timeoutMs maxOutputBytes res s'
  | .killProcessGroup _, .unit res => allowedKillGroup s res s'
  | .reap h, .unit res => allowedReap s h res s'
  | .activeProcessCount, .count n => s' = s ∧ n = s.activeHandles.length
  | _, _ => False

/-- Single-step request sum covering all 9 effectful operations of `ProcessApiM`. -/
inductive PkgStepReq where
  /-- Validated `ProcessApiM.spawn` request. -/
  | spawn (req : SpawnRequest)
  /-- `ProcessApiM.awaitOutput` request. -/
  | awaitOutput (h : ProcessHandle) (stdin : ByteArray) (timeoutMs maxOutputBytes : Option Nat)
  /-- `ProcessApiM.killProcessGroup` request. -/
  | killProcessGroup (h : ProcessHandle)
  /-- `ProcessApiM.reap` request. -/
  | reap (h : ProcessHandle)
  /-- One-shot `ProcessApiM.run` request. -/
  | run (req : ExecRequest)
  /-- One-shot exit-checked `ProcessApiM.runChecked` request. -/
  | runChecked (req : ExecRequest)
  /-- Convenience `ProcessApiM.runCommand` request. -/
  | runCommand (program : String) (args : Array String)
  /-- Convenience `ProcessApiM.runCommandChecked` request. -/
  | runCommandChecked (program : String) (args : Array String)
  /-- Active unreaped handle query `ProcessApiM.activeProcessCount`. -/
  | activeProcessCount
  deriving BEq, DecidableEq, Inhabited

/-- Single-step output sum for `PkgStepReq` transitions in `Core.RefinesStepFrom`. -/
inductive PkgStepOut where
  /-- Spawn result returned by `ProcessApiM.spawn`. -/
  | spawned (res : Except ProcessError ProcessHandle)
  /-- Stream/wait outcome returned by `ProcessApiM.awaitOutput`. -/
  | awaited (res : Except ProcessError ExecOutcome)
  /-- Unit result returned by `ProcessApiM.killProcessGroup` or `ProcessApiM.reap`. -/
  | unit (res : Except ProcessError Unit)
  /-- Command execution result returned by `run`, `runChecked`, `runCommand`, or `runCommandChecked`. -/
  | execRes (res : Except ProcessError ExecResult)
  /-- Active handle count returned by `ProcessApiM.activeProcessCount`. -/
  | count (n : Nat)
  deriving Inhabited

/-- Execute one `PkgStepReq` against an arbitrary `ProcessApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : ProcessApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .spawn req => .spawned <$> api.spawn req
  | .awaitOutput h stdin timeoutMs maxOutputBytes =>
    .awaited <$> api.awaitOutput h stdin timeoutMs maxOutputBytes
  | .killProcessGroup h => .unit <$> api.killProcessGroup h
  | .reap h => .unit <$> api.reap h
  | .run req => .execRes <$> api.run req
  | .runChecked req => .execRes <$> api.runChecked req
  | .runCommand program args => .execRes <$> api.runCommand program args
  | .runCommandChecked program args => .execRes <$> api.runCommandChecked program args
  | .activeProcessCount => .count <$> api.activeProcessCount

/-- Allowed outcome and error metadata relation for `run`/`runChecked`/`runCommand`/`runCommandChecked`. -/
def allowedExecResult (checked : Bool) (req : ExecRequest)
    (res : Except ProcessError ExecResult) : Prop :=
  match res with
  | .ok out =>
    (checked = true → out.exitCode = 0) ∧
    ∀ lim, req.maxOutputBytes = some lim → out.stdout.size + out.stderr.size ≤ lim
  | .error err =>
    err.message ≠ "" ∧
    (err.kind = .timedOut → req.timeoutMs.isSome = true ∧ err.program = some req.program) ∧
    (err.kind = .outputLimitExceeded →
      req.maxOutputBytes.isSome = true ∧
      err.program = some req.program ∧
      ∀ lim, req.maxOutputBytes = some lim →
        (err.stdout.map ByteArray.size |>.getD 0) +
          (err.stderr.map ByteArray.size |>.getD 0) ≤ lim) ∧
    (err.kind = .terminatedBySignal → err.program = some req.program ∧ err.signal ≠ none) ∧
    (err.kind = .nonZeroExit →
      checked = true ∧
      err.program = some req.program ∧
      err.exitCode ≠ none ∧
      err.exitCode ≠ some 0 ∧
      err.stdout ≠ none ∧
      err.stderr ≠ none)

/-- Allowed `ProcessApiM.run` or `ProcessApiM.runChecked` step conserving `activeHandles`. -/
def allowedPkgRun (checked : Bool) (s : ProcessModelState) (req : ExecRequest)
    (res : Except ProcessError ExecResult) (s' : ProcessModelState) : Prop :=
  match validateRequestModel req with
  | .error verr => res = .error verr ∧ s' = s
  | .ok _ =>
    s'.activeHandles = s.activeHandles ∧
    (s'.nextHandleId = s.nextHandleId ∨ s'.nextHandleId = s.nextHandleId + 1) ∧
    allowedExecResult checked req res

/-- Relational single-step contract for all 9 effectful `ProcessApiM` operations over `ProcessModelState`. -/
def allowedPkgStep (s : ProcessModelState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : ProcessModelState) : Prop :=
  processStateWf s = true ∧
  processStateWf s' = true ∧
  match req, out with
  | .spawn r, .spawned res =>
    match validateSpawnRequestModel r with
    | .error err => res = .error err ∧ s' = s
    | .ok _ => allowedRawSpawn s res s'
  | .awaitOutput h _ timeoutMs maxOutputBytes, .awaited res =>
    if timeoutMs == some 0 then
      res = .error { kind := .invalidInput, message := "timeoutMs must be greater than zero" } ∧ s' = s
    else
      allowedAwaitCore s h timeoutMs maxOutputBytes res s'
  | .killProcessGroup _, .unit res => allowedKillGroup s res s'
  | .reap h, .unit res => allowedReap s h res s'
  | .run r, .execRes res => allowedPkgRun false s r res s'
  | .runChecked r, .execRes res => allowedPkgRun true s r res s'
  | .runCommand prog args, .execRes res => allowedPkgRun false s (mkCommandRequestModel prog args) res s'
  | .runCommandChecked prog args, .execRes res => allowedPkgRun true s (mkCommandRequestModel prog args) res s'
  | .activeProcessCount, .count n => s' = s ∧ n = s.activeHandles.length
  | _, _ => False

end LeanSwe.Process.Model
