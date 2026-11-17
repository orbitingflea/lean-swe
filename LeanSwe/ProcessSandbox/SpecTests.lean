import Core.NondetTest
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model

namespace LeanSwe.ProcessSandbox

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.ProcessSandbox.Model

/-- Remove the first `(handleId, boxHandleId)` entry matching `id`. -/
def eraseFirstForwarder (id : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | p :: rest => if p.1 == id then rest else p :: eraseFirstForwarder id rest

/-- Deterministic mock state for verifying `ProcessSandboxApiM` over `StateM` and `ExceptT`. -/
structure MockSandboxState where
  /-- Next candidate handle ID (`1` used as fallback when outside `1 .. UInt64.size - 1`). -/
  nextHandleId : Nat := 1
  /-- Currently open `PlanHandle` IDs. -/
  openPlans : List Nat := []
  /-- Currently active (un-reaped) `BoxHandle` IDs. -/
  activeBoxes : List Nat := []
  /-- Currently running `PortForwarderHandle` `(handleId, boxHandleId)` pairs. -/
  activeForwarders : List (Nat × Nat) := []
  /-- Whether host supports Linux + `bwrap` + namespaces + Landlock ABI >= 4 + `seccomp`. -/
  hostBaseAvailable : Bool := true
  /-- Whether direct `/sys/fs/cgroup` `memory` delegation (`memory.max` + `memory.swap.max=0`) is enforceable. -/
  memoryCgroupAvailable : Bool := true
  /-- Whether direct `/sys/fs/cgroup` `pids` delegation (`pids.max`) is enforceable. -/
  pidsCgroupAvailable : Bool := true
  /-- Host runtime preset returned by `discoverHostPreset`. -/
  preset : HostRuntimePreset := {}
  /-- Optional error injected at `spawnBox`. -/
  failSpawnWith : Option SandboxError := none
  /-- Optional error injected at `startPortForwarders`. -/
  failForwarderStartWith : Option SandboxError := none
  /-- Scripted guest execution result or `execvp` error returned by `readBoxOutput`. -/
  scriptedOutput : Except SandboxError SandboxResult :=
    .ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
  /-- Whether `readBoxOutput` throws a monadic cancellation exception in `ExceptT`. -/
  throwOnReadOutput : Bool := false
  /-- Whether `startPortForwarders` throws a monadic cancellation exception in `ExceptT`. -/
  throwOnStartForwarders : Bool := false
  /-- Last `PreflightReq` passed to `preflight`. -/
  lastPreflightReq : Option PreflightReq := none
  /-- Last `CompiledSandboxPlan` sealed via `sealPlan`. -/
  lastSealedPlan : Option CompiledSandboxPlan := none
  /-- Last `Array PortForward` passed to `startPortForwarders`. -/
  lastStartedForwards : Option (Array PortForward) := none
  /-- Last `stdin` payload passed to `readBoxOutput`. -/
  lastReadStdin : Option ByteArray := none
  /-- Last `timeoutMs` deadline passed to `readBoxOutput`. -/
  lastReadTimeoutMs : Option Nat := none
  /-- Total `spawnBox` invocations. -/
  spawnCalls : Nat := 0
  /-- Total `readBoxOutput` invocations (guest command started). -/
  guestExecCalls : Nat := 0
  /-- Total `killProcessGroup` invocations. -/
  killPgCalls : Nat := 0
  /-- Total `pidfdKill` invocations. -/
  pidfdKillCalls : Nat := 0
  /-- Total `reapBox` invocations. -/
  reapCalls : Nat := 0
  deriving Inhabited

instance : Repr MockSandboxState where
  reprPrec s _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "openPlans := " ++ repr s.openPlans,
        "activeBoxes := " ++ repr s.activeBoxes,
        "activeForwarders := " ++ repr s.activeForwarders,
        "hostBaseAvailable := " ++ repr s.hostBaseAvailable,
        "memoryCgroupAvailable := " ++ repr s.memoryCgroupAvailable,
        "pidsCgroupAvailable := " ++ repr s.pidsCgroupAvailable,
        "spawnCalls := " ++ repr s.spawnCalls,
        "guestExecCalls := " ++ repr s.guestExecCalls,
        "killPgCalls := " ++ repr s.killPgCalls,
        "pidfdKillCalls := " ++ repr s.pidfdKillCalls,
        "reapCalls := " ++ repr s.reapCalls
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Normalize a `SandboxRawError` with guaranteed non-empty diagnostic message for mocks. -/
def mockMapRawError : SandboxRawError → SandboxError
  | .unavailable errno? detail =>
    { kind := .unavailable, path := none, errnoCode := errno?,
      message := if detail.isEmpty then "sandbox unavailable" else detail }
  | .notFound p errno detail =>
    { kind := .notFound, path := some p, errnoCode := some errno,
      message := if detail.isEmpty then "not found" else detail }
  | .permissionDenied p? errno detail =>
    { kind := .permissionDenied, path := p?, errnoCode := some errno,
      message := if detail.isEmpty then "permission denied" else detail }
  | .invalidArgument p? errno? detail =>
    { kind := .invalidInput, path := p?, errnoCode := errno?,
      message := if detail.isEmpty then "invalid argument" else detail }
  | .ioError p? errno detail =>
    { kind := .ioError, path := p?, errnoCode := some errno,
      message := if detail.isEmpty then "io error" else detail }
  | .userError detail =>
    { kind := .ioError, path := none, errnoCode := none,
      message := if detail.isEmpty then "sandbox error" else detail }

/-- Allocate a valid 64-bit handle ID from `s.nextHandleId`. -/
def allocMockHandleId (s : MockSandboxState) : Nat :=
  if isValidSandboxHandleId s.nextHandleId then s.nextHandleId else 1

/-- Deterministic `RawProcessSandboxOpsM (StateM MockSandboxState)` test double. -/
def mockRawOps : RawProcessSandboxOpsM (StateM MockSandboxState) :=
  { mapRawError := mockMapRawError
    hostSeccompArch := fun s =>
      if s.hostBaseAvailable then
        (.ok .x86_64, s)
      else
        (.error { kind := .unavailable, message := "sandbox host architecture unavailable" }, s)
    preflight := fun req s =>
      let s' := { s with lastPreflightReq := some req }
      if !s.hostBaseAvailable then
        (.error { kind := .unavailable, message := "sandbox host backend unavailable" }, s')
      else if req.needMemoryCgroup && !s.memoryCgroupAvailable then
        (.error { kind := .unavailable, message := "direct cgroup v2 memory controller unavailable" }, s')
      else if req.needPidsCgroup && !s.pidsCgroupAvailable then
        (.error { kind := .unavailable, message := "direct cgroup v2 pids controller unavailable" }, s')
      else
        (.ok (), s')
    discoverHostPreset := fun s => (.ok s.preset, s)
    sealPlan := fun plan s =>
      let id := allocMockHandleId s
      (.ok { handleId := id },
        { s with
          nextHandleId := id + 1
          openPlans := id :: s.openPlans
          lastSealedPlan := some plan })
    closePlan := fun ph s =>
      if !isValidSandboxHandleId ph.handleId || !s.openPlans.contains ph.handleId then
        (.error { kind := .invalidInput, message := "invalid or closed plan handle" }, s)
      else
        (.ok (), { s with openPlans := s.openPlans.erase ph.handleId })
    spawnBox := fun ph s =>
      if !isValidSandboxHandleId ph.handleId || !s.openPlans.contains ph.handleId then
        (.error { kind := .invalidInput, message := "invalid plan handle for spawnBox" }, s)
      else
        let s' := { s with spawnCalls := s.spawnCalls + 1 }
        match s.failSpawnWith with
        | some err =>
          (.error { err with message := if err.message.isEmpty then "spawnBox failed" else err.message }, s')
        | none =>
          let id := allocMockHandleId s'
          let bh : BoxHandle := { handleId := id, pid := 200, pgid := 200, pidfd := 5 }
          (.ok bh, { s' with nextHandleId := id + 1, activeBoxes := id :: s'.activeBoxes })
    startPortForwarders := fun bh fwds s =>
      if !isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle for startPortForwarders" }, s)
      else
        let s' := { s with lastStartedForwards := some fwds }
        match s.failForwarderStartWith with
        | some err =>
          (.error { err with message := if err.message.isEmpty then "forwarder start failed" else err.message }, s')
        | none =>
          let id := allocMockHandleId s'
          (.ok { handleId := id, boxHandleId := bh.handleId },
            { s' with
              nextHandleId := id + 1
              activeForwarders := (id, bh.handleId) :: s'.activeForwarders })
    stopPortForwarders := fun fh s =>
      if !isValidSandboxHandleId fh.handleId || !s.activeForwarders.any (fun p => p.1 == fh.handleId) then
        (.error { kind := .invalidInput, message := "invalid or stopped forwarder handle" }, s)
      else
        (.ok (), { s with activeForwarders := eraseFirstForwarder fh.handleId s.activeForwarders })
    readBoxOutput := fun bh stdin timeoutMs maxOut? s =>
      if !isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle for readBoxOutput" }, s)
      else
        let s' :=
          { s with
            guestExecCalls := s.guestExecCalls + 1
            lastReadStdin := some stdin
            lastReadTimeoutMs := some timeoutMs }
        match s.scriptedOutput with
        | .error err =>
          (.error { err with message := if err.message.isEmpty then "guest exec failed" else err.message }, s')
        | .ok res =>
          match maxOut? with
          | none =>
            let cleanOutcome :=
              if res.outcome == .outputLimitExceeded then .exited 1 else res.outcome
            (.ok { res with outcome := cleanOutcome }, s')
          | some cap =>
            let outCap := res.stdout.extract 0 (Nat.min res.stdout.size cap)
            let rem := cap - outCap.size
            let errCap := res.stderr.extract 0 (Nat.min res.stderr.size rem)
            let cappedOutcome :=
              if res.stdout.size + res.stderr.size > cap then .outputLimitExceeded else res.outcome
            (.ok { outcome := cappedOutcome, stdout := outCap, stderr := errCap }, s')
    killProcessGroup := fun bh s =>
      if !isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle for killProcessGroup" }, s)
      else
        (.ok (), { s with killPgCalls := s.killPgCalls + 1 })
    pidfdKill := fun bh s =>
      if !isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle for pidfdKill" }, s)
      else
        (.ok (), { s with pidfdKillCalls := s.pidfdKillCalls + 1 })
    reapBox := fun bh s =>
      if !isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle for reapBox" }, s)
      else
        (.ok (), { s with activeBoxes := s.activeBoxes.erase bh.handleId, reapCalls := s.reapCalls + 1 })
    activeResourceCounts := fun s =>
      ({ openPlans := s.openPlans.length
         activeBoxes := s.activeBoxes.length
         activeForwarders := s.activeForwarders.length }, s) }

/-- Lift a `StateM MockSandboxState` action into `ExceptT String (StateM MockSandboxState)`. -/
def liftMockState {α : Type} (act : StateM MockSandboxState α) :
    ExceptT String (StateM MockSandboxState) α :=
  ExceptT.mk (fun s => let (a, s') := act s; (.ok a, s'))

/-- Exception-capable `RawProcessSandboxOpsM (ExceptT String (StateM MockSandboxState))` for `MonadFinally` cancellation tests. -/
def mockRawOpsEx : RawProcessSandboxOpsM (ExceptT String (StateM MockSandboxState)) :=
  { mapRawError := mockRawOps.mapRawError
    hostSeccompArch := liftMockState mockRawOps.hostSeccompArch
    preflight := fun req => liftMockState (mockRawOps.preflight req)
    discoverHostPreset := liftMockState mockRawOps.discoverHostPreset
    sealPlan := fun plan => liftMockState (mockRawOps.sealPlan plan)
    closePlan := fun ph => liftMockState (mockRawOps.closePlan ph)
    spawnBox := fun ph => liftMockState (mockRawOps.spawnBox ph)
    startPortForwarders := fun bh fwds =>
      ExceptT.mk fun s =>
        if s.throwOnStartForwarders then
          (.error "cancelled-during-forwarder-start", s)
        else
          let (r, s') := (mockRawOps.startPortForwarders bh fwds).run s
          (.ok r, s')
    stopPortForwarders := fun fh => liftMockState (mockRawOps.stopPortForwarders fh)
    readBoxOutput := fun bh stdin timeoutMs maxOut? =>
      ExceptT.mk fun s =>
        if s.throwOnReadOutput then
          (.error "cancelled-during-read",
            { s with
              guestExecCalls := s.guestExecCalls + 1
              lastReadStdin := some stdin
              lastReadTimeoutMs := some timeoutMs })
        else
          let (r, s') := (mockRawOps.readBoxOutput bh stdin timeoutMs maxOut?).run s
          (.ok r, s')
    killProcessGroup := fun bh => liftMockState (mockRawOps.killProcessGroup bh)
    pidfdKill := fun bh => liftMockState (mockRawOps.pidfdKill bh)
    reapBox := fun bh => liftMockState (mockRawOps.reapBox bh)
    activeResourceCounts := liftMockState mockRawOps.activeResourceCounts }

/-- `api.validateSpec` rejects empty `program`, NUL bytes in `program`, or NUL bytes in `args` with `.invalidInput`. -/
def test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let specEmpty ← nondet BoxSpec
  assume (specEmpty.program = "")
  match api.validateSpec specEmpty with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")
  let specNulProg ← nondet BoxSpec
  assume ('\x00' ∈ specNulProg.program.toList)
  match api.validateSpec specNulProg with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")
  let specNulArg ← nondet BoxSpec
  let idx ← nondet Nat
  assume (idx < specNulArg.args.size)
  assume ('\x00' ∈ specNulArg.args[idx]!.toList)
  match api.validateSpec specNulArg with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `api.validateSpec` rejects `cwd` values that are empty, contain NUL bytes, are relative, or contain `".."` segments. -/
def test_psandbox_validateSpec_rejectsInvalidCwd
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let spec ← nondet BoxSpec
  let d ← nondet String
  assume (spec.cwd = some d)
  assume (normalizeCleanAbsPath d = none)
  match api.validateSpec spec with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `api.validateSpec` rejects empty, NUL, relative, or `".."` mount `hostPath` or `boxPath` across `readOnly`, `readWrite`, and `scratch`. -/
def test_psandbox_validateSpec_rejectsInvalidMountPaths
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let badPath ← nondet String
  assume (normalizeCleanAbsPath badPath = none)
  let badMounts : List SandboxMount :=
    [ .readOnly badPath "/work"
    , .readOnly "/host/src" badPath
    , .readWrite badPath "/work"
    , .readWrite "/host/src" badPath
    , .scratch badPath
    ]
  NondetTest.assert (badMounts.all (fun m =>
    match api.validateSpec { program := "/bin/true", mounts := #[m] } with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false) = true)

/-- `api.validateSpec` rejects duplicate target `boxPath` entries (including lexically equivalent paths like `"/work"` and `"/work/"`). -/
def test_psandbox_validateSpec_rejectsDuplicateBoxPath
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let m₁ ← nondet SandboxMount
  let m₂ ← nondet SandboxMount
  let canonBp ← nondet String
  assume ((validateAndNormalizeMount m₁).map mountBoxPath = .ok canonBp)
  assume ((validateAndNormalizeMount m₂).map mountBoxPath = .ok canonBp)
  match api.validateSpec { program := "/bin/true", mounts := #[m₁, m₂] } with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `api.validateSpec` rejects any mount targeting `"/"` or shadowing/writing `/usr`, `/bin`, `/sbin`, `/lib`, `/lib64`, `/etc`, `/dev`, or `/proc`. -/
def test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let bp ← nondet String
  let bSegs ← nondet (List String)
  assume (parseCleanAbsSegs bp = some bSegs)
  assume (isReservedBoxSegs bSegs = true)
  let attempts : List SandboxMount :=
    [ .readOnly "/var/data" bp
    , .readWrite "/var/data" bp
    , .scratch bp
    ]
  NondetTest.assert (attempts.all (fun m =>
    match api.validateSpec { program := "/bin/true", mounts := #[m] } with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false) = true)

/-- `api.validateSpec` rejects port `0` (`boxPort = 0` or `hostPort = 0`) and duplicate `boxPort`s while allowing distinct `boxPort`s to target the same valid `hostPort`. -/
def test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let p ← nondet UInt16
  assume (p != 0)
  let zeroBox : BoxSpec := { program := "/bin/true", portForwards := #[{ boxPort := 0, hostPort := p }] }
  let zeroHost : BoxSpec := { program := "/bin/true", portForwards := #[{ boxPort := p, hostPort := 0 }] }
  let dupBox : BoxSpec :=
    { program := "/bin/true"
      portForwards := #[{ boxPort := p, hostPort := 8080 }, { boxPort := p, hostPort := 8081 }] }
  NondetTest.assert (match api.validateSpec zeroBox with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match api.validateSpec zeroHost with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match api.validateSpec dupBox with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  let p₂ ← nondet UInt16
  assume (p₂ != 0 ∧ p₂ ≠ p)
  let sharedHost : BoxSpec :=
    { program := "/bin/true"
      portForwards := #[{ boxPort := p, hostPort := 9000 }, { boxPort := p₂, hostPort := 9000 }] }
  NondetTest.assert ((api.validateSpec sharedHost).isOk = true)

/-- `api.validateSpec` rejects `timeoutMs = 0`, `memoryMaxBytes = some 0`, and `pidsMax = some 0` while accepting `fileSizeMaxBytes = some 0` and `maxOutputBytes = some 0`. -/
def test_psandbox_validateSpec_limitsRules
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let zeroTimeout : BoxSpec := { program := "/bin/true", limits := { timeoutMs := 0 } }
  let zeroMem : BoxSpec := { program := "/bin/true", limits := { memoryMaxBytes := some 0 } }
  let zeroPids : BoxSpec := { program := "/bin/true", limits := { pidsMax := some 0 } }
  let zeroFileAndOut : BoxSpec :=
    { program := "/bin/true"
      limits := { timeoutMs := 100, fileSizeMaxBytes := some 0, maxOutputBytes := some 0 } }
  NondetTest.assert (match api.validateSpec zeroTimeout with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match api.validateSpec zeroMem with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match api.validateSpec zeroPids with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert ((api.validateSpec zeroFileAndOut).isOk = true)

/-- `api.validateSpec` rejects empty env keys, `'='` in env keys, or NUL bytes in env keys or values. -/
def test_psandbox_validateSpec_rejectsInvalidEnv
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let spec ← nondet BoxSpec
  let idx ← nondet Nat
  assume (idx < spec.env.size)
  assume (isValidEnvPair spec.env[idx]! = false)
  match api.validateSpec spec with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `api.validateSpec` defaults `cwd = none` to `"/tmp"`, injects `.scratch "/tmp"` iff no mount targets `"/tmp"`, injects `("PATH", "/usr/bin:/bin")` iff `"PATH"` is absent, deduplicates env keys (last-write-wins), and is idempotent. -/
def test_psandbox_validateSpec_defaultsOverridesAndIdempotence
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let k ← nondet String
  let v₁ ← nondet String
  let v₂ ← nondet String
  assume (isValidEnvPair (k, v₁) = true ∧ isValidEnvPair (k, v₂) = true)
  assume (k ≠ "PATH")
  let specDefault : BoxSpec :=
    { program := "python3"
      args := #["-c", "pass"]
      cwd := none
      mounts := #[.readOnly "/work/src" "/workspace/"]
      env := #[(k, v₁), (k, v₂)] }
  match api.validateSpec specDefault with
  | .error _ => NondetTest.assert False
  | .ok valid =>
    NondetTest.assert (valid.cwd = "/tmp")
    NondetTest.assert (valid.mounts = #[.scratch "/tmp", .readOnly "/work/src" "/workspace"])
    NondetTest.assert (valid.env = #[("PATH", "/usr/bin:/bin"), (k, v₂)])
    NondetTest.assert (api.validateSpec (validBoxSpecToBoxSpec valid) = .ok valid)
  let customPath ← nondet String
  assume (!hasNulChar customPath.toList)
  let specCustomTmpAndPath : BoxSpec :=
    { program := "/usr/bin/env"
      cwd := some "/workspace/sub/"
      mounts := #[.readWrite "/host/tmp" "/tmp/"]
      env := #[("PATH", customPath)] }
  match api.validateSpec specCustomTmpAndPath with
  | .error _ => NondetTest.assert False
  | .ok validCustom =>
    NondetTest.assert (validCustom.cwd = "/workspace/sub")
    NondetTest.assert (validCustom.mounts = #[.readWrite "/host/tmp" "/tmp"])
    NondetTest.assert (validCustom.env = #[("PATH", customPath)])
    NondetTest.assert (api.validateSpec (validBoxSpecToBoxSpec validCustom) = .ok validCustom)

/-- Running an invalid `BoxSpec` fails immediately with `.invalidInput` and leaves `MockSandboxState` untouched. -/
def test_psandbox_run_invalidSpec_hasZeroSideEffects
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  let spec ← nondet BoxSpec
  match api.validateSpec spec with
  | .ok _ => assume False
  | .error _ =>
    let (res, s₁) := (api.run spec).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ s₁ = s₀)

/-- `isAvailable` probes full host capability without leaking resources, and when either `preflight` or pre-`execvp` `spawnBox` setup fails `run` fails closed with `.unavailable`, zero guest execution, and conserved resources. -/
def test_psandbox_isAvailable_and_failClosedUnavailable
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  let (avail, sAvail) := api.isAvailable.run s₀
  let expectedAvail :=
    s₀.hostBaseAvailable && s₀.memoryCgroupAvailable && s₀.pidsCgroupAvailable
  NondetTest.assert (avail = expectedAvail ∧
    sAvail.openPlans = s₀.openPlans ∧
    sAvail.activeBoxes = s₀.activeBoxes ∧
    sAvail.activeForwarders = s₀.activeForwarders ∧
    sAvail.spawnCalls = s₀.spawnCalls ∧
    sAvail.guestExecCalls = s₀.guestExecCalls)
  let sUnavail ← nondet MockSandboxState
  let spec ← nondet BoxSpec
  assume ((api.validateSpec spec).isOk = true)
  assume (!sUnavail.hostBaseAvailable ∨
    (spec.limits.memoryMaxBytes.isSome && !sUnavail.memoryCgroupAvailable) ∨
    (spec.limits.pidsMax.isSome && !sUnavail.pidsCgroupAvailable))
  let (res, s₁) := (api.run spec).run sUnavail
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .unavailable ∧ e.message ≠ "") ∧
    s₁.spawnCalls = sUnavail.spawnCalls ∧
    s₁.guestExecCalls = sUnavail.guestExecCalls ∧
    s₁.openPlans = sUnavail.openPlans ∧
    s₁.activeBoxes = sUnavail.activeBoxes ∧
    s₁.activeForwarders = sUnavail.activeForwarders)
  let sSpawnUnavail ← nondet MockSandboxState
  let specSpawn ← nondet BoxSpec
  assume ((api.validateSpec specSpawn).isOk = true)
  assume (sSpawnUnavail.hostBaseAvailable = true ∧
    sSpawnUnavail.memoryCgroupAvailable = true ∧
    sSpawnUnavail.pidsCgroupAvailable = true)
  let sPreExecFail : MockSandboxState :=
    { sSpawnUnavail with
      failSpawnWith := some { kind := .unavailable, message := "pre-execvp setup failed" } }
  let (resSpawn, s₂) := (api.run specSpawn).run sPreExecFail
  NondetTest.assert ((∃ e, resSpawn = .error e ∧ e.kind = .unavailable ∧ e.message ≠ "") ∧
    s₂.guestExecCalls = sPreExecFail.guestExecCalls ∧
    s₂.openPlans = sPreExecFail.openPlans ∧
    s₂.activeBoxes = sPreExecFail.activeBoxes ∧
    s₂.activeForwarders = sPreExecFail.activeForwarders)

/-- `run` compiles an empty-root, clean-env, direct-`cgroup v2` plan that filters presets to allowlists, preserves top-level symlinks, masks nested host `$HOME` under `/usr` (including through symlinked preset roots), resolves synthetic `/etc/hosts` box-locally, preserves stable depth-sorted mounts, blocks `socket(AF_UNIX, ...)` while allowing anonymous `socketpair`, and sets `clone3` `ENOSYS` fallback. -/
def test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧ s₀.pidsCgroupAvailable = true)
  assume (s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
  let sWithPreset : MockSandboxState :=
    { s₀ with
      preset :=
        { systemEntries :=
            #[ .readOnlyDir "/usr"
             , .topSymlink "/bin" "usr/bin"
             , .topSymlink "/lib" "usr/lib"
             , .readOnlyDir "/home" ]
          etcPaths := #["/etc/passwd", "/etc/localtime", "/etc/shadow"]
          excludedHomePaths :=
            #[ "/usr/local/homes/user"
             , "/lib/custom_home/bob"
             , "/home/user" ] } }
  let spec : BoxSpec :=
    { program := "env"
      mounts := #[.readOnly "/data/sub" "/work/sub", .readOnly "/data" "/work"] }
  let (_, s₁) := (api.run spec).run sWithPreset
  match s₁.lastSealedPlan with
  | none => NondetTest.assert False
  | some plan =>
    NondetTest.assert (isValidCompiledPlan plan = true)
    NondetTest.assert (plan.emptyRoot = true ∧
      plan.directCgroupV2Fs = true ∧
      plan.blockUnixSocketAndSmc = true ∧
      plan.allowAnonUnixSocketpair = true ∧
      plan.clone3EnosysFallback = true ∧
      plan.cleanEnv = true)
    NondetTest.assert (plan.presetSystemEntries =
      #[.readOnlyDir "/usr", .topSymlink "/bin" "usr/bin", .topSymlink "/lib" "usr/lib"])
    NondetTest.assert (plan.presetEtcPaths = #["/etc/passwd", "/etc/localtime"])
    NondetTest.assert (plan.maskedPresetPaths =
      #["/usr/local/homes/user", "/usr/lib/custom_home/bob"])
    NondetTest.assert (resolveBoxPath plan "/etc/hosts" = .virtualEtcHosts)
    NondetTest.assert (plan.cwd = "/tmp")
    NondetTest.assert (plan.env = #[("PATH", "/usr/bin:/bin")])
    NondetTest.assert (plan.userMounts.toList.map mountBoxPath = ["/tmp", "/work", "/work/sub"])

/-- `run` returns all exit codes (including `125`, `126`, `127`, `137`, `255`), signals, timeouts, and output-cap outcomes cleanly without magic exit numbers, and bounds `stdout.size + stderr.size ≤ limit`. -/
def test_psandbox_run_outcomesAndOutputCap
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let code ← nondet Int
  let sig ← nondet Int
  let outBytes ← nondet ByteArray
  let errBytes ← nondet ByteArray
  let baseState : MockSandboxState := {}
  let (rExit, sExit) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := none } }).run
      { baseState with scriptedOutput := .ok { outcome := .exited code, stdout := outBytes, stderr := errBytes } }
  NondetTest.assert (rExit = .ok { outcome := .exited code, stdout := outBytes, stderr := errBytes } ∧
    sExit.openPlans = [] ∧ sExit.activeBoxes = [] ∧ sExit.activeForwarders = [])
  let (rSig, _) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := none } }).run
      { baseState with scriptedOutput := .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes } }
  NondetTest.assert (rSig = .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes })
  let (rTout, _) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := none } }).run
      { baseState with scriptedOutput := .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes } }
  NondetTest.assert (rTout = .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes })
  let (rNoLim, _) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := none } }).run
      { baseState with scriptedOutput := .ok { outcome := .outputLimitExceeded, stdout := outBytes, stderr := errBytes } }
  match rNoLim with
  | .ok res => NondetTest.assert (res.outcome ≠ .outputLimitExceeded)
  | .error e => NondetTest.assert (e.message ≠ "")
  let cap ← nondet Nat
  let (rCap, _) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := some cap } }).run
      { baseState with scriptedOutput := .ok { outcome := .exited 0, stdout := outBytes, stderr := errBytes } }
  match rCap with
  | .error _ => NondetTest.assert False
  | .ok res =>
    NondetTest.assert (res.stdout.size + res.stderr.size ≤ cap)
    if outBytes.size + errBytes.size > cap then
      NondetTest.assert (res.outcome = .outputLimitExceeded)
    else
      NondetTest.assert (res.outcome = .exited 0 ∧ res.stdout = outBytes ∧ res.stderr = errBytes)

/-- `run` forwards `spec.stdin` and `spec.limits.timeoutMs` verbatim to `readBoxOutput` without dropping or zeroing either parameter. -/
def test_psandbox_run_forwardsStdinAndTimeoutMs
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  let stdinBytes ← nondet ByteArray
  let timeoutMs ← nondet Nat
  assume (timeoutMs > 0)
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧ s₀.pidsCgroupAvailable = true)
  assume (s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
  assume (s₀.scriptedOutput.isOk = true)
  let spec : BoxSpec :=
    { program := "/bin/cat"
      stdin := stdinBytes
      limits := { timeoutMs := timeoutMs } }
  let (res, s₁) := (api.run spec).run s₀
  NondetTest.assert (res.isOk = true ∧
    s₁.lastReadStdin = some stdinBytes ∧
    s₁.lastReadTimeoutMs = some timeoutMs ∧
    s₁.openPlans = s₀.openPlans ∧
    s₁.activeBoxes = s₀.activeBoxes ∧
    s₁.activeForwarders = s₀.activeForwarders)

/-- `run` brackets `(boxPort, hostPort)` forwarders when `portForwards` is non-empty, skips starting forwarders when empty, and never runs the guest if forwarder startup fails. -/
def test_psandbox_run_portForwarderBracket
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧ s₀.pidsCgroupAvailable = true)
  assume (s₀.failSpawnWith = none)
  assume (s₀.scriptedOutput.isOk = true)
  let fwds : Array PortForward := #[{ boxPort := 8080, hostPort := 18080 }]
  let specFwd : BoxSpec := { program := "/bin/true", portForwards := fwds }
  let (rOk, sOk) := (api.run specFwd).run { s₀ with failForwarderStartWith := none }
  NondetTest.assert (rOk.isOk = true ∧
    sOk.lastStartedForwards = some fwds ∧
    sOk.activeForwarders = s₀.activeForwarders ∧
    sOk.activeBoxes = s₀.activeBoxes ∧
    sOk.openPlans = s₀.openPlans)
  let specNoFwd : BoxSpec := { program := "/bin/true", portForwards := #[] }
  let (rNoFwd, sNoFwd) := (api.run specNoFwd).run { s₀ with failForwarderStartWith := none }
  NondetTest.assert (rNoFwd.isOk = true ∧
    sNoFwd.lastStartedForwards = s₀.lastStartedForwards ∧
    sNoFwd.activeForwarders = s₀.activeForwarders)
  let fwdErr : SandboxError := { kind := .ioError, message := "bind failed" }
  let (rFail, sFail) := (api.run specFwd).run { s₀ with failForwarderStartWith := some fwdErr }
  NondetTest.assert ((∃ e, rFail = .error e ∧ e.kind = .ioError ∧ e.message ≠ "") ∧
    sFail.guestExecCalls = s₀.guestExecCalls ∧
    sFail.activeForwarders = s₀.activeForwarders ∧
    sFail.activeBoxes = s₀.activeBoxes ∧
    sFail.openPlans = s₀.openPlans)

/-- Across all normal outcomes and errors, `run` conserves `openPlans`, `activeBoxes`, and `activeForwarders` and executes `killProcessGroup`, `pidfdKill`, and `reapBox` whenever `spawnBox` succeeded. -/
def test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  let spec ← nondet BoxSpec
  let (res, s₁) := (api.run spec).run s₀
  NondetTest.assert (s₁.openPlans = s₀.openPlans ∧
    s₁.activeBoxes = s₀.activeBoxes ∧
    s₁.activeForwarders = s₀.activeForwarders)
  match res with
  | .error err => NondetTest.assert (err.message ≠ "")
  | .ok _ => pure ()
  if s₁.activeBoxes == s₀.activeBoxes && s₁.spawnCalls == s₀.spawnCalls + 1 && s₀.failSpawnWith.isNone then
    NondetTest.assert (s₁.killPgCalls = s₀.killPgCalls + 1 ∧
      s₁.pidfdKillCalls = s₀.pidfdKillCalls + 1 ∧
      s₁.reapCalls = s₀.reapCalls + 1)
  else
    pure ()

/-- Under `MonadFinally` (`ExceptT String (StateM MockSandboxState)`), uncaught cancellation exceptions during `startPortForwarders` or `readBoxOutput` still stop forwarders, kill/pidfdKill/reap the box, and close the sealed plan. -/
def test_psandbox_run_monadFinallyCleansUpOnCancellation
    {runner} [NondetTest runner]
    (mkApiEx : ProcessSandboxBuilder (ExceptT String (StateM MockSandboxState))) : runner Unit := do
  let apiEx := mkApiEx mockRawOpsEx
  let s₀ ← nondet MockSandboxState
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧ s₀.pidsCgroupAvailable = true)
  assume (s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
  let spec : BoxSpec :=
    { program := "/bin/sleep"
      args := #["60"]
      portForwards := #[{ boxPort := 3000, hostPort := 13000 }] }
  let (rReadCancel, sReadCancel) :=
    (apiEx.run spec).run { s₀ with throwOnReadOutput := true, throwOnStartForwarders := false }
  NondetTest.assert (rReadCancel = .error "cancelled-during-read" ∧
    sReadCancel.openPlans = s₀.openPlans ∧
    sReadCancel.activeBoxes = s₀.activeBoxes ∧
    sReadCancel.activeForwarders = s₀.activeForwarders ∧
    sReadCancel.killPgCalls = s₀.killPgCalls + 1 ∧
    sReadCancel.pidfdKillCalls = s₀.pidfdKillCalls + 1 ∧
    sReadCancel.reapCalls = s₀.reapCalls + 1)
  let (rFwdCancel, sFwdCancel) :=
    (apiEx.run spec).run { s₀ with throwOnReadOutput := false, throwOnStartForwarders := true }
  NondetTest.assert (rFwdCancel = .error "cancelled-during-forwarder-start" ∧
    sFwdCancel.guestExecCalls = s₀.guestExecCalls ∧
    sFwdCancel.openPlans = s₀.openPlans ∧
    sFwdCancel.activeBoxes = s₀.activeBoxes ∧
    sFwdCancel.activeForwarders = s₀.activeForwarders ∧
    sFwdCancel.killPgCalls = s₀.killPgCalls + 1 ∧
    sFwdCancel.pidfdKillCalls = s₀.pidfdKillCalls + 1 ∧
    sFwdCancel.reapCalls = s₀.reapCalls + 1)

/-- Concrete 3-category shared-kernel checks covering blocked `socket(AF_UNIX, ...)` vs allowed `socketpair`, `clone3` `ENOSYS` fallback vs `CLONE_NEW*` block, `/tmp` scratch vs `readOnly` vs `readWrite`, and `allowBoxLocalhost` vs `portForwards`. -/
def test_psandbox_model_threeCategorySyscallSemantics
    {runner} [NondetTest runner]
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState :=
      stepGuestSyscall) : runner Unit := do
  let st₀ ← nondet SandboxWorldState
  assume (st₀.box.boxMemoryBytes = 0 ∧ st₀.box.boxProcs = [1])
  let preset : HostRuntimePreset :=
    { systemEntries := #[.readOnlyDir "/usr", .topSymlink "/bin" "usr/bin"]
      etcPaths := #["/etc/passwd"]
      excludedHomePaths := #["/usr/local/homes/dev"] }
  let spec : BoxSpec :=
    { program := "/bin/sh"
      mounts :=
        #[ .readOnly "/host/ro" "/ro"
         , .readWrite "/host/rw" "/rw" ]
      allowBoxLocalhost := true
      portForwards := #[{ boxPort := 8080, hostPort := 18080 }]
      limits :=
        { timeoutMs := 5000
          memoryMaxBytes := some 4096
          pidsMax := some 4
          fileSizeMaxBytes := some 16 } }
  match validateSpecPure spec with
  | .error _ => NondetTest.assert False
  | .ok valid =>
    let plan := compilePlan valid preset
    let payload := "ok".toUTF8
    let bigPayload := String.ofList (List.replicate 32 'x') |>.toUTF8
    NondetTest.assert (stepFn plan st₀ (.adminOp (.unixSocketOrSmcOp "/var/run/docker.sock")) =
      .error .blockedBySeccompOrNamespace)
    NondetTest.assert (stepFn plan st₀ (.anonUnixSocketpair .stream) = .ok st₀)
    NondetTest.assert (stepFn plan st₀ (.anonUnixSocketpair .seqpacket) = .ok st₀)
    NondetTest.assert (stepFn plan st₀ (.anonUnixSocketpair .disallowedOther) =
      .error .blockedBySeccompOrNamespace)
    NondetTest.assert (stepFn plan st₀ .clone3Attempt = .error .clone3FallbackEnosys)
    NondetTest.assert (stepFn plan st₀ (.cloneProc 2 true) = .error .blockedBySeccompOrNamespace)
    NondetTest.assert ((stepFn plan st₀ (.fsRead "/home/u/.ssh/id_rsa")).isOk = false)
    NondetTest.assert ((stepFn plan st₀ (.fsRead "/usr/local/homes/dev/.ssh/id_rsa")).isOk = false)
    NondetTest.assert (stepFn plan st₀ (.fsWrite "/ro/file.txt" payload) = .error .readOnlyFilesystem)
    NondetTest.assert (stepFn plan st₀ (.fsWrite "/rw/big.txt" bigPayload) = .error .fileSizeLimitExceeded)
    NondetTest.assert (stepFn plan st₀ (.fsRead "/") = .ok st₀)
    NondetTest.assert (stepFn plan st₀ (.fsWrite "/" payload) = .error .readOnlyFilesystem)
    NondetTest.assert (stepFn plan st₀ (.fsRead "/etc/hosts") = .ok st₀)
    NondetTest.assert (stepFn plan st₀ (.fsWrite "/etc/hosts" payload) = .error .readOnlyFilesystem)
    NondetTest.assert (stepFn plan st₀ (.fsRead "/usr/local/homes/dev") = .error .unmountedOrMaskedPath)
    match stepFn plan st₀ (.fsWrite "/tmp/scratch.txt" payload) with
    | .error _ => NondetTest.assert False
    | .ok stTmp =>
      NondetTest.assert (stTmp.host = st₀.host ∧
        lookupFsBytes stTmp.box.scratchFs "/tmp/scratch.txt" = some payload)
    match stepFn plan st₀ (.tcpSend true 9090 payload) with
    | .error _ => NondetTest.assert False
    | .ok stLo =>
      NondetTest.assert (stLo.host = st₀.host ∧
        stLo.box.boxLocalPorts = st₀.box.boxLocalPorts ++ [(9090, payload)])
    match stepFn plan st₀ (.tcpSend true 8080 payload) with
    | .error _ => NondetTest.assert False
    | .ok stFwd =>
      NondetTest.assert (stFwd.host.hostPorts = st₀.host.hostPorts ++ [(18080, payload)] ∧
        stFwd.host.hostFs = st₀.host.hostFs ∧
        stFwd.host.hostAdminState = st₀.host.hostAdminState)
    match stepFn plan st₀ (.fsWrite "/rw/out.txt" payload) with
    | .error _ => NondetTest.assert False
    | .ok stRw =>
      NondetTest.assert (lookupHostFile stRw.host "/host/rw/out.txt" = some payload ∧
        stRw.host.hostPorts = st₀.host.hostPorts ∧
        stRw.host.hostAdminState = st₀.host.hostAdminState)

/-- Frozen model specification: `HostState` never changes outside explicit `readWrite` mounts and `portForwards` across arbitrary `List GuestSyscall` traces (`SpecHostUnchangedOutsideGrants`). -/
def test_psandbox_model_hostUnchangedOutsideGrants
    {runner} [NondetTest runner]
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState :=
      stepGuestSyscall) : runner Unit :=
  NondetTest.assert (SpecHostUnchangedOutsideGrantsOn stepFn)

/-- Frozen model specification: whole-box `pids.max` and `memory.max` hold throughout execution and zero box processes survive teardown (`SpecZeroSurvivingBoxProcs`). -/
def test_psandbox_model_zeroSurvivingBoxProcs
    {runner} [NondetTest runner]
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState :=
      stepGuestSyscall)
    (teardownFn : SandboxWorldState → SandboxWorldState := reapAndTeardownBox) : runner Unit :=
  NondetTest.assert (SpecZeroSurvivingBoxProcsOn stepFn teardownFn)

/-- Frozen model specification: `validateSpecPure` and `compilePlan` produce sound empty-root, `$HOME`-masked, clean-env, direct-`cgroup v2` plans (`SpecCompilePlanSound`). -/
def test_psandbox_model_compilePlanSound
    {runner} [NondetTest runner]
    (validateFn : BoxSpec → Except SandboxError ValidBoxSpec := validateSpecPure)
    (compileFn : ValidBoxSpec → HostRuntimePreset → CompiledSandboxPlan := compilePlan) : runner Unit :=
  NondetTest.assert (SpecCompilePlanSoundOn validateFn compileFn)

/-- `api.compileSeccompBpf` emits a structurally valid Linux `seccomp_check_filter` cBPF program (`1..160` instructions, forward in-bounds jumps, aligned low-word `BPF_ABS` offsets `{0, 4, 16 + 8 * i}`, total `{ALLOW, EPERM, ENOSYS}` verdicts), and `api.encodeSeccompBpf` serializes contiguous `8 * n`-byte little-endian `struct sock_filter` records. -/
def test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let arch ← nondet SeccompArch
  let inp ← nondet SeccompData
  let compiled := api.compileSeccompBpf arch
  NondetTest.assert (isValidLinuxSeccompProg compiled = true)
  let verdict := evalBpf compiled inp
  NondetTest.assert (verdict = some 0x7fff0000 ∨ verdict = some 0x00050001 ∨ verdict = some 0x00050026)
  let rawProg ← nondet (Array SockFilter)
  let wire := api.encodeSeccompBpf rawProg
  NondetTest.assert (wire.size = 8 * rawProg.size)
  NondetTest.assert (wire = encodeSeccompBpfModel rawProg)
  let idx ← nondet Nat
  assume (idx < rawProg.size)
  let insn := rawProg[idx]!
  let base := 8 * idx
  NondetTest.assert (
    wire[base]! = UInt8.ofNat (insn.code.toNat % 256) ∧
    wire[base + 1]! = UInt8.ofNat ((insn.code.toNat / 256) % 256) ∧
    wire[base + 2]! = insn.jt ∧
    wire[base + 3]! = insn.jf ∧
    wire[base + 4]! = UInt8.ofNat (insn.k.toNat % 256) ∧
    wire[base + 5]! = UInt8.ofNat ((insn.k.toNat / 256) % 256) ∧
    wire[base + 6]! = UInt8.ofNat ((insn.k.toNat / 65536) % 256) ∧
    wire[base + 7]! = UInt8.ofNat ((insn.k.toNat / 16777216) % 256))

/-- Across every `SeccompArch`, `ValidCompiledPlan`, `SandboxWorldState`, and `SeccompData`, `evalBpf (api.compileSeccompBpf arch) inp` agrees bidirectionally with `Model.stepGuestSyscall` via `decodeSeccompSyscall` (`ENOSYS` iff `.clone3Attempt`, `EPERM` iff `.blockedBySeccompOrNamespace`, and `ALLOW` iff `none | .anonUnixSocketpair (.stream | .seqpacket) | .cloneProc _ false`). -/
def test_seccomp_evalBpf_matchesStepGuestSyscallModel
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let arch ← nondet SeccompArch
  let plan ← nondet CompiledSandboxPlan
  let st ← nondet SandboxWorldState
  let inp ← nondet SeccompData
  assume (isValidCompiledPlan plan = true)
  let verdict := evalBpf (api.compileSeccompBpf arch) inp
  match decodeSeccompSyscall arch inp with
  | none =>
    NondetTest.assert (verdict = some 0x7fff0000)
  | some sc =>
    if verdict == some 0x00050026 then
      NondetTest.assert (sc = .clone3Attempt ∧ stepGuestSyscall plan st sc = .error .clone3FallbackEnosys)
    else if verdict == some 0x00050001 then
      NondetTest.assert (stepGuestSyscall plan st sc = .error .blockedBySeccompOrNamespace)
    else
      NondetTest.assert (verdict = some 0x7fff0000 ∧
        stepGuestSyscall plan st sc ≠ .error .blockedBySeccompOrNamespace ∧
        stepGuestSyscall plan st sc ≠ .error .clone3FallbackEnosys ∧
        (sc = .anonUnixSocketpair .stream ∨
          sc = .anonUnixSocketpair .seqpacket ∨
          ∃ pid, sc = .cloneProc pid false))

/-- Direct non-circular raw `(arch, nr, args)` rule check (classes 1 and 2): mismatched `seccomp_data.arch` on either `x86_64` (`0xc000003e`) or `aarch64` (`0xc00000b7`) and `x86_64` unsigned `nr ≥ 0x40000000` (`__X32_SYSCALL_BIT` / negative `int nr`) always return `SECCOMP_RET_ERRNO | EPERM` (`0x00050001`). -/
def test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let inpBadX ← nondet SeccompData
  assume (inpBadX.arch ≠ 0xc000003e)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .x86_64) inpBadX = some 0x00050001)
  let inpBadA ← nondet SeccompData
  assume (inpBadA.arch ≠ 0xc00000b7)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .aarch64) inpBadA = some 0x00050001)
  let inpX32 ← nondet SeccompData
  assume (inpX32.arch = 0xc000003e ∧ inpX32.nr ≥ 0x40000000)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .x86_64) inpX32 = some 0x00050001)

/-- Direct non-circular raw `(arch, nr, args)` rule check (classes 3 and 4): `clone3` (`435`) returns `SECCOMP_RET_ERRNO | ENOSYS` (`0x00050026`), and `clone` (`56` on `x86_64`, `220` on `aarch64`) returns `EPERM` (`0x00050001`) iff `(args[0].lo32 &&& 0x7e020000) != 0` and `ALLOW` (`0x7fff0000`) otherwise (preserving `0x80` `CSIGNAL` and `SIGCHLD`). -/
def test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let inp ← nondet SeccompData
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 435 } = some 0x00050026)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 435 } = some 0x00050026)
  let expectedClone : UInt32 :=
    if (inp.args.a0.toUInt32 &&& 0x7e020000) != 0 then 0x00050001 else 0x7fff0000
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 56 } = some expectedClone)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 220 } = some expectedClone)

/-- Direct non-circular raw `(arch, nr, args)` rule check (classes 5 and 6): `socket` (`41` on `x86_64`, `198` on `aarch64`) blocks `AF_UNIX` (`1`) and `AF_SMC` (`43`) with `EPERM` and allows all other domains, while `socketpair` (`53` on `x86_64`, `199` on `aarch64`) allows iff `args[0].lo32 == 1 ∧ args[2].lo32 == 0 ∧ (args[1].lo32 &&& 0xfff7f7ff) ∈ {1, 5}` and returns `EPERM` otherwise. -/
def test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let inp ← nondet SeccompData
  let dom := inp.args.a0.toUInt32
  let expectedSock : UInt32 := if dom == 1 || dom == 43 then 0x00050001 else 0x7fff0000
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 41 } = some expectedSock)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 198 } = some expectedSock)
  let baseType := inp.args.a1.toUInt32 &&& 0xfff7f7ff
  let proto := inp.args.a2.toUInt32
  let expectedPair : UInt32 :=
    if dom == 1 && proto == 0 && (baseType == 1 || baseType == 5) then 0x7fff0000 else 0x00050001
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 53 } = some expectedPair)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 199 } = some expectedPair)

/-- Direct non-circular raw `(arch, nr, args)` rule check (class 7): `sendto` (`44` / `206`, `args[3].lo32`), `sendmsg` (`46` / `211`, `args[2].lo32`), and `sendmmsg` (`307` / `269`, `args[3].lo32`) return `EPERM` (`0x00050001`) iff `MSG_FASTOPEN` (`0x20000000`) is set in the exact per-syscall `flags` argument and `ALLOW` (`0x7fff0000`) otherwise. -/
def test_seccomp_rawSendFastopen_exactArgIndices
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let inp ← nondet SeccompData
  let expArg3 : UInt32 :=
    if (inp.args.a3.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000
  let expArg2 : UInt32 :=
    if (inp.args.a2.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 44 } = some expArg3)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 206 } = some expArg3)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 46 } = some expArg2)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 211 } = some expArg2)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 307 } = some expArg3)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 269 } = some expArg3)

/-- Direct non-circular raw `(arch, nr, args)` rule check (classes 8 and 9): all 33 admin/escape syscalls (including `acct` `163`/`89` and `mount_setattr` `442`/`442`, excluding `fsconfig` `431`) return `EPERM` (`0x00050001`) on both `x86_64` and `aarch64`, and every other native in-range syscall returns `ALLOW` (`0x7fff0000`). -/
def test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let rawX86Deny33 : List UInt32 :=
    [ 169, 246, 320, 165, 166, 155, 167, 168, 432, 430, 433, 429, 428, 442
    , 175, 313, 176, 163, 164, 227, 305, 159, 321, 425, 426, 427, 250, 248
    , 249, 298, 323, 272, 308 ]
  let rawAarch64Deny33 : List UInt32 :=
    [ 142, 104, 294, 40, 39, 41, 224, 225, 432, 430, 433, 429, 428, 442
    , 105, 273, 106, 89, 170, 112, 266, 171, 280, 425, 426, 427, 219, 217
    , 218, 241, 282, 97, 268 ]
  NondetTest.assert (rawX86Deny33.length = 33 ∧ allDistinct rawX86Deny33 = true)
  NondetTest.assert (rawAarch64Deny33.length = 33 ∧ allDistinct rawAarch64Deny33 = true)
  let inp ← nondet SeccompData
  NondetTest.assert (rawX86Deny33.all (fun nr =>
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := nr } == some 0x00050001) = true)
  NondetTest.assert (rawAarch64Deny33.all (fun nr =>
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := nr } == some 0x00050001) = true)
  let inpAllowX ← nondet SeccompData
  assume (inpAllowX.arch = 0xc000003e ∧ inpAllowX.nr < 0x40000000 ∧
    !([435, 56, 41, 53, 44, 46, 307] ++ rawX86Deny33).contains inpAllowX.nr)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .x86_64) inpAllowX = some 0x7fff0000)
  let inpAllowA ← nondet SeccompData
  assume (inpAllowA.arch = 0xc00000b7 ∧
    !([435, 220, 198, 199, 206, 211, 269] ++ rawAarch64Deny33).contains inpAllowA.nr)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .aarch64) inpAllowA = some 0x7fff0000)

/-- External trust boundary assumptions for `LeanSwe.ProcessSandbox` grounded end-to-end in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- Empty-root `bwrap --unshare-all --as-pid-1` confinement (`--remount-ro /`) hides unlisted host paths (`/home`, host `cwd`), binds synthetic read-only `/etc/hosts` (`127.0.0.1 localhost\n::1 localhost\n`) via fresh `open("/proc/self/fd/<memfd>", O_RDONLY)` descriptors, and masks existing nested host `$HOME` / `passwd.pw_dir` directories (including through symlinked preset roots) with `--perms 0000 --tmpfs <mask> --remount-ro <mask>` while providing an ephemeral writable `/tmp` `tmpfs` and `cwd = "/tmp"` by default unless overridden by `BoxSpec`. -/
  emptyRootPresetHomeMaskAndDefaultTmp : Prop
  /-- `leanswe_psandbox_host_arch` reports the host's native `AUDIT_ARCH_X86_64` or `AUDIT_ARCH_AARCH64` constant (`0` otherwise), and the bounded C loader in `psandbox_init.c` validates `0 < n <= 160` and `byte_len == 8 * n`, copies the Lean-encoded `sock_filter` slice unchanged into fixed `struct sock_filter buf[160]`, and installs it via arch-correct `seccomp(SECCOMP_SET_MODE_FILTER, 0, &prog)` (with `ENOSYS` `prctl` fallback) after `PR_SET_NO_NEW_PRIVS = 1`. -/
  cSeccompLoaderPassesFilterSliceUnchanged : Prop
  /-- The Linux kernel validates and executes the installed `seccomp` classic BPF filter on `struct seccomp_data` (reading little-endian low 32-bit argument words at byte offset `16 + 8 * i`) and enforces `SECCOMP_RET_ALLOW`, `SECCOMP_RET_ERRNO | EPERM`, and `SECCOMP_RET_ERRNO | ENOSYS` across `fork` and `execve` as modeled by `evalBpf`. -/
  linuxKernelAppliesSeccompCBPFAsDocumented : Prop
  /-- On `x86_64` and `aarch64`, the Linux kernel offers no syscall outside `clone3`, `clone` (`CLONE_NEW*` mask `0x7e020000`), `unshare`, and `setns` that creates or enters a kernel namespace. -/
  linuxKernelOffersNoUnmodeledNamespaceSyscall : Prop
  /-- Landlock ABI v4 (`handled_access_fs` masked strictly to ABI v4 bits without `IOCTL_DEV`, strictly `READ_DIR` on `"/"`, directory bits stripped when `!S_ISDIR`, `EXECUTE` on presets/mounts/`/tmp`) sets `handled_access_net = 0` when `allowBoxLocalhost = true` and `BIND_TCP | CONNECT_TCP` when `false`, while isolated `net` namespace + `SCM_RIGHTS` `poll()` forwarder (`MAX_RELAY_SLOTS = 128`, `16 KiB` ring buffers, `MSG_NOSIGNAL`, independent half-close `SHUT_WR` drain) relays `(boxPort, hostPort)` without exposing other host ports. -/
  landlockV4AndIsolatedNetPortForwarding : Prop
  /-- Direct `/sys/fs/cgroup` per-box sibling cgroup directories (`memory.max`, `memory.swap.max = "0"` ignoring `ENOENT` on swapless kernels, `pids.max = pidsMax + 2` for the 2 wrapper tasks, `cgroup.procs` before `execvp`, never `systemd-run --user --scope`) enforce combined whole-box RAM and process caps across forked children and fail closed to `.unavailable` on preflight or pre-`execvp` setup failure. -/
  directCgroupV2WholeBoxLimitsFailClosed : Prop
  /-- Dedicated `pthread_once` spawner thread (`bwrap --die-with-parent`), `leanswe-psandbox-init` (`PR_SET_CHILD_SUBREAPER` + `PR_SET_PDEATHSIG(SIGKILL)` + `O_CLOEXEC` `status_pipe`/`exec_err_pipe` + `kill(-1, SIGKILL)` + blocking `waitpid(-1, 0)` until `ECHILD`), and host `MonadFinally` (`killProcessGroup` + `pidfdKill` + `cgroup.kill = "1"` + `cgroup.events` `populated 0` `rmdir` + `stopPortForwarders` + `closePlan`) leave zero surviving grandchild processes, cgroup directories, or open FDs across normal exit, signal, timeout, output cap, or error. -/
  subreaperPidfdAndCgroupKillLeaveZeroOrphans : Prop

private def stubRunGeneric {m : Type → Type} [Monad m] [MonadFinally m]
    (raw : RawProcessSandboxOpsM m) (spec : BoxSpec) : m (Except SandboxError SandboxResult) := do
  match validateSpecPure spec with
  | .error e => return .error e
  | .ok valid =>
    let req : PreflightReq :=
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }
    match ← raw.preflight req with
    | .error e =>
      return .error { e with kind := .unavailable, message := if e.message.isEmpty then "unavailable" else e.message }
    | .ok () =>
      match ← raw.discoverHostPreset with
      | .error e =>
        return .error { e with message := if e.message.isEmpty then "preset error" else e.message }
      | .ok preset =>
        let plan := compilePlan valid preset
        match ← raw.sealPlan plan with
        | .error e =>
          return .error { e with message := if e.message.isEmpty then "sealPlan error" else e.message }
        | .ok ph =>
          let (res, _) ← tryFinally' (do
            match ← raw.spawnBox ph with
            | .error e =>
              return .error { e with message := if e.message.isEmpty then "spawnBox error" else e.message }
            | .ok bh =>
              let (boxRes, _) ← tryFinally' (do
                let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
                  if plan.portForwards.isEmpty then
                    pure (Except.ok none)
                  else do
                    match ← raw.startPortForwarders bh plan.portForwards with
                    | .error e =>
                      pure (Except.error { e with message := if e.message.isEmpty then "forwarder error" else e.message })
                    | .ok fh =>
                      pure (Except.ok (some fh))
                match fwdRes with
                | .error e => return .error e
                | .ok fwdOpt =>
                  let (ioRes, _) ← tryFinally'
                    (raw.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                    (fun _ =>
                      match fwdOpt with
                      | some fh => do let _ ← raw.stopPortForwarders fh; pure ()
                      | none => pure ())
                  match ioRes with
                  | .error e =>
                    return .error { e with message := if e.message.isEmpty then "io error" else e.message }
                  | .ok out =>
                    return .ok out
              ) (fun _ => do
                let _ ← raw.killProcessGroup bh
                let _ ← raw.pidfdKill bh
                let _ ← raw.reapBox bh
                pure ())
              return boxRes
          ) (fun _ => do
            let _ ← raw.closePlan ph
            pure ())
          return res

private def stubMkApi {m : Type → Type} [Monad m] [MonadFinally m]
    (raw : RawProcessSandboxOpsM m) : ProcessSandboxApiM m :=
  { validateSpec := validateSpecPure
    compileSeccompBpf := fun _ => #[]
    encodeSeccompBpf := fun _ => ByteArray.empty
    run := stubRunGeneric raw
    isAvailable := do
      match ← raw.preflight { needMemoryCgroup := true, needPidsCgroup := true } with
      | .ok () => return true
      | .error _ => return false }

private def stubApi : ProcessSandboxApi :=
  { validateSpec := validateSpecPure
    compileSeccompBpf := fun _ => #[]
    encodeSeccompBpf := fun _ => ByteArray.empty
    run := fun _ => pure (.error { kind := .unavailable, message := "stub" })
    isAvailable := pure false }

private def validAcceptStub (s : BoxSpec) : ValidBoxSpec :=
  { program := s.program
    args := s.args
    cwd := s.cwd.getD "/tmp"
    stdin := s.stdin
    mounts := s.mounts
    allowBoxLocalhost := s.allowBoxLocalhost
    portForwards := s.portForwards
    env := s.env
    limits := s.limits }

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h { program := "" } rfl
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsInvalidCwd
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h { program := "sh", cwd := some "relative/dir" } "relative/dir" rfl (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsInvalidMountPaths
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h "../escape" (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsDuplicateBoxPath
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h (.scratch "/work") (.scratch "/work/") "/work" rfl rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h "/usr/bin" ["usr", "bin"] rfl rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h 8080 (by decide)
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_limitsRules
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  simp [Core.AllPass, test_psandbox_validateSpec_limitsRules, Bind.bind, assert] at h

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsInvalidEnv
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h { program := "sh", env := #[("BAD=KEY", "1")] } 0 (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_defaultsOverridesAndIdempotence
    { stubApi with
      validateSpec := fun s =>
        match validateSpecPure s with
        | .error e => .error e
        | .ok v => .ok { v with cwd := "/" } }) := by
  intro h
  have h0 := h "FOO" "1" "2" (by decide) (by decide)
  have hEval :
      validateSpecPure
        { program := "python3"
          args := #["-c", "pass"]
          cwd := none
          mounts := #[.readOnly "/work/src" "/workspace/"]
          env := #[("FOO", "1"), ("FOO", "2")] } =
      .ok
        { program := "python3"
          args := #["-c", "pass"]
          cwd := "/tmp"
          stdin := ByteArray.empty
          mounts := #[.scratch "/tmp", .readOnly "/work/src" "/workspace"]
          allowBoxLocalhost := false
          portForwards := #[]
          env := #[("PATH", "/usr/bin:/bin"), ("FOO", "2")]
          limits := {} } := rfl
  dsimp [test_psandbox_validateSpec_defaultsOverridesAndIdempotence] at h0
  rw [hEval] at h0
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_invalidSpec_hasZeroSideEffects
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s => (.error { kind := .invalidInput, message := "leaked" }, { s with spawnCalls := s.spawnCalls + 1 }) })) := by
  intro h
  have h0 := h {} { program := "" }
  simp [stubMkApi, validateSpecPure, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandbox_isAvailable_and_failClosedUnavailable
    (fun raw => { stubMkApi raw with isAvailable := pure true })) := by
  intro h
  have h0 := h { hostBaseAvailable := false }
  simp [Bind.bind, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s =>
          (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty },
            { s with lastSealedPlan := some { program := "env", emptyRoot := false } }) })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  simp [Bind.bind, isValidCompiledPlan, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_outcomesAndOutputCap
    (fun raw =>
      { stubMkApi raw with
        run := fun _ => pure (.error { kind := .unavailable, message := "hijacked exit 125" }) })) := by
  intro h
  have h0 := h 125 9 ByteArray.empty ByteArray.empty
  simp [Bind.bind, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_portForwarderBracket
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s =>
          (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, s) })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl⟩ rfl rfl
  simp [Bind.bind, StateT.run, Except.isOk, Except.toBool, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s =>
          (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty },
            { s with openPlans := 99 :: s.openPlans }) })) := by
  intro h
  have h0 := h {} { program := "/bin/true" }
  simp [Bind.bind, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_monadFinallyCleansUpOnCancellation
    (fun raw =>
      { validateSpec := validateSpecPure
        compileSeccompBpf := fun _ => #[]
        encodeSeccompBpf := fun _ => ByteArray.empty
        isAvailable := pure true
        run := fun spec => do
          match validateSpecPure spec with
          | .error e => return .error e
          | .ok valid =>
            let preset ← raw.discoverHostPreset
            match preset with
            | .error e => return .error e
            | .ok pr =>
              let plan := compilePlan valid pr
              match ← raw.sealPlan plan with
              | .error e => return .error e
              | .ok ph =>
                match ← raw.spawnBox ph with
                | .error e =>
                  let _ ← raw.closePlan ph
                  return .error e
                | .ok bh =>
                  let r ← raw.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes
                  let _ ← raw.killProcessGroup bh
                  let _ ← raw.pidfdKill bh
                  let _ ← raw.reapBox bh
                  let _ ← raw.closePlan ph
                  return r })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  dsimp [test_psandbox_run_monadFinallyCleansUpOnCancellation, mockRawOpsEx, mockRawOps,
    liftMockState, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd,
    Bind.bind, Pure.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h0
  exact absurd h0.1.2.1 (by decide)

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics
    (fun _ st _ => .ok st)) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, validateSpecPure,
    normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux, hasNulChar,
    validateMountsList, validateAndNormalizeMount, isReservedBoxSegs, reservedSystemTopDirs,
    formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs, defaultSandboxPath,
    defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  cases h0.1

example : ¬ Core.AllPass (test_psandbox_model_hostUnchangedOutsideGrants
    (fun _ st _ => .ok { st with host := { st.host with hostAdminState := { powerGeneration := 1 } } })) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_hostUnchangedOutsideGrants,
    SpecHostUnchangedOutsideGrantsOn, assert] at h
  let validPlan : CompiledSandboxPlan := compilePlan default {}
  have hv : ValidCompiledPlan validPlan := rfl
  have hBlk := (h.1.1 validPlan {} (.adminOp .rebootOrKexec) hv).1 rfl
  simp [Except.isOk, Except.toBool] at hBlk

example : ¬ Core.AllPass (test_psandbox_model_zeroSurvivingBoxProcs
    stepGuestSyscall
    (fun st => st)) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_zeroSurvivingBoxProcs,
    SpecZeroSurvivingBoxProcsOn, assert] at h
  let validPlan : CompiledSandboxPlan := compilePlan default {}
  have hv : ValidCompiledPlan validPlan := rfl
  let stInit : SandboxWorldState := { box := { boxProcs := [1], boxMemoryBytes := 0 } }
  have hSurv := h.1 validPlan stInit [] hv
    (by intro maxP hp; injection hp with hpEq; subst hpEq; decide)
    (by intro maxM hm; injection hm with hmEq; subst hmEq; decide)
  have hProcs := hSurv.2.2.1
  simp [stInit, runGuestTraceWith] at hProcs

example : ¬ Core.AllPass (test_psandbox_model_compilePlanSound
    validateSpecPure
    (fun valid _ => { program := valid.program, emptyRoot := false })) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_compilePlanSound,
    SpecCompilePlanSoundOn, assert] at h
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  have hSound := h.1 { program := "/bin/true" } default {} hVal
  exact absurd hSound.2.1 (by decide)

private def mutantSilentUnsandboxedFallback (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec => do
      match validateSpecPure spec with
      | .error e => return .error e
      | .ok _ =>
        return .ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }

example : ¬ Core.AllPass (test_psandbox_isAvailable_and_failClosedUnavailable
    mutantSilentUnsandboxedFallback) := by
  intro h
  have h0 := h {}
  dsimp [test_psandbox_isAvailable_and_failClosedUnavailable, Bind.bind, nondet, assume, assert] at h0
  have hUnavail := h0.2 { hostBaseAvailable := false } { program := "/bin/true" } rfl (Or.inl rfl)
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  dsimp [mutantSilentUnsandboxedFallback, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure] at hUnavail
  rw [hVal] at hUnavail
  rcases hUnavail.1.1 with ⟨e, he, _⟩
  cases he

private def mutantMagicExit97And98 (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec => do
      match ← stubRunGeneric raw spec with
      | .error e => return .error e
      | .ok res =>
        match res.outcome with
        | .exited 97 => return .error { kind := .unavailable, message := "magic exit 97" }
        | .exited 98 => return .ok { res with outcome := .timedOut }
        | _ => return .ok res }

example : ¬ Core.AllPass (test_psandbox_run_outcomesAndOutputCap mutantMagicExit97And98) := by
  intro h
  have h97 := h 97 9 ByteArray.empty ByteArray.empty
  dsimp [test_psandbox_run_outcomesAndOutputCap, mutantMagicExit97And98, stubRunGeneric,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h97
  cases h97.1.1

example : ¬ Core.AllPass (test_psandbox_run_outcomesAndOutputCap
    (fun raw =>
      { stubMkApi raw with
        run := fun spec => do
          match ← stubRunGeneric raw spec with
          | .error e => return .error e
          | .ok res =>
            if res.outcome == .exited 98 then return .ok { res with outcome := .timedOut }
            else return .ok res })) := by
  intro h
  have h98 := h 98 9 ByteArray.empty ByteArray.empty
  dsimp [test_psandbox_run_outcomesAndOutputCap, stubRunGeneric,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h98
  injection h98.1.1 with hRes
  injection hRes with hOut
  cases hOut

private def mutantRoBindRootStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .fsRead _ => .ok st
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics mutantRoBindRootStep) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, mutantRoBindRootStep,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  have hHome := h0.2.2.2.2.2.2.1
  simp [Except.isOk, Except.toBool] at hHome

private def mutantOmitDefaultTmpCompile (valid : ValidBoxSpec) (preset : HostRuntimePreset) :
    CompiledSandboxPlan :=
  let base := compilePlan valid preset
  { base with userMounts := base.userMounts.filter (fun m => mountBoxPath m != "/tmp") }

example : ¬ Core.AllPass (test_psandbox_model_compilePlanSound
    validateSpecPure mutantOmitDefaultTmpCompile) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_compilePlanSound,
    SpecCompilePlanSoundOn, assert] at h
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  have hSound := h.1 { program := "/bin/true" } default {} hVal
  exact absurd hSound.1 (by unfold ValidCompiledPlan; decide)

private def mutantLeakHostLoopbackStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .tcpSend true port payload =>
    if port == 0 then .error .networkBlocked
    else
      .ok { st with host := { st.host with hostPorts := st.host.hostPorts ++ [(port, payload)] } }
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_hostUnchangedOutsideGrants mutantLeakHostLoopbackStep) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_hostUnchangedOutsideGrants,
    SpecHostUnchangedOutsideGrantsOn, assert] at h
  let basePlan := compilePlan { (default : ValidBoxSpec) with allowBoxLocalhost := true } {}
  have hv : ValidCompiledPlan basePlan := rfl
  have hBoxLocal := (h.1.1 basePlan {} (.tcpSend true 9999 ByteArray.empty) hv).2 rfl
  rcases hBoxLocal with ⟨st', hStep, hHostEq⟩
  dsimp [mutantLeakHostLoopbackStep] at hStep
  injection hStep with hSt
  subst hSt
  have hLen := congrArg (fun hs => hs.hostPorts.length) hHostEq
  simp at hLen

private def mutantInheritHostEnvCompile (valid : ValidBoxSpec) (preset : HostRuntimePreset) :
    CompiledSandboxPlan :=
  let base := compilePlan valid preset
  { base with env := base.env.push ("SECRET_KEY", "leaked_host_token") }

example : ¬ Core.AllPass (test_psandbox_model_compilePlanSound
    validateSpecPure mutantInheritHostEnvCompile) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_compilePlanSound,
    SpecCompilePlanSoundOn, assert] at h
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  have hSound := h.1 { program := "/bin/true" } default {} hVal
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hEnvProp, _⟩ := hSound
  have hEnv := hEnvProp ("SECRET_KEY", "leaked_host_token") (by decide)
  rcases hEnv with hPath | hInSpec
  · injection hPath with hk _; exact absurd hk (by decide)
  · simp at hInSpec

private def mutantPerProcessRlimitMemStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .mmapAnon bytes =>
    if match plan.limits.memoryMaxBytes with
        | some maxM => decide (bytes > maxM)
        | none => false then
      .error .memoryLimitExceeded
    else
      .ok { st with box := { st.box with boxMemoryBytes := st.box.boxMemoryBytes + bytes } }
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_zeroSurvivingBoxProcs
    mutantPerProcessRlimitMemStep reapAndTeardownBox) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_zeroSurvivingBoxProcs,
    SpecZeroSurvivingBoxProcsOn, assert] at h
  let smallValid : ValidBoxSpec :=
    { (default : ValidBoxSpec) with
      limits := { timeoutMs := 1000, memoryMaxBytes := some 1024, pidsMax := some 8 } }
  let smallPlan : CompiledSandboxPlan := compilePlan smallValid {}
  have hv : ValidCompiledPlan smallPlan := rfl
  let stInit : SandboxWorldState := { box := { boxProcs := [1], boxMemoryBytes := 0 } }
  let twoChildTrace : List GuestSyscall := [.cloneProc 2 false, .mmapAnon 1024, .mmapAnon 1024]
  have hRes := h.1 smallPlan stInit twoChildTrace hv
    (by intro maxP hp; injection hp with hpEq; subst hpEq; decide)
    (by intro maxM hm; injection hm with hmEq; subst hmEq; decide)
  have hMem := hRes.2.1 1024 rfl
  exact absurd hMem (by decide)

example : ¬ Core.AllPass (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s =>
          (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty },
            { s with lastSealedPlan := some { (compilePlan default {}) with directCgroupV2Fs := false } }) })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  simp [Bind.bind, isValidCompiledPlan, StateT.run, assert] at h0

private def mutantFallbackOnSpawnUnavailable (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec => do
      match validateSpecPure spec with
      | .error e => return .error e
      | .ok valid =>
        let req : PreflightReq :=
          { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
            needPidsCgroup := valid.limits.pidsMax.isSome }
        match ← raw.preflight req with
        | .error e => return .error { e with kind := .unavailable, message := "unavailable" }
        | .ok () =>
          match ← raw.discoverHostPreset with
          | .error e => return .error e
          | .ok preset =>
            match ← raw.sealPlan (compilePlan valid preset) with
            | .error e => return .error e
            | .ok ph =>
              let sp ← raw.spawnBox ph
              let _ ← raw.closePlan ph
              match sp with
              | .error _ =>
                return .ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
              | .ok bh =>
                let _ ← raw.reapBox bh
                return .ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }

example : ¬ Core.AllPass (test_psandbox_isAvailable_and_failClosedUnavailable
    mutantFallbackOnSpawnUnavailable) := by
  intro h
  have h0 := h {}
  dsimp [test_psandbox_isAvailable_and_failClosedUnavailable, Bind.bind, nondet, assume, assert] at h0
  have hUnavail := h0.2 { hostBaseAvailable := false } { program := "/bin/true" } rfl (Or.inl rfl)
  have hSpawn := hUnavail.2 {} { program := "/bin/true" } rfl ⟨rfl, rfl, rfl⟩
  dsimp [mutantFallbackOnSpawnUnavailable, mockRawOps, allocMockHandleId, isValidSandboxHandleId,
    UInt64.size, validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars,
    splitSlashAux, hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure] at hSpawn
  rcases hSpawn.1.1 with ⟨e, he, _⟩
  cases he

private def mutantDropStdinRun (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec =>
      stubRunGeneric { raw with readBoxOutput := fun bh _ t m => raw.readBoxOutput bh ByteArray.empty t m } spec }

example : ¬ Core.AllPass (test_psandbox_run_forwardsStdinAndTimeoutMs mutantDropStdinRun) := by
  intro h
  have h0 := h {} ("payload".toUTF8) 5000 (by decide) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  dsimp [test_psandbox_run_forwardsStdinAndTimeoutMs, mutantDropStdinRun, stubRunGeneric,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h0
  have hStdin := h0.1.2.1
  injection hStdin with hEq
  have hSz := congrArg ByteArray.size hEq
  exact absurd hSz (by decide)

private def mutantDropTimeoutRun (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec =>
      stubRunGeneric { raw with readBoxOutput := fun bh stdin _ m => raw.readBoxOutput bh stdin 0 m } spec }

example : ¬ Core.AllPass (test_psandbox_run_forwardsStdinAndTimeoutMs mutantDropTimeoutRun) := by
  intro h
  have h0 := h {} ByteArray.empty 5000 (by decide) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  dsimp [test_psandbox_run_forwardsStdinAndTimeoutMs, mutantDropTimeoutRun, stubRunGeneric,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h0
  have hTout := h0.1.2.2.1
  exact absurd hTout (by decide)

private def insertByDepthUnstable {α : Type} (depth : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if depth x < depth y then x :: y :: ys else y :: insertByDepthUnstable depth x ys

private def sortByDepthUnstable {α : Type} (depth : α → Nat) : List α → List α
  | [] => []
  | x :: xs => insertByDepthUnstable depth x (sortByDepthUnstable depth xs)

private def mutantUnstableMountSortRun (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec =>
      stubRunGeneric
        { raw with
          sealPlan := fun plan =>
            raw.sealPlan { plan with userMounts := (sortByDepthUnstable mountBoxDepth plan.userMounts.toList).toArray } }
        spec }

example : ¬ Core.AllPass (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan
    mutantUnstableMountSortRun) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  dsimp [test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan, mutantUnstableMountSortRun,
    stubRunGeneric, mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sanitizePresetSystemEntry,
    allowlistedSystemRootPaths, allowlistedEtcPaths, parseSafePresetTargetSegs,
    expandPresetTopSymlink, isStrictlyNestedInDirs, dedupByFirst, presetEntryBoxPath,
    sortByDepth, insertByDepth, sortByDepthUnstable, insertByDepthUnstable,
    mountBoxDepth, mountBoxPath, tryFinally', MonadFinally.tryFinally',
    Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure, assert] at h0
  have hMounts := h0.2.2.2.2.2.2.2.2.1
  exact absurd hMounts (by decide)

private def mutantSkipSymlinkHomeExpandCompile (valid : ValidBoxSpec) (preset : HostRuntimePreset) :
    CompiledSandboxPlan :=
  let base := compilePlan valid preset
  { base with maskedPresetPaths := #[] }

example : ¬ Core.AllPass (test_psandbox_model_compilePlanSound
    validateSpecPure mutantSkipSymlinkHomeExpandCompile) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_compilePlanSound,
    SpecCompilePlanSoundOn, assert] at h
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  let symPreset : HostRuntimePreset :=
    { systemEntries := #[.readOnlyDir "/usr", .topSymlink "/lib" "usr/lib"]
      excludedHomePaths := #["/lib/custom_home/bob"] }
  have hSound := h.1 { program := "/bin/true" } default symPreset hVal
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hMaskProp⟩ := hSound
  dsimp [mutantSkipSymlinkHomeExpandCompile] at hMaskProp
  have hInSys :
      (.readOnlyDir "/usr" : PresetSystemEntry) ∈
        (compilePlan default symPreset).presetSystemEntries.toList := by
    change (.readOnlyDir "/usr" : PresetSystemEntry) ∈
      [.readOnlyDir "/usr", .topSymlink "/lib" "usr/lib"]
    exact List.Mem.head _
  have hMask := hMaskProp "/lib/custom_home/bob" ["lib", "custom_home", "bob"] (by decide) rfl
    ⟨.readOnlyDir "/usr", hInSys, ["usr"], rfl, by decide, by decide, by decide⟩
  exact absurd hMask.1 (by decide)

private def mutantBlockAnonSocketpairOnlyStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .anonUnixSocketpair _ => .error .blockedBySeccompOrNamespace
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics
    mutantBlockAnonSocketpairOnlyStep) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, mutantBlockAnonSocketpairOnlyStep,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  cases h0.2.1

private def mutantClone3EpermOnlyStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .clone3Attempt => .error .blockedBySeccompOrNamespace
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics
    mutantClone3EpermOnlyStep) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, mutantClone3EpermOnlyStep,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  cases h0.2.2.2.2.1

private def mutantWritableEtcHostsStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .fsWrite "/etc/hosts" _ => .ok st
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics
    mutantWritableEtcHostsStep) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, mutantWritableEtcHostsStep,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  cases h0.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private def encodeSeccompBigEndianMutant (prog : Array SockFilter) : ByteArray :=
  ByteArray.mk (prog.toList.flatMap fun insn =>
    let c := insn.code.toNat
    let k := insn.k.toNat
    [ UInt8.ofNat ((c / 256) % 256)
    , UInt8.ofNat (c % 256)
    , insn.jt
    , insn.jf
    , UInt8.ofNat ((k / 16777216) % 256)
    , UInt8.ofNat ((k / 65536) % 256)
    , UInt8.ofNat ((k / 256) % 256)
    , UInt8.ofNat (k % 256) ]).toArray

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubApi with
      compileSeccompBpf := fun _ => #[]
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have h0 := h .x86_64 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubApi with
      compileSeccompBpf := fun _ => (List.replicate 161 (bpfStmt BPF_RET_K 0x7fff0000)).toArray
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have hValid := (h .x86_64 {}).1
  unfold isValidLinuxSeccompProg SECCOMP_MAX_INSNS at hValid
  have hSz : ((List.replicate 161 (bpfStmt BPF_RET_K 0x7fff0000)).toArray).size = 161 := by simp
  dsimp only [stubApi] at hValid
  rw [hSz] at hValid
  have hGt : decide (161 ≤ 160) = false := rfl
  have hPos : decide (0 < 161) = true := rfl
  rw [hPos, hGt] at hValid
  cases hValid

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_LD_W_ABS 20, bpfStmt BPF_RET_K 0x7fff0000]
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have h0 := h .x86_64 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubApi with
      compileSeccompBpf := fun _ => #[bpfJump BPF_JMP_JEQ_K 0 5 0, bpfStmt BPF_RET_K 0x7fff0000]
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have h0 := h .x86_64 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubApi with
      compileSeccompBpf := fun _ => #[bpfStmt 0x0000 0, bpfStmt BPF_RET_K 0x7fff0000]
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have h0 := h .x86_64 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x7fff0000]
      encodeSeccompBpf := encodeSeccompBigEndianMutant }) := by
  intro h
  have h0 := h .x86_64 {}
  have hWire := h0.2.2 #[bpfStmt BPF_RET_K 0x7fff0000]
  have hIdx := hWire.2.2 0 (by decide)
  exact absurd hIdx.1.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_evalBpf_matchesStepGuestSyscallModel
    { stubApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x7fff0000] }) := by
  intro h
  let validPlan := compilePlan default {}
  have hv : isValidCompiledPlan validPlan = true := rfl
  have h0 := h .x86_64 validPlan {} { arch := 0xc000003e, nr := 169 } hv
  exact h0.1.2.1 rfl

example : ¬ Core.AllPass (test_seccomp_evalBpf_matchesStepGuestSyscallModel
    { stubApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x00050001] }) := by
  intro h
  let validPlan := compilePlan default {}
  have hv : isValidCompiledPlan validPlan = true := rfl
  have h0 := h .x86_64 validPlan {} { arch := 0xc000003e, nr := 435 } hv
  cases h0.1

example : ¬ Core.AllPass (test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit
    { stubApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x7fff0000] }) := by
  intro h
  have h0 := h { arch := 0x40000003, nr := 0 } (by decide)
  exact absurd h0.1 (by decide)

private def mutantX32JsetInsteadOfJgeBpf : SeccompArch → Array SockFilter
  | .x86_64 =>
    #[ bpfStmt BPF_LD_W_ABS 4
     , bpfJump BPF_JMP_JEQ_K 0xc000003e 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JSET_K 0x40000000 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000 ]
  | .aarch64 =>
    #[ bpfStmt BPF_LD_W_ABS 4
     , bpfJump BPF_JMP_JEQ_K 0xc00000b7 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit
    { stubApi with compileSeccompBpf := mutantX32JsetInsteadOfJgeBpf }) := by
  intro h
  have h1 := h { arch := 0x40000003 } (by decide)
  have h2 := h1.2 { arch := 0x40000028 } (by decide)
  have h3 := h2.2 { arch := 0xc000003e, nr := 0x80000000 } ⟨rfl, by decide⟩
  exact absurd h3.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    { stubApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x00050001] }) := by
  intro h
  have h0 := h {}
  exact absurd h0.1 (by decide)

private def mutantCloneMask0x80CollisionBpf : SeccompArch → Array SockFilter
  | arch =>
    let cloneNr : UInt32 := match arch with | .x86_64 => 56 | .aarch64 => 220
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K 435 0 1
     , bpfStmt BPF_RET_K 0x00050026
     , bpfJump BPF_JMP_JEQ_K cloneNr 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfStmt BPF_ALU_AND_K 0x7e020080
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    { stubApi with compileSeccompBpf := mutantCloneMask0x80CollisionBpf }) := by
  intro h
  have h0 := h { args := { a0 := 0x80 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantCloneOmitNewnsBpf : SeccompArch → Array SockFilter
  | arch =>
    let cloneNr : UInt32 := match arch with | .x86_64 => 56 | .aarch64 => 220
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K 435 0 1
     , bpfStmt BPF_RET_K 0x00050026
     , bpfJump BPF_JMP_JEQ_K cloneNr 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfStmt BPF_ALU_AND_K 0x7e000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    { stubApi with compileSeccompBpf := mutantCloneOmitNewnsBpf }) := by
  intro h
  have h0 := h { args := { a0 := 0x00020000 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantCloneHighWordEndianBpf : SeccompArch → Array SockFilter
  | arch =>
    let cloneNr : UInt32 := match arch with | .x86_64 => 56 | .aarch64 => 220
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K 435 0 1
     , bpfStmt BPF_RET_K 0x00050026
     , bpfJump BPF_JMP_JEQ_K cloneNr 0 5
     , bpfStmt BPF_LD_W_ABS 20
     , bpfStmt BPF_ALU_AND_K 0x7e020000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    { stubApi with compileSeccompBpf := mutantCloneHighWordEndianBpf }) := by
  intro h
  have h0 := h { args := { a0 := 0x10000000 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantSocketAllowSmcBpf : SeccompArch → Array SockFilter
  | arch =>
    let sockNr : UInt32 := match arch with | .x86_64 => 41 | .aarch64 => 198
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sockNr 0 4
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x00050001 ]

example : ¬ Core.AllPass (test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair
    { stubApi with compileSeccompBpf := mutantSocketAllowSmcBpf }) := by
  intro h
  have h0 := h { args := { a0 := 43 } }
  exact absurd h0.1 (by decide)

private def mutantSocketpairUnmaskedCloexecBpf : SeccompArch → Array SockFilter
  | arch =>
    let sockNr : UInt32 := match arch with | .x86_64 => 41 | .aarch64 => 198
    let pairNr : UInt32 := match arch with | .x86_64 => 53 | .aarch64 => 199
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sockNr 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 1 0
     , bpfJump BPF_JMP_JEQ_K 43 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfJump BPF_JMP_JEQ_K pairNr 0 9
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 0 5
     , bpfStmt BPF_LD_W_ABS 32
     , bpfJump BPF_JMP_JEQ_K 0 0 3
     , bpfStmt BPF_LD_W_ABS 24
     , bpfJump BPF_JMP_JEQ_K 1 2 0
     , bpfJump BPF_JMP_JEQ_K 5 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair
    { stubApi with compileSeccompBpf := mutantSocketpairUnmaskedCloexecBpf }) := by
  intro h
  have h0 := h { args := { a0 := 1, a1 := 0x00080001, a2 := 0 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantSocketpairIgnoreProtoBpf : SeccompArch → Array SockFilter
  | arch =>
    let sockNr : UInt32 := match arch with | .x86_64 => 41 | .aarch64 => 198
    let pairNr : UInt32 := match arch with | .x86_64 => 53 | .aarch64 => 199
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sockNr 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 1 0
     , bpfJump BPF_JMP_JEQ_K 43 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfJump BPF_JMP_JEQ_K pairNr 0 8
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 0 4
     , bpfStmt BPF_LD_W_ABS 24
     , bpfStmt BPF_ALU_AND_K 0xfff7f7ff
     , bpfJump BPF_JMP_JEQ_K 1 2 0
     , bpfJump BPF_JMP_JEQ_K 5 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair
    { stubApi with compileSeccompBpf := mutantSocketpairIgnoreProtoBpf }) := by
  intro h
  have h0 := h { args := { a0 := 1, a1 := 1, a2 := 6 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantSendtoWrongArg2Bpf : SeccompArch → Array SockFilter
  | arch =>
    let sendtoNr : UInt32 := match arch with | .x86_64 => 44 | .aarch64 => 206
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sendtoNr 0 5
     , bpfStmt BPF_LD_W_ABS 32
     , bpfStmt BPF_ALU_AND_K 0x20000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSendFastopen_exactArgIndices
    { stubApi with compileSeccompBpf := mutantSendtoWrongArg2Bpf }) := by
  intro h
  have h0 := h { args := { a2 := 0, a3 := 0x20000000 } }
  exact absurd h0.1 (by decide)

private def mutantSendmsgWrongArg3Bpf : SeccompArch → Array SockFilter
  | arch =>
    let sendtoNr : UInt32 := match arch with | .x86_64 => 44 | .aarch64 => 206
    let sendmsgNr : UInt32 := match arch with | .x86_64 => 46 | .aarch64 => 211
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sendtoNr 0 5
     , bpfStmt BPF_LD_W_ABS 40
     , bpfStmt BPF_ALU_AND_K 0x20000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfJump BPF_JMP_JEQ_K sendmsgNr 0 5
     , bpfStmt BPF_LD_W_ABS 40
     , bpfStmt BPF_ALU_AND_K 0x20000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSendFastopen_exactArgIndices
    { stubApi with compileSeccompBpf := mutantSendmsgWrongArg3Bpf }) := by
  intro h
  have h0 := h { args := { a2 := 0x20000000, a3 := 0 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantOmitAcctBpf : SeccompArch → Array SockFilter
  | arch =>
    let acctNr : UInt32 := match arch with | .x86_64 => 163 | .aarch64 => 89
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K acctNr 0 1
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x00050001 ]

example : ¬ Core.AllPass (test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls
    { stubApi with compileSeccompBpf := mutantOmitAcctBpf }) := by
  intro h
  have h0 := h.2.2 {}
  exact absurd h0.1 (by decide)

private def mutantOmitMountSetattrBpf : SeccompArch → Array SockFilter
  | _ =>
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K 442 0 1
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x00050001 ]

example : ¬ Core.AllPass (test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls
    { stubApi with compileSeccompBpf := mutantOmitMountSetattrBpf }) := by
  intro h
  have h0 := h.2.2 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls
    { stubApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x00050001] }) := by
  intro h
  have h0 := h.2.2 {}
  have hAllowX := h0.2.2 { arch := 0xc000003e, nr := 431 } ⟨rfl, by decide, by decide⟩
  exact absurd hAllowX.1 (by decide)

end LeanSwe.ProcessSandbox
