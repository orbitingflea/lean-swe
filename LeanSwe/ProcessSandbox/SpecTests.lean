import Core.NondetTest
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Interface

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
  /-- Native `SeccompArch` returned by `hostSeccompArch` (`none` simulates an unsupported host architecture). -/
  hostSeccompArch? : Option SeccompArch := some .x86_64
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
  /-- Last encoded `seccomp` BPF byte payload passed to `sealPlan`. -/
  lastSealedSeccompBytes : Option ByteArray := none
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
        "hostSeccompArch? := " ++ repr s.hostSeccompArch?,
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

/-- Decode a raw Linux `AUDIT_ARCH_*` constant (`0xc000003e` or `0xc00000b7`) into `SeccompArch` for mock verification. -/
def mockDecodeHostAuditArch (raw : UInt32) : Except SandboxError SeccompArch :=
  if raw == 0xc000003e then
    .ok .x86_64
  else if raw == 0xc00000b7 then
    .ok .aarch64
  else
    .error { kind := .unavailable, message := "unsupported host architecture for seccomp" }

/-- Check whether `seccompBytes` is a non-empty 8-byte-aligned cBPF filter of at most `SECCOMP_MAX_INSNS` instructions. -/
def isValidMockSeccompBytes (seccompBytes : ByteArray) : Bool :=
  seccompBytes.size != 0 && seccompBytes.size % 8 == 0 &&
    decide (seccompBytes.size ≤ 8 * SECCOMP_MAX_INSNS)

/-- Validate mandatory `CompiledSandboxPlan` and `seccompBytes` invariants and frame `LSWP0002` output for mock verification. -/
def mockEncodePlan (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Except SandboxError ByteArray :=
  if !plan.emptyRoot || !plan.directCgroupV2Fs || !plan.blockUnixSocketAndSmc ||
      !plan.allowAnonUnixSocketpair || !plan.clone3EnosysFallback || !plan.cleanEnv ||
      plan.program.isEmpty then
    .error { kind := .invalidInput, message := "compiled plan failed mandatory sandbox invariant check" }
  else if !isValidMockSeccompBytes seccompBytes then
    .error { kind := .invalidInput, message := "compiled seccomp BPF filter failed size or 8-byte alignment check" }
  else
    let n := seccompBytes.size / 8
    let trailer := ByteArray.mk #[
      UInt8.ofNat (n % 256),
      UInt8.ofNat ((n / 256) % 256),
      UInt8.ofNat ((n / 65536) % 256),
      UInt8.ofNat ((n / 16777216) % 256)]
    .ok ("LSWP0002".toUTF8 ++ trailer ++ seccompBytes)

/-- Allocate a valid 64-bit handle ID from `s.nextHandleId`. -/
def allocMockHandleId (s : MockSandboxState) : Nat :=
  if isValidSandboxHandleId s.nextHandleId then s.nextHandleId else 1

/-- Deterministic `RawProcessSandboxOpsM (StateM MockSandboxState)` test double. -/
def mockRawOps : RawProcessSandboxOpsM (StateM MockSandboxState) :=
  { mapRawError := mockMapRawError
    decodeHostAuditArch := mockDecodeHostAuditArch
    encodePlan := mockEncodePlan
    hostSeccompArch := fun s =>
      match s.hostSeccompArch? with
      | some arch => (.ok arch, s)
      | none =>
        (.error { kind := .unavailable, message := "unsupported host architecture for seccomp" }, s)
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
    sealPlan := fun plan seccompBytes s =>
      if !isValidMockSeccompBytes seccompBytes then
        (.error { kind := .invalidInput, message := "invalid seccomp filter bytes for sealPlan" }, s)
      else
        let id := allocMockHandleId s
        (.ok { handleId := id },
          { s with
            nextHandleId := id + 1
            openPlans := id :: s.openPlans
            lastSealedPlan := some plan
            lastSealedSeccompBytes := some seccompBytes })
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
    decodeHostAuditArch := mockRawOps.decodeHostAuditArch
    encodePlan := mockRawOps.encodePlan
    hostSeccompArch := liftMockState mockRawOps.hostSeccompArch
    preflight := fun req => liftMockState (mockRawOps.preflight req)
    discoverHostPreset := liftMockState mockRawOps.discoverHostPreset
    sealPlan := fun plan seccompBytes => liftMockState (mockRawOps.sealPlan plan seccompBytes)
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
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
    s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
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
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
    s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
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
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
    s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
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
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
    s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
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

/-- `run` queries `raw.hostSeccompArch`, seals `api.encodeSeccompBpf (api.compileSeccompBpf arch)` for both `.x86_64` and `.aarch64` (producing architecture-specific valid cBPF filters matching `auditArchOf arch`), and fails closed with `.unavailable`, zero `spawnCalls`, zero `guestExecCalls`, and conserved resources when `hostSeccompArch` fails. -/
def test_seccomp_run_queriesHostArchAndSealsEncodedFilter
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let arch ← nondet SeccompArch
  let s₀ ← nondet MockSandboxState
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧ s₀.pidsCgroupAvailable = true)
  assume (s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
  assume (s₀.scriptedOutput.isOk = true)
  let sArch : MockSandboxState := { s₀ with hostSeccompArch? := some arch }
  let (resOk, sOk) := (api.run { program := "/bin/true" }).run sArch
  let expectedProg := Seccomp.compileSeccompBpf arch
  let expectedBytes := Seccomp.encodeSeccompBpf expectedProg
  NondetTest.assert (resOk.isOk = true ∧
    isValidLinuxSeccompProg expectedProg = true ∧
    expectedBytes = encodeSeccompBpfModel expectedProg ∧
    evalBpf expectedProg { arch := auditArchOf arch, nr := 0 } = some 0x7fff0000 ∧
    evalBpf expectedProg { arch := 0, nr := 0 } = some 0x00050001 ∧
    sOk.lastSealedSeccompBytes = some expectedBytes ∧
    sOk.openPlans = sArch.openPlans ∧
    sOk.activeBoxes = sArch.activeBoxes ∧
    sOk.activeForwarders = sArch.activeForwarders)
  let sNoArch ← nondet MockSandboxState
  let specFail ← nondet BoxSpec
  assume ((api.validateSpec specFail).isOk = true)
  assume (sNoArch.hostBaseAvailable = true ∧
    sNoArch.memoryCgroupAvailable = true ∧
    sNoArch.pidsCgroupAvailable = true ∧
    sNoArch.hostSeccompArch? = none)
  let (resFail, sFail) := (api.run specFail).run sNoArch
  NondetTest.assert ((∃ e, resFail = .error e ∧ e.kind = .unavailable ∧ e.message ≠ "") ∧
    sFail.spawnCalls = sNoArch.spawnCalls ∧
    sFail.guestExecCalls = sNoArch.guestExecCalls ∧
    sFail.openPlans = sNoArch.openPlans ∧
    sFail.activeBoxes = sNoArch.activeBoxes ∧
    sFail.activeForwarders = sNoArch.activeForwarders)

/-- External trust boundary assumptions for `LeanSwe.ProcessSandbox` grounded end-to-end in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- Empty-root `bwrap --unshare-all --as-pid-1` confinement (`--remount-ro /`) hides unlisted host paths (`/home`, host `cwd`), binds synthetic read-only `/etc/hosts` (`127.0.0.1 localhost\n::1 localhost\n`) via fresh `open("/proc/self/fd/<memfd>", O_RDONLY)` descriptors, and masks existing nested host `$HOME` / `passwd.pw_dir` directories (including through symlinked preset roots) with `--perms 0000 --tmpfs <mask> --remount-ro <mask>` while providing an ephemeral writable `/tmp` `tmpfs` and `cwd = "/tmp"` by default unless overridden by `BoxSpec`. -/
  emptyRootPresetHomeMaskAndDefaultTmp : Prop
  /-- `leanswe_psandbox_host_arch` reports the host's native `AUDIT_ARCH_X86_64` or `AUDIT_ARCH_AARCH64` constant (`0` otherwise), and the bounded Rust loader in `psandbox-init` (`LeanSwe/ProcessSandbox/Init/rust/src/{init_sys,ops}.rs`) validates `0 < n <= 160` and `byte_len == 8 * n`, copies the Lean-encoded `sock_filter` slice unchanged into a fixed 4-byte-aligned `[u32; 320]` buffer (`init_sys::copy_seccomp_aligned`), and installs it via arch-correct `syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, 0, &prog)` (with `ENOSYS` `prctl(PR_SET_SECCOMP, ...)` fallback in `ops::install_seccomp`) after `PR_SET_NO_NEW_PRIVS = 1`. -/
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

end LeanSwe.ProcessSandbox
