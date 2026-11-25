import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Interface

namespace LeanSwe.ProcessSandbox

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

end LeanSwe.ProcessSandbox
