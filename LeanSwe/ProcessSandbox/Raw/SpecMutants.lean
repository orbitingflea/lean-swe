import Core.NondetTest
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.ProcessSandbox.Raw`. -/

namespace LeanSwe.ProcessSandbox.Raw

open Core (NondetTest)
open Core.NondetTest

private def mapRawErrStub : SandboxRawError → SandboxError
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

private def decodeArchStub (raw : UInt32) : Except SandboxError SeccompArch :=
  if raw == 0xc000003e then .ok .x86_64
  else if raw == 0xc00000b7 then .ok .aarch64
  else .error { kind := .unavailable, message := "unsupported host arch" }

private def encodePlanStub (_plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Except SandboxError ByteArray :=
  if seccompBytes.size == 0 || seccompBytes.size % 8 != 0 || seccompBytes.size > 8 * SECCOMP_MAX_INSNS then
    .error { kind := .invalidInput, message := "invalid seccomp bytes" }
  else
    let n := seccompBytes.size / 8
    let hdr := "LSWP0002".toUTF8 ++ ByteArray.mk #[
      UInt8.ofNat (n % 256),
      UInt8.ofNat ((n / 256) % 256),
      UInt8.ofNat ((n / 65536) % 256),
      UInt8.ofNat ((n / 16777216) % 256)]
    .ok (hdr ++ seccompBytes)

private def stubRawOps : RawProcessSandboxOps :=
  { mapRawError := mapRawErrStub
    decodeHostAuditArch := decodeArchStub
    encodePlan := encodePlanStub
    hostSeccompArch := pure (.error { kind := .unavailable, message := "stub" })
    preflight := fun _ => pure (.error { kind := .unavailable, message := "stub" })
    discoverHostPreset := pure (.ok {})
    sealPlan := fun _ _ => pure (.error { kind := .unavailable, message := "stub" })
    closePlan := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    spawnBox := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    startPortForwarders := fun _ _ => pure (.error { kind := .invalidInput, message := "closed" })
    stopPortForwarders := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    readBoxOutput := fun _ _ _ _ => pure (.error { kind := .invalidInput, message := "closed" })
    killProcessGroup := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    pidfdKill := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    reapBox := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    activeResourceCounts := pure {} }

private structure RawMockState where
  nextId : Nat := 1
  plans : List Nat := []
  boxes : List Nat := []
  fwds : List (Nat × Nat) := []
  preflightOk : Bool := true
  deriving Repr, BEq, DecidableEq, Inhabited

private def stubStatefulRawOps : RawProcessSandboxOpsM (StateM RawMockState) :=
  { mapRawError := mapRawErrStub
    decodeHostAuditArch := decodeArchStub
    encodePlan := encodePlanStub
    hostSeccompArch := fun s =>
      if s.preflightOk then (.ok .x86_64, s)
      else (.error { kind := .unavailable, message := "unsupported host arch" }, s)
    preflight := fun _ s =>
      if s.preflightOk then (.ok (), s)
      else (.error { kind := .unavailable, message := "unavailable" }, s)
    discoverHostPreset := fun s => (.ok {}, s)
    sealPlan := fun _ _ s =>
      let id := if isValidSandboxHandleId s.nextId then s.nextId else 1
      (.ok { handleId := id }, { s with nextId := id + 1, plans := id :: s.plans })
    closePlan := fun ph s =>
      if !isValidSandboxHandleId ph.handleId || !s.plans.contains ph.handleId then
        (.error { kind := .invalidInput, message := "invalid plan handle" }, s)
      else
        (.ok (), { s with plans := s.plans.erase ph.handleId })
    spawnBox := fun ph s =>
      if !isValidSandboxHandleId ph.handleId || !s.plans.contains ph.handleId then
        (.error { kind := .invalidInput, message := "invalid plan handle" }, s)
      else
        let id := if isValidSandboxHandleId s.nextId then s.nextId else 1
        let bh : BoxHandle := { handleId := id, pid := 100, pgid := 100, pidfd := 4 }
        (.ok bh, { s with nextId := id + 1, boxes := id :: s.boxes })
    startPortForwarders := fun bh _ s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        let id := if isValidSandboxHandleId s.nextId then s.nextId else 1
        (.ok { handleId := id, boxHandleId := bh.handleId },
          { s with nextId := id + 1, fwds := (id, bh.handleId) :: s.fwds })
    stopPortForwarders := fun fh s =>
      if !isValidSandboxHandleId fh.handleId || !s.fwds.any (fun p => p.1 == fh.handleId) then
        (.error { kind := .invalidInput, message := "invalid forwarder handle" }, s)
      else
        (.ok (), { s with fwds := s.fwds.filter (fun p => p.1 != fh.handleId) })
    readBoxOutput := fun bh _ _ _ s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, s)
    killProcessGroup := fun bh s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        (.ok (), s)
    pidfdKill := fun bh s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        (.ok (), s)
    reapBox := fun bh s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        (.ok (), { s with boxes := s.boxes.erase bh.handleId })
    activeResourceCounts := fun s =>
      ({ openPlans := s.plans.length, activeBoxes := s.boxes.length, activeForwarders := s.fwds.length }, s) }

example : ¬ Core.AllPass (test_psandboxRaw_isValidSandboxHandleId_bounds (fun _ => true)) := by
  intro h
  have h0 := h 1
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_isValidSandboxHandleId_bounds (fun id => decide (0 < id))) := by
  intro h
  have h0 := h 1
  simp [Bind.bind, assert, UInt64.size] at h0

example : ¬ Core.AllPass (test_psandboxRaw_mapRawError_returnsNonEmptyMessage
    { stubRawOps with mapRawError := fun _ => { kind := .ioError, message := "" } }) := by
  intro h
  have h0 := h (.userError "")
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_mapRawError_preservesKindAndFields
    { stubRawOps with
      mapRawError := fun
        | .unavailable errno? _ => { kind := .ioError, errnoCode := errno?, message := "wrong kind" }
        | other => mapRawErrStub other }) := by
  intro h
  have h0 := h (.unavailable none "missing landlock")
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_decodeHostAuditArch_exactConstantsAndFailClosed
    { stubRawOps with decodeHostAuditArch := fun _ => .ok .x86_64 }) := by
  intro h
  cases h.2.1

example : ¬ Core.AllPass (test_psandboxRaw_decodeHostAuditArch_exactConstantsAndFailClosed
    { stubRawOps with
      decodeHostAuditArch := fun raw =>
        if raw == 0xc000003e then .ok .x86_64
        else if raw == 0xc00000b7 then .ok .aarch64
        else .error { kind := .ioError, message := "wrong error kind" } }) := by
  intro h
  have h0 := h.2.2 0 ⟨by decide, by decide⟩
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002
    { stubRawOps with
      encodePlan := fun _ seccompBytes => .ok ("LSWP0002".toUTF8 ++ ByteArray.mk #[0, 0, 0, 0] ++ seccompBytes) }) := by
  intro h
  have h0 := h { program := "/bin/true" } ByteArray.empty (Or.inl rfl)
  exact h0.1

example : ¬ Core.AllPass (test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002
    { stubRawOps with
      encodePlan := fun _ seccompBytes =>
        if seccompBytes.size == 0 || seccompBytes.size > 8 * SECCOMP_MAX_INSNS then
          .error { kind := .invalidInput, message := "bad" }
        else
          .ok ("LSWP0002".toUTF8 ++ ByteArray.mk #[1, 0, 0, 0] ++ seccompBytes) }) := by
  intro h
  have h0 := h { program := "/bin/true" } (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7]) (Or.inr (Or.inl (by decide)))
  exact h0.1

private def mutantEncodeSkipMaxCap (_ : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Except SandboxError ByteArray :=
  if seccompBytes.size == 0 || seccompBytes.size % 8 != 0 then
    .error { kind := .invalidInput, message := "bad" }
  else
    .ok ("LSWP0002".toUTF8 ++ ByteArray.mk #[161, 0, 0, 0] ++ seccompBytes)

example : ¬ Core.AllPass (test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002
    { stubRawOps with encodePlan := mutantEncodeSkipMaxCap }) := by
  intro h
  have hStep : ∀ (bs : ByteArray), bs.size = 1288 → False := by
    intro bs hSz
    have hGt : bs.size > 8 * SECCOMP_MAX_INSNS := by rw [hSz]; decide
    have h0 := h { program := "/bin/true" } bs (Or.inr (Or.inr hGt))
    dsimp only [test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002,
      stubRawOps, mutantEncodeSkipMaxCap, Bind.bind, Core.AllPassRun, assume, assert] at h0
    rw [hSz] at h0
    exact h0.1
  exact hStep (ByteArray.mk (Array.replicate 1288 0)) (by simp [ByteArray.size])

private def mutantEncodeWrongMagic (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Except SandboxError ByteArray :=
  match encodePlanStub plan seccompBytes with
  | .error e => .error e
  | .ok _ => .ok ("LSWP0001".toUTF8 ++ ByteArray.mk #[1, 0, 0, 0] ++ seccompBytes)

private def sampleSeccompBytes8 : ByteArray :=
  ByteArray.mk #[6, 0, 0, 0, 0, 0, 0xff, 0x7f]

example : ¬ Core.AllPass (test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002
    { stubRawOps with encodePlan := mutantEncodeWrongMagic }) := by
  intro h
  have hGood := (h { program := "/bin/true" } ByteArray.empty (Or.inl rfl)).2
    sampleSeccompBytes8 ⟨by decide, by decide, by decide⟩
  have hOk : mutantEncodeWrongMagic { program := "/bin/true" } sampleSeccompBytes8 =
      .ok ("LSWP0001".toUTF8 ++ ByteArray.mk #[1, 0, 0, 0] ++ sampleSeccompBytes8) := by
    unfold mutantEncodeWrongMagic encodePlanStub SECCOMP_MAX_INSNS
    have hCond : (sampleSeccompBytes8.size == 0 || sampleSeccompBytes8.size % 8 != 0 ||
        decide (sampleSeccompBytes8.size > 8 * 160)) = false := by decide
    rw [hCond]
    rfl
  dsimp only [stubRawOps, Bind.bind, Pure.pure, Core.AllPassRun, nondet, assert] at hGood
  rw [hOk] at hGood
  have hAny := hGood { program := "/bin/true" } sampleSeccompBytes8
  rw [hOk] at hAny
  exact absurd hAny.1.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002
    { stubRawOps with
      encodePlan := fun _ _ => .error { kind := .invalidInput, message := "always fail" } }) := by
  intro h
  let b8 := ByteArray.mk #[6, 0, 0, 0, 0, 0, 0xff, 0x7f]
  have hGood := (h { program := "/bin/true" } ByteArray.empty (Or.inl rfl)).2 b8 ⟨by decide, by decide, by decide⟩
  exact hGood.1

private def mutantEncodeWrongInsnCount (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Except SandboxError ByteArray :=
  match encodePlanStub plan seccompBytes with
  | .error e => .error e
  | .ok _ => .ok ("LSWP0002".toUTF8 ++ ByteArray.mk #[2, 0, 0, 0] ++ seccompBytes)

example : ¬ Core.AllPass (test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002
    { stubRawOps with encodePlan := mutantEncodeWrongInsnCount }) := by
  intro h
  have hGood := (h { program := "/bin/true" } ByteArray.empty (Or.inl rfl)).2
    sampleSeccompBytes8 ⟨by decide, by decide, by decide⟩
  have hOk : mutantEncodeWrongInsnCount { program := "/bin/true" } sampleSeccompBytes8 =
      .ok ("LSWP0002".toUTF8 ++ ByteArray.mk #[2, 0, 0, 0] ++ sampleSeccompBytes8) := by
    unfold mutantEncodeWrongInsnCount encodePlanStub SECCOMP_MAX_INSNS
    have hCond : (sampleSeccompBytes8.size == 0 || sampleSeccompBytes8.size % 8 != 0 ||
        decide (sampleSeccompBytes8.size > 8 * 160)) = false := by decide
    rw [hCond]
    rfl
  dsimp only [stubRawOps, Bind.bind, Pure.pure, Core.AllPassRun, nondet, assert] at hGood
  rw [hOk] at hGood
  have hAny := hGood { program := "/bin/true" } sampleSeccompBytes8
  rw [hOk] at hAny
  exact absurd hAny.1.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_psandboxRaw_hostSeccompArch_failClosedUnavailable
    { stubStatefulRawOps with
      hostSeccompArch := fun s => (.error { kind := .ioError, message := "wrong error kind" }, s) }) := by
  intro h
  have h0 := h {}
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_preflight_failClosedUnavailable
    { stubStatefulRawOps with
      preflight := fun _ s => (.error { kind := .ioError, message := "not fail-closed kind" }, s) }) := by
  intro h
  have h0 := h {} {}
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_planLifecycle_conservesOpenPlansAndRejectsClosed
    { stubStatefulRawOps with
      closePlan := fun _ s => (.ok (), s) }) := by
  intro h
  have h0 := h {} { program := "/bin/true" } (ByteArray.mk #[6, 0, 0, 0, 0, 0, 0xff, 0x7f])
  simp [Bind.bind, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_boxAndForwarderLifecycle_conservesResources
    { stubStatefulRawOps with
      reapBox := fun bh s =>
        if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
          (.error { kind := .invalidInput, message := "invalid" }, s)
        else
          (.ok (), s) }) := by
  intro h
  have h0 := h {} { program := "/bin/true" } (ByteArray.mk #[6, 0, 0, 0, 0, 0, 0xff, 0x7f])
    #[{ boxPort := 8080, hostPort := 8080 }] (by decide) (by decide)
  simp [Bind.bind, stubStatefulRawOps, isValidSandboxHandleId, UInt64.size, StateT.run, assert] at h0

end LeanSwe.ProcessSandbox.Raw
