import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests
import LeanSwe.ProcessSandbox.Proofs.ApiProofs
import LeanSwe.ProcessSandbox.Proofs.ApiSpawnOkProofs

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model

private theorem byteArray_extract_zero_size (bs : ByteArray) (n : Nat) :
    (bs.extract 0 (Nat.min bs.size n)).size = Nat.min bs.size n := by
  simp [ByteArray.size_extract]

private theorem byteArray_extract_zero_eq_self (bs : ByteArray) (n : Nat) (h : bs.size ≤ n) :
    bs.extract 0 (Nat.min bs.size n) = bs := by
  have hMin : Nat.min bs.size n = bs.size := Nat.min_eq_left h
  rw [hMin]
  simp

/-- Proof of `test_psandbox_run_outcomesAndOutputCap` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_outcomesAndOutputCap :
    AllPass (test_psandbox_run_outcomesAndOutputCap Internal.mkApiM) := by
  intro code sig outBytes errBytes
  let specNone : BoxSpec := { program := "/bin/sh", limits := { maxOutputBytes := none } }
  let validNone : ValidBoxSpec :=
    { program := "/bin/sh"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := { maxOutputBytes := none } }
  have hValNone : validateSpecPure specNone = .ok validNone :=
    validateSpecPure_simple "/bin/sh" ByteArray.empty 60_000 none (by decide) (by decide) (by decide)
  let sExit0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .exited code, stdout := outBytes, stderr := errBytes } }
  have hRunExit := runGeneric_mock_spawn_ok (s₀ := sExit0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  have hEmpNone : ∀ p : HostRuntimePreset, (compilePlan validNone p).portForwards.isEmpty = true := fun _ => rfl
  simp only [hEmpNone, ↓reduceIte] at hRunExit
  have hReadExit :
      mockReadResult sExit0.scriptedOutput none =
        .ok { outcome := .exited code, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadExit] at hRunExit
  let sSig0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes } }
  have hRunSig := runGeneric_mock_spawn_ok (s₀ := sSig0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  simp only [hEmpNone, ↓reduceIte] at hRunSig
  have hReadSig :
      mockReadResult sSig0.scriptedOutput none =
        .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadSig] at hRunSig
  let sTout0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes } }
  have hRunTout := runGeneric_mock_spawn_ok (s₀ := sTout0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  simp only [hEmpNone, ↓reduceIte] at hRunTout
  have hReadTout :
      mockReadResult sTout0.scriptedOutput none =
        .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadTout] at hRunTout
  let sNoLim0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .outputLimitExceeded, stdout := outBytes, stderr := errBytes } }
  have hRunNoLim := runGeneric_mock_spawn_ok (s₀ := sNoLim0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  simp only [hEmpNone, ↓reduceIte] at hRunNoLim
  have hReadNoLim :
      mockReadResult sNoLim0.scriptedOutput none =
        .ok { outcome := .exited 1, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadNoLim] at hRunNoLim
  dsimp only [Internal.mkApiM]
  dsimp only [specNone, sExit0] at hRunExit
  dsimp only [specNone, sSig0] at hRunSig
  dsimp only [specNone, sTout0] at hRunTout
  dsimp only [specNone, sNoLim0] at hRunNoLim
  rw [hRunExit]
  dsimp only [assert]
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [hRunSig]
  dsimp only [assert]
  refine ⟨rfl, ?_⟩
  rw [hRunTout]
  dsimp only [assert]
  refine ⟨rfl, ?_⟩
  rw [hRunNoLim]
  dsimp only [assert]
  refine ⟨by simp, ?_⟩
  intro cap
  dsimp only []
  let specCap : BoxSpec := { program := "/bin/sh", limits := { maxOutputBytes := some cap } }
  let validCap : ValidBoxSpec :=
    { program := "/bin/sh"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := { maxOutputBytes := some cap } }
  have hValCap : validateSpecPure specCap = .ok validCap :=
    validateSpecPure_simple "/bin/sh" ByteArray.empty 60_000 (some cap) (by decide) (by decide) (by decide)
  let sCap0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .exited 0, stdout := outBytes, stderr := errBytes } }
  have hRunCap := runGeneric_mock_spawn_ok (s₀ := sCap0) hValCap rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  have hEmpCap : (compilePlan validCap sCap0.preset).portForwards.isEmpty = true := rfl
  simp only [hEmpCap, ↓reduceIte] at hRunCap
  dsimp only [specCap, sCap0] at hRunCap
  rw [hRunCap]
  dsimp only [validCap, mockReadResult]
  let outCap := outBytes.extract 0 (Nat.min outBytes.size cap)
  let rem := cap - outCap.size
  let errCap := errBytes.extract 0 (Nat.min errBytes.size rem)
  have hOutSz : outCap.size = Nat.min outBytes.size cap := byteArray_extract_zero_size outBytes cap
  have hErrSz : errCap.size = Nat.min errBytes.size rem := byteArray_extract_zero_size errBytes rem
  have h1 : outCap.size ≤ cap := hOutSz ▸ Nat.min_le_right _ _
  have h2 : errCap.size ≤ cap - outCap.size := hErrSz ▸ Nat.min_le_right _ _
  have hBound : outCap.size + errCap.size ≤ cap := by omega
  dsimp only [Bind.bind]
  refine ⟨hBound, ?_⟩
  by_cases hOver : outBytes.size + errBytes.size > cap
  · simp only [hOver, ↓reduceIte]
    exact ⟨trivial, trivial⟩
  · simp only [hOver, ↓reduceIte]
    have hLeOut : outBytes.size ≤ cap := by omega
    have hOutEq : outCap = outBytes := byteArray_extract_zero_eq_self outBytes cap hLeOut
    have hRemEq : rem = cap - outBytes.size := by simp [rem, hOutEq]
    have hLeErr : errBytes.size ≤ rem := by rw [hRemEq]; omega
    have hErrEq : errCap = errBytes := byteArray_extract_zero_eq_self errBytes rem hLeErr
    exact ⟨⟨trivial, hOutEq, hErrEq⟩, trivial⟩

private theorem reach_outcomes_helper (code sig : Int) (outBytes errBytes : ByteArray) (cap : Nat) :
    CanReach (test_psandbox_run_outcomesAndOutputCap Internal.mkApiM) := by
  refine ⟨code, sig, outBytes, errBytes, ?_⟩
  let specNone : BoxSpec := { program := "/bin/sh", limits := { maxOutputBytes := none } }
  let validNone : ValidBoxSpec :=
    { program := "/bin/sh"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := { maxOutputBytes := none } }
  have hValNone : validateSpecPure specNone = .ok validNone :=
    validateSpecPure_simple "/bin/sh" ByteArray.empty 60_000 none (by decide) (by decide) (by decide)
  let sExit0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .exited code, stdout := outBytes, stderr := errBytes } }
  have hRunExit := runGeneric_mock_spawn_ok (s₀ := sExit0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  have hEmpNone : ∀ p : HostRuntimePreset, (compilePlan validNone p).portForwards.isEmpty = true := fun _ => rfl
  simp only [hEmpNone, ↓reduceIte] at hRunExit
  have hReadExit :
      mockReadResult sExit0.scriptedOutput none =
        .ok { outcome := .exited code, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadExit] at hRunExit
  let sSig0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes } }
  have hRunSig := runGeneric_mock_spawn_ok (s₀ := sSig0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  simp only [hEmpNone, ↓reduceIte] at hRunSig
  have hReadSig :
      mockReadResult sSig0.scriptedOutput none =
        .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadSig] at hRunSig
  let sTout0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes } }
  have hRunTout := runGeneric_mock_spawn_ok (s₀ := sTout0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  simp only [hEmpNone, ↓reduceIte] at hRunTout
  have hReadTout :
      mockReadResult sTout0.scriptedOutput none =
        .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadTout] at hRunTout
  let sNoLim0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .outputLimitExceeded, stdout := outBytes, stderr := errBytes } }
  have hRunNoLim := runGeneric_mock_spawn_ok (s₀ := sNoLim0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  simp only [hEmpNone, ↓reduceIte] at hRunNoLim
  have hReadNoLim :
      mockReadResult sNoLim0.scriptedOutput none =
        .ok { outcome := .exited 1, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadNoLim] at hRunNoLim
  dsimp only [Internal.mkApiM]
  dsimp only [specNone, sExit0] at hRunExit
  dsimp only [specNone, sSig0] at hRunSig
  dsimp only [specNone, sTout0] at hRunTout
  dsimp only [specNone, sNoLim0] at hRunNoLim
  rw [hRunExit]
  dsimp only [assert]
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [hRunSig]
  dsimp only [assert]
  refine ⟨rfl, ?_⟩
  rw [hRunTout]
  dsimp only [assert]
  refine ⟨rfl, ?_⟩
  rw [hRunNoLim]
  dsimp only [assert]
  refine ⟨by simp, cap, ?_⟩
  dsimp only []
  let specCap : BoxSpec := { program := "/bin/sh", limits := { maxOutputBytes := some cap } }
  let validCap : ValidBoxSpec :=
    { program := "/bin/sh"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := { maxOutputBytes := some cap } }
  have hValCap : validateSpecPure specCap = .ok validCap :=
    validateSpecPure_simple "/bin/sh" ByteArray.empty 60_000 (some cap) (by decide) (by decide) (by decide)
  let sCap0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .exited 0, stdout := outBytes, stderr := errBytes } }
  have hRunCap := runGeneric_mock_spawn_ok (s₀ := sCap0) hValCap rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
  have hEmpCap : (compilePlan validCap sCap0.preset).portForwards.isEmpty = true := rfl
  simp only [hEmpCap, ↓reduceIte] at hRunCap
  dsimp only [specCap, sCap0] at hRunCap
  rw [hRunCap]
  dsimp only [validCap, mockReadResult]
  let outCap := outBytes.extract 0 (Nat.min outBytes.size cap)
  let rem := cap - outCap.size
  let errCap := errBytes.extract 0 (Nat.min errBytes.size rem)
  have hOutSz : outCap.size = Nat.min outBytes.size cap := byteArray_extract_zero_size outBytes cap
  have hErrSz : errCap.size = Nat.min errBytes.size rem := byteArray_extract_zero_size errBytes rem
  have h1 : outCap.size ≤ cap := hOutSz ▸ Nat.min_le_right _ _
  have h2 : errCap.size ≤ cap - outCap.size := hErrSz ▸ Nat.min_le_right _ _
  have hBound : outCap.size + errCap.size ≤ cap := by omega
  dsimp only [Bind.bind]
  refine ⟨hBound, ?_⟩
  by_cases hOver : outBytes.size + errBytes.size > cap
  · simp only [hOver, ↓reduceIte]
    exact ⟨trivial, trivial⟩
  · simp only [hOver, ↓reduceIte]
    have hLeOut : outBytes.size ≤ cap := by omega
    have hOutEq : outCap = outBytes := byteArray_extract_zero_eq_self outBytes cap hLeOut
    have hRemEq : rem = cap - outBytes.size := by simp [rem, hOutEq]
    have hLeErr : errBytes.size ≤ rem := by rw [hRemEq]; omega
    have hErrEq : errCap = errBytes := byteArray_extract_zero_eq_self errBytes rem hLeErr
    exact ⟨⟨trivial, hOutEq, hErrEq⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_outcomesAndOutputCap`. -/
theorem reach_psandbox_run_outcomesAndOutputCap :
    CanReach (test_psandbox_run_outcomesAndOutputCap Internal.mkApiM) :=
  reach_outcomes_helper 0 9 ByteArray.empty ByteArray.empty 10

/-- Proof of `test_psandbox_run_forwardsStdinAndTimeoutMs` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_forwardsStdinAndTimeoutMs :
    AllPass (test_psandbox_run_forwardsStdinAndTimeoutMs Internal.mkApiM) := by
  intro s₀ stdinBytes timeoutMs hTimeout ⟨hB, hM, hP, hArch⟩ ⟨hSpFail, _⟩ hScriptOk
  rcases Option.isSome_iff_exists.mp hArch with ⟨arch, hArchEq⟩
  let spec : BoxSpec :=
    { program := "/bin/cat"
      stdin := stdinBytes
      limits := { timeoutMs := timeoutMs } }
  let valid : ValidBoxSpec :=
    { program := "/bin/cat"
      args := #[]
      cwd := "/tmp"
      stdin := stdinBytes
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := { timeoutMs := timeoutMs } }
  have hTimeoutNeZero : (timeoutMs == 0) = false := beq_false_of_ne (Nat.ne_of_gt hTimeout)
  have hVal : validateSpecPure spec = .ok valid :=
    validateSpecPure_simple "/bin/cat" stdinBytes timeoutMs (some (16 * 1024 * 1024))
      (by decide) (by decide) hTimeoutNeZero
  have hRun := runGeneric_mock_spawn_ok (s₀ := s₀) hVal hB (fun _ => hM) (fun _ => hP) hArchEq hSpFail
  have hEmpty : (compilePlan valid s₀.preset).portForwards.isEmpty = true := rfl
  simp only [hEmpty, ↓reduceIte] at hRun
  dsimp only [Internal.mkApiM]
  cases hScr : s₀.scriptedOutput with
  | error _ => simp [hScr, Except.isOk, Except.toBool] at hScriptOk
  | ok res =>
    have hReadOk : ∃ r, mockReadResult (.ok res) valid.limits.maxOutputBytes = .ok r := by
      simp only [mockReadResult]
      exact ⟨_, rfl⟩
    rcases hReadOk with ⟨r, hReadEq⟩
    rw [hScr, hReadEq] at hRun
    rw [hRun]
    dsimp only [assert]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

private theorem reach_stdin_helper (s₀ : MockSandboxState) (stdinBytes : ByteArray) (timeoutMs : Nat)
    (hTimeout : timeoutMs > 0)
    (hPre : s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
      s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
    (hFail : s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
    (hScr : s₀.scriptedOutput.isOk = true) :
    CanReach (test_psandbox_run_forwardsStdinAndTimeoutMs Internal.mkApiM) :=
  ⟨s₀, stdinBytes, timeoutMs, hTimeout, hPre, hFail, hScr,
    proof_psandbox_run_forwardsStdinAndTimeoutMs s₀ stdinBytes timeoutMs hTimeout hPre hFail hScr⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_forwardsStdinAndTimeoutMs`. -/
theorem reach_psandbox_run_forwardsStdinAndTimeoutMs :
    CanReach (test_psandbox_run_forwardsStdinAndTimeoutMs Internal.mkApiM) :=
  reach_stdin_helper {} ByteArray.empty 100 (by decide) ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl

/-- Proof of `test_psandbox_run_portForwarderBracket` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_portForwarderBracket :
    AllPass (test_psandbox_run_portForwarderBracket Internal.mkApiM) := by
  intro s₀ ⟨hB, hM, hP, hArch⟩ hSpFail hScriptOk
  rcases Option.isSome_iff_exists.mp hArch with ⟨arch, hArchEq⟩
  let fwds : Array PortForward := #[{ boxPort := 8080, hostPort := 18080 }]
  let specFwd : BoxSpec := { program := "/bin/true", portForwards := fwds }
  let validFwd : ValidBoxSpec :=
    { program := "/bin/true"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := fwds
      env := #[("PATH", "/usr/bin:/bin")]
      limits := {} }
  have hValFwd : validateSpecPure specFwd = .ok validFwd := by
    dsimp only [specFwd, validFwd, fwds, validateSpecPure, hasNulChar, validateMountsList,
      allDistinct, isValidEnvPair, dedupEnvPairs, defaultSandboxPath, defaultSandboxCwd,
      mountBoxPath, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  let specNoFwd : BoxSpec := { program := "/bin/true", portForwards := #[] }
  let validNoFwd : ValidBoxSpec :=
    { program := "/bin/true"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := {} }
  have hValNoFwd : validateSpecPure specNoFwd = .ok validNoFwd :=
    validateSpecPure_simple "/bin/true" ByteArray.empty 60_000 (some (16 * 1024 * 1024))
      (by decide) (by decide) (by decide)
  let sOk0 : MockSandboxState := { s₀ with failForwarderStartWith := none }
  have hArchOk0 : sOk0.hostSeccompArch? = some arch := hArchEq
  have hRunOk := runGeneric_mock_spawn_ok (s₀ := sOk0) hValFwd hB (fun _ => hM) (fun _ => hP) hArchOk0 hSpFail
  have hNotEmp : (compilePlan validFwd sOk0.preset).portForwards.isEmpty = false := rfl
  simp only [hNotEmp, Bool.false_eq_true, ↓reduceIte] at hRunOk
  have hRunNoFwd := runGeneric_mock_spawn_ok (s₀ := sOk0) hValNoFwd hB (fun _ => hM) (fun _ => hP) hArchOk0 hSpFail
  have hEmpNoFwd : (compilePlan validNoFwd sOk0.preset).portForwards.isEmpty = true := rfl
  simp only [hEmpNoFwd, ↓reduceIte] at hRunNoFwd
  let fwdErr : SandboxError := { kind := .ioError, message := "bind failed" }
  let sFail0 : MockSandboxState := { s₀ with failForwarderStartWith := some fwdErr }
  have hArchFail0 : sFail0.hostSeccompArch? = some arch := hArchEq
  have hRunFail := runGeneric_mock_spawn_ok (s₀ := sFail0) hValFwd hB (fun _ => hM) (fun _ => hP) hArchFail0 hSpFail
  have hNotEmpFail : (compilePlan validFwd sFail0.preset).portForwards.isEmpty = false := rfl
  simp only [hNotEmpFail, Bool.false_eq_true, ↓reduceIte] at hRunFail
  cases hScr : s₀.scriptedOutput with
  | error _ => simp [hScr, Except.isOk, Except.toBool] at hScriptOk
  | ok res =>
    have hReadFwd : ∃ r, mockReadResult (.ok res) validFwd.limits.maxOutputBytes = .ok r := by
      simp only [mockReadResult]; exact ⟨_, rfl⟩
    have hReadNoFwd : ∃ r, mockReadResult (.ok res) validNoFwd.limits.maxOutputBytes = .ok r := by
      simp only [mockReadResult]; exact ⟨_, rfl⟩
    rcases hReadFwd with ⟨r1, hR1⟩
    rcases hReadNoFwd with ⟨r2, hR2⟩
    dsimp only [specFwd, sOk0, fwds] at hRunOk
    dsimp only [specNoFwd, sOk0] at hRunNoFwd
    dsimp only [specFwd, sFail0, fwds, fwdErr] at hRunFail
    rw [hScr] at hRunOk hRunNoFwd hRunFail
    rw [hR1] at hRunOk
    rw [hR2] at hRunNoFwd
    dsimp only [Internal.mkApiM]
    rw [hRunOk]
    dsimp only [assert]
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    rw [hRunNoFwd]
    dsimp only [assert]
    refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
    rw [hRunFail]
    dsimp only [assert]
    exact ⟨⟨⟨_, rfl, by decide, by decide⟩, rfl, rfl, rfl, rfl⟩, trivial⟩

private theorem reach_fwd_helper (s₀ : MockSandboxState)
    (hPre : s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
      s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
    (hSpFail : s₀.failSpawnWith = none)
    (hScr : s₀.scriptedOutput.isOk = true) :
    CanReach (test_psandbox_run_portForwarderBracket Internal.mkApiM) :=
  ⟨s₀, hPre, hSpFail, hScr,
    proof_psandbox_run_portForwarderBracket s₀ hPre hSpFail hScr⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_portForwarderBracket`. -/
theorem reach_psandbox_run_portForwarderBracket :
    CanReach (test_psandbox_run_portForwarderBracket Internal.mkApiM) :=
  reach_fwd_helper {} ⟨rfl, rfl, rfl, rfl⟩ rfl rfl

/-- Proof of `test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_conservesResourcesOnAllOutcomesAndErrors :
    AllPass (test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors Internal.mkApiM) := by
  intro s₀ spec
  dsimp only [Internal.mkApiM]
  rcases except_cases (validateSpecPure spec) with ⟨e0, hVal⟩ | ⟨valid, hVal⟩
  · rw [runGeneric_mock_invalid hVal]
    dsimp only [assert]
    refine ⟨⟨rfl, rfl, rfl⟩, ?_, ?_⟩
    · exact ensureNonEmptyMsg_ne_empty "invalid sandbox specification" e0 (by decide)
    · have hNe : (s₀.spawnCalls == s₀.spawnCalls + 1) = false :=
        beq_false_of_ne (by omega)
      simp only [beq_self_eq_true, Bool.true_and, hNe, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        Pure.pure]
  · by_cases hPre :
        !s₀.hostBaseAvailable ∨
        (valid.limits.memoryMaxBytes.isSome && !s₀.memoryCgroupAvailable) ∨
        (valid.limits.pidsMax.isSome && !s₀.pidsCgroupAvailable)
    · obtain ⟨e, hRunEq, hMsg⟩ := runGeneric_mock_preflight_err hVal hPre
      rw [hRunEq]
      dsimp only [assert]
      refine ⟨⟨rfl, rfl, rfl⟩, hMsg, ?_⟩
      have hNe : (s₀.spawnCalls == s₀.spawnCalls + 1) = false :=
        beq_false_of_ne (by omega)
      simp only [beq_self_eq_true, Bool.true_and, hNe, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        Pure.pure]
    · have hHost : s₀.hostBaseAvailable = true := by
        cases hb : s₀.hostBaseAvailable
        · exfalso; exact hPre (Or.inl (by simp [hb]))
        · rfl
      have hMem : valid.limits.memoryMaxBytes.isSome = true → s₀.memoryCgroupAvailable = true := by
        intro hm
        cases hmc : s₀.memoryCgroupAvailable
        · exfalso; exact hPre (Or.inr (Or.inl (by simp [hm, hmc])))
        · rfl
      have hPids : valid.limits.pidsMax.isSome = true → s₀.pidsCgroupAvailable = true := by
        intro hp
        cases hpc : s₀.pidsCgroupAvailable
        · exfalso; exact hPre (Or.inr (Or.inr (by simp [hp, hpc])))
        · rfl
      cases hArch : s₀.hostSeccompArch? with
      | none =>
        have hRun := runGeneric_mock_host_arch_none hVal hHost hMem hPids hArch
        rw [hRun]
        dsimp only [assert]
        refine ⟨⟨rfl, rfl, rfl⟩, by decide, ?_⟩
        have hNe : (s₀.spawnCalls == s₀.spawnCalls + 1) = false :=
          beq_false_of_ne (by omega)
        simp only [beq_self_eq_true, Bool.true_and, hNe, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          Pure.pure]
      | some arch =>
        cases hSpFail : s₀.failSpawnWith with
        | some err =>
          have hRun := runGeneric_mock_spawn_fail hVal hHost hMem hPids hArch hSpFail
          rw [hRun]
          dsimp only [assert]
          refine ⟨⟨rfl, rfl, rfl⟩,
            ensureNonEmptyMsg_ne_empty "failed to spawn sandbox" _ (by decide), ?_⟩
          simp only [Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
            Pure.pure]
        | none =>
          have hRun := runGeneric_mock_spawn_ok hVal hHost hMem hPids hArch hSpFail
          have hCond : (s₀.activeBoxes == s₀.activeBoxes &&
              (s₀.spawnCalls + 1 == s₀.spawnCalls + 1) && (none : Option SandboxError).isNone) = true := by
            simp
          by_cases hEmpty : (compilePlan valid s₀.preset).portForwards.isEmpty = true
          · simp only [hEmpty, ↓reduceIte] at hRun
            rw [hRun]
            dsimp only [assert]
            refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
            cases hRead : mockReadResult s₀.scriptedOutput valid.limits.maxOutputBytes with
            | ok _ =>
              dsimp only [Pure.pure]
              simp only [hCond, ↓reduceIte]
              exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩
            | error _ =>
              dsimp only [assert]
              refine ⟨ensureNonEmptyMsg_ne_empty "sandbox I/O failed" _ (by decide), ?_⟩
              simp only [hCond, ↓reduceIte]
              exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩
          · have hEmptyF : (compilePlan valid s₀.preset).portForwards.isEmpty = false :=
              Bool.eq_false_iff.mpr hEmpty
            simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte] at hRun
            cases hFwdFail : s₀.failForwarderStartWith with
            | some ferr =>
              simp only [hFwdFail] at hRun
              rw [hRun]
              dsimp only [assert]
              refine ⟨⟨rfl, rfl, rfl⟩,
                ensureNonEmptyMsg_ne_empty "failed to start port forwarders" _ (by decide), ?_⟩
              simp only [hCond, ↓reduceIte]
              exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩
            | none =>
              simp only [hFwdFail] at hRun
              rw [hRun]
              dsimp only [assert]
              refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
              cases hRead : mockReadResult s₀.scriptedOutput valid.limits.maxOutputBytes with
              | ok _ =>
                dsimp only [Pure.pure]
                simp only [hCond, ↓reduceIte]
                exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩
              | error _ =>
                dsimp only [assert]
                refine ⟨ensureNonEmptyMsg_ne_empty "sandbox I/O failed" _ (by decide), ?_⟩
                simp only [hCond, ↓reduceIte]
                exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩

private theorem reach_conserves_helper (s₀ : MockSandboxState) (spec : BoxSpec) :
    CanReach (test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors Internal.mkApiM) :=
  ⟨s₀, spec, proof_psandbox_run_conservesResourcesOnAllOutcomesAndErrors s₀ spec⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors`. -/
theorem reach_psandbox_run_conservesResourcesOnAllOutcomesAndErrors :
    CanReach (test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors Internal.mkApiM) :=
  reach_conserves_helper {} { program := "/bin/true" }

end LeanSwe.ProcessSandbox.Proofs
