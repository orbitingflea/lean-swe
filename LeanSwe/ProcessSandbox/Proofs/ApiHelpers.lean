import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests
import LeanSwe.ProcessSandbox.Proofs.SeccompBytesLemma

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model

theorem ensureNonEmptyMsg_ne_empty (fallback : String) (err : SandboxError)
    (hf : fallback ≠ "") : (Internal.ensureNonEmptyMsg fallback err).message ≠ "" := by
  unfold Internal.ensureNonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    rw [hem] at h
    contradiction

/-- `Internal.ensureNonEmptyMsg` preserves the original `SandboxErrorKind`. -/
theorem ensureNonEmptyMsg_kind (fallback : String) (err : SandboxError) :
    (Internal.ensureNonEmptyMsg fallback err).kind = err.kind := by
  unfold Internal.ensureNonEmptyMsg
  split <;> rfl

/-- Allocation always yields a valid sandbox handle identifier. -/
theorem isValidSandboxHandleId_alloc (s : MockSandboxState) :
    isValidSandboxHandleId (allocMockHandleId s) = true := by
  unfold allocMockHandleId
  split
  · assumption
  · decide

/-- Case split on an `Except` value yielding an explicit `.error` or `.ok` witness. -/
theorem except_cases {ε α : Type} (x : Except ε α) :
    (∃ e, x = .error e) ∨ (∃ a, x = .ok a) := by
  cases x
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

private theorem validateAndNormalizeMount_error_kind {m : SandboxMount} {e : SandboxError}
    (h : validateAndNormalizeMount m = .error e) : e.kind = .invalidInput := by
  cases m with
  | readOnly hp bp =>
    dsimp only [validateAndNormalizeMount] at h
    cases h1 : parseCleanAbsSegs hp with
    | none => rw [h1] at h; cases h; rfl
    | some hSegs =>
      cases h2 : parseCleanAbsSegs bp with
      | none => rw [h1, h2] at h; cases h; rfl
      | some bSegs =>
        rw [h1, h2] at h
        dsimp only at h
        cases hres : isReservedBoxSegs bSegs
        · simp only [hres, Bool.false_eq_true, ↓reduceIte] at h; cases h
        · simp only [hres] at h; cases h; rfl
  | readWrite hp bp =>
    dsimp only [validateAndNormalizeMount] at h
    cases h1 : parseCleanAbsSegs hp with
    | none => rw [h1] at h; cases h; rfl
    | some hSegs =>
      cases h2 : parseCleanAbsSegs bp with
      | none => rw [h1, h2] at h; cases h; rfl
      | some bSegs =>
        rw [h1, h2] at h
        dsimp only at h
        cases hres : isReservedBoxSegs bSegs
        · simp only [hres, Bool.false_eq_true, ↓reduceIte] at h; cases h
        · simp only [hres] at h; cases h; rfl
  | scratch bp =>
    dsimp only [validateAndNormalizeMount] at h
    cases h1 : parseCleanAbsSegs bp with
    | none => rw [h1] at h; cases h; rfl
    | some bSegs =>
      rw [h1] at h
      dsimp only at h
      cases hres : isReservedBoxSegs bSegs
      · simp only [hres, Bool.false_eq_true, ↓reduceIte] at h; cases h
      · simp only [hres] at h; cases h; rfl

private theorem validateMountsList_error_kind {ms : List SandboxMount} {e : SandboxError}
    (h : validateMountsList ms = .error e) : e.kind = .invalidInput := by
  induction ms with
  | nil => simp [validateMountsList] at h
  | cons m rest ih =>
    unfold validateMountsList at h
    cases hm : validateAndNormalizeMount m with
    | error em =>
      rw [hm] at h
      cases h
      exact validateAndNormalizeMount_error_kind hm
    | ok normM =>
      rw [hm] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases hr : validateMountsList rest with
      | error er =>
        rw [hr] at h
        cases h
        exact ih hr
      | ok normRest =>
        rw [hr] at h
        cases h

private def validateSpecTail (spec : BoxSpec) (normCwd : String) (normMounts : List SandboxMount) :
    Except SandboxError ValidBoxSpec :=
  if !allDistinct (normMounts.map mountBoxPath) then
    .error { kind := .invalidInput, message := "duplicate mount boxPath in BoxSpec" }
  else if spec.portForwards.toList.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0) then
    .error { kind := .invalidInput, message := "portForwards ports must be in 1..65535" }
  else if !allDistinct (spec.portForwards.toList.map (·.boxPort)) then
    .error { kind := .invalidInput, message := "duplicate boxPort in portForwards" }
  else if !spec.env.toList.all isValidEnvPair then
    .error { kind := .invalidInput, message := "invalid environment variable entry" }
  else if spec.limits.timeoutMs == 0 then
    .error { kind := .invalidInput, message := "limits.timeoutMs must be greater than zero" }
  else if spec.limits.memoryMaxBytes == some 0 then
    .error { kind := .invalidInput, message := "limits.memoryMaxBytes must be greater than zero when set" }
  else if spec.limits.pidsMax == some 0 then
    .error { kind := .invalidInput, message := "limits.pidsMax must be greater than zero when set" }
  else
    let mountsWithDefaultTmp :=
      if normMounts.any (fun m => mountBoxPath m == "/tmp") then normMounts
      else .scratch "/tmp" :: normMounts
    let deduped := dedupEnvPairs spec.env.toList
    let cleanEnv :=
      if deduped.any (fun kv => kv.1 == "PATH") then deduped
      else ("PATH", defaultSandboxPath) :: deduped
    .ok
      { program := spec.program
        args := spec.args
        cwd := normCwd
        stdin := spec.stdin
        mounts := mountsWithDefaultTmp.toArray
        allowBoxLocalhost := spec.allowBoxLocalhost
        portForwards := spec.portForwards
        env := cleanEnv.toArray
        limits := spec.limits }

private theorem validateSpecTail_error_kind {spec : BoxSpec} {normCwd : String}
    {normMounts : List SandboxMount} {e : SandboxError}
    (h : validateSpecTail spec normCwd normMounts = .error e) : e.kind = .invalidInput := by
  unfold validateSpecTail at h
  cases h1 : !allDistinct (normMounts.map mountBoxPath)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    cases h2 : spec.portForwards.toList.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0)
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      cases h3 : !allDistinct (spec.portForwards.toList.map (·.boxPort))
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        cases h4 : !spec.env.toList.all isValidEnvPair
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
          cases h5 : spec.limits.timeoutMs == 0
          · simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
            cases h6 : spec.limits.memoryMaxBytes == some 0
            · simp only [h6, Bool.false_eq_true, ↓reduceIte] at h
              cases h7 : spec.limits.pidsMax == some 0
              · simp only [h7, Bool.false_eq_true, ↓reduceIte] at h; cases h
              · simp only [h7, ↓reduceIte] at h; cases h; rfl
            · simp only [h6, ↓reduceIte] at h; cases h; rfl
          · simp only [h5, ↓reduceIte] at h; cases h; rfl
        · simp only [h4, ↓reduceIte] at h; cases h; rfl
      · simp only [h3, ↓reduceIte] at h; cases h; rfl
    · simp only [h2, ↓reduceIte] at h; cases h; rfl
  · simp only [h1, ↓reduceIte] at h; cases h; rfl

private theorem validateSpecTail_limits {spec : BoxSpec} {normCwd : String}
    {normMounts : List SandboxMount} {valid : ValidBoxSpec}
    (h : validateSpecTail spec normCwd normMounts = .ok valid) : valid.limits = spec.limits := by
  unfold validateSpecTail at h
  cases h1 : !allDistinct (normMounts.map mountBoxPath)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    cases h2 : spec.portForwards.toList.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0)
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      cases h3 : !allDistinct (spec.portForwards.toList.map (·.boxPort))
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        cases h4 : !spec.env.toList.all isValidEnvPair
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
          cases h5 : spec.limits.timeoutMs == 0
          · simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
            cases h6 : spec.limits.memoryMaxBytes == some 0
            · simp only [h6, Bool.false_eq_true, ↓reduceIte] at h
              cases h7 : spec.limits.pidsMax == some 0
              · simp only [h7, Bool.false_eq_true, ↓reduceIte] at h
                cases h; rfl
              · simp only [h7, ↓reduceIte] at h; cases h
            · simp only [h6, ↓reduceIte] at h; cases h
          · simp only [h5, ↓reduceIte] at h; cases h
        · simp only [h4, ↓reduceIte] at h; cases h
      · simp only [h3, ↓reduceIte] at h; cases h
    · simp only [h2, ↓reduceIte] at h; cases h
  · simp only [h1, ↓reduceIte] at h; cases h

/-- `validateSpecPure` errors always have `.invalidInput` kind. -/
theorem validateSpecPure_error_kind {spec : BoxSpec} {e : SandboxError}
    (h : validateSpecPure spec = .error e) : e.kind = .invalidInput := by
  unfold validateSpecPure at h
  cases h1 : spec.program.isEmpty
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    cases h2 : hasNulChar spec.program.toList
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      cases h3 : spec.args.toList.any (fun a => hasNulChar a.toList)
      · simp only [h3, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at h
        cases hcwd : spec.cwd with
        | none =>
          rw [hcwd] at h
          dsimp only at h
          cases hm : validateMountsList spec.mounts.toList with
          | error em =>
            rw [hm] at h; cases h; exact validateMountsList_error_kind hm
          | ok normMounts =>
            rw [hm] at h
            exact validateSpecTail_error_kind h
        | some d =>
          rw [hcwd] at h
          dsimp only at h
          cases hnorm : normalizeCleanAbsPath d with
          | none => rw [hnorm] at h; cases h; rfl
          | some cleanD =>
            rw [hnorm] at h
            dsimp only at h
            cases hm : validateMountsList spec.mounts.toList with
            | error em =>
              rw [hm] at h; cases h; exact validateMountsList_error_kind hm
            | ok normMounts =>
              rw [hm] at h
              exact validateSpecTail_error_kind h
      · simp only [h3, ↓reduceIte] at h; cases h; rfl
    · simp only [h2, ↓reduceIte] at h; cases h; rfl
  · simp only [h1, ↓reduceIte] at h; cases h; rfl

/-- `validateSpecPure` preserves normalized timeout and maxOutputBytes limits. -/
theorem validateSpecPure_limits {spec : BoxSpec} {valid : ValidBoxSpec}
    (h : validateSpecPure spec = .ok valid) : valid.limits = spec.limits := by
  unfold validateSpecPure at h
  cases h1 : spec.program.isEmpty
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    cases h2 : hasNulChar spec.program.toList
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      cases h3 : spec.args.toList.any (fun a => hasNulChar a.toList)
      · simp only [h3, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at h
        cases hcwd : spec.cwd with
        | none =>
          rw [hcwd] at h
          dsimp only at h
          cases hm : validateMountsList spec.mounts.toList with
          | error _ => rw [hm] at h; cases h
          | ok normMounts =>
            rw [hm] at h
            exact validateSpecTail_limits h
        | some d =>
          rw [hcwd] at h
          dsimp only at h
          cases hnorm : normalizeCleanAbsPath d with
          | none => rw [hnorm] at h; cases h
          | some cleanD =>
            rw [hnorm] at h
            dsimp only at h
            cases hm : validateMountsList spec.mounts.toList with
            | error _ => rw [hm] at h; cases h
            | ok normMounts =>
              rw [hm] at h
              exact validateSpecTail_limits h
      · simp only [h3, ↓reduceIte] at h; cases h
    · simp only [h2, ↓reduceIte] at h; cases h
  · simp only [h1, ↓reduceIte] at h; cases h

/-- Validation result for a minimal default-mount sandbox specification. -/
theorem validateSpecPure_simple (prog : String) (stdin : ByteArray)
    (timeoutMs : Nat) (maxOut? : Option Nat)
    (hProgNe : prog.isEmpty = false) (hProgNul : hasNulChar prog.toList = false)
    (hTout : (timeoutMs == 0) = false) :
    validateSpecPure
      { program := prog
        stdin := stdin
        limits := { timeoutMs := timeoutMs, maxOutputBytes := maxOut? } } =
      .ok
        { program := prog
          args := #[]
          cwd := "/tmp"
          stdin := stdin
          mounts := #[.scratch "/tmp"]
          allowBoxLocalhost := false
          portForwards := #[]
          env := #[("PATH", "/usr/bin:/bin")]
          limits := { timeoutMs := timeoutMs, maxOutputBytes := maxOut? } } := by
  unfold validateSpecPure
  simp only [hProgNe, hProgNul, hTout, Bool.false_eq_true, ↓reduceIte, List.any_nil,
    validateMountsList, dedupEnvPairs, defaultSandboxPath, defaultSandboxCwd,
    Bind.bind, Except.bind]
  rfl

/-- Unfold `StateM` bind application to state-passing evaluation. -/
theorem stateM_bind_apply {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f) s = (f (x s).1) (x s).2 := rfl

/-- Equational lemma for `StateT.bind` at state `s`. -/
theorem stateM_bind_eq {σ α β : Type} {x : StateM σ α} {f : α → StateM σ β} {s : σ}
    {a : α} {s₁ : σ} (hx : x s = (a, s₁)) :
    (x >>= f) s = f a s₁ := by
  rw [stateM_bind_apply, hx]

/-- Unfold `StateM` `tryFinally'` application to state-passing evaluation. -/
theorem stateM_tryFinally'_apply {σ α β : Type} (x : StateM σ α)
    (f : Option α → StateM σ β) (s : σ) :
    (tryFinally' x f) s =
      let (a, s₁) := x s
      let (b, s₂) := (f (some a)) s₁
      ((a, b), s₂) := rfl

/-- Equational lemma for `MonadFinally.tryFinally'` in `StateM`. -/
theorem stateM_tryFinally'_eq {σ α β : Type} {x : StateM σ α}
    {f : Option α → StateM σ β} {s : σ} {a : α} {b : β} {s₁ s₂ : σ}
    (hx : x s = (a, s₁)) (hf : (f (some a)) s₁ = (b, s₂)) :
    (tryFinally' x f) s = ((a, b), s₂) := by
  rw [stateM_tryFinally'_apply, hx]
  dsimp only
  rw [hf]

/-- Pure reference model of `mockRawOps.readBoxOutput` truncation and error formatting. -/
def mockReadResult (scripted : Except SandboxError SandboxResult)
    (maxOut? : Option Nat) : Except SandboxError SandboxResult :=
  match scripted with
  | .error err =>
    .error { err with message := if err.message.isEmpty then "guest exec failed" else err.message }
  | .ok res =>
    match maxOut? with
    | none =>
      let cleanOutcome :=
        if res.outcome == .outputLimitExceeded then .exited 1 else res.outcome
      .ok { res with outcome := cleanOutcome }
    | some cap =>
      let outCap := res.stdout.extract 0 (Nat.min res.stdout.size cap)
      let rem := cap - outCap.size
      let errCap := res.stderr.extract 0 (Nat.min res.stderr.size rem)
      let cappedOutcome :=
        if res.stdout.size + res.stderr.size > cap then .outputLimitExceeded else res.outcome
      .ok { outcome := cappedOutcome, stdout := outCap, stderr := errCap }

/-- Equational characterization of `mockRawOps.readBoxOutput`. -/
theorem mockRawOps_readBoxOutput_eq (bh : BoxHandle) (stdin : ByteArray)
    (timeoutMs : Nat) (maxOut? : Option Nat) (s : MockSandboxState)
    (hValid : isValidSandboxHandleId bh.handleId = true)
    (hActive : s.activeBoxes.contains bh.handleId = true) :
    (mockRawOps.readBoxOutput bh stdin timeoutMs maxOut?) s =
      (mockReadResult s.scriptedOutput maxOut?,
       { s with
         guestExecCalls := s.guestExecCalls + 1
         lastReadStdin := some stdin
         lastReadTimeoutMs := some timeoutMs }) := by
  dsimp only [mockRawOps]
  have hBad : (!isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId) = false := by
    rw [hValid, hActive]; rfl
  simp only [hBad, Bool.false_eq_true, ↓reduceIte]
  cases s.scriptedOutput with
  | error _ =>
    simp only [mockReadResult]
  | ok _ =>
    cases maxOut? with
    | none =>
      simp only [mockReadResult]
    | some _ =>
      simp only [mockReadResult]

/-- Symbolic result of `Internal.runGeneric mockRawOps` when specification validation fails. -/
theorem runGeneric_mock_invalid {s₀ : MockSandboxState} {spec : BoxSpec}
    {e0 : SandboxError} (hVal : validateSpecPure spec = .error e0) :
    StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
      (.error (Internal.ensureNonEmptyMsg "invalid sandbox specification" e0), s₀) := by
  dsimp only [StateT.run]
  simp only [Internal.runGeneric, hVal, Pure.pure, StateT.pure]

/-- Symbolic result of `Internal.runGeneric mockRawOps` when `preflight` fails. -/
theorem runGeneric_mock_preflight_err {s₀ : MockSandboxState} {spec : BoxSpec}
    {valid : ValidBoxSpec} (hVal : validateSpecPure spec = .ok valid)
    (hFail : !s₀.hostBaseAvailable ∨
      (valid.limits.memoryMaxBytes.isSome && !s₀.memoryCgroupAvailable) ∨
      (valid.limits.pidsMax.isSome && !s₀.pidsCgroupAvailable)) :
    let req : PreflightReq :=
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }
    ∃ e : SandboxError, StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
        (.error { e with kind := .unavailable }, { s₀ with lastPreflightReq := some req }) ∧
      e.message ≠ "" := by
  intro req
  have hPre : ∃ err : SandboxError, (mockRawOps.preflight req) s₀ =
      (.error err, { s₀ with lastPreflightReq := some req }) := by
    dsimp only [mockRawOps]
    by_cases hb : (!s₀.hostBaseAvailable) = true
    · simp only [hb, ↓reduceIte]; exact ⟨_, rfl⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      by_cases hm : (req.needMemoryCgroup && !s₀.memoryCgroupAvailable) = true
      · simp only [hm, ↓reduceIte]; exact ⟨_, rfl⟩
      · simp only [hm, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : (req.needPidsCgroup && !s₀.pidsCgroupAvailable) = true
        · simp only [hp, ↓reduceIte]; exact ⟨_, rfl⟩
        · exfalso
          rcases hFail with h1 | h2 | h3
          · exact hb h1
          · exact hm h2
          · exact hp h3
  rcases hPre with ⟨err, hPreEq⟩
  refine ⟨Internal.ensureNonEmptyMsg "sandbox unavailable" err, ?_,
    ensureNonEmptyMsg_ne_empty "sandbox unavailable" err (by decide)⟩
  dsimp only [StateT.run, Internal.runGeneric]
  rw [hVal]
  dsimp only
  rw [stateM_bind_apply, hPreEq]
  rfl


end LeanSwe.ProcessSandbox.Proofs
