import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model

private theorem ensureNonEmptyMsg_ne_empty (fallback : String) (err : SandboxError)
    (hf : fallback ≠ "") : (Internal.ensureNonEmptyMsg fallback err).message ≠ "" := by
  unfold Internal.ensureNonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    rw [hem] at h
    contradiction

private theorem ensureNonEmptyMsg_kind (fallback : String) (err : SandboxError) :
    (Internal.ensureNonEmptyMsg fallback err).kind = err.kind := by
  unfold Internal.ensureNonEmptyMsg
  split <;> rfl

private theorem isValidSandboxHandleId_alloc (s : MockSandboxState) :
    isValidSandboxHandleId (allocMockHandleId s) = true := by
  unfold allocMockHandleId
  split
  · assumption
  · decide

private theorem except_cases {ε α : Type} (x : Except ε α) :
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

private theorem validateSpecPure_error_kind {spec : BoxSpec} {e : SandboxError}
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

private theorem validateSpecPure_limits {spec : BoxSpec} {valid : ValidBoxSpec}
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

private theorem validateSpecPure_simple (prog : String) (stdin : ByteArray)
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

private theorem stateM_bind_apply {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f) s = (f (x s).1) (x s).2 := rfl

private theorem stateM_bind_eq {σ α β : Type} {x : StateM σ α} {f : α → StateM σ β} {s : σ}
    {a : α} {s₁ : σ} (hx : x s = (a, s₁)) :
    (x >>= f) s = f a s₁ := by
  rw [stateM_bind_apply, hx]

private theorem stateM_tryFinally'_apply {σ α β : Type} (x : StateM σ α)
    (f : Option α → StateM σ β) (s : σ) :
    (tryFinally' x f) s =
      let (a, s₁) := x s
      let (b, s₂) := (f (some a)) s₁
      ((a, b), s₂) := rfl

private theorem stateM_tryFinally'_eq {σ α β : Type} {x : StateM σ α}
    {f : Option α → StateM σ β} {s : σ} {a : α} {b : β} {s₁ s₂ : σ}
    (hx : x s = (a, s₁)) (hf : (f (some a)) s₁ = (b, s₂)) :
    (tryFinally' x f) s = ((a, b), s₂) := by
  rw [stateM_tryFinally'_apply, hx]
  dsimp only
  rw [hf]

private theorem exceptT_stateM_bind_ok {ε σ α β : Type}
    (x : ExceptT ε (StateM σ) α) (f : α → ExceptT ε (StateM σ) β) (s : σ)
    {a : α} {s₁ : σ} (hx : x.run s = (.ok a, s₁)) :
    (x >>= f).run s = (f a).run s₁ := by
  dsimp only [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, StateT.bind] at hx ⊢
  rw [hx]

private theorem exceptT_stateM_bind_err {ε σ α β : Type}
    (x : ExceptT ε (StateM σ) α) (f : α → ExceptT ε (StateM σ) β) (s : σ)
    {e : ε} {s₁ : σ} (hx : x.run s = (.error e, s₁)) :
    (x >>= f).run s = (.error e, s₁) := by
  dsimp only [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, StateT.bind] at hx ⊢
  rw [hx]
  dsimp only
  rfl

private theorem exceptT_stateM_tryFinally'_err {ε σ α β : Type}
    (x : ExceptT ε (StateM σ) α) (f : Option α → ExceptT ε (StateM σ) β) (s : σ)
    {e : ε} {b : β} {s₁ s₂ : σ}
    (hx : x.run s = (.error e, s₁))
    (hf : (f none).run s₁ = (.ok b, s₂)) :
    (tryFinally' x f).run s = (.error e, s₂) := by
  dsimp only [tryFinally', MonadFinally.tryFinally', ExceptT.mk, ExceptT.run,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure] at hx hf ⊢
  rw [hx]
  dsimp only
  rw [hf]
  rfl

private def mockReadResult (scripted : Except SandboxError SandboxResult)
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

private theorem mockRawOps_readBoxOutput_eq (bh : BoxHandle) (stdin : ByteArray)
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

private theorem runGeneric_mock_invalid {s₀ : MockSandboxState} {spec : BoxSpec}
    {e0 : SandboxError} (hVal : validateSpecPure spec = .error e0) :
    StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
      (.error (Internal.ensureNonEmptyMsg "invalid sandbox specification" e0), s₀) := by
  dsimp only [StateT.run]
  simp only [Internal.runGeneric, hVal, Pure.pure, StateT.pure]

private theorem runGeneric_mock_preflight_err {s₀ : MockSandboxState} {spec : BoxSpec}
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

private theorem mock_ioBracket_none (bh : BoxHandle) (stdin : ByteArray) (timeoutMs : Nat)
    (maxOut? : Option Nat) (s : MockSandboxState)
    (hValid : isValidSandboxHandleId bh.handleId = true)
    (hActive : s.activeBoxes.contains bh.handleId = true) :
    ((do
      let (ioRes, _) ← tryFinally'
        (mockRawOps.readBoxOutput bh stdin timeoutMs maxOut?)
        (fun _ => pure ())
      match ioRes with
      | .error e => return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
      | .ok out => return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
      (match mockReadResult s.scriptedOutput maxOut? with
       | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
       | .ok out => .ok out,
       { s with
         guestExecCalls := s.guestExecCalls + 1
         lastReadStdin := some stdin
         lastReadTimeoutMs := some timeoutMs }) := by
  rw [stateM_bind_apply, stateM_tryFinally'_apply,
    mockRawOps_readBoxOutput_eq bh stdin timeoutMs maxOut? s hValid hActive]
  dsimp only [Pure.pure, StateT.pure]
  cases mockReadResult s.scriptedOutput maxOut? <;> rfl

private theorem mock_ioBracket_some (bh : BoxHandle) (fh : PortForwarderHandle)
    (stdin : ByteArray) (timeoutMs : Nat) (maxOut? : Option Nat) (s : MockSandboxState)
    (baseFwds : List (Nat × Nat))
    (hBhValid : isValidSandboxHandleId bh.handleId = true)
    (hBhActive : s.activeBoxes.contains bh.handleId = true)
    (hFhValid : isValidSandboxHandleId fh.handleId = true)
    (hFwdsEq : s.activeForwarders = (fh.handleId, fh.boxHandleId) :: baseFwds) :
    ((do
      let (ioRes, _) ← tryFinally'
        (mockRawOps.readBoxOutput bh stdin timeoutMs maxOut?)
        (fun _ => do
          let _ ← mockRawOps.stopPortForwarders fh
          pure ())
      match ioRes with
      | .error e => return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
      | .ok out => return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
      (match mockReadResult s.scriptedOutput maxOut? with
       | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
       | .ok out => .ok out,
       { s with
         activeForwarders := baseFwds
         guestExecCalls := s.guestExecCalls + 1
         lastReadStdin := some stdin
         lastReadTimeoutMs := some timeoutMs }) := by
  rw [stateM_bind_apply, stateM_tryFinally'_apply,
    mockRawOps_readBoxOutput_eq bh stdin timeoutMs maxOut? s hBhValid hBhActive]
  dsimp only
  have hStop :
      (mockRawOps.stopPortForwarders fh)
        { s with
          guestExecCalls := s.guestExecCalls + 1
          lastReadStdin := some stdin
          lastReadTimeoutMs := some timeoutMs } =
        (.ok (),
          { s with
            activeForwarders := baseFwds
            guestExecCalls := s.guestExecCalls + 1
            lastReadStdin := some stdin
            lastReadTimeoutMs := some timeoutMs }) := by
    dsimp only [mockRawOps]
    have hAny : s.activeForwarders.any (fun p => p.1 == fh.handleId) = true := by
      rw [hFwdsEq]; simp
    have hBad : (!isValidSandboxHandleId fh.handleId ||
        !s.activeForwarders.any (fun p => p.1 == fh.handleId)) = false := by
      rw [hFhValid, hAny]; rfl
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hEr : eraseFirstForwarder fh.handleId s.activeForwarders = baseFwds := by
      rw [hFwdsEq]; simp [eraseFirstForwarder]
    rw [hEr]
  rw [stateM_bind_apply, hStop]
  dsimp only [Pure.pure, StateT.pure]
  cases mockReadResult s.scriptedOutput maxOut? <;> rfl

private theorem mock_boxKillReap (bh : BoxHandle) (baseBoxes : List Nat) (s : MockSandboxState)
    (hValid : isValidSandboxHandleId bh.handleId = true)
    (hBoxesEq : s.activeBoxes = bh.handleId :: baseBoxes) :
    (do
      let _ ← mockRawOps.killProcessGroup bh
      let _ ← mockRawOps.pidfdKill bh
      let _ ← mockRawOps.reapBox bh
      pure ()) s =
      ((),
       { s with
         activeBoxes := baseBoxes
         killPgCalls := s.killPgCalls + 1
         pidfdKillCalls := s.pidfdKillCalls + 1
         reapCalls := s.reapCalls + 1 }) := by
  have hMem : s.activeBoxes.contains bh.handleId = true := by
    rw [hBoxesEq]; simp
  have hBad : (!isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId) = false := by
    rw [hValid, hMem]; rfl
  have hK : (mockRawOps.killProcessGroup bh) s =
      (.ok (), { s with killPgCalls := s.killPgCalls + 1 }) := by
    dsimp only [mockRawOps]; simp only [hBad, Bool.false_eq_true, ↓reduceIte]
  have hP : (mockRawOps.pidfdKill bh) { s with killPgCalls := s.killPgCalls + 1 } =
      (.ok (), { s with killPgCalls := s.killPgCalls + 1, pidfdKillCalls := s.pidfdKillCalls + 1 }) := by
    dsimp only [mockRawOps]; simp only [hBad, Bool.false_eq_true, ↓reduceIte]
  have hR : (mockRawOps.reapBox bh)
      { s with killPgCalls := s.killPgCalls + 1, pidfdKillCalls := s.pidfdKillCalls + 1 } =
      (.ok (),
        { s with
          activeBoxes := baseBoxes
          killPgCalls := s.killPgCalls + 1
          pidfdKillCalls := s.pidfdKillCalls + 1
          reapCalls := s.reapCalls + 1 }) := by
    dsimp only [mockRawOps]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hEr : s.activeBoxes.erase bh.handleId = baseBoxes := by
      rw [hBoxesEq]; simp [List.erase]
    rw [hEr]
  rw [stateM_bind_apply, hK]
  dsimp only
  rw [stateM_bind_apply, hP]
  dsimp only
  rw [stateM_bind_apply, hR]
  rfl

private theorem mock_boxBracket_none (bh : BoxHandle) (valid : ValidBoxSpec)
    (baseBoxes : List Nat) (s : MockSandboxState)
    (hValid : isValidSandboxHandleId bh.handleId = true)
    (hBoxesEq : s.activeBoxes = bh.handleId :: baseBoxes)
    (hEmpty : valid.portForwards.isEmpty = true) :
    ((do
      let (boxRes, _) ← tryFinally' (do
        let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
          if valid.portForwards.isEmpty then
            pure (.ok none)
          else do
            match ← mockRawOps.startPortForwarders bh valid.portForwards with
            | .error e =>
              pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
            | .ok fh =>
              pure (.ok (some fh))
        match fwdRes with
        | .error e => return .error e
        | .ok fwdOpt =>
          let (ioRes, _) ← tryFinally'
            (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
            (fun _ =>
              match fwdOpt with
              | some fh => do
                let _ ← mockRawOps.stopPortForwarders fh
                pure ()
              | none => pure ())
          match ioRes with
          | .error e =>
            return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
          | .ok out =>
            return .ok out
      ) (fun _ => do
        let _ ← mockRawOps.killProcessGroup bh
        let _ ← mockRawOps.pidfdKill bh
        let _ ← mockRawOps.reapBox bh
        pure ())
      return boxRes) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
      (match mockReadResult s.scriptedOutput valid.limits.maxOutputBytes with
       | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
       | .ok out => .ok out,
       { s with
         activeBoxes := baseBoxes
         lastReadStdin := some valid.stdin
         lastReadTimeoutMs := some valid.limits.timeoutMs
         guestExecCalls := s.guestExecCalls + 1
         killPgCalls := s.killPgCalls + 1
         pidfdKillCalls := s.pidfdKillCalls + 1
         reapCalls := s.reapCalls + 1 }) := by
  have hActive : s.activeBoxes.contains bh.handleId = true := by rw [hBoxesEq]; simp
  have hIo := mock_ioBracket_none bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes s hValid hActive
  let sIo :=
    { s with
      guestExecCalls := s.guestExecCalls + 1
      lastReadStdin := some valid.stdin
      lastReadTimeoutMs := some valid.limits.timeoutMs }
  have hKill := mock_boxKillReap bh baseBoxes sIo hValid (by simp [sIo, hBoxesEq])
  have hBody :
      ((do
        let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
          if valid.portForwards.isEmpty then
            pure (.ok none)
          else do
            match ← mockRawOps.startPortForwarders bh valid.portForwards with
            | .error e =>
              pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
            | .ok fh =>
              pure (.ok (some fh))
        match fwdRes with
        | .error e => return .error e
        | .ok fwdOpt =>
          let (ioRes, _) ← tryFinally'
            (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
            (fun _ =>
              match fwdOpt with
              | some fh => do
                let _ ← mockRawOps.stopPortForwarders fh
                pure ()
              | none => pure ())
          match ioRes with
          | .error e =>
            return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
          | .ok out =>
            return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
        (match mockReadResult s.scriptedOutput valid.limits.maxOutputBytes with
         | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
         | .ok out => .ok out, sIo) := by
    simp only [hEmpty, ↓reduceIte]
    rw [stateM_bind_eq (x := pure (Except.ok none)) rfl]
    dsimp only
    exact hIo
  exact stateM_bind_eq (stateM_tryFinally'_eq hBody hKill)

private theorem mock_boxBracket_fwd (bh : BoxHandle) (valid : ValidBoxSpec)
    (baseBoxes : List Nat) (s : MockSandboxState)
    (hValid : isValidSandboxHandleId bh.handleId = true)
    (hBoxesEq : s.activeBoxes = bh.handleId :: baseBoxes)
    (hNotEmpty : valid.portForwards.isEmpty = false) :
    match s.failForwarderStartWith with
    | some ferr =>
      let err' := Internal.ensureNonEmptyMsg "failed to start port forwarders"
        { ferr with message := if ferr.message.isEmpty then "forwarder start failed" else ferr.message }
      ((do
        let (boxRes, _) ← tryFinally' (do
          let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
            if valid.portForwards.isEmpty then
              pure (.ok none)
            else do
              match ← mockRawOps.startPortForwarders bh valid.portForwards with
              | .error e =>
                pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
              | .ok fh =>
                pure (.ok (some fh))
          match fwdRes with
          | .error e => return .error e
          | .ok fwdOpt =>
            let (ioRes, _) ← tryFinally'
              (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
              (fun _ =>
                match fwdOpt with
                | some fh => do
                  let _ ← mockRawOps.stopPortForwarders fh
                  pure ()
                | none => pure ())
            match ioRes with
            | .error e =>
              return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
            | .ok out =>
              return .ok out
        ) (fun _ => do
          let _ ← mockRawOps.killProcessGroup bh
          let _ ← mockRawOps.pidfdKill bh
          let _ ← mockRawOps.reapBox bh
          pure ())
        return boxRes) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
        (.error err',
         { s with
           activeBoxes := baseBoxes
           lastStartedForwards := some valid.portForwards
           killPgCalls := s.killPgCalls + 1
           pidfdKillCalls := s.pidfdKillCalls + 1
           reapCalls := s.reapCalls + 1 })
    | none =>
      let sStart := { s with lastStartedForwards := some valid.portForwards }
      let idFwd := allocMockHandleId sStart
      ((do
        let (boxRes, _) ← tryFinally' (do
          let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
            if valid.portForwards.isEmpty then
              pure (.ok none)
            else do
              match ← mockRawOps.startPortForwarders bh valid.portForwards with
              | .error e =>
                pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
              | .ok fh =>
                pure (.ok (some fh))
          match fwdRes with
          | .error e => return .error e
          | .ok fwdOpt =>
            let (ioRes, _) ← tryFinally'
              (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
              (fun _ =>
                match fwdOpt with
                | some fh => do
                  let _ ← mockRawOps.stopPortForwarders fh
                  pure ()
                | none => pure ())
            match ioRes with
            | .error e =>
              return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
            | .ok out =>
              return .ok out
        ) (fun _ => do
          let _ ← mockRawOps.killProcessGroup bh
          let _ ← mockRawOps.pidfdKill bh
          let _ ← mockRawOps.reapBox bh
          pure ())
        return boxRes) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
        (match mockReadResult s.scriptedOutput valid.limits.maxOutputBytes with
         | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
         | .ok out => .ok out,
         { s with
           nextHandleId := idFwd + 1
           activeBoxes := baseBoxes
           lastStartedForwards := some valid.portForwards
           lastReadStdin := some valid.stdin
           lastReadTimeoutMs := some valid.limits.timeoutMs
           guestExecCalls := s.guestExecCalls + 1
           killPgCalls := s.killPgCalls + 1
           pidfdKillCalls := s.pidfdKillCalls + 1
           reapCalls := s.reapCalls + 1 }) := by
  have hActive : s.activeBoxes.contains bh.handleId = true := by rw [hBoxesEq]; simp
  have hBad : (!isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId) = false := by
    rw [hValid, hActive]; rfl
  cases hFail : s.failForwarderStartWith with
  | some ferr =>
    dsimp only
    have hStart : (mockRawOps.startPortForwarders bh valid.portForwards) s =
        (.error { ferr with message := if ferr.message.isEmpty then "forwarder start failed" else ferr.message },
         { s with lastStartedForwards := some valid.portForwards }) := by
      dsimp only [mockRawOps]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      rw [hFail]
    let sStart := { s with lastStartedForwards := some valid.portForwards }
    have hKill := mock_boxKillReap bh baseBoxes sStart hValid (by simp [sStart, hBoxesEq])
    let err' := Internal.ensureNonEmptyMsg "failed to start port forwarders"
      { ferr with message := if ferr.message.isEmpty then "forwarder start failed" else ferr.message }
    have hBody :
        ((do
          let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
            if valid.portForwards.isEmpty then
              pure (.ok none)
            else do
              match ← mockRawOps.startPortForwarders bh valid.portForwards with
              | .error e =>
                pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
              | .ok fh =>
                pure (.ok (some fh))
          match fwdRes with
          | .error e => return .error e
          | .ok fwdOpt =>
            let (ioRes, _) ← tryFinally'
              (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
              (fun _ =>
                match fwdOpt with
                | some fh => do
                  let _ ← mockRawOps.stopPortForwarders fh
                  pure ()
                | none => pure ())
            match ioRes with
            | .error e =>
              return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
            | .ok out =>
              return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
          (.error err', sStart) := by
      simp only [hNotEmpty, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_eq hStart]
      dsimp only
      rw [stateM_bind_eq (x := pure (Except.error _)) rfl]
      rfl
    rw [stateM_bind_eq (stateM_tryFinally'_eq hBody hKill)]
    dsimp only [Pure.pure, StateT.pure, sStart]
    rw [hFail]
  | none =>
    dsimp only
    let sStart := { s with lastStartedForwards := some valid.portForwards }
    let idFwd := allocMockHandleId sStart
    let fh : PortForwarderHandle := { handleId := idFwd, boxHandleId := bh.handleId }
    let sFwd := { sStart with nextHandleId := idFwd + 1, activeForwarders := (idFwd, bh.handleId) :: s.activeForwarders }
    have hFhValid : isValidSandboxHandleId idFwd = true := isValidSandboxHandleId_alloc sStart
    have hStart : (mockRawOps.startPortForwarders bh valid.portForwards) s = (.ok fh, sFwd) := by
      dsimp only [mockRawOps]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      dsimp only [sStart, idFwd, fh, sFwd]
      rw [hFail]
    have hActiveFwd : sFwd.activeBoxes.contains bh.handleId = true := by simp [sFwd, sStart, hBoxesEq]
    have hIo := mock_ioBracket_some bh fh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes
      sFwd s.activeForwarders hValid hActiveFwd hFhValid rfl
    let sIo :=
      { sFwd with
        activeForwarders := s.activeForwarders
        guestExecCalls := s.guestExecCalls + 1
        lastReadStdin := some valid.stdin
        lastReadTimeoutMs := some valid.limits.timeoutMs }
    have hKill := mock_boxKillReap bh baseBoxes sIo hValid (by simp [sIo, sFwd, sStart, hBoxesEq])
    have hBody :
        ((do
          let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
            if valid.portForwards.isEmpty then
              pure (.ok none)
            else do
              match ← mockRawOps.startPortForwarders bh valid.portForwards with
              | .error e =>
                pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
              | .ok fh =>
                pure (.ok (some fh))
          match fwdRes with
          | .error e => return .error e
          | .ok fwdOpt =>
            let (ioRes, _) ← tryFinally'
              (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
              (fun _ =>
                match fwdOpt with
                | some fh => do
                  let _ ← mockRawOps.stopPortForwarders fh
                  pure ()
                | none => pure ())
            match ioRes with
            | .error e =>
              return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
            | .ok out =>
              return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
          (match mockReadResult sFwd.scriptedOutput valid.limits.maxOutputBytes with
           | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
           | .ok out => .ok out, sIo) := by
      simp only [hNotEmpty, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_eq hStart]
      dsimp only
      rw [stateM_bind_eq (x := pure (Except.ok (some fh))) rfl]
      dsimp only
      exact hIo
    rw [stateM_bind_eq (stateM_tryFinally'_eq hBody hKill)]
    dsimp only [Pure.pure, StateT.pure, sIo, sFwd, sStart, idFwd]
    rw [hFail]

private theorem runGeneric_mock_spawn_fail {s₀ : MockSandboxState} {spec : BoxSpec}
    {valid : ValidBoxSpec} {err : SandboxError}
    (hVal : validateSpecPure spec = .ok valid)
    (hHost : s₀.hostBaseAvailable = true)
    (hMem : valid.limits.memoryMaxBytes.isSome = true → s₀.memoryCgroupAvailable = true)
    (hPids : valid.limits.pidsMax.isSome = true → s₀.pidsCgroupAvailable = true)
    (hFail : s₀.failSpawnWith = some err) :
    let req : PreflightReq :=
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }
    let plan := compilePlan valid s₀.preset
    let idPlan := allocMockHandleId s₀
    let err' := Internal.ensureNonEmptyMsg "failed to spawn sandbox"
      { err with message := if err.message.isEmpty then "spawnBox failed" else err.message }
    StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
      (.error err',
       { s₀ with
         nextHandleId := idPlan + 1
         lastPreflightReq := some req
         lastSealedPlan := some plan
         spawnCalls := s₀.spawnCalls + 1 }) := by
  intro req plan idPlan err'
  have hPre : (mockRawOps.preflight req) s₀ =
      (.ok (), { s₀ with lastPreflightReq := some req }) := by
    dsimp only [mockRawOps]
    have hb : (!s₀.hostBaseAvailable) = false := by simp [hHost]
    have hm : (req.needMemoryCgroup && !s₀.memoryCgroupAvailable) = false := by
      cases hc : valid.limits.memoryMaxBytes.isSome
      · simp [req, hc]
      · simp [req, hc, hMem hc]
    have hp : (req.needPidsCgroup && !s₀.pidsCgroupAvailable) = false := by
      cases hc : valid.limits.pidsMax.isSome
      · simp [req, hc]
      · simp [req, hc, hPids hc]
    simp [hb, hm, hp]
  let sPref := { s₀ with lastPreflightReq := some req }
  let sSeal := { sPref with nextHandleId := idPlan + 1, openPlans := idPlan :: s₀.openPlans, lastSealedPlan := some plan }
  have hSeal : (mockRawOps.sealPlan plan) sPref = (.ok { handleId := idPlan }, sSeal) := rfl
  have hPhValid : isValidSandboxHandleId idPlan = true := isValidSandboxHandleId_alloc s₀
  have hPhMem : sSeal.openPlans.contains idPlan = true := by simp [sSeal]
  have hBadPlan : (!isValidSandboxHandleId idPlan || !sSeal.openPlans.contains idPlan) = false := by
    rw [hPhValid, hPhMem]; rfl
  have hSp : (mockRawOps.spawnBox { handleId := idPlan }) sSeal =
      (.error { err with message := if err.message.isEmpty then "spawnBox failed" else err.message },
       { sSeal with spawnCalls := s₀.spawnCalls + 1 }) := by
    dsimp only [mockRawOps]
    simp only [hBadPlan, Bool.false_eq_true, ↓reduceIte]
    simp [sSeal, sPref, hFail]
  have hClose : (mockRawOps.closePlan { handleId := idPlan }) { sSeal with spawnCalls := s₀.spawnCalls + 1 } =
      (.ok (), { s₀ with nextHandleId := idPlan + 1, lastPreflightReq := some req, lastSealedPlan := some plan, spawnCalls := s₀.spawnCalls + 1 }) := by
    dsimp only [mockRawOps]
    simp only [hBadPlan, Bool.false_eq_true, ↓reduceIte]
    have hEr : sSeal.openPlans.erase idPlan = s₀.openPlans := by simp [sSeal, List.erase]
    simp only [sSeal, sPref, hEr]
  dsimp only [StateT.run, Internal.runGeneric]
  rw [hVal]
  dsimp only
  rw [stateM_bind_apply, hPre]
  dsimp only
  rw [stateM_bind_apply]
  change (match (mockRawOps.discoverHostPreset) sPref with | _ => _) = _
  have hDisc : (mockRawOps.discoverHostPreset) sPref = (.ok s₀.preset, sPref) := rfl
  rw [hDisc]
  dsimp only
  rw [stateM_bind_apply, hSeal]
  dsimp only
  rw [stateM_bind_apply, stateM_tryFinally'_apply, stateM_bind_apply, hSp]
  dsimp only [Pure.pure, StateT.pure]
  rw [stateM_bind_apply, hClose]
  rfl

private theorem runGeneric_mock_spawn_ok {s₀ : MockSandboxState} {spec : BoxSpec}
    {valid : ValidBoxSpec}
    (hVal : validateSpecPure spec = .ok valid)
    (hHost : s₀.hostBaseAvailable = true)
    (hMem : valid.limits.memoryMaxBytes.isSome = true → s₀.memoryCgroupAvailable = true)
    (hPids : valid.limits.pidsMax.isSome = true → s₀.pidsCgroupAvailable = true)
    (hNoFailSpawn : s₀.failSpawnWith = none) :
    let req : PreflightReq :=
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }
    let plan := compilePlan valid s₀.preset
    let idPlan := allocMockHandleId s₀
    let sPref := { s₀ with lastPreflightReq := some req }
    let sSeal := { sPref with nextHandleId := idPlan + 1, openPlans := idPlan :: s₀.openPlans, lastSealedPlan := some plan }
    let sSpawnPre := { sSeal with spawnCalls := s₀.spawnCalls + 1 }
    let idBox := allocMockHandleId sSpawnPre
    let sSpawn := { sSpawnPre with nextHandleId := idBox + 1, activeBoxes := idBox :: s₀.activeBoxes }
    if plan.portForwards.isEmpty then
      StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
        (match mockReadResult s₀.scriptedOutput valid.limits.maxOutputBytes with
         | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
         | .ok out => .ok out,
         { s₀ with
           nextHandleId := idBox + 1
           lastPreflightReq := some req
           lastSealedPlan := some plan
           lastReadStdin := some valid.stdin
           lastReadTimeoutMs := some valid.limits.timeoutMs
           spawnCalls := s₀.spawnCalls + 1
           guestExecCalls := s₀.guestExecCalls + 1
           killPgCalls := s₀.killPgCalls + 1
           pidfdKillCalls := s₀.pidfdKillCalls + 1
           reapCalls := s₀.reapCalls + 1 })
    else
      match s₀.failForwarderStartWith with
      | some ferr =>
        let err' := Internal.ensureNonEmptyMsg "failed to start port forwarders"
          { ferr with message := if ferr.message.isEmpty then "forwarder start failed" else ferr.message }
        StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
          (.error err',
           { s₀ with
             nextHandleId := idBox + 1
             lastPreflightReq := some req
             lastSealedPlan := some plan
             lastStartedForwards := some plan.portForwards
             spawnCalls := s₀.spawnCalls + 1
             killPgCalls := s₀.killPgCalls + 1
             pidfdKillCalls := s₀.pidfdKillCalls + 1
             reapCalls := s₀.reapCalls + 1 })
      | none =>
        let sStart := { sSpawn with lastStartedForwards := some plan.portForwards }
        let idFwd := allocMockHandleId sStart
        StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
          (match mockReadResult s₀.scriptedOutput valid.limits.maxOutputBytes with
           | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
           | .ok out => .ok out,
           { s₀ with
             nextHandleId := idFwd + 1
             lastPreflightReq := some req
             lastSealedPlan := some plan
             lastStartedForwards := some plan.portForwards
             lastReadStdin := some valid.stdin
             lastReadTimeoutMs := some valid.limits.timeoutMs
             spawnCalls := s₀.spawnCalls + 1
             guestExecCalls := s₀.guestExecCalls + 1
             killPgCalls := s₀.killPgCalls + 1
             pidfdKillCalls := s₀.pidfdKillCalls + 1
             reapCalls := s₀.reapCalls + 1 }) := by
  intro req plan idPlan sPref sSeal sSpawnPre idBox sSpawn
  have hPre : (mockRawOps.preflight req) s₀ = (.ok (), sPref) := by
    dsimp only [mockRawOps]
    have hb : (!s₀.hostBaseAvailable) = false := by simp [hHost]
    have hm : (req.needMemoryCgroup && !s₀.memoryCgroupAvailable) = false := by
      cases hc : valid.limits.memoryMaxBytes.isSome
      · simp [req, hc]
      · simp [req, hc, hMem hc]
    have hp : (req.needPidsCgroup && !s₀.pidsCgroupAvailable) = false := by
      cases hc : valid.limits.pidsMax.isSome
      · simp [req, hc]
      · simp [req, hc, hPids hc]
    simp [hb, hm, hp, sPref]
  have hDisc : (mockRawOps.discoverHostPreset) sPref = (.ok s₀.preset, sPref) := rfl
  have hSeal : (mockRawOps.sealPlan plan) sPref = (.ok { handleId := idPlan }, sSeal) := rfl
  have hPhValid : isValidSandboxHandleId idPlan = true := isValidSandboxHandleId_alloc s₀
  have hPhMem : sSeal.openPlans.contains idPlan = true := by simp [sSeal]
  have hBadPlan : (!isValidSandboxHandleId idPlan || !sSeal.openPlans.contains idPlan) = false := by
    rw [hPhValid, hPhMem]; rfl
  have hBhValid : isValidSandboxHandleId idBox = true := isValidSandboxHandleId_alloc sSpawnPre
  let bh : BoxHandle := { handleId := idBox, pid := 200, pgid := 200, pidfd := 5 }
  have hSp : (mockRawOps.spawnBox { handleId := idPlan }) sSeal = (.ok bh, sSpawn) := by
    dsimp only [mockRawOps]
    simp only [hBadPlan, Bool.false_eq_true, ↓reduceIte]
    simp [sSeal, sPref, hNoFailSpawn, sSpawnPre, sSpawn, idBox, bh]
  have hPlanFwds : plan.portForwards = valid.portForwards := rfl
  have hSetup :
      StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
        let (res, sOuter) :=
          let (boxRes, sBox) :=
            ((do
              let (boxRes, _) ← tryFinally' (do
                let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
                  if valid.portForwards.isEmpty then
                    pure (.ok none)
                  else do
                    match ← mockRawOps.startPortForwarders bh valid.portForwards with
                    | .error e =>
                      pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
                    | .ok fh =>
                      pure (.ok (some fh))
                match fwdRes with
                | .error e => return .error e
                | .ok fwdOpt =>
                  let (ioRes, _) ← tryFinally'
                    (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                    (fun _ =>
                      match fwdOpt with
                      | some fh => do
                        let _ ← mockRawOps.stopPortForwarders fh
                        pure ()
                      | none => pure ())
                  match ioRes with
                  | .error e =>
                    return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
                  | .ok out =>
                    return .ok out
              ) (fun _ => do
                let _ ← mockRawOps.killProcessGroup bh
                let _ ← mockRawOps.pidfdKill bh
                let _ ← mockRawOps.reapBox bh
                pure ())
              return boxRes) : StateM MockSandboxState (Except SandboxError SandboxResult)) sSpawn
          let (_, sClosed) := (mockRawOps.closePlan { handleId := idPlan }) sBox
          (boxRes, sClosed)
        (res, sOuter) := by
    dsimp only [StateT.run, Internal.runGeneric]
    rw [hVal]
    dsimp only
    rw [stateM_bind_apply, hPre]
    dsimp only
    rw [stateM_bind_apply, hDisc]
    dsimp only
    rw [stateM_bind_apply, hSeal]
    dsimp only
    rw [stateM_bind_apply, stateM_tryFinally'_apply, stateM_bind_apply, hSp]
    dsimp only [Pure.pure, StateT.pure]
    rw [stateM_bind_apply]
    rfl
  by_cases hEmpty : plan.portForwards.isEmpty = true
  · simp only [hEmpty, ↓reduceIte]
    have hEmptyV : valid.portForwards.isEmpty = true := hEmpty
    have hBox := mock_boxBracket_none bh valid s₀.activeBoxes sSpawn hBhValid rfl hEmptyV
    rw [hSetup, hBox]
    dsimp only
    have hOpen : sSpawn.openPlans = idPlan :: s₀.openPlans := rfl
    have hOpenMem : sSpawn.openPlans.contains idPlan = true := by rw [hOpen]; simp
    have hBadC : (!isValidSandboxHandleId idPlan || !sSpawn.openPlans.contains idPlan) = false := by
      rw [hPhValid, hOpenMem]; rfl
    dsimp only [mockRawOps]
    simp only [hBadC, Bool.false_eq_true, ↓reduceIte]
    have hEr : sSpawn.openPlans.erase idPlan = s₀.openPlans := by rw [hOpen]; simp [List.erase]
    rw [hEr]
  · have hEmptyF : plan.portForwards.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
    simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte]
    have hEmptyVF : valid.portForwards.isEmpty = false := hEmptyF
    have hBox := mock_boxBracket_fwd bh valid s₀.activeBoxes sSpawn hBhValid rfl hEmptyVF
    have hFailEq : sSpawn.failForwarderStartWith = s₀.failForwarderStartWith := rfl
    rw [hFailEq] at hBox
    cases hFwdFail : s₀.failForwarderStartWith with
    | some ferr =>
      simp only [hFwdFail] at hBox ⊢
      rw [hSetup, hBox]
      dsimp only
      have hOpen : sSpawn.openPlans = idPlan :: s₀.openPlans := rfl
      have hOpenMem : sSpawn.openPlans.contains idPlan = true := by rw [hOpen]; simp
      have hBadC : (!isValidSandboxHandleId idPlan || !sSpawn.openPlans.contains idPlan) = false := by
        rw [hPhValid, hOpenMem]; rfl
      dsimp only [mockRawOps]
      simp only [hBadC, Bool.false_eq_true, ↓reduceIte]
      have hEr : sSpawn.openPlans.erase idPlan = s₀.openPlans := by rw [hOpen]; simp [List.erase]
      rw [hEr]
      rfl
    | none =>
      simp only [hFwdFail] at hBox ⊢
      rw [hSetup, hBox]
      dsimp only
      have hOpen : sSpawn.openPlans = idPlan :: s₀.openPlans := rfl
      have hOpenMem : sSpawn.openPlans.contains idPlan = true := by rw [hOpen]; simp
      have hBadC : (!isValidSandboxHandleId idPlan || !sSpawn.openPlans.contains idPlan) = false := by
        rw [hPhValid, hOpenMem]; rfl
      dsimp only [mockRawOps]
      simp only [hBadC, Bool.false_eq_true, ↓reduceIte]
      have hEr : sSpawn.openPlans.erase idPlan = s₀.openPlans := by rw [hOpen]; simp [List.erase]
      rw [hEr]
      rfl

private theorem byteArray_extract_zero_size (bs : ByteArray) (n : Nat) :
    (bs.extract 0 (Nat.min bs.size n)).size = Nat.min bs.size n := by
  simp [ByteArray.size_extract]

private theorem byteArray_extract_zero_eq_self (bs : ByteArray) (n : Nat) (h : bs.size ≤ n) :
    bs.extract 0 (Nat.min bs.size n) = bs := by
  have hMin : Nat.min bs.size n = bs.size := Nat.min_eq_left h
  rw [hMin]
  simp

/-- Proof of `test_psandbox_run_invalidSpec_hasZeroSideEffects` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_invalidSpec_hasZeroSideEffects :
    AllPass (test_psandbox_run_invalidSpec_hasZeroSideEffects Internal.mkApiM) := by
  intro s₀ spec
  dsimp only [Internal.mkApiM, Internal.validateSpec]
  rcases except_cases (validateSpecPure spec) with ⟨e0, hVal⟩ | ⟨valid, hVal⟩
  · rw [hVal]
    dsimp only
    rw [runGeneric_mock_invalid hVal]
    dsimp only [assert]
    exact ⟨⟨⟨Internal.ensureNonEmptyMsg "invalid sandbox specification" e0, rfl,
      by rw [ensureNonEmptyMsg_kind]; exact validateSpecPure_error_kind hVal,
      ensureNonEmptyMsg_ne_empty "invalid sandbox specification" e0 (by decide)⟩, rfl⟩, trivial⟩
  · rw [hVal]
    simp [assume]

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_invalidSpec_hasZeroSideEffects`. -/
theorem reach_psandbox_run_invalidSpec_hasZeroSideEffects :
    CanReach (test_psandbox_run_invalidSpec_hasZeroSideEffects Internal.mkApiM) := by
  let spec : BoxSpec := { program := "" }
  have hVal : validateSpecPure spec =
      .error { kind := .invalidInput, message := "program must not be empty" } := rfl
  refine ⟨{}, spec, ?_⟩
  dsimp only [Internal.mkApiM, Internal.validateSpec]
  rw [hVal]
  dsimp only
  rw [runGeneric_mock_invalid hVal]
  dsimp only [assert]
  exact ⟨⟨⟨_, rfl, by decide, by decide⟩, rfl⟩, trivial⟩

/-- Proof of `test_psandbox_isAvailable_and_failClosedUnavailable` for `Internal.mkApiM`. -/
theorem proof_psandbox_isAvailable_and_failClosedUnavailable :
    AllPass (test_psandbox_isAvailable_and_failClosedUnavailable Internal.mkApiM) := by
  intro s₀
  dsimp only [Internal.mkApiM, Internal.validateSpec]
  have hAvail :
      StateT.run (Internal.isAvailableGeneric mockRawOps) s₀ =
        (s₀.hostBaseAvailable && s₀.memoryCgroupAvailable && s₀.pidsCgroupAvailable,
         { s₀ with lastPreflightReq := some { needMemoryCgroup := true, needPidsCgroup := true } }) := by
    dsimp only [StateT.run, Internal.isAvailableGeneric]
    rw [stateM_bind_apply]
    dsimp only [mockRawOps]
    cases s₀.hostBaseAvailable <;> cases s₀.memoryCgroupAvailable <;> cases s₀.pidsCgroupAvailable <;>
      rfl
  rw [hAvail]
  dsimp only [assert]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro sUnavail spec hSpecOk hCondUnavail
  rcases except_cases (validateSpecPure spec) with ⟨_, hVal⟩ | ⟨valid, hVal⟩
  · simp [hVal, Except.isOk, Except.toBool] at hSpecOk
  · have hLim := validateSpecPure_limits hVal
    have hFail : !sUnavail.hostBaseAvailable ∨
        (valid.limits.memoryMaxBytes.isSome && !sUnavail.memoryCgroupAvailable) ∨
        (valid.limits.pidsMax.isSome && !sUnavail.pidsCgroupAvailable) := by
      rw [hLim]
      exact hCondUnavail
    obtain ⟨e, hRunEq, hMsg⟩ := runGeneric_mock_preflight_err hVal hFail
    rw [hRunEq]
    dsimp only [assert]
    refine ⟨⟨⟨{ e with kind := .unavailable }, rfl, rfl, hMsg⟩, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    intro sSpawnUnavail specSpawn hSpawnOk ⟨hB, hM, hP⟩
    rcases except_cases (validateSpecPure specSpawn) with ⟨_, hValSp⟩ | ⟨validSp, hValSp⟩
    · simp [hValSp, Except.isOk, Except.toBool] at hSpawnOk
    · let sPreExecFail : MockSandboxState :=
        { sSpawnUnavail with
          failSpawnWith := some { kind := .unavailable, message := "pre-execvp setup failed" } }
      have hSp := runGeneric_mock_spawn_fail (s₀ := sPreExecFail) hValSp hB (fun _ => hM) (fun _ => hP) rfl
      dsimp only at hSp
      rw [hSp]
      dsimp only [assert]
      exact ⟨⟨⟨_, rfl, by decide, by decide⟩, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_isAvailable_and_failClosedUnavailable`. -/
theorem reach_psandbox_isAvailable_and_failClosedUnavailable :
    CanReach (test_psandbox_isAvailable_and_failClosedUnavailable Internal.mkApiM) := by
  let spec : BoxSpec := { program := "/bin/true" }
  let valid : ValidBoxSpec :=
    { program := "/bin/true"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := {} }
  let sUnavail : MockSandboxState := { hostBaseAvailable := false }
  have hVal : validateSpecPure spec = .ok valid :=
    validateSpecPure_simple "/bin/true" ByteArray.empty 60_000 (some (16 * 1024 * 1024))
      (by decide) (by decide) (by decide)
  refine ⟨{}, ?_⟩
  dsimp only [Internal.mkApiM, Internal.validateSpec]
  have hAvail :
      StateT.run (Internal.isAvailableGeneric mockRawOps) ({} : MockSandboxState) =
        (true, { ({} : MockSandboxState) with lastPreflightReq := some { needMemoryCgroup := true, needPidsCgroup := true } }) :=
    rfl
  rw [hAvail]
  dsimp only [assert]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, sUnavail, spec, ?_⟩
  refine ⟨by rw [hVal]; rfl, Or.inl rfl, ?_⟩
  obtain ⟨e, hRunEq, hMsg⟩ := runGeneric_mock_preflight_err (s₀ := sUnavail) hVal (Or.inl rfl)
  rw [hRunEq]
  dsimp only [assert]
  refine ⟨⟨⟨{ e with kind := .unavailable }, rfl, rfl, hMsg⟩, rfl, rfl, rfl, rfl, rfl⟩, {}, spec, ?_⟩
  refine ⟨by rw [hVal]; rfl, ⟨rfl, rfl, rfl⟩, ?_⟩
  let sPreExecFail : MockSandboxState :=
    { failSpawnWith := some { kind := .unavailable, message := "pre-execvp setup failed" } }
  have hSp := runGeneric_mock_spawn_fail (s₀ := sPreExecFail) hVal rfl (fun _ => rfl) (fun _ => rfl) rfl
  dsimp only at hSp
  rw [hSp]
  dsimp only [assert]
  exact ⟨⟨⟨_, rfl, by decide, by decide⟩, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- Proof of `test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan :
    AllPass (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan Internal.mkApiM) := by
  intro s₀ ⟨hB, hM, hP⟩ ⟨hSpFail, _⟩
  let preset0 : HostRuntimePreset :=
    { systemEntries :=
        #[ .readOnlyDir "/usr"
         , .topSymlink "/bin" "usr/bin"
         , .topSymlink "/lib" "usr/lib"
         , .readOnlyDir "/home" ]
      etcPaths := #["/etc/passwd", "/etc/localtime", "/etc/shadow"]
      excludedHomePaths :=
        #[ "/usr/local/homes/user"
         , "/lib/custom_home/bob"
         , "/home/user" ] }
  let sWithPreset : MockSandboxState := { s₀ with preset := preset0 }
  let spec : BoxSpec :=
    { program := "env"
      mounts := #[.readOnly "/data/sub" "/work/sub", .readOnly "/data" "/work"] }
  let valid : ValidBoxSpec :=
    { program := "env"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp", .readOnly "/data/sub" "/work/sub", .readOnly "/data" "/work"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := {} }
  have hVal : validateSpecPure spec = .ok valid := by
    dsimp only [spec, valid, validateSpecPure, hasNulChar, normalizeCleanAbsPath, parseCleanAbsSegs,
      splitSlashChars, splitSlashAux, validateMountsList, validateAndNormalizeMount,
      isReservedBoxSegs, reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair,
      dedupEnvPairs, defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
    rfl
  have hRun := runGeneric_mock_spawn_ok (s₀ := sWithPreset) hVal hB (fun _ => hM) (fun _ => hP) hSpFail
  have hEmpty : (compilePlan valid sWithPreset.preset).portForwards.isEmpty = true := rfl
  simp only [hEmpty, ↓reduceIte] at hRun
  have hPresetEq : sWithPreset.preset = preset0 := rfl
  rw [hPresetEq] at hRun
  dsimp only [Internal.mkApiM]
  rw [hRun]
  dsimp only
  simp only [assert]
  exact ⟨by decide, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan`. -/
theorem reach_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan :
    CanReach (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan Internal.mkApiM) :=
  ⟨{}, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩,
    proof_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩⟩

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
  have hRunExit := runGeneric_mock_spawn_ok (s₀ := sExit0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl
  have hEmpNone : ∀ p : HostRuntimePreset, (compilePlan validNone p).portForwards.isEmpty = true := fun _ => rfl
  simp only [hEmpNone, ↓reduceIte] at hRunExit
  have hReadExit :
      mockReadResult sExit0.scriptedOutput none =
        .ok { outcome := .exited code, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadExit] at hRunExit
  let sSig0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes } }
  have hRunSig := runGeneric_mock_spawn_ok (s₀ := sSig0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl
  simp only [hEmpNone, ↓reduceIte] at hRunSig
  have hReadSig :
      mockReadResult sSig0.scriptedOutput none =
        .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadSig] at hRunSig
  let sTout0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes } }
  have hRunTout := runGeneric_mock_spawn_ok (s₀ := sTout0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl
  simp only [hEmpNone, ↓reduceIte] at hRunTout
  have hReadTout :
      mockReadResult sTout0.scriptedOutput none =
        .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes } := rfl
  rw [show validNone.limits.maxOutputBytes = none from rfl, hReadTout] at hRunTout
  let sNoLim0 : MockSandboxState :=
    { scriptedOutput := .ok { outcome := .outputLimitExceeded, stdout := outBytes, stderr := errBytes } }
  have hRunNoLim := runGeneric_mock_spawn_ok (s₀ := sNoLim0) hValNone rfl (fun _ => rfl) (fun _ => rfl) rfl
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
  have hRunCap := runGeneric_mock_spawn_ok (s₀ := sCap0) hValCap rfl (fun _ => rfl) (fun _ => rfl) rfl
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
    CanReach (test_psandbox_run_outcomesAndOutputCap Internal.mkApiM) := by
  refine ⟨0, 9, ByteArray.empty, ByteArray.empty, ?_⟩
  have hAll := proof_psandbox_run_outcomesAndOutputCap 0 9 ByteArray.empty ByteArray.empty
  dsimp only [assert] at hAll ⊢
  refine ⟨hAll.1, hAll.2.1, hAll.2.2.1, hAll.2.2.2.1, 10, ?_⟩
  exact hAll.2.2.2.2 10

/-- Proof of `test_psandbox_run_forwardsStdinAndTimeoutMs` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_forwardsStdinAndTimeoutMs :
    AllPass (test_psandbox_run_forwardsStdinAndTimeoutMs Internal.mkApiM) := by
  intro s₀ stdinBytes timeoutMs hTimeout ⟨hB, hM, hP⟩ ⟨hSpFail, _⟩ hScriptOk
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
  have hRun := runGeneric_mock_spawn_ok (s₀ := s₀) hVal hB (fun _ => hM) (fun _ => hP) hSpFail
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

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_forwardsStdinAndTimeoutMs`. -/
theorem reach_psandbox_run_forwardsStdinAndTimeoutMs :
    CanReach (test_psandbox_run_forwardsStdinAndTimeoutMs Internal.mkApiM) :=
  ⟨{}, ByteArray.empty, 100, by decide, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
    proof_psandbox_run_forwardsStdinAndTimeoutMs {} ByteArray.empty 100
      (by decide) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl⟩

/-- Proof of `test_psandbox_run_portForwarderBracket` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_portForwarderBracket :
    AllPass (test_psandbox_run_portForwarderBracket Internal.mkApiM) := by
  intro s₀ ⟨hB, hM, hP⟩ hSpFail hScriptOk
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
  have hRunOk := runGeneric_mock_spawn_ok (s₀ := sOk0) hValFwd hB (fun _ => hM) (fun _ => hP) hSpFail
  have hNotEmp : (compilePlan validFwd sOk0.preset).portForwards.isEmpty = false := rfl
  simp only [hNotEmp, Bool.false_eq_true, ↓reduceIte] at hRunOk
  have hRunNoFwd := runGeneric_mock_spawn_ok (s₀ := sOk0) hValNoFwd hB (fun _ => hM) (fun _ => hP) hSpFail
  have hEmpNoFwd : (compilePlan validNoFwd sOk0.preset).portForwards.isEmpty = true := rfl
  simp only [hEmpNoFwd, ↓reduceIte] at hRunNoFwd
  let fwdErr : SandboxError := { kind := .ioError, message := "bind failed" }
  let sFail0 : MockSandboxState := { s₀ with failForwarderStartWith := some fwdErr }
  have hRunFail := runGeneric_mock_spawn_ok (s₀ := sFail0) hValFwd hB (fun _ => hM) (fun _ => hP) hSpFail
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

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_portForwarderBracket`. -/
theorem reach_psandbox_run_portForwarderBracket :
    CanReach (test_psandbox_run_portForwarderBracket Internal.mkApiM) :=
  ⟨{}, ⟨rfl, rfl, rfl⟩, rfl, rfl,
    proof_psandbox_run_portForwarderBracket {} ⟨rfl, rfl, rfl⟩ rfl rfl⟩

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
      cases hSpFail : s₀.failSpawnWith with
      | some err =>
        have hRun := runGeneric_mock_spawn_fail hVal hHost hMem hPids hSpFail
        rw [hRun]
        dsimp only [assert]
        refine ⟨⟨rfl, rfl, rfl⟩,
          ensureNonEmptyMsg_ne_empty "failed to spawn sandbox" _ (by decide), ?_⟩
        simp only [Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          Pure.pure]
      | none =>
        have hRun := runGeneric_mock_spawn_ok hVal hHost hMem hPids hSpFail
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

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors`. -/
theorem reach_psandbox_run_conservesResourcesOnAllOutcomesAndErrors :
    CanReach (test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors Internal.mkApiM) :=
  ⟨{}, { program := "/bin/true" },
    proof_psandbox_run_conservesResourcesOnAllOutcomesAndErrors {} { program := "/bin/true" }⟩

private theorem runGeneric_mockEx_cancel_setup (sRun0 : MockSandboxState)
    (hB : sRun0.hostBaseAvailable = true)
    (hM : sRun0.memoryCgroupAvailable = true)
    (hP : sRun0.pidsCgroupAvailable = true)
    (hSpFail : sRun0.failSpawnWith = none) :
    let valid : ValidBoxSpec :=
      { program := "/bin/sleep"
        args := #["60"]
        cwd := "/tmp"
        stdin := ByteArray.empty
        mounts := #[.scratch "/tmp"]
        allowBoxLocalhost := false
        portForwards := #[{ boxPort := 3000, hostPort := 13000 }]
        env := #[("PATH", "/usr/bin:/bin")]
        limits := {} }
    let req : PreflightReq := { needMemoryCgroup := true, needPidsCgroup := true }
    let plan := compilePlan valid sRun0.preset
    let idPlan := allocMockHandleId sRun0
    let sPref := { sRun0 with lastPreflightReq := some req }
    let sSeal := { sPref with nextHandleId := idPlan + 1, openPlans := idPlan :: sRun0.openPlans, lastSealedPlan := some plan }
    let sSpawnPre := { sSeal with spawnCalls := sRun0.spawnCalls + 1 }
    let idBox := allocMockHandleId sSpawnPre
    let bh : BoxHandle := { handleId := idBox, pid := 200, pgid := 200, pidfd := 5 }
    let sSpawn := { sSpawnPre with nextHandleId := idBox + 1, activeBoxes := idBox :: sRun0.activeBoxes }
    (mockRawOpsEx.preflight req).run sRun0 = (.ok (.ok ()), sPref) ∧
    (mockRawOpsEx.discoverHostPreset).run sPref = (.ok (.ok sRun0.preset), sPref) ∧
    (mockRawOpsEx.sealPlan plan).run sPref = (.ok (.ok { handleId := idPlan }), sSeal) ∧
    (mockRawOpsEx.spawnBox { handleId := idPlan }).run sSeal = (.ok (.ok bh), sSpawn) := by
  intro valid req plan idPlan sPref sSeal sSpawnPre idBox bh sSpawn
  have hPre : (mockRawOpsEx.preflight req).run sRun0 = (.ok (.ok ()), sPref) := by
    dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
    simp [hB, hM, hP, sPref, req]
  have hPres : (mockRawOpsEx.discoverHostPreset).run sPref = (.ok (.ok sRun0.preset), sPref) := rfl
  have hSeal : (mockRawOpsEx.sealPlan plan).run sPref = (.ok (.ok { handleId := idPlan }), sSeal) := rfl
  have hPhValid : isValidSandboxHandleId idPlan = true := isValidSandboxHandleId_alloc sRun0
  have hPhMem : sSeal.openPlans.contains idPlan = true := by simp [sSeal]
  have hBad : (!isValidSandboxHandleId idPlan || !sSeal.openPlans.contains idPlan) = false := by
    rw [hPhValid, hPhMem]; rfl
  have hSp : (mockRawOpsEx.spawnBox { handleId := idPlan }).run sSeal = (.ok (.ok bh), sSpawn) := by
    dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    dsimp only [sSeal, sPref, sSpawnPre, sSpawn, idBox, bh]
    rw [hSpFail]
  exact ⟨hPre, hPres, hSeal, hSp⟩

/-- Proof of `test_psandbox_run_monadFinallyCleansUpOnCancellation` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_monadFinallyCleansUpOnCancellation :
    AllPass (test_psandbox_run_monadFinallyCleansUpOnCancellation Internal.mkApiM) := by
  intro s₀ ⟨hB, hM, hP⟩ ⟨hSpFail, hFwdFail⟩
  let spec : BoxSpec :=
    { program := "/bin/sleep"
      args := #["60"]
      portForwards := #[{ boxPort := 3000, hostPort := 13000 }] }
  let valid : ValidBoxSpec :=
    { program := "/bin/sleep"
      args := #["60"]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[{ boxPort := 3000, hostPort := 13000 }]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := {} }
  have hVal : validateSpecPure spec = .ok valid := by
    dsimp only [spec, valid, validateSpecPure, hasNulChar, validateMountsList,
      allDistinct, isValidEnvPair, dedupEnvPairs, defaultSandboxPath, defaultSandboxCwd,
      mountBoxPath, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  let sRead0 : MockSandboxState := { s₀ with throwOnReadOutput := true, throwOnStartForwarders := false }
  obtain ⟨hPre1, hPres1, hSeal1, hSp1⟩ := runGeneric_mockEx_cancel_setup sRead0 hB hM hP hSpFail
  let req : PreflightReq := { needMemoryCgroup := true, needPidsCgroup := true }
  let plan := compilePlan valid s₀.preset
  let idPlan1 := allocMockHandleId sRead0
  let sPref1 := { sRead0 with lastPreflightReq := some req }
  let sSeal1 := { sPref1 with nextHandleId := idPlan1 + 1, openPlans := idPlan1 :: s₀.openPlans, lastSealedPlan := some plan }
  let sSpawnPre1 := { sSeal1 with spawnCalls := s₀.spawnCalls + 1 }
  let idBox1 := allocMockHandleId sSpawnPre1
  let bh1 : BoxHandle := { handleId := idBox1, pid := 200, pgid := 200, pidfd := 5 }
  let sSpawn1 := { sSpawnPre1 with nextHandleId := idBox1 + 1, activeBoxes := idBox1 :: s₀.activeBoxes }
  have hPhValid1 : isValidSandboxHandleId idPlan1 = true := isValidSandboxHandleId_alloc sRead0
  have hBhValid1 : isValidSandboxHandleId idBox1 = true := isValidSandboxHandleId_alloc sSpawnPre1
  have hBhActive1 : sSpawn1.activeBoxes.contains idBox1 = true := by simp [sSpawn1]
  let sStart1 := { sSpawn1 with lastStartedForwards := some plan.portForwards }
  let idFwd1 := allocMockHandleId sStart1
  let fh1 : PortForwarderHandle := { handleId := idFwd1, boxHandleId := idBox1 }
  let sFwd1 := { sStart1 with nextHandleId := idFwd1 + 1, activeForwarders := (idFwd1, idBox1) :: s₀.activeForwarders }
  have hFhValid1 : isValidSandboxHandleId idFwd1 = true := isValidSandboxHandleId_alloc sStart1
  have hStart1 : (mockRawOpsEx.startPortForwarders bh1 plan.portForwards).run sSpawn1 = (.ok (.ok fh1), sFwd1) := by
    dsimp only [mockRawOpsEx, mockRawOps, ExceptT.mk, ExceptT.run]
    have hThrow : sSpawn1.throwOnStartForwarders = false := rfl
    simp only [hThrow, Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.run]
    have hBhId : bh1.handleId = idBox1 := rfl
    have hBad : (!isValidSandboxHandleId bh1.handleId || !sSpawn1.activeBoxes.contains bh1.handleId) = false := by
      rw [hBhId, hBhValid1, hBhActive1]; rfl
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hFailNone : sSpawn1.failForwarderStartWith = none := hFwdFail
    dsimp only [sStart1, idFwd1, fh1, sFwd1]
    rw [hFailNone]
  let sReadErr1 :=
    { sFwd1 with
      guestExecCalls := s₀.guestExecCalls + 1
      lastReadStdin := some valid.stdin
      lastReadTimeoutMs := some valid.limits.timeoutMs }
  have hRead1 : (mockRawOpsEx.readBoxOutput bh1 valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes).run sFwd1 =
      (.error "cancelled-during-read", sReadErr1) := rfl
  let sStop1 := { sReadErr1 with activeForwarders := s₀.activeForwarders }
  let ioFin1 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ =>
      match some fh1 with
      | some fh => do
        let _ ← mockRawOpsEx.stopPortForwarders fh
        pure ()
      | none => pure ()
  have hStop1 : (ioFin1 none).run sReadErr1 = (.ok (), sStop1) := by
    have hS : (mockRawOpsEx.stopPortForwarders fh1).run sReadErr1 = (.ok (.ok ()), sStop1) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      have hAny : sReadErr1.activeForwarders.any (fun p => p.1 == fh1.handleId) = true := by
        simp [sReadErr1, sFwd1, fh1]
      have hFhId : fh1.handleId = idFwd1 := rfl
      have hBad : (!isValidSandboxHandleId fh1.handleId ||
          !sReadErr1.activeForwarders.any (fun p => p.1 == fh1.handleId)) = false := by
        rw [hAny, hFhId, hFhValid1]; rfl
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : eraseFirstForwarder fh1.handleId sReadErr1.activeForwarders = s₀.activeForwarders := by
        simp [sReadErr1, sFwd1, fh1, eraseFirstForwarder]
      rw [hEr]
    exact exceptT_stateM_bind_ok _ _ _ hS
  have hIoTry1 := exceptT_stateM_tryFinally'_err _ ioFin1 _ hRead1 hStop1
  let sKillReap1 :=
    { sStop1 with
      activeBoxes := s₀.activeBoxes
      killPgCalls := s₀.killPgCalls + 1
      pidfdKillCalls := s₀.pidfdKillCalls + 1
      reapCalls := s₀.reapCalls + 1 }
  let boxFin1 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ => do
      let _ ← mockRawOpsEx.killProcessGroup bh1
      let _ ← mockRawOpsEx.pidfdKill bh1
      let _ ← mockRawOpsEx.reapBox bh1
      pure ()
  have hBoxFin1 : (boxFin1 none).run sStop1 = (.ok (), sKillReap1) := by
    have hMem : sStop1.activeBoxes.contains bh1.handleId = true := by
      simp [sStop1, sReadErr1, sFwd1, sStart1, sSpawn1, bh1]
    have hBhId : bh1.handleId = idBox1 := rfl
    have hBad : (!isValidSandboxHandleId bh1.handleId || !sStop1.activeBoxes.contains bh1.handleId) = false := by
      rw [hMem, hBhId, hBhValid1]; rfl
    have hK : (mockRawOpsEx.killProcessGroup bh1).run sStop1 =
        (.ok (.ok ()), { sStop1 with killPgCalls := s₀.killPgCalls + 1 }) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]; rfl
    have hP : (mockRawOpsEx.pidfdKill bh1).run { sStop1 with killPgCalls := s₀.killPgCalls + 1 } =
        (.ok (.ok ()), { sStop1 with killPgCalls := s₀.killPgCalls + 1, pidfdKillCalls := s₀.pidfdKillCalls + 1 }) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]; rfl
    have hR : (mockRawOpsEx.reapBox bh1).run
        { sStop1 with killPgCalls := s₀.killPgCalls + 1, pidfdKillCalls := s₀.pidfdKillCalls + 1 } =
        (.ok (.ok ()), sKillReap1) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : sStop1.activeBoxes.erase bh1.handleId = s₀.activeBoxes := by
        simp [sStop1, sReadErr1, sFwd1, sStart1, sSpawn1, bh1, List.erase]
      rw [hEr]
    dsimp only [boxFin1]
    rw [exceptT_stateM_bind_ok _ _ _ hK, exceptT_stateM_bind_ok _ _ _ hP,
      exceptT_stateM_bind_ok _ _ _ hR]
    rfl
  let sClose1 := { sKillReap1 with openPlans := s₀.openPlans }
  let planFin1 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ => do
      let _ ← mockRawOpsEx.closePlan { handleId := idPlan1 }
      pure ()
  have hPlanFin1 : (planFin1 none).run sKillReap1 = (.ok (), sClose1) := by
    have hC : (mockRawOpsEx.closePlan { handleId := idPlan1 }).run sKillReap1 = (.ok (.ok ()), sClose1) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      have hOpen : sKillReap1.openPlans = idPlan1 :: s₀.openPlans := rfl
      have hMem : sKillReap1.openPlans.contains idPlan1 = true := by rw [hOpen]; simp
      have hBad : (!isValidSandboxHandleId idPlan1 || !sKillReap1.openPlans.contains idPlan1) = false := by
        rw [hPhValid1, hMem]; rfl
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : sKillReap1.openPlans.erase idPlan1 = s₀.openPlans := by
        rw [hOpen]; simp [List.erase]
      rw [hEr]
    exact exceptT_stateM_bind_ok _ _ _ hC
  have hPre1' : (mockRawOpsEx.preflight
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }).run sRead0 =
      (.ok (.ok ()), sPref1) := hPre1
  have hPres1' : (mockRawOpsEx.discoverHostPreset).run sPref1 =
      (.ok (.ok s₀.preset), sPref1) := hPres1
  have hSeal1' : (mockRawOpsEx.sealPlan (compilePlan valid s₀.preset)).run sPref1 =
      (.ok (.ok { handleId := idPlan1 }), sSeal1) := hSeal1
  have hSp1' : (mockRawOpsEx.spawnBox { handleId := idPlan1 }).run sSeal1 =
      (.ok (.ok bh1), sSpawn1) := hSp1
  have hRunReadCancel :
      (Internal.runGeneric mockRawOpsEx spec).run sRead0 = (.error "cancelled-during-read", sClose1) := by
    dsimp only [Internal.runGeneric]
    rw [hVal]
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hPre1']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hPres1']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hSeal1']
    dsimp only
    have hOuterErr :
        ((do
          match ← mockRawOpsEx.spawnBox { handleId := idPlan1 } with
          | .error e => return Except.error (Internal.ensureNonEmptyMsg "failed to spawn sandbox" e)
          | .ok bh =>
            let (boxRes, _) ← tryFinally' (do
              let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
                if plan.portForwards.isEmpty then
                  pure (.ok none)
                else do
                  match ← mockRawOpsEx.startPortForwarders bh plan.portForwards with
                  | .error e =>
                    pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
                  | .ok fh =>
                    pure (.ok (some fh))
              match fwdRes with
              | .error e => return Except.error e
              | .ok fwdOpt =>
                let (ioRes, _) ← tryFinally'
                  (mockRawOpsEx.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                  (fun _ =>
                    match fwdOpt with
                    | some fh => do
                      let _ ← mockRawOpsEx.stopPortForwarders fh
                      pure ()
                    | none => pure ())
                match ioRes with
                | .error e => return Except.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
                | .ok out => return Except.ok out
            ) (fun _ => do
              let _ ← mockRawOpsEx.killProcessGroup bh
              let _ ← mockRawOpsEx.pidfdKill bh
              let _ ← mockRawOpsEx.reapBox bh
              pure ())
            return boxRes) : ExceptT String (StateM MockSandboxState) (Except SandboxError SandboxResult)).run sSeal1 =
          (.error "cancelled-during-read", sKillReap1) := by
      rw [exceptT_stateM_bind_ok _ _ _ hSp1']
      dsimp only
      have hMidErr :
          ((do
            let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
              if plan.portForwards.isEmpty then
                pure (.ok none)
              else do
                match ← mockRawOpsEx.startPortForwarders bh1 plan.portForwards with
                | .error e =>
                  pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
                | .ok fh =>
                  pure (.ok (some fh))
            match fwdRes with
            | .error e => return Except.error e
            | .ok fwdOpt =>
              let (ioRes, _) ← tryFinally'
                (mockRawOpsEx.readBoxOutput bh1 valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                (fun _ =>
                  match fwdOpt with
                  | some fh => do
                    let _ ← mockRawOpsEx.stopPortForwarders fh
                    pure ()
                  | none => pure ())
              match ioRes with
              | .error e => return Except.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
              | .ok out => return Except.ok out) : ExceptT String (StateM MockSandboxState) (Except SandboxError SandboxResult)).run sSpawn1 =
            (.error "cancelled-during-read", sStop1) := by
        have hNotEmp : plan.portForwards.isEmpty = false := rfl
        simp only [hNotEmp, Bool.false_eq_true, ↓reduceIte]
        rw [exceptT_stateM_bind_ok _ _ _ hStart1]
        dsimp only
        rw [exceptT_stateM_bind_ok (x := pure (Except.ok (some fh1))) _ _ rfl]
        dsimp only
        exact exceptT_stateM_bind_err _ _ _ hIoTry1
      have hMidTry := exceptT_stateM_tryFinally'_err _ boxFin1 _ hMidErr hBoxFin1
      exact exceptT_stateM_bind_err _ _ _ hMidTry
    dsimp only [plan] at hOuterErr
    have hOuterTry := exceptT_stateM_tryFinally'_err _ planFin1 _ hOuterErr hPlanFin1
    exact exceptT_stateM_bind_err _ _ _ hOuterTry
  let sFwd0 : MockSandboxState := { s₀ with throwOnReadOutput := false, throwOnStartForwarders := true }
  obtain ⟨hPre2, hPres2, hSeal2, hSp2⟩ := runGeneric_mockEx_cancel_setup sFwd0 hB hM hP hSpFail
  let idPlan2 := allocMockHandleId sFwd0
  let sPref2 := { sFwd0 with lastPreflightReq := some req }
  let sSeal2 := { sPref2 with nextHandleId := idPlan2 + 1, openPlans := idPlan2 :: s₀.openPlans, lastSealedPlan := some plan }
  let sSpawnPre2 := { sSeal2 with spawnCalls := s₀.spawnCalls + 1 }
  let idBox2 := allocMockHandleId sSpawnPre2
  let bh2 : BoxHandle := { handleId := idBox2, pid := 200, pgid := 200, pidfd := 5 }
  let sSpawn2 := { sSpawnPre2 with nextHandleId := idBox2 + 1, activeBoxes := idBox2 :: s₀.activeBoxes }
  have hPhValid2 : isValidSandboxHandleId idPlan2 = true := isValidSandboxHandleId_alloc sFwd0
  have hBhValid2 : isValidSandboxHandleId idBox2 = true := isValidSandboxHandleId_alloc sSpawnPre2
  have hStartErr2 : (mockRawOpsEx.startPortForwarders bh2 plan.portForwards).run sSpawn2 =
      (.error "cancelled-during-forwarder-start", sSpawn2) := rfl
  let sKillReap2 :=
    { sSpawn2 with
      activeBoxes := s₀.activeBoxes
      killPgCalls := s₀.killPgCalls + 1
      pidfdKillCalls := s₀.pidfdKillCalls + 1
      reapCalls := s₀.reapCalls + 1 }
  let boxFin2 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ => do
      let _ ← mockRawOpsEx.killProcessGroup bh2
      let _ ← mockRawOpsEx.pidfdKill bh2
      let _ ← mockRawOpsEx.reapBox bh2
      pure ()
  have hBoxFin2 : (boxFin2 none).run sSpawn2 = (.ok (), sKillReap2) := by
    have hMem : sSpawn2.activeBoxes.contains bh2.handleId = true := by simp [sSpawn2, bh2]
    have hBhId : bh2.handleId = idBox2 := rfl
    have hBad : (!isValidSandboxHandleId bh2.handleId || !sSpawn2.activeBoxes.contains bh2.handleId) = false := by
      rw [hMem, hBhId, hBhValid2]; rfl
    have hK : (mockRawOpsEx.killProcessGroup bh2).run sSpawn2 =
        (.ok (.ok ()), { sSpawn2 with killPgCalls := s₀.killPgCalls + 1 }) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]; rfl
    have hP : (mockRawOpsEx.pidfdKill bh2).run { sSpawn2 with killPgCalls := s₀.killPgCalls + 1 } =
        (.ok (.ok ()), { sSpawn2 with killPgCalls := s₀.killPgCalls + 1, pidfdKillCalls := s₀.pidfdKillCalls + 1 }) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]; rfl
    have hR : (mockRawOpsEx.reapBox bh2).run
        { sSpawn2 with killPgCalls := s₀.killPgCalls + 1, pidfdKillCalls := s₀.pidfdKillCalls + 1 } =
        (.ok (.ok ()), sKillReap2) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : sSpawn2.activeBoxes.erase bh2.handleId = s₀.activeBoxes := by
        simp [sSpawn2, bh2, List.erase]
      rw [hEr]
    dsimp only [boxFin2]
    rw [exceptT_stateM_bind_ok _ _ _ hK, exceptT_stateM_bind_ok _ _ _ hP,
      exceptT_stateM_bind_ok _ _ _ hR]
    rfl
  let sClose2 := { sKillReap2 with openPlans := s₀.openPlans }
  let planFin2 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ => do
      let _ ← mockRawOpsEx.closePlan { handleId := idPlan2 }
      pure ()
  have hPlanFin2 : (planFin2 none).run sKillReap2 = (.ok (), sClose2) := by
    have hC : (mockRawOpsEx.closePlan { handleId := idPlan2 }).run sKillReap2 = (.ok (.ok ()), sClose2) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      have hOpen : sKillReap2.openPlans = idPlan2 :: s₀.openPlans := rfl
      have hMem : sKillReap2.openPlans.contains idPlan2 = true := by rw [hOpen]; simp
      have hBad : (!isValidSandboxHandleId idPlan2 || !sKillReap2.openPlans.contains idPlan2) = false := by
        rw [hPhValid2, hMem]; rfl
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : sKillReap2.openPlans.erase idPlan2 = s₀.openPlans := by
        rw [hOpen]; simp [List.erase]
      rw [hEr]
    exact exceptT_stateM_bind_ok _ _ _ hC
  have hPre2' : (mockRawOpsEx.preflight
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }).run sFwd0 =
      (.ok (.ok ()), sPref2) := hPre2
  have hPres2' : (mockRawOpsEx.discoverHostPreset).run sPref2 =
      (.ok (.ok s₀.preset), sPref2) := hPres2
  have hSeal2' : (mockRawOpsEx.sealPlan (compilePlan valid s₀.preset)).run sPref2 =
      (.ok (.ok { handleId := idPlan2 }), sSeal2) := hSeal2
  have hSp2' : (mockRawOpsEx.spawnBox { handleId := idPlan2 }).run sSeal2 =
      (.ok (.ok bh2), sSpawn2) := hSp2
  have hRunFwdCancel :
      (Internal.runGeneric mockRawOpsEx spec).run sFwd0 = (.error "cancelled-during-forwarder-start", sClose2) := by
    dsimp only [Internal.runGeneric]
    rw [hVal]
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hPre2']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hPres2']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hSeal2']
    dsimp only
    have hOuterErr :
        ((do
          match ← mockRawOpsEx.spawnBox { handleId := idPlan2 } with
          | .error e => return Except.error (Internal.ensureNonEmptyMsg "failed to spawn sandbox" e)
          | .ok bh =>
            let (boxRes, _) ← tryFinally' (do
              let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
                if plan.portForwards.isEmpty then
                  pure (.ok none)
                else do
                  match ← mockRawOpsEx.startPortForwarders bh plan.portForwards with
                  | .error e =>
                    pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
                  | .ok fh =>
                    pure (.ok (some fh))
              match fwdRes with
              | .error e => return Except.error e
              | .ok fwdOpt =>
                let (ioRes, _) ← tryFinally'
                  (mockRawOpsEx.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                  (fun _ =>
                    match fwdOpt with
                    | some fh => do
                      let _ ← mockRawOpsEx.stopPortForwarders fh
                      pure ()
                    | none => pure ())
                match ioRes with
                | .error e => return Except.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
                | .ok out => return Except.ok out
            ) (fun _ => do
              let _ ← mockRawOpsEx.killProcessGroup bh
              let _ ← mockRawOpsEx.pidfdKill bh
              let _ ← mockRawOpsEx.reapBox bh
              pure ())
            return boxRes) : ExceptT String (StateM MockSandboxState) (Except SandboxError SandboxResult)).run sSeal2 =
          (.error "cancelled-during-forwarder-start", sKillReap2) := by
      rw [exceptT_stateM_bind_ok _ _ _ hSp2']
      dsimp only
      have hMidErr :
          ((do
            let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
              if plan.portForwards.isEmpty then
                pure (.ok none)
              else do
                match ← mockRawOpsEx.startPortForwarders bh2 plan.portForwards with
                | .error e =>
                  pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
                | .ok fh =>
                  pure (.ok (some fh))
            match fwdRes with
            | .error e => return Except.error e
            | .ok fwdOpt =>
              let (ioRes, _) ← tryFinally'
                (mockRawOpsEx.readBoxOutput bh2 valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                (fun _ =>
                  match fwdOpt with
                  | some fh => do
                    let _ ← mockRawOpsEx.stopPortForwarders fh
                    pure ()
                  | none => pure ())
              match ioRes with
              | .error e => return Except.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
              | .ok out => return Except.ok out) : ExceptT String (StateM MockSandboxState) (Except SandboxError SandboxResult)).run sSpawn2 =
            (.error "cancelled-during-forwarder-start", sSpawn2) := by
        have hNotEmp : plan.portForwards.isEmpty = false := rfl
        simp only [hNotEmp, Bool.false_eq_true, ↓reduceIte]
        exact exceptT_stateM_bind_err _ _ _ hStartErr2
      have hMidTry := exceptT_stateM_tryFinally'_err _ boxFin2 _ hMidErr hBoxFin2
      exact exceptT_stateM_bind_err _ _ _ hMidTry
    dsimp only [plan] at hOuterErr
    have hOuterTry := exceptT_stateM_tryFinally'_err _ planFin2 _ hOuterErr hPlanFin2
    exact exceptT_stateM_bind_err _ _ _ hOuterTry
  dsimp only [Internal.mkApiM]
  dsimp only [spec, sRead0] at hRunReadCancel
  dsimp only [spec, sFwd0] at hRunFwdCancel
  rw [hRunReadCancel]
  dsimp only [assert]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [hRunFwdCancel]
  dsimp only [assert]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_monadFinallyCleansUpOnCancellation`. -/
theorem reach_psandbox_run_monadFinallyCleansUpOnCancellation :
    CanReach (test_psandbox_run_monadFinallyCleansUpOnCancellation Internal.mkApiM) :=
  ⟨{}, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩,
    proof_psandbox_run_monadFinallyCleansUpOnCancellation {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩⟩

end LeanSwe.ProcessSandbox.Proofs
