import Core.Obeys
import LeanSwe.EnvVars.Types
import LeanSweProofs.EnvVars.Model
import LeanSwe.Process.Types
import LeanSweProofs.Process.Model
import LeanSwe.Git.Types
import LeanSweProofs.Git.Model
import LeanSweProofs.Git.Model.Refines
import LeanSwe.Git.Impl

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open LeanSwe.EnvVars
open LeanSwe.Process
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Unfold `StateM` pure on `.run`. -/
@[simp] theorem stateM_pure_run {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α).run s = (a, s) := rfl

/-- Unfold `StateM` bind on `.run`. -/
theorem stateM_bind_run {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := by
  dsimp only [StateT.run, Bind.bind, StateT.bind]
  cases x s
  rfl

/-- Unfold `StateT.bind` on `.run`. -/
theorem stateT_bind_run {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (StateT.bind x f).run s = (f (x.run s).1).run (x.run s).2 := by
  dsimp only [StateT.run, StateT.bind]
  cases x s
  rfl

/-- Unfold `Except` `>>=` without unfolding `StateM` `>>=`. -/
theorem except_bind_eq {ε α β : Type} (x : Except ε α) (f : α → Except ε β) :
    (x >>= f) = Except.bind x f := rfl

/-- Unfold `Except` `pure` without unfolding `StateM` `pure`. -/
theorem except_pure_eq {ε α : Type} (a : α) :
    (pure a : Except ε α) = Except.ok a := rfl

/-- Unfold `StateM` map (`<$>`) on `.run`. -/
theorem stateM_map_run {σ α β : Type} (f : α → β) (x : StateM σ α) (s : σ) :
    (f <$> x).run s = (f (x.run s).1, (x.run s).2) := by
  dsimp only [Functor.map, StateT.map, StateT.run]
  cases x s
  rfl

/-- Unfold `MonadFinally.tryFinally'` on `StateM`. -/
theorem stateM_tryFinally'_run {σ α β : Type} (x : StateM σ α) (k : Option α → StateM σ β) (s : σ) :
    (MonadFinally.tryFinally' x k).run s =
      (((x.run s).1, ((k (some (x.run s).1)).run (x.run s).2).1),
       ((k (some (x.run s).1)).run (x.run s).2).2) := by
  have h : (MonadFinally.tryFinally' x k).run s =
      let (a, s1) := x.run s
      let (b, s2) := (k (some a)).run s1
      ((a, b), s2) := rfl
  rw [h]
  cases x.run s with
  | mk a s1 =>
    dsimp only
    cases (k (some a)).run s1 with
    | mk b s2 => rfl

/-- Reflexivity of `allowedHostTransition` on any well-formed `GitHostState`. -/
theorem allowedHostTransition_refl {s : GitHostState} (hwf : hostStepWf s = true) :
    allowedHostTransition s s :=
  ⟨hwf, hwf, rfl, rfl, Nat.le_refl _⟩

/-- Transitivity of `allowedHostTransition`. -/
theorem allowedHostTransition_trans {s₁ s₂ s₃ : GitHostState}
    (h12 : allowedHostTransition s₁ s₂) (h23 : allowedHostTransition s₂ s₃) :
    allowedHostTransition s₁ s₃ :=
  ⟨h12.1, h23.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, Nat.le_trans h12.2.2.2.2 h23.2.2.2.2⟩

/-- Convert `0 < s.length` into `s ≠ ""`. -/
theorem ne_empty_of_len_pos {s : String} (h : 0 < s.length) : s ≠ "" := by
  intro hemp
  subst hemp
  simp at h

/-- Non-empty left prefix guarantees concatenation is non-empty. -/
theorem str_append_ne_empty_left (a b : String) (ha : 0 < a.length) : a ++ b ≠ "" := by
  apply ne_empty_of_len_pos
  rw [String.length_append]
  omega

/-- Non-empty left prefix guarantees 3-part concatenation is non-empty. -/
theorem interp3_ne_empty (a b c : String) (ha : 0 < a.length) : a ++ b ++ c ≠ "" := by
  apply ne_empty_of_len_pos
  simp only [String.length_append]
  omega

/-- Convert `s.isEmpty ≠ true` into `s ≠ ""`. -/
theorem ne_empty_of_not_isEmpty {s : String} (h : ¬s.isEmpty = true) : s ≠ "" := by
  intro hemp
  subst hemp
  exact h rfl

/-- `String.ofList cs` is non-empty whenever `cs.isEmpty = false`. -/
theorem not_isEmpty_ofList {cs : List Char} (h : cs.isEmpty = false) :
    !(String.ofList cs).isEmpty = true := by
  cases cs with
  | nil => cases h
  | cons c rest =>
    have hne : String.ofList (c :: rest) ≠ "" := by
      apply ne_empty_of_len_pos
      rw [String.length_ofList]
      exact Nat.succ_pos _
    cases hs : (String.ofList (c :: rest)).isEmpty with
    | false => rfl
    | true => exact False.elim (hne (String.isEmpty_iff.mp hs))

/-- `Impl.ensureNonEmptyMsg` always yields a non-empty string when `fallback ≠ ""`. -/
theorem ensureNonEmptyMsg_ne_empty {fallback msg : String} (hfb : fallback ≠ "") :
    Impl.ensureNonEmptyMsg fallback msg ≠ "" := by
  unfold Impl.ensureNonEmptyMsg
  dsimp only
  split
  · exact hfb
  · next h => exact ne_empty_of_not_isEmpty h

/-- `Impl.mapEnvVarsErrorImpl` produces `.commandFailed` with a non-empty message. -/
theorem mapEnvVarsErrorImpl_spec (e : EnvVarsError) :
    (Impl.mapEnvVarsErrorImpl e).kind = .commandFailed ∧
    (Impl.mapEnvVarsErrorImpl e).message ≠ "" := by
  unfold Impl.mapEnvVarsErrorImpl
  dsimp only
  refine ⟨rfl, ?_⟩
  split
  · decide
  · next h => exact ne_empty_of_not_isEmpty h

/-- `Impl.mapProcessErrorImpl` produces `.timeout`/`.invalidInput`/`.commandFailed` with a non-empty message. -/
theorem mapProcessErrorImpl_spec (cmd : String) (e : ProcessError) :
    ((Impl.mapProcessErrorImpl cmd e).kind = .timeout ∨
     (Impl.mapProcessErrorImpl cmd e).kind = .invalidInput ∨
     (Impl.mapProcessErrorImpl cmd e).kind = .commandFailed) ∧
    (Impl.mapProcessErrorImpl cmd e).message ≠ "" := by
  unfold Impl.mapProcessErrorImpl
  dsimp only
  constructor
  · cases e.kind <;> simp
  · split
    · apply ne_empty_of_len_pos
      have h4 : (toString ("git " : String)).length = 4 := rfl
      simp only [String.length_append, h4]
      omega
    · next h => exact ne_empty_of_not_isEmpty h

/-- `Impl.classifyError` always returns a non-empty message and never `.invalidPath` or `.parseError`. -/
theorem classifyError_spec (cmd : String) (out : GitRawOutput) :
    (Impl.classifyError cmd out).message ≠ "" ∧
    (Impl.classifyError cmd out).kind ≠ .invalidPath ∧
    (Impl.classifyError cmd out).kind ≠ .parseError := by
  dsimp only [Impl.classifyError]
  refine ⟨?_, ?_⟩
  · apply ensureNonEmptyMsg_ne_empty
    apply ne_empty_of_len_pos
    have h4 : (toString ("git " : String)).length = 4 := rfl
    simp only [String.length_append, h4]
    omega
  · by_cases hBlank : (Impl.trimAsciiWhitespace (Impl.decodeUtf8Lossy out.stderr)).isEmpty = true
    · simp only [hBlank, ↓reduceIte]
      repeat' (split; try exact ⟨by decide, by decide⟩)
      exact ⟨by decide, by decide⟩
    · simp only [hBlank, Bool.false_eq_true, ↓reduceIte]
      repeat' (split; try exact ⟨by decide, by decide⟩)
      exact ⟨by decide, by decide⟩

/-- `Model.validateFsPathArg` errors always carry non-empty messages. -/
theorem validateFsPathArg_err_nonEmpty {p : String} {e : GitError}
    (h : validateFsPathArg p = .error e) : e.message ≠ "" := by
  unfold validateFsPathArg at h
  split at h
  · cases h; decide
  · split at h
    · cases h; decide
    · cases h

/-- `Model.validateCloneEndpoint` errors always carry non-empty messages and `.invalidInput`. -/
theorem validateCloneEndpoint_err_spec {p : String} {e : GitError}
    (h : validateCloneEndpoint p = .error e) : e.kind = .invalidInput ∧ e.message ≠ "" := by
  unfold validateCloneEndpoint at h
  split at h
  · cases h; exact ⟨rfl, by decide⟩
  · cases h

/-- `Model.validateRelRepoPath` errors always carry non-empty messages. -/
theorem validateRelRepoPath_err_nonEmpty {p : String} {e : GitError}
    (h : validateRelRepoPath p = .error e) : e.message ≠ "" := by
  unfold validateRelRepoPath at h
  split at h
  · cases h; exact interp3_ne_empty _ _ _ (by decide)
  · dsimp only at h
    split at h
    · cases h; exact interp3_ne_empty _ _ _ (by decide)
    · split at h
      · cases h; exact interp3_ne_empty _ _ _ (by decide)
      · cases h

/-- `Model.validateCommitOptions` errors always carry non-empty messages. -/
theorem validateCommitOptions_err_nonEmpty {opts : CommitOptions} {e : GitError}
    (h : validateCommitOptions opts = .error e) : e.message ≠ "" := by
  unfold validateCommitOptions at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h; decide
  · cases hN : opts.authorName with
    | none =>
      rw [hN] at h; dsimp only at h
      cases hE : opts.authorEmail with
      | none => rw [hE] at h; cases h
      | some em =>
        rw [hE] at h; dsimp only at h
        split at h
        · cases h; decide
        · cases h
    | some n =>
      rw [hN] at h; dsimp only at h
      split at h
      · cases h; decide
      · cases hE : opts.authorEmail with
        | none => rw [hE] at h; cases h
        | some em =>
          rw [hE] at h; dsimp only at h
          split at h
          · cases h; decide
          · cases h

/-- `Impl.decodeUtf8Checked` errors carry non-empty messages. -/
theorem decodeUtf8Checked_err_nonEmpty {bs : ByteArray} {e : GitError}
    (h : Impl.decodeUtf8Checked bs = .error e) : e.message ≠ "" := by
  unfold Impl.decodeUtf8Checked at h
  cases hU : String.fromUTF8? bs with
  | some s => rw [hU] at h; cases h
  | none => rw [hU] at h; cases h; decide

/-- `Model.mkCommitId` guarantees `isValidCommitIdStr` on `.ok` and non-empty message on `.error`. -/
theorem mkCommitId_spec (s : String) :
    match mkCommitId s with
    | .ok cid => isValidCommitIdStr cid.hex = true
    | .error e => e.message ≠ "" := by
  by_cases hv : isValidCommitIdStr s = true
  · simp [mkCommitId, hv]
  · simp only [mkCommitId, hv]
    exact interp3_ne_empty _ _ _ (by decide)

/-- `Model.mkRefName` guarantees `isValidRefNameStr` on `.ok` and non-empty message on `.error`. -/
theorem mkRefName_spec (s : String) :
    match mkRefName s with
    | .ok r => isValidRefNameStr r.raw = true
    | .error e => e.message ≠ "" := by
  by_cases hv : isValidRefNameStr s = true
  · simp [mkRefName, hv]
  · simp only [mkRefName, hv]
    exact interp3_ne_empty _ _ _ (by decide)

/-- Lift `caps.env.listEnv` through `Impl.mkRawOpsM` preserving `GitHostState` and error invariants. -/
theorem mkRawOpsM_listEnv_step {W : Type} {proj : W → GitHostState}
    {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) :
    let r := ((Impl.mkRawOpsM caps).listEnv).run w
    allowedHostTransition (proj w) (proj r.2) ∧
    match r.1 with
    | .ok _ => True
    | .error e => e.kind = .commandFailed ∧ e.message ≠ "" := by
  have hStep := hCaps w (.env .listEnv) hwf
  simp only [execCapsStep, LeanSwe.EnvVars.Model.execPkgStep, stateM_map_run,
    allowedHostCapsStep, LeanSwe.EnvVars.Model.allowedPkgStep] at hStep
  rcases hStep with ⟨hw1, hw2, hProc, hEnvEq, _⟩
  dsimp only [Impl.mkRawOpsM]
  rw [stateM_bind_run]
  have hTrans : allowedHostTransition (proj w) (proj (caps.env.listEnv.run w).2) :=
    ⟨hw1, hw2, hEnvEq, by rw [hProc], by rw [hProc]; exact Nat.le_refl _⟩
  cases hr : (caps.env.listEnv.run w).1 with
  | ok env =>
    simp only [stateM_pure_run]
    exact ⟨hTrans, trivial⟩
  | error e =>
    simp only [stateM_pure_run]
    exact ⟨hTrans, trivial, (mapEnvVarsErrorImpl_spec e).2⟩

/-- Lift `caps.proc.run` through `Impl.mkRawOpsM.execGit` preserving `GitHostState` and error invariants. -/
theorem mkRawOpsM_execGit_step {W : Type} {proj : W → GitHostState}
    {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (envOverrides : Array (String × Option String)) (req : GitRawRequest)
    (w : W) (hwf : hostStepWf (proj w) = true) :
    let r := ((Impl.mkRawOpsM caps).execGit envOverrides req).run w
    allowedHostTransition (proj w) (proj r.2) ∧
    match r.1 with
    | .ok _ => True
    | .error e =>
      (e.kind = .timeout ∨ e.kind = .invalidInput ∨ e.kind = .commandFailed) ∧
      e.message ≠ "" := by
  let execReq : ExecRequest :=
    { program := "git"
      args := req.args
      cwd := req.cwd
      env := envOverrides
      inheritEnv := true
      stdin := req.stdin
      timeoutMs := req.timeoutMs
      maxOutputBytes := req.maxOutputBytes }
  have hStep := hCaps w (.proc (.run execReq)) hwf
  simp only [execCapsStep, LeanSwe.Process.Model.execPkgStep, stateM_map_run,
    allowedHostCapsStep, LeanSwe.Process.Model.allowedPkgStep] at hStep
  rcases hStep with ⟨hw1, hw2, hEnvEq, _, _, hRun⟩
  dsimp only [Impl.mkRawOpsM]
  rw [stateM_bind_run]
  have hTrans : allowedHostTransition (proj w) (proj ((caps.proc.run execReq).run w).2) := by
    unfold LeanSwe.Process.Model.allowedPkgRun at hRun
    cases hVal : LeanSwe.Process.Model.validateRequestModel execReq with
    | error _ =>
      rw [hVal] at hRun
      rcases hRun with ⟨_, hEq⟩
      exact ⟨hw1, hw2, hEnvEq, by rw [hEq], by rw [hEq]; exact Nat.le_refl _⟩
    | ok _ =>
      rw [hVal] at hRun
      rcases hRun with ⟨hAct, hNext, _⟩
      refine ⟨hw1, hw2, hEnvEq, hAct, ?_⟩
      rcases hNext with hEq | hSucc
      · rw [hEq]; exact Nat.le_refl _
      · rw [hSucc]; exact Nat.le_succ _
  cases hr : ((caps.proc.run execReq).run w).1 with
  | ok res =>
    simp only [stateM_pure_run]
    exact ⟨hTrans, trivial⟩
  | error e =>
    simp only [stateM_pure_run]
    exact ⟨hTrans, mapProcessErrorImpl_spec (req.args[0]?.getD "git") e⟩

/-- Step contract for `Impl.runGitRaw (Impl.mkRawOpsM caps)`. -/
theorem runGitRaw_caps_step {W : Type} {proj : W → GitHostState}
    {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (req : GitRawRequest) (w : W) (hwf : hostStepWf (proj w) = true) :
    let r := (Impl.runGitRaw (Impl.mkRawOpsM caps) req).run w
    allowedHostTransition (proj w) (proj r.2) ∧
    match r.1 with
    | .ok _ => True
    | .error e =>
      e.message ≠ "" ∧
      e.kind ≠ .notARepo ∧
      e.kind ≠ .parseError ∧
      (req.cwd = none → e.kind ≠ .invalidPath) := by
  unfold Impl.runGitRaw
  cases hCwd : Impl.validateCwd? req.cwd with
  | error e =>
    simp only [stateM_pure_run]
    refine ⟨allowedHostTransition_refl hwf, ?_⟩
    cases hq : req.cwd with
    | none => simp [Impl.validateCwd?, hq] at hCwd
    | some p =>
      simp only [Impl.validateCwd?, hq] at hCwd
      split at hCwd
      · cases hCwd
      · cases hCwd
        exact ⟨by decide, by decide, by decide, fun h => nomatch h⟩
  | ok _ =>
    cases hExt : Impl.validateExtraEnv req.extraEnv with
    | error e =>
      simp only [stateM_pure_run]
      refine ⟨allowedHostTransition_refl hwf, ?_⟩
      unfold Impl.validateExtraEnv at hExt
      split at hExt
      · cases hExt
      · cases hExt; exact ⟨by decide, by decide, by decide, fun _ => by decide⟩
    | ok _ =>
      dsimp only
      split
      · simp only [stateM_pure_run]
        exact ⟨allowedHostTransition_refl hwf, by decide, by decide, by decide, fun _ => by decide⟩
      · rw [stateM_bind_run]
        have hEnv := mkRawOpsM_listEnv_step hCaps w hwf
        dsimp only at hEnv
        cases hEnvRes : ((Impl.mkRawOpsM caps).listEnv.run w).1 with
        | error e =>
          rw [hEnvRes] at hEnv
          simp only [stateM_pure_run]
          exact ⟨hEnv.1, hEnv.2.2, by rw [hEnv.2.1]; decide, by rw [hEnv.2.1]; decide,
            fun _ => by rw [hEnv.2.1]; decide⟩
        | ok inherited =>
          have hExec := mkRawOpsM_execGit_step hCaps (Impl.cleanGitEnvImpl inherited req.extraEnv) req
            ((Impl.mkRawOpsM caps).listEnv.run w).2 hEnv.1.2.1
          dsimp only at hExec
          have hTrans := allowedHostTransition_trans hEnv.1 hExec.1
          dsimp only
          cases hExRes : (((Impl.mkRawOpsM caps).execGit (Impl.cleanGitEnvImpl inherited req.extraEnv) req).run
              ((Impl.mkRawOpsM caps).listEnv.run w).2).1 with
          | ok _ => exact ⟨hTrans, trivial⟩
          | error e =>
            rw [hExRes] at hExec
            refine ⟨hTrans, hExec.2.2, ?_, ?_, ?_⟩
            · rcases hExec.2.1 with hk | hk | hk <;> rw [hk] <;> decide
            · rcases hExec.2.1 with hk | hk | hk <;> rw [hk] <;> decide
            · intro _; rcases hExec.2.1 with hk | hk | hk <;> rw [hk] <;> decide

/-- Step contract for `Impl.runGitChecked (Impl.mkRawOpsM caps)`. -/
theorem runGitChecked_caps_step {W : Type} {proj : W → GitHostState}
    {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (cmd : String) (req : GitRawRequest) (w : W) (hwf : hostStepWf (proj w) = true) :
    let r := (Impl.runGitChecked (Impl.mkRawOpsM caps) cmd req).run w
    allowedHostTransition (proj w) (proj r.2) ∧
    match r.1 with
    | .ok _ => True
    | .error e =>
      e.message ≠ "" ∧
      e.kind ≠ .parseError ∧
      (req.cwd = none → e.kind ≠ .invalidPath) := by
  unfold Impl.runGitChecked
  rw [stateM_bind_run]
  have hRaw := runGitRaw_caps_step hCaps req w hwf
  dsimp only at hRaw
  cases hRes : ((Impl.runGitRaw (Impl.mkRawOpsM caps) req).run w).1 with
  | error e =>
    rw [hRes] at hRaw
    simp only [stateM_pure_run]
    exact ⟨hRaw.1, hRaw.2.1, hRaw.2.2.2.1, hRaw.2.2.2.2⟩
  | ok out =>
    dsimp only
    split
    · simp only [stateM_pure_run]
      exact ⟨hRaw.1, trivial⟩
    · simp only [stateM_pure_run]
      have hc := classifyError_spec cmd out
      exact ⟨hRaw.1, hc.1, hc.2.2, fun _ => hc.2.1⟩

end LeanSwe.Git.Proofs
