import Core.Assumptions
import LeanSwe.EnvVars.Interface
import LeanSwe.Process.Interface
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open LeanSwe.Git

/-- Unfold `IO` pure on a world token. -/
theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

/-- Unfold `IO` bind on a world token. -/
theorem io_bind_eq {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld) :
    (x >>= f) w =
      match x w with
      | EST.Out.ok a w' => f a w'
      | EST.Out.error e w' => EST.Out.error e w' := by
  change EST.bind x f w = _
  unfold EST.bind
  cases x w <;> rfl

/-- Simplify `IO` bind when the first action succeeds with `EST.Out.ok`. -/
theorem io_bind_ok {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

/-- `LeanSwe.EnvVars.defaultApi.listEnv` never throws an uncaught `IO.Error`. -/
theorem envvars_listEnv_never_throws (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.EnvVars.defaultApi.listEnv w = EST.Out.ok res w' :=
  LeanSwe.EnvVars.defaultApi_listEnv_never_throws w

/-- `LeanSwe.Process.defaultApi.run` never throws an uncaught `IO.Error`. -/
theorem process_run_never_throws (req : LeanSwe.Process.ExecRequest)
    (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.defaultApi.run req w = EST.Out.ok res w' :=
  LeanSwe.Process.defaultApi_run_never_throws req w

/-- `Git.defaultOps.listEnv` never throws and maps all errors to `.commandFailed`. -/
theorem defaultOps_listEnv_res (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.defaultOps.listEnv w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind = .commandFailed := by
  dsimp only [LeanSwe.Git.defaultOps, LeanSwe.Git.Impl.mkRawOpsM]
  rcases envvars_listEnv_never_throws w with ⟨res, w', hw⟩
  rw [io_bind_ok _ _ _ hw]
  cases res with
  | ok env => exact ⟨.ok env, w', rfl, fun _ h => by cases h⟩
  | error e => exact ⟨.error (LeanSwe.Git.Impl.mapEnvVarsErrorImpl e), w', rfl, fun _ h => by cases h; rfl⟩

/-- `Impl.mapProcessErrorImpl` produces only `.timeout`, `.invalidInput`, or `.commandFailed`. -/
theorem mapProcessErrorImpl_kinds (cmd : String) (e : LeanSwe.Process.ProcessError) :
    (LeanSwe.Git.Impl.mapProcessErrorImpl cmd e).kind = .timeout ∨
    (LeanSwe.Git.Impl.mapProcessErrorImpl cmd e).kind = .invalidInput ∨
    (LeanSwe.Git.Impl.mapProcessErrorImpl cmd e).kind = .commandFailed := by
  dsimp only [LeanSwe.Git.Impl.mapProcessErrorImpl]
  cases e.kind <;> simp

/-- `Git.defaultOps.execGit` never throws and restricts errors to `.timeout`, `.invalidInput`, or `.commandFailed`. -/
theorem defaultOps_execGit_res (envOverrides : Array (String × Option String))
    (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.defaultOps.execGit envOverrides req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        e.kind = .timeout ∨ e.kind = .invalidInput ∨ e.kind = .commandFailed := by
  dsimp only [LeanSwe.Git.defaultOps, LeanSwe.Git.Impl.mkRawOpsM]
  rcases process_run_never_throws
      { program := "git", args := req.args, cwd := req.cwd, env := envOverrides,
        stdin := req.stdin, timeoutMs := req.timeoutMs, maxOutputBytes := req.maxOutputBytes } w with ⟨res, w', hw⟩
  rw [io_bind_ok _ _ _ hw]
  cases res with
  | ok out => exact ⟨_, w', rfl, fun _ h => by cases h⟩
  | error e =>
    refine ⟨_, w', rfl, fun _ h => ?_⟩
    cases h
    exact mapProcessErrorImpl_kinds (req.args[0]?.getD "git") e

/-- `Impl.runGitRaw Git.defaultOps` never throws and bounds error kinds cleanly. -/
theorem runGitRaw_res (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.Impl.runGitRaw LeanSwe.Git.defaultOps req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        (e.kind = .invalidPath ∧ ∃ p, req.cwd = some p ∧ LeanSwe.Git.Model.isValidPathArg p = false) ∨
        e.kind = .invalidInput ∨
        e.kind = .timeout ∨
        e.kind = .commandFailed := by
  unfold LeanSwe.Git.Impl.runGitRaw
  cases hcwd : LeanSwe.Git.Impl.validateCwd? req.cwd with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he
    cases hreq : req.cwd with
    | none => simp [LeanSwe.Git.Impl.validateCwd?, hreq] at hcwd
    | some p =>
      simp only [LeanSwe.Git.Impl.validateCwd?, hreq] at hcwd
      split at hcwd
      · cases hcwd
      · cases hcwd
        rename_i hinv
        have hPathEq : LeanSwe.Git.Impl.isValidPathArgImpl p = LeanSwe.Git.Model.isValidPathArg p := by
          unfold LeanSwe.Git.Impl.isValidPathArgImpl LeanSwe.Git.Model.isValidPathArg
          have hNul : ∀ cs, LeanSwe.Git.Impl.hasNulCharImpl cs = LeanSwe.Git.Model.hasNulChar cs := by
            intro cs; induction cs with | nil => rfl | cons c r ih => simp [LeanSwe.Git.Impl.hasNulCharImpl, LeanSwe.Git.Model.hasNulChar, ih]
          dsimp only
          rw [hNul]
        rw [hPathEq] at hinv
        have hinvF : LeanSwe.Git.Model.isValidPathArg p = false := Bool.eq_false_iff.mpr hinv
        exact Or.inl ⟨rfl, p, rfl, hinvF⟩
  | ok _ =>
    dsimp only
    cases henv : LeanSwe.Git.Impl.validateExtraEnv req.extraEnv with
    | error e =>
      dsimp only
      refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he
      unfold LeanSwe.Git.Impl.validateExtraEnv at henv
      split at henv
      · cases henv
      · cases henv; exact Or.inr (Or.inl rfl)
    | ok _ =>
      dsimp only
      split
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; exact Or.inr (Or.inl rfl)
      · rcases defaultOps_listEnv_res w with ⟨renv, w1, hw1, hkenv⟩
        rw [io_bind_ok _ _ _ hw1]
        cases renv with
        | error e =>
          refine ⟨_, w1, rfl, fun _ he => ?_⟩
          cases he
          exact Or.inr (Or.inr (Or.inr (hkenv e rfl)))
        | ok inherited =>
          rcases defaultOps_execGit_res (LeanSwe.Git.Impl.cleanGitEnvImpl inherited req.extraEnv) req w1 with
            ⟨re, w2, hw2, hke⟩
          exact ⟨re, w2, hw2, fun e he => by
            rcases hke e he with h | h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h))⟩

/-- `Impl.classifyError` never produces `.invalidPath` or `.parseError`. -/
theorem classifyError_kinds (cmd : String) (out : GitRawOutput) :
    (LeanSwe.Git.Impl.classifyError cmd out).kind ≠ .invalidPath ∧
    (LeanSwe.Git.Impl.classifyError cmd out).kind ≠ .parseError := by
  dsimp only [LeanSwe.Git.Impl.classifyError]
  by_cases hBlank : (LeanSwe.Git.Impl.trimAsciiWhitespace (LeanSwe.Git.Impl.decodeUtf8Lossy out.stderr)).isEmpty = true
  · simp only [hBlank, ↓reduceIte]
    repeat' (split; try exact ⟨by decide, by decide⟩)
    exact ⟨by decide, by decide⟩
  · simp only [hBlank, Bool.false_eq_true, ↓reduceIte]
    repeat' (split; try exact ⟨by decide, by decide⟩)
    exact ⟨by decide, by decide⟩

/-- `Impl.runGitChecked Git.defaultOps` never throws and never produces `.parseError` (nor `.invalidPath` on valid `cwd`). -/
theorem runGitChecked_res (cmd : String) (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultOps cmd req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        (req.cwd.elim True (fun p => LeanSwe.Git.Model.isValidPathArg p = true) → e.kind ≠ .invalidPath) ∧
        e.kind ≠ .parseError := by
  unfold LeanSwe.Git.Impl.runGitChecked
  rcases runGitRaw_res req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e =>
    dsimp only
    refine ⟨_, w1, rfl, fun _ he => ?_⟩
    cases he
    rcases hkr e rfl with ⟨h1, p, hp, hinv⟩ | h | h | h
    · refine ⟨fun hvalid => ?_, by rw [h1]; decide⟩
      simp [hp, hinv] at hvalid
    · exact ⟨fun _ => by rw [h]; decide, by rw [h]; decide⟩
    · exact ⟨fun _ => by rw [h]; decide, by rw [h]; decide⟩
    · exact ⟨fun _ => by rw [h]; decide, by rw [h]; decide⟩
  | ok out =>
    dsimp only
    split
    · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
    · refine ⟨_, w1, rfl, fun e he => ?_⟩
      rw [← Except.error.inj he]
      have hk := classifyError_kinds cmd out
      exact ⟨fun _ => hk.1, hk.2⟩

/-- Binding unit continuation after `runGitChecked` never throws or returns `.parseError`. -/
theorem bind_runGitChecked_never_parseError (cmd : String) (req : GitRawRequest)
    (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultOps cmd req >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ())) w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .parseError := by
  rcases runGitChecked_res cmd req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e => exact ⟨_, w1, rfl, fun _ he => by cases he; exact (hkr e rfl).2⟩
  | ok _ => exact ⟨_, w1, rfl, fun _ h => by cases h⟩

/-- Binding unit continuation after `runGitChecked` with `cwd = none` never throws or returns `.invalidPath`/`.parseError`. -/
theorem bind_runGitChecked_no_cwd (cmd : String) (req : GitRawRequest)
    (hcwd : req.cwd = none) (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultOps cmd req >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ())) w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .invalidPath ∧ e.kind ≠ .parseError := by
  rcases runGitChecked_res cmd req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e =>
    refine ⟨_, w1, rfl, fun _ he => ?_⟩
    cases he
    exact ⟨(hkr e rfl).1 (by simp [hcwd]), (hkr e rfl).2⟩
  | ok _ => exact ⟨_, w1, rfl, fun _ h => by cases h⟩

/-- Lift a non-throwing `EST.Out.ok` characterization into `Core.NeverErrorKindIO`. -/
theorem neverErrorKindIO_of_ok {α : Type} (kind : GitErrorKind)
    (act : IO (Except GitError α)) (w : Void IO.RealWorld)
    (h : ∃ res w', act w = EST.Out.ok res w' ∧ ∀ e, res = .error e → e.kind ≠ kind) :
    Core.NeverErrorKindIO GitError.kind kind act w := by
  rcases h with ⟨res, w', hw, hk⟩
  unfold Core.NeverErrorKindIO
  rw [hw]
  cases res with
  | ok _ => trivial
  | error e => exact hk e rfl

/-- `Model.validateFsPathArg` produces only `.invalidPath` or `.invalidInput`. -/
theorem validateFsPathArg_kinds (p : String) (e : GitError)
    (h : LeanSwe.Git.Model.validateFsPathArg p = .error e) :
    e.kind = .invalidPath ∨ e.kind = .invalidInput := by
  unfold LeanSwe.Git.Model.validateFsPathArg at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h; exact Or.inr rfl
    · cases h

/-- `Impl.validateRepoPath` never produces `.notARepo` or `.parseError`. -/
theorem validateRepoPath_never (repoPath : String) (e : GitError)
    (h : LeanSwe.Git.Impl.validateRepoPath repoPath = .error e) :
    e.kind ≠ .notARepo ∧ e.kind ≠ .parseError := by
  have hEq : LeanSwe.Git.Impl.validateRepoPath repoPath = LeanSwe.Git.Model.validateFsPathArg repoPath := by
    have hPathEq : LeanSwe.Git.Impl.isValidPathArgImpl repoPath = LeanSwe.Git.Model.isValidPathArg repoPath := by
      unfold LeanSwe.Git.Impl.isValidPathArgImpl LeanSwe.Git.Model.isValidPathArg
      have hNul : ∀ cs, LeanSwe.Git.Impl.hasNulCharImpl cs = LeanSwe.Git.Model.hasNulChar cs := by
        intro cs; induction cs with | nil => rfl | cons c r ih => simp [LeanSwe.Git.Impl.hasNulCharImpl, LeanSwe.Git.Model.hasNulChar, ih]
      dsimp only
      rw [hNul]
    unfold LeanSwe.Git.Impl.validateRepoPath LeanSwe.Git.Impl.validateFsPathArgImpl LeanSwe.Git.Model.validateFsPathArg
    rw [hPathEq]
  rw [hEq] at h
  rcases validateFsPathArg_kinds repoPath e h with hk | hk <;> rw [hk] <;> exact ⟨by decide, by decide⟩

/-- `Model.validateCloneEndpoint` produces only `.invalidInput`. -/
theorem validateCloneEndpoint_kind (p : String) (e : GitError)
    (h : LeanSwe.Git.Model.validateCloneEndpoint p = .error e) :
    e.kind = .invalidInput := by
  unfold LeanSwe.Git.Model.validateCloneEndpoint at h
  split at h
  · cases h; rfl
  · cases h

end LeanSwe.Git.Proofs
