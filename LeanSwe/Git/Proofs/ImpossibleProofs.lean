import Core.Assumptions
import LeanSwe.EnvVars.Proofs
import LeanSwe.Process.Proofs.EndToEnd
import LeanSwe.Process.Impl
import LeanSwe.Process.Interface
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open LeanSwe.Git

private theorem io_bind_ok {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

private theorem envvars_listEnv_never_throws (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.EnvVars.listEnv w = EST.Out.ok res w' := by
  have h := LeanSwe.EnvVars.Proofs.envvars_listEnv_never_notFound w
  unfold Core.NeverErrorKindIO at h
  cases hr : LeanSwe.EnvVars.listEnv w with
  | ok res w' => exact ⟨res, w', rfl⟩
  | error e w' => rw [hr] at h; exact False.elim h

private theorem process_run_never_throws (req : LeanSwe.Process.ExecRequest)
    (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.run req w = EST.Out.ok res w' :=
  LeanSwe.Process.Proofs.process_run_never_throws req w

private theorem defaultRawOps_listEnv_res (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.defaultRawOps.listEnv w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind = .commandFailed := by
  dsimp only [LeanSwe.Git.defaultRawOps]
  rcases envvars_listEnv_never_throws w with ⟨res, w', hw⟩
  rw [io_bind_ok _ _ _ hw]
  cases res with
  | ok env => exact ⟨.ok env, w', rfl, fun _ h => by cases h⟩
  | error e => exact ⟨.error (LeanSwe.Git.mapEnvVarsError e), w', rfl, fun _ h => by cases h; rfl⟩

private theorem mapProcessError_kinds (cmd : String) (e : LeanSwe.Process.ProcessError) :
    (LeanSwe.Git.mapProcessError cmd e).kind = .timeout ∨
    (LeanSwe.Git.mapProcessError cmd e).kind = .invalidInput ∨
    (LeanSwe.Git.mapProcessError cmd e).kind = .commandFailed := by
  dsimp only [LeanSwe.Git.mapProcessError]
  cases e.kind <;> simp

private theorem defaultRawOps_execGit_res (envOverrides : Array (String × Option String))
    (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.defaultRawOps.execGit envOverrides req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        e.kind = .timeout ∨ e.kind = .invalidInput ∨ e.kind = .commandFailed := by
  dsimp only [LeanSwe.Git.defaultRawOps]
  rcases process_run_never_throws
      { program := "git", args := req.args, cwd := req.cwd, env := envOverrides,
        stdin := req.stdin, timeoutMs := req.timeoutMs, maxOutputBytes := req.maxOutputBytes } w with ⟨res, w', hw⟩
  rw [io_bind_ok _ _ _ hw]
  cases res with
  | ok out => exact ⟨_, w', rfl, fun _ h => by cases h⟩
  | error e =>
    refine ⟨_, w', rfl, fun _ h => ?_⟩
    cases h
    exact mapProcessError_kinds (req.args[0]?.getD "git") e

private theorem runGitRaw_res (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.Impl.runGitRaw LeanSwe.Git.defaultRawOps req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        (e.kind = .invalidPath ∧ req.cwd.isSome = true) ∨
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
      · cases hcwd; exact Or.inl ⟨rfl, rfl⟩
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
      · rcases defaultRawOps_listEnv_res w with ⟨renv, w1, hw1, hkenv⟩
        rw [io_bind_ok _ _ _ hw1]
        cases renv with
        | error e =>
          refine ⟨_, w1, rfl, fun _ he => ?_⟩
          cases he
          exact Or.inr (Or.inr (Or.inr (hkenv e rfl)))
        | ok inherited =>
          rcases defaultRawOps_execGit_res (LeanSwe.Git.Model.cleanGitEnv inherited req.extraEnv) req w1 with
            ⟨re, w2, hw2, hke⟩
          exact ⟨re, w2, hw2, fun e he => by
            rcases hke e he with h | h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h))⟩

private theorem classifyError_kinds (cmd : String) (out : GitRawOutput) :
    (LeanSwe.Git.Impl.classifyError cmd out).kind ≠ .invalidPath ∧
    (LeanSwe.Git.Impl.classifyError cmd out).kind ≠ .parseError := by
  dsimp only [LeanSwe.Git.Impl.classifyError]
  repeat' (split; try exact ⟨by decide, by decide⟩)
  exact ⟨by decide, by decide⟩

private theorem runGitChecked_res (cmd : String) (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps cmd req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        (req.cwd = none → e.kind ≠ .invalidPath) ∧
        e.kind ≠ .parseError := by
  unfold LeanSwe.Git.Impl.runGitChecked
  rcases runGitRaw_res req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e =>
    dsimp only
    refine ⟨_, w1, rfl, fun _ he => ?_⟩
    cases he
    rcases hkr e rfl with ⟨h1, h2⟩ | h | h | h
    · exact ⟨fun hnone => by simp [hnone] at h2, by rw [h1]; decide⟩
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

private theorem bind_runGitChecked_never_parseError (cmd : String) (req : GitRawRequest)
    (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps cmd req >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ())) w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .parseError := by
  rcases runGitChecked_res cmd req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e => exact ⟨_, w1, rfl, fun _ he => by cases he; exact (hkr e rfl).2⟩
  | ok _ => exact ⟨_, w1, rfl, fun _ h => by cases h⟩

private theorem bind_runGitChecked_no_cwd (cmd : String) (req : GitRawRequest)
    (hcwd : req.cwd = none) (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps cmd req >>= fun r =>
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
    exact ⟨(hkr e rfl).1 hcwd, (hkr e rfl).2⟩
  | ok _ => exact ⟨_, w1, rfl, fun _ h => by cases h⟩

private theorem neverErrorKindIO_of_ok {α : Type} (kind : GitErrorKind)
    (act : IO (Except GitError α)) (w : Void IO.RealWorld)
    (h : ∃ res w', act w = EST.Out.ok res w' ∧ ∀ e, res = .error e → e.kind ≠ kind) :
    Core.NeverErrorKindIO GitError.kind kind act w := by
  rcases h with ⟨res, w', hw, hk⟩
  unfold Core.NeverErrorKindIO
  rw [hw]
  cases res with
  | ok _ => trivial
  | error e => exact hk e rfl

private theorem validateRepoPath_never (repoPath : String) (e : GitError)
    (h : LeanSwe.Git.Impl.validateRepoPath repoPath = .error e) :
    e.kind = .invalidPath := by
  unfold LeanSwe.Git.Impl.validateRepoPath at h
  split at h
  · cases h
  · cases h; rfl

private theorem isRepo_res (repoPath : String) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.isRepo repoPath w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .notARepo ∧ e.kind ≠ .parseError := by
  rw [show LeanSwe.Git.isRepo repoPath = LeanSwe.Git.Impl.isRepoImpl LeanSwe.Git.defaultRawOps repoPath from rfl]
  unfold LeanSwe.Git.Impl.isRepoImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he
    have hk := validateRepoPath_never repoPath e hv
    rw [hk]
    exact ⟨by decide, by decide⟩
  | ok _ =>
    dsimp only
    rcases runGitRaw_res { cwd := some repoPath, args := #["rev-parse", "--git-dir"] } w with
      ⟨r, w1, hw1, hkr⟩
    rw [io_bind_ok _ _ _ hw1]
    cases r with
    | error e =>
      dsimp only
      refine ⟨_, w1, rfl, fun _ he => ?_⟩
      cases he
      rcases hkr e rfl with ⟨h, _⟩ | h | h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩
    | ok out =>
      dsimp only
      split
      · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
      · split
        · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
        · refine ⟨_, w1, rfl, fun e he => ?_⟩
          rw [← Except.error.inj he]
          rename_i hne
          have hk := classifyError_kinds "rev-parse" out
          refine ⟨?_, hk.2⟩
          intro heq
          apply hne
          simp [heq]
          decide

/-- `Git.isRepo` handles `notARepo` by returning `Ok false`, so it never fails with `.notARepo`. -/
theorem git_isRepo_never_notARepo (repoPath : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .notARepo (Git.isRepo repoPath) w :=
  neverErrorKindIO_of_ok .notARepo (Git.isRepo repoPath) w (by
    rcases isRepo_res repoPath w with ⟨res, w', hw, hk⟩
    exact ⟨res, w', hw, fun e he => (hk e he).1⟩)

/-- `Git.isRepo` never fails with `.parseError`. -/
theorem git_isRepo_never_parseError (repoPath : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.isRepo repoPath) w :=
  neverErrorKindIO_of_ok .parseError (Git.isRepo repoPath) w (by
    rcases isRepo_res repoPath w with ⟨res, w', hw, hk⟩
    exact ⟨res, w', hw, fun e he => (hk e he).2⟩)

/-- `Git.isAncestor` never fails with `.parseError`. -/
theorem git_isAncestor_never_parseError (repoPath : String) (ancestor descendant : CommitId)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.isAncestor repoPath ancestor descendant) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.isAncestor repoPath ancestor descendant =
      LeanSwe.Git.Impl.isAncestorImpl LeanSwe.Git.defaultRawOps repoPath ancestor descendant from rfl]
  unfold LeanSwe.Git.Impl.isAncestorImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · rcases runGitRaw_res { cwd := some repoPath, args := #["merge-base", "--is-ancestor", ancestor.hex, descendant.hex] } w with
        ⟨r, w1, hw1, hkr⟩
      rw [io_bind_ok _ _ _ hw1]
      cases r with
      | error e =>
        dsimp only
        refine ⟨_, w1, rfl, fun _ he => ?_⟩
        cases he
        rcases hkr e rfl with ⟨h, _⟩ | h | h | h <;> rw [h] <;> decide
      | ok out =>
        dsimp only
        split
        · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
        · split
          · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
          · refine ⟨_, w1, rfl, fun e he => ?_⟩
            rw [← Except.error.inj he]
            exact (classifyError_kinds "merge-base" out).2

/-- `Git.init` never fails with `.parseError`. -/
theorem git_init_never_parseError (path : String) (bare : Bool) (initialBranch? : Option RefName)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.init path bare initialBranch?) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.init path bare initialBranch? =
      LeanSwe.Git.Impl.initImpl LeanSwe.Git.defaultRawOps path bare initialBranch? from rfl]
  unfold LeanSwe.Git.Impl.initImpl
  split
  · refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; dsimp only; decide
  · cases initialBranch? with
    | none =>
      dsimp only
      exact bind_runGitChecked_never_parseError "init" _ w
    | some b =>
      dsimp only
      split
      · dsimp only
        exact bind_runGitChecked_never_parseError "init" _ w
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; dsimp only; decide

private theorem clone_io_cases (source target : String) (opts : CloneOptions) :
    (Git.clone source target opts =
      pure (Except.error { kind := .invalidInput, message := "invalid clone source or target" })) ∨
    (Git.clone source target opts =
      pure (Except.error { kind := .invalidInput, message := "clone depth must be positive" })) ∨
    (∃ (b : String), Git.clone source target opts = pure (Except.error ({ kind := .invalidRef, message := toString "invalid clone branch: '" ++ toString b ++ toString "'" } : GitError))) ∨
    (∃ args, Git.clone source target opts =
      (LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps "clone" { args := args } >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ()))) := by
  dsimp only [Git.clone, LeanSwe.Git.defaultApi, LeanSwe.Git.Impl.mkApiM]
  unfold LeanSwe.Git.Impl.cloneImpl
  split
  · exact Or.inl rfl
  · cases hd : opts.depth? with
    | none =>
      dsimp only
      cases opts.branch? with
      | none => exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
      | some b =>
        dsimp only
        by_cases hb : LeanSwe.Git.Model.isValidRefNameStr b = true
        · simp [hb]; exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
        · simp [hb]; exact Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))
    | some d =>
      cases d with
      | zero => exact Or.inr (Or.inl rfl)
      | succ n =>
        dsimp only
        cases opts.branch? with
        | none => exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
        | some b =>
          dsimp only
          by_cases hb : LeanSwe.Git.Model.isValidRefNameStr b = true
          · simp [hb]; exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
          · simp [hb]; exact Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))

private theorem clone_res (source target : String) (opts : CloneOptions)
    (w : Void IO.RealWorld) :
    ∃ res w', Git.clone source target opts w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .invalidPath ∧ e.kind ≠ .parseError := by
  rcases clone_io_cases source target opts with h | h | ⟨b, h⟩ | ⟨args, h⟩
  · rw [h]; refine ⟨_, w, rfl, fun _ he => ?_⟩; cases he; dsimp only; exact ⟨by decide, by decide⟩
  · rw [h]; refine ⟨_, w, rfl, fun _ he => ?_⟩; cases he; dsimp only; exact ⟨by decide, by decide⟩
  · rw [h]; refine ⟨_, w, rfl, fun _ he => ?_⟩; cases he; dsimp only; exact ⟨by decide, by decide⟩
  · rw [h]; exact bind_runGitChecked_no_cwd "clone" _ rfl w

/-- `Git.clone` does not run with a `cwd` and maps path checks to `.invalidInput`, so it never fails with `.invalidPath`. -/
theorem git_clone_never_invalidPath (source target : String) (opts : CloneOptions)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .invalidPath (Git.clone source target opts) w :=
  neverErrorKindIO_of_ok .invalidPath (Git.clone source target opts) w (by
    rcases clone_res source target opts w with ⟨res, w', hw, hk⟩
    exact ⟨res, w', hw, fun e he => (hk e he).1⟩)

/-- `Git.clone` never fails with `.parseError`. -/
theorem git_clone_never_parseError (source target : String) (opts : CloneOptions)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.clone source target opts) w :=
  neverErrorKindIO_of_ok .parseError (Git.clone source target opts) w (by
    rcases clone_res source target opts w with ⟨res, w', hw, hk⟩
    exact ⟨res, w', hw, fun e he => (hk e he).2⟩)

/-- `Git.add` never fails with `.parseError`. -/
theorem git_add_never_parseError (repoPath : String) (paths : Array String) (all : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.add repoPath paths all) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.add repoPath paths all =
      LeanSwe.Git.Impl.addImpl LeanSwe.Git.defaultRawOps repoPath paths all from rfl]
  unfold LeanSwe.Git.Impl.addImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · split
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; dsimp only; decide
      · exact bind_runGitChecked_never_parseError "add" _ w

/-- `Git.createBranch` never fails with `.parseError`. -/
theorem git_createBranch_never_parseError (repoPath : String) (branch : RefName)
    (startPoint? : Option String) (force : Bool) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError
      (Git.createBranch repoPath branch startPoint? force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.createBranch repoPath branch startPoint? force =
      LeanSwe.Git.Impl.createBranchImpl LeanSwe.Git.defaultRawOps repoPath branch startPoint? force from rfl]
  unfold LeanSwe.Git.Impl.createBranchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · cases startPoint? with
      | none =>
        dsimp only
        exact bind_runGitChecked_never_parseError "branch" _ w
      | some sp =>
        dsimp only
        split
        · dsimp only
          exact bind_runGitChecked_never_parseError "branch" _ w
        · refine ⟨_, w, rfl, fun _ he => ?_⟩
          cases he; dsimp only; decide

/-- `Git.deleteBranch` never fails with `.parseError`. -/
theorem git_deleteBranch_never_parseError (repoPath : String) (branch : RefName) (force : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError
      (Git.deleteBranch repoPath branch force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.deleteBranch repoPath branch force =
      LeanSwe.Git.Impl.deleteBranchImpl LeanSwe.Git.defaultRawOps repoPath branch force from rfl]
  unfold LeanSwe.Git.Impl.deleteBranchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · exact bind_runGitChecked_never_parseError "branch" _ w

/-- `Git.checkout` never fails with `.parseError`. -/
theorem git_checkout_never_parseError (repoPath : String) (target : CheckoutTarget) (force : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.checkout repoPath target force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.checkout repoPath target force =
      LeanSwe.Git.Impl.checkoutImpl LeanSwe.Git.defaultRawOps repoPath target force from rfl]
  unfold LeanSwe.Git.Impl.checkoutImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    cases target with
    | branch b =>
      dsimp only
      split
      · dsimp only
        exact bind_runGitChecked_never_parseError "checkout" _ w
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; dsimp only; decide
    | commit cid =>
      dsimp only
      split
      · dsimp only
        exact bind_runGitChecked_never_parseError "checkout" _ w
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; dsimp only; decide
    | ref spec =>
      dsimp only
      split
      · dsimp only
        exact bind_runGitChecked_never_parseError "checkout" _ w
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; dsimp only; decide

/-- `Git.switch` never fails with `.parseError`. -/
theorem git_switch_never_parseError (repoPath : String) (branch : RefName) (create : Bool)
    (startPoint? : Option String) (force : Bool) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError
      (Git.switch repoPath branch create startPoint? force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.switch repoPath branch create startPoint? force =
      LeanSwe.Git.Impl.switchImpl LeanSwe.Git.defaultRawOps repoPath branch create startPoint? force from rfl]
  unfold LeanSwe.Git.Impl.switchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · split
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; dsimp only; decide
      · cases startPoint? with
        | none =>
          dsimp only
          exact bind_runGitChecked_never_parseError "switch" _ w
        | some sp =>
          dsimp only
          split
          · dsimp only
            exact bind_runGitChecked_never_parseError "switch" _ w
          · refine ⟨_, w, rfl, fun _ he => ?_⟩
            cases he; dsimp only; decide

/-- `Git.reset` never fails with `.parseError`. -/
theorem git_reset_never_parseError (repoPath : String) (mode : ResetMode) (rev : String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.reset repoPath mode rev) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.reset repoPath mode rev =
      LeanSwe.Git.Impl.resetImpl LeanSwe.Git.defaultRawOps repoPath mode rev from rfl]
  unfold LeanSwe.Git.Impl.resetImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · exact bind_runGitChecked_never_parseError "reset" _ w

/-- `Git.fetch` never fails with `.parseError`. -/
theorem git_fetch_never_parseError (repoPath remote : String) (refspec? : Option String)
    (prune : Bool) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.fetch repoPath remote refspec? prune) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.fetch repoPath remote refspec? prune =
      LeanSwe.Git.Impl.fetchImpl LeanSwe.Git.defaultRawOps repoPath remote refspec? prune from rfl]
  unfold LeanSwe.Git.Impl.fetchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · cases refspec? with
      | none =>
        dsimp only
        exact bind_runGitChecked_never_parseError "fetch" _ w
      | some r =>
        dsimp only
        split
        · dsimp only
          exact bind_runGitChecked_never_parseError "fetch" _ w
        · refine ⟨_, w, rfl, fun _ he => ?_⟩
          cases he; dsimp only; decide

/-- `Git.worktreeAdd` never fails with `.parseError`. -/
theorem git_worktreeAdd_never_parseError (repoPath : String) (opts : WorktreeAddOptions)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.worktreeAdd repoPath opts) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.worktreeAdd repoPath opts =
      LeanSwe.Git.Impl.worktreeAddImpl LeanSwe.Git.defaultRawOps repoPath opts from rfl]
  unfold LeanSwe.Git.Impl.worktreeAddImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · split
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; dsimp only; decide
      · cases opts.newBranch? with
        | none =>
          dsimp only
          cases opts.target? with
          | none =>
            dsimp only
            exact bind_runGitChecked_never_parseError "worktree" _ w
          | some t =>
            dsimp only
            split
            · dsimp only
              exact bind_runGitChecked_never_parseError "worktree" _ w
            · refine ⟨_, w, rfl, fun _ he => ?_⟩
              cases he; dsimp only; decide
        | some b =>
          dsimp only
          split
          · dsimp only
            cases opts.target? with
            | none =>
              dsimp only
              exact bind_runGitChecked_never_parseError "worktree" _ w
            | some t =>
              dsimp only
              split
              · dsimp only
                exact bind_runGitChecked_never_parseError "worktree" _ w
              · refine ⟨_, w, rfl, fun _ he => ?_⟩
                cases he; dsimp only; decide
          · refine ⟨_, w, rfl, fun _ he => ?_⟩
            cases he; dsimp only; decide

/-- `Git.worktreeRemove` never fails with `.parseError`. -/
theorem git_worktreeRemove_never_parseError (repoPath wtPath : String) (force : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.worktreeRemove repoPath wtPath force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.worktreeRemove repoPath wtPath force =
      LeanSwe.Git.Impl.worktreeRemoveImpl LeanSwe.Git.defaultRawOps repoPath wtPath force from rfl]
  unfold LeanSwe.Git.Impl.worktreeRemoveImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he; rw [validateRepoPath_never repoPath e hv]; decide
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · exact bind_runGitChecked_never_parseError "worktree" _ w

end LeanSwe.Git.Proofs
