import Core.Assumptions
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.Proofs.ImpossibleBase

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open LeanSwe.Git

private theorem isRepo_res (repoPath : String) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.isRepo repoPath w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .notARepo ∧ e.kind ≠ .parseError := by
  rw [show LeanSwe.Git.isRepo repoPath = LeanSwe.Git.Impl.isRepoImpl LeanSwe.Git.defaultOps repoPath from rfl]
  unfold LeanSwe.Git.Impl.isRepoImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact validateRepoPath_never repoPath e hv⟩
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
      LeanSwe.Git.Impl.isAncestorImpl LeanSwe.Git.defaultOps repoPath ancestor descendant from rfl]
  unfold LeanSwe.Git.Impl.isAncestorImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
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
      LeanSwe.Git.Impl.initImpl LeanSwe.Git.defaultOps path bare initialBranch? from rfl]
  unfold LeanSwe.Git.Impl.initImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath path with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never path e hv).2⟩
  | ok _ =>
    dsimp only
    let runAfter : Array String → IO (Except GitError Unit) := fun bArgs =>
      LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultOps "init"
        { cwd := none, args := #["init"] ++ (if bare then #["--bare"] else #[]) ++ bArgs ++ #["--", path] } >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ())
    have hrun : ∀ bArgs, ∃ res w', runAfter bArgs w = EST.Out.ok res w' ∧ ∀ e, res = .error e → e.kind ≠ .parseError := by
      intro bArgs
      exact bind_runGitChecked_never_parseError "init" _ w
    cases initialBranch? with
    | none => exact hrun #[]
    | some b =>
      dsimp only
      split
      · exact hrun #["-b", b.raw]
      · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

private theorem clone_res (source target : String) (opts : CloneOptions)
    (w : Void IO.RealWorld) :
    ∃ res w', Git.clone source target opts w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .invalidPath ∧ e.kind ≠ .parseError := by
  rw [show Git.clone source target opts =
      LeanSwe.Git.Impl.cloneImpl LeanSwe.Git.defaultOps source target opts from rfl]
  unfold LeanSwe.Git.Impl.cloneImpl
  cases hs : LeanSwe.Git.Model.validateCloneEndpoint source with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; rw [validateCloneEndpoint_kind source e hs]; exact ⟨by decide, by decide⟩⟩
  | ok _ =>
    cases ht : LeanSwe.Git.Model.validateCloneEndpoint target with
    | error e =>
      dsimp only
      exact ⟨_, w, rfl, fun _ he => by cases he; rw [validateCloneEndpoint_kind target e ht]; exact ⟨by decide, by decide⟩⟩
    | ok _ =>
      dsimp only
      let afterBranch : Array String → Array String → IO (Except GitError Unit) := fun depthArgs bArgs =>
        LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultOps "clone"
          { cwd := none, args := #["clone"] ++ (if opts.bare then #["--bare"] else #[]) ++
              (if opts.singleBranch then #["--single-branch"] else #[]) ++
              depthArgs ++ bArgs ++ #["--", source, target] } >>= fun r =>
          match r with
          | Except.error e => pure (Except.error e)
          | Except.ok _ => pure (Except.ok ())
      have hafter : ∀ depthArgs bArgs, ∃ res w', afterBranch depthArgs bArgs w = EST.Out.ok res w' ∧
          ∀ e, res = .error e → e.kind ≠ .invalidPath ∧ e.kind ≠ .parseError := by
        intro depthArgs bArgs
        exact bind_runGitChecked_no_cwd "clone" _ rfl w
      have hbody : ∀ depthArgs, ∃ res w',
          (match
              match opts.branch? with
              | none => Except.ok #[]
              | some b =>
                if LeanSwe.Git.Model.isValidRefNameStr b then Except.ok #["--branch", b]
                else Except.error ({ kind := GitErrorKind.invalidRef, message := s!"invalid clone branch: '{b}'" } : GitError) with
            | Except.error e => pure (Except.error e)
            | Except.ok bArgs => afterBranch depthArgs bArgs) w = EST.Out.ok res w' ∧
          ∀ e : GitError, res = Except.error e → e.kind ≠ GitErrorKind.invalidPath ∧ e.kind ≠ GitErrorKind.parseError := by
        intro depthArgs
        cases opts.branch? with
        | none => exact hafter depthArgs #[]
        | some b =>
          dsimp only
          split
          · exact hafter depthArgs #["--branch", b]
          · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; exact ⟨by decide, by decide⟩⟩
      cases hd : opts.depth? with
      | none => exact hbody #[]
      | some d =>
        cases d with
        | zero => exact ⟨_, w, rfl, fun _ he => by cases he; exact ⟨by decide, by decide⟩⟩
        | succ n => exact hbody #["--depth", toString (n + 1)]

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
      LeanSwe.Git.Impl.addImpl LeanSwe.Git.defaultOps repoPath paths all from rfl]
  unfold LeanSwe.Git.Impl.addImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; decide⟩
    · split
      · exact ⟨_, w, rfl, fun _ he => by cases he; decide⟩
      · exact bind_runGitChecked_never_parseError "add" _ w

/-- `Git.createBranch` never fails with `.parseError`. -/
theorem git_createBranch_never_parseError (repoPath : String) (branch : RefName)
    (startPoint? : Option String) (force : Bool) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError
      (Git.createBranch repoPath branch startPoint? force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.createBranch repoPath branch startPoint? force =
      LeanSwe.Git.Impl.createBranchImpl LeanSwe.Git.defaultOps repoPath branch startPoint? force from rfl]
  unfold LeanSwe.Git.Impl.createBranchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · cases startPoint? with
      | none =>
        dsimp only
        exact bind_runGitChecked_never_parseError "branch" _ w
      | some sp =>
        dsimp only
        split
        · exact bind_runGitChecked_never_parseError "branch" _ w
        · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.deleteBranch` never fails with `.parseError`. -/
theorem git_deleteBranch_never_parseError (repoPath : String) (branch : RefName) (force : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError
      (Git.deleteBranch repoPath branch force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.deleteBranch repoPath branch force =
      LeanSwe.Git.Impl.deleteBranchImpl LeanSwe.Git.defaultOps repoPath branch force from rfl]
  unfold LeanSwe.Git.Impl.deleteBranchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · exact bind_runGitChecked_never_parseError "branch" _ w

/-- `Git.checkout` never fails with `.parseError`. -/
theorem git_checkout_never_parseError (repoPath : String) (target : CheckoutTarget) (force : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.checkout repoPath target force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.checkout repoPath target force =
      LeanSwe.Git.Impl.checkoutImpl LeanSwe.Git.defaultOps repoPath target force from rfl]
  unfold LeanSwe.Git.Impl.checkoutImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    cases target with
    | branch b =>
      dsimp only
      split
      · exact bind_runGitChecked_never_parseError "checkout" _ w
      · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    | commit cid =>
      dsimp only
      split
      · exact bind_runGitChecked_never_parseError "checkout" _ w
      · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    | ref spec =>
      dsimp only
      split
      · exact bind_runGitChecked_never_parseError "checkout" _ w
      · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.switch` never fails with `.parseError`. -/
theorem git_switch_never_parseError (repoPath : String) (branch : RefName) (create : Bool)
    (startPoint? : Option String) (force : Bool) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError
      (Git.switch repoPath branch create startPoint? force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.switch repoPath branch create startPoint? force =
      LeanSwe.Git.Impl.switchImpl LeanSwe.Git.defaultOps repoPath branch create startPoint? force from rfl]
  unfold LeanSwe.Git.Impl.switchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · split
      · exact ⟨_, w, rfl, fun _ he => by cases he; decide⟩
      · cases startPoint? with
        | none =>
          dsimp only
          exact bind_runGitChecked_never_parseError "switch" _ w
        | some sp =>
          dsimp only
          split
          · exact bind_runGitChecked_never_parseError "switch" _ w
          · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.reset` never fails with `.parseError`. -/
theorem git_reset_never_parseError (repoPath : String) (mode : ResetMode) (rev : String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.reset repoPath mode rev) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.reset repoPath mode rev =
      LeanSwe.Git.Impl.resetImpl LeanSwe.Git.defaultOps repoPath mode rev from rfl]
  unfold LeanSwe.Git.Impl.resetImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · exact bind_runGitChecked_never_parseError "reset" _ w

/-- `Git.fetch` never fails with `.parseError`. -/
theorem git_fetch_never_parseError (repoPath remote : String) (refspec? : Option String)
    (prune : Bool) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.fetch repoPath remote refspec? prune) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.fetch repoPath remote refspec? prune =
      LeanSwe.Git.Impl.fetchImpl LeanSwe.Git.defaultOps repoPath remote refspec? prune from rfl]
  unfold LeanSwe.Git.Impl.fetchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · cases refspec? with
      | none =>
        dsimp only
        exact bind_runGitChecked_never_parseError "fetch" _ w
      | some r =>
        dsimp only
        split
        · exact bind_runGitChecked_never_parseError "fetch" _ w
        · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.worktreeAdd` never fails with `.parseError`. -/
theorem git_worktreeAdd_never_parseError (repoPath : String) (opts : WorktreeAddOptions)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.worktreeAdd repoPath opts) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.worktreeAdd repoPath opts =
      LeanSwe.Git.Impl.worktreeAddImpl LeanSwe.Git.defaultOps repoPath opts from rfl]
  unfold LeanSwe.Git.Impl.worktreeAddImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    cases hv2 : LeanSwe.Git.Impl.validateRepoPath opts.path with
    | error e =>
      dsimp only
      exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never opts.path e hv2).2⟩
    | ok _ =>
      dsimp only
      split
      · exact ⟨_, w, rfl, fun _ he => by cases he; decide⟩
      · have hAfter : ∀ (bArgs : Array String), ∃ res w',
            (match
                match opts.target? with
                | none => Except.ok #[]
                | some t =>
                  if LeanSwe.Git.Model.isValidStrictRevSpec t then Except.ok #[t]
                  else Except.error ({ kind := GitErrorKind.invalidInput, message := s!"invalid worktree target: '{t}'" } : GitError) with
              | Except.error e => pure (Except.error e)
              | Except.ok tArgs => do
                let args :=
                  #["worktree", "add"] ++
                  (if opts.force then #["--force"] else #[]) ++
                  (if opts.detach then #["--detach"] else #[]) ++
                  bArgs ++ #["--", opts.path] ++ tArgs
                match ← LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultOps "worktree" { cwd := some repoPath, args := args } with
                | Except.error e => return Except.error e
                | Except.ok _ => return Except.ok ()) w = EST.Out.ok res w' ∧
            ∀ e : GitError, res = Except.error e → e.kind ≠ GitErrorKind.parseError := by
          intro bArgs
          cases opts.target? with
          | none => exact bind_runGitChecked_never_parseError "worktree" _ w
          | some t =>
            dsimp only
            split
            · exact bind_runGitChecked_never_parseError "worktree" _ w
            · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
        cases opts.newBranch? with
        | none => exact hAfter #[]
        | some b =>
          dsimp only
          split
          · exact hAfter #["-b", b.raw]
          · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.worktreeRemove` never fails with `.parseError`. -/
theorem git_worktreeRemove_never_parseError (repoPath wtPath : String) (force : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.worktreeRemove repoPath wtPath force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.worktreeRemove repoPath wtPath force =
      LeanSwe.Git.Impl.worktreeRemoveImpl LeanSwe.Git.defaultOps repoPath wtPath force from rfl]
  unfold LeanSwe.Git.Impl.worktreeRemoveImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    cases hv2 : LeanSwe.Git.Impl.validateRepoPath wtPath with
    | error e =>
      dsimp only
      exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never wtPath e hv2).2⟩
    | ok _ =>
      dsimp only
      exact bind_runGitChecked_never_parseError "worktree" _ w

end LeanSwe.Git.Proofs
