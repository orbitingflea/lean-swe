import Core.Obeys
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Model.Refines
import LeanSwe.Git.Impl
import LeanSwe.Git.Proofs.ObeysBase
import LeanSwe.Git.Proofs.ObeysQueryOps1

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Step contract helper `bind_checked_unit_parse` for any matcher continuation `k`. -/
theorem bind_checked_unit_parse {W : Type} {proj : W → GitHostState}
    {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (cmd : String) (req : GitRawRequest) (w : W) (hwf : hostStepWf (proj w) = true)
    (k : Except GitError GitRawOutput → StateM W (Except GitError Unit))
    (hErr : ∀ e, k (.error e) = pure (.error e))
    (hOk : ∀ out, k (.ok out) = pure (.ok ())) :
    allowedGuardedStep (proj w)
      (proj ((@Bind.bind (StateM W) (@Monad.toBind (StateM W) inferInstance) _ _
        (Impl.runGitChecked (Impl.mkRawOpsM caps) cmd req) k).run w).2)
      (.ok ()) [.parseError] (fun _ => True)
      ((@Bind.bind (StateM W) (@Monad.toBind (StateM W) inferInstance) _ _
        (Impl.runGitChecked (Impl.mkRawOpsM caps) cmd req) k).run w).1 := by
  dsimp only [allowedGuardedStep]
  rw [stateM_bind_run]
  have hChk := runGitChecked_caps_step hCaps cmd req w hwf
  dsimp only at hChk
  cases hr : ((Impl.runGitChecked (Impl.mkRawOpsM caps) cmd req).run w).1 with
  | error e =>
    rw [hr] at hChk
    rw [hErr e]
    simp only [stateM_pure_run]
    refine ⟨hChk.1, hChk.2.1, ?_⟩
    intro k' hk'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
    subst hk'; exact hChk.2.2.1
  | ok out =>
    rw [hOk out]
    simp only [stateM_pure_run]
    exact ⟨hChk.1, trivial⟩

/-- Step contract helper `bind_checked_unit_no_cwd` for any matcher continuation `k`. -/
theorem bind_checked_unit_no_cwd {W : Type} {proj : W → GitHostState}
    {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (cmd : String) (req : GitRawRequest) (hcwd : req.cwd = none)
    (w : W) (hwf : hostStepWf (proj w) = true)
    (k : Except GitError GitRawOutput → StateM W (Except GitError Unit))
    (hErr : ∀ e, k (.error e) = pure (.error e))
    (hOk : ∀ out, k (.ok out) = pure (.ok ())) :
    allowedGuardedStep (proj w)
      (proj ((@Bind.bind (StateM W) (@Monad.toBind (StateM W) inferInstance) _ _
        (Impl.runGitChecked (Impl.mkRawOpsM caps) cmd req) k).run w).2)
      (.ok ()) [.invalidPath, .parseError] (fun _ => True)
      ((@Bind.bind (StateM W) (@Monad.toBind (StateM W) inferInstance) _ _
        (Impl.runGitChecked (Impl.mkRawOpsM caps) cmd req) k).run w).1 := by
  dsimp only [allowedGuardedStep]
  rw [stateM_bind_run]
  have hChk := runGitChecked_caps_step hCaps cmd req w hwf
  dsimp only at hChk
  cases hr : ((Impl.runGitChecked (Impl.mkRawOpsM caps) cmd req).run w).1 with
  | error e =>
    rw [hr] at hChk
    rw [hErr e]
    simp only [stateM_pure_run]
    refine ⟨hChk.1, hChk.2.1, ?_⟩
    intro k' hk'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
    rcases hk' with rfl | rfl
    · exact hChk.2.2.2 hcwd
    · exact hChk.2.2.1
  | ok out =>
    rw [hOk out]
    simp only [stateM_pure_run]
    exact ⟨hChk.1, trivial⟩

/-- Step contract helper `obeys_init`. -/
theorem obeys_init {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) (bare : Bool) (b? : Option RefName) :
    let r := (Impl.initImpl (Impl.mkRawOpsM caps) p bare b?).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateInit p b?)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.initImpl Impl.validateRepoPath preValidateInit
  simp only [except_bind_eq, Except.bind]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok u =>
    cases u
    simp only [Except.mapError]
    cases b? with
    | none =>
      dsimp only
      apply bind_checked_unit_parse hCaps "init"
        { cwd := none, args := #["init"] ++ (if bare then #["--bare"] else #[]) ++ #[] ++ #["--", p] } w hwf <;> (intro _; rfl)
    | some b =>
      dsimp only
      cases hb : isValidRefNameStr b.raw with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
        exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
      | true =>
        simp only [↓reduceIte]
        apply bind_checked_unit_parse hCaps "init"
          { cwd := none, args := #["init"] ++ (if bare then #["--bare"] else #[]) ++ #["-b", b.raw] ++ #["--", p] } w hwf <;> (intro _; rfl)

/-- Step contract helper `obeys_clone`. -/
theorem obeys_clone {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (src dst : String) (opts : CloneOptions) :
    let r := (Impl.cloneImpl (Impl.mkRawOpsM caps) src dst opts).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateClone src dst opts)
      [.invalidPath, .parseError] (fun _ => True) r.1 := by
  unfold Impl.cloneImpl preValidateClone
  simp only [except_bind_eq, Except.bind]
  cases hs : validateCloneEndpoint src with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, (validateCloneEndpoint_err_spec hs).2⟩
  | ok _ =>
    cases ht : validateCloneEndpoint dst with
    | error e =>
      simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, (validateCloneEndpoint_err_spec ht).2⟩
    | ok _ =>
      simp only [Except.mapError]
      cases hd : opts.depth? with
      | none =>
        dsimp only
        simp only [show (none == some 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
        cases opts.branch? with
        | none =>
          dsimp only
          apply bind_checked_unit_no_cwd hCaps "clone"
            { cwd := none
              args := #["clone"] ++ (if opts.bare then #["--bare"] else #[]) ++
                (if opts.singleBranch then #["--single-branch"] else #[]) ++
                #[] ++ #[] ++ #["--", src, dst] } rfl w hwf <;> (intro _; rfl)
        | some b =>
          dsimp only
          cases hb : isValidRefNameStr b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
            exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
          | true =>
            simp only [↓reduceIte]
            apply bind_checked_unit_no_cwd hCaps "clone"
              { cwd := none
                args := #["clone"] ++ (if opts.bare then #["--bare"] else #[]) ++
                  (if opts.singleBranch then #["--single-branch"] else #[]) ++
                  #[] ++ #["--branch", b] ++ #["--", src, dst] } rfl w hwf <;> (intro _; rfl)
      | some d =>
        cases d with
        | zero =>
          simp only [beq_self_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
          exact ⟨trivial, hwf, trivial, by decide⟩
        | succ n =>
          dsimp only
          have hNe0 : (some (n + 1) == some 0) = false := by simp
          simp only [hNe0, Bool.false_eq_true, ↓reduceIte]
          cases opts.branch? with
          | none =>
            dsimp only
            apply bind_checked_unit_no_cwd hCaps "clone"
              { cwd := none
                args := #["clone"] ++ (if opts.bare then #["--bare"] else #[]) ++
                  (if opts.singleBranch then #["--single-branch"] else #[]) ++
                  #["--depth", toString (n + 1)] ++ #[] ++ #["--", src, dst] } rfl w hwf <;> (intro _; rfl)
          | some b =>
            dsimp only
            cases hb : isValidRefNameStr b with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
              exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
            | true =>
              simp only [↓reduceIte]
              apply bind_checked_unit_no_cwd hCaps "clone"
                { cwd := none
                  args := #["clone"] ++ (if opts.bare then #["--bare"] else #[]) ++
                    (if opts.singleBranch then #["--single-branch"] else #[]) ++
                    #["--depth", toString (n + 1)] ++ #["--branch", b] ++ #["--", src, dst] } rfl w hwf <;> (intro _; rfl)

/-- Step contract helper `obeys_add`. -/
theorem obeys_add {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) (paths : Array String) (all : Bool) :
    let r := (Impl.addImpl (Impl.mkRawOpsM caps) p paths all).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateAdd p paths all)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.addImpl Impl.validateRepoPath preValidateAdd
  simp only [except_bind_eq, Except.bind]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok u =>
    cases u
    simp only [Except.mapError]
    cases hEmpty : (!all && paths.isEmpty) with
    | true =>
      simp only [↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, by decide⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hPs : paths.all isValidPathArg with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
        exact ⟨trivial, hwf, trivial, by decide⟩
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        apply bind_checked_unit_parse hCaps "add"
          { cwd := some p
            args := if all then (if paths.isEmpty then #["add", "--all"] else #["add", "--all", "--"] ++ paths)
              else #["add", "--"] ++ paths } w hwf <;> (intro _; rfl)

/-- Step contract helper `obeys_commit`. -/
theorem obeys_commit {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) (opts : CommitOptions) :
    let r := (Impl.commitImpl (Impl.mkRawOpsM caps) p opts).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateCommit p opts)
      [] (fun cid => isValidCommitIdStr cid.hex = true) r.1 := by
  unfold Impl.commitImpl Impl.validateRepoPath preValidateCommit
  simp only [except_bind_eq, Except.bind]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok u =>
    cases u
    simp only [Except.mapError]
    cases hOpts : validateCommitOptions opts with
    | error e =>
      simp only [stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, validateCommitOptions_err_nonEmpty hOpts⟩
    | ok _ =>
      simp only [allowedGuardedStep]
      rw [stateM_bind_run]
      let nEnv := match opts.authorName with
        | none => #[]
        | some n => #[("GIT_AUTHOR_NAME", some n), ("GIT_COMMITTER_NAME", some n)]
      let eEnv := match opts.authorEmail with
        | none => #[]
        | some em => #[("GIT_AUTHOR_EMAIL", some em), ("GIT_COMMITTER_EMAIL", some em)]
      let req : GitRawRequest :=
        { cwd := some p
          args := #["commit", "--no-gpg-sign", "-m", opts.message] ++
            (if opts.allowEmpty then #["--allow-empty"] else #[])
          extraEnv := nEnv ++ eEnv }
      have hChk := runGitChecked_caps_step hCaps "commit" req w hwf
      dsimp only at hChk
      cases hr : ((Impl.runGitChecked (Impl.mkRawOpsM caps) "commit" req).run w).1 with
      | error e =>
        rw [hr] at hChk
        simp only [stateM_pure_run]
        exact ⟨hChk.1, hChk.2.1, fun _ h => nomatch h⟩
      | ok _ =>
        dsimp only
        have hRp := obeys_revParseCommit hCaps
          ((Impl.runGitChecked (Impl.mkRawOpsM caps) "commit" req).run w).2 hChk.1.2.1 p "HEAD"
        have hPreHead : preValidateRevParseCommit p "HEAD" = .ok () := by
          have hH : isValidRevSpec "HEAD" = true := by decide
          unfold preValidateRevParseCommit
          rw [hv]
          simp [except_bind_eq, Except.bind, Except.mapError, hH]
        dsimp only at hRp
        rw [hPreHead] at hRp
        simp only [allowedGuardedStep] at hRp
        exact ⟨allowedHostTransition_trans hChk.1 hRp.1, hRp.2⟩

/-- Step contract helper `obeys_createBranch`. -/
theorem obeys_createBranch {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true)
    (p : String) (b : RefName) (sp? : Option String) (force : Bool) :
    let r := (Impl.createBranchImpl (Impl.mkRawOpsM caps) p b sp? force).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateCreateBranch p b sp?)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.createBranchImpl Impl.validateRepoPath preValidateCreateBranch
  simp only [except_bind_eq, Except.bind]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok u =>
    cases u
    simp only [Except.mapError]
    cases hb : isValidRefNameStr b.raw with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases sp? with
      | none =>
        dsimp only
        apply bind_checked_unit_parse hCaps "branch"
          { cwd := some p, args := #["branch"] ++ (if force then #["-f"] else #[]) ++ #["--", b.raw] ++ #[] } w hwf <;> (intro _; rfl)
      | some sp =>
        dsimp only
        cases hSp : isValidStrictRevSpec sp with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
          exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
        | true =>
          simp only [↓reduceIte]
          apply bind_checked_unit_parse hCaps "branch"
            { cwd := some p, args := #["branch"] ++ (if force then #["-f"] else #[]) ++ #["--", b.raw] ++ #[sp] } w hwf <;> (intro _; rfl)

/-- Step contract helper `obeys_deleteBranch`. -/
theorem obeys_deleteBranch {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) (b : RefName) (force : Bool) :
    let r := (Impl.deleteBranchImpl (Impl.mkRawOpsM caps) p b force).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateDeleteBranch p b)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.deleteBranchImpl Impl.validateRepoPath preValidateDeleteBranch
  simp only [except_bind_eq, Except.bind]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok u =>
    cases u
    simp only [Except.mapError]
    cases hb : isValidRefNameStr b.raw with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      apply bind_checked_unit_parse hCaps "branch"
        { cwd := some p, args := #["branch", if force then "-D" else "-d", "--", b.raw] } w hwf <;> (intro _; rfl)

/-- Step contract helper `obeys_checkout`. -/
theorem obeys_checkout {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) (t : CheckoutTarget) (force : Bool) :
    let r := (Impl.checkoutImpl (Impl.mkRawOpsM caps) p t force).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateCheckout p t)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.checkoutImpl Impl.validateRepoPath preValidateCheckout
  simp only [except_bind_eq, Except.bind]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok u =>
    cases u
    simp only [Except.mapError]
    cases t with
    | branch b =>
      dsimp only
      cases hb : isValidRefNameStr b.raw with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
        exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
      | true =>
        simp only [↓reduceIte]
        apply bind_checked_unit_parse hCaps "checkout"
          { cwd := some p, args := #["checkout"] ++ (if force then #["--force"] else #[]) ++ #[b.raw, "--"] } w hwf <;> (intro _; rfl)
    | commit cid =>
      dsimp only
      cases hc : isValidCommitIdStr cid.hex with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
        exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
      | true =>
        simp only [↓reduceIte]
        apply bind_checked_unit_parse hCaps "checkout"
          { cwd := some p, args := #["checkout"] ++ (if force then #["--force"] else #[]) ++ #["--detach", cid.hex, "--"] } w hwf <;> (intro _; rfl)
    | ref spec =>
      dsimp only
      cases hr : isValidStrictRevSpec spec with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
        exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
      | true =>
        simp only [↓reduceIte]
        apply bind_checked_unit_parse hCaps "checkout"
          { cwd := some p, args := #["checkout"] ++ (if force then #["--force"] else #[]) ++ #[spec, "--"] } w hwf <;> (intro _; rfl)

end LeanSwe.Git.Proofs
