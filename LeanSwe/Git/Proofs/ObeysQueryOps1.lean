import Core.Obeys
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Model.Refines
import LeanSwe.Git.Impl
import LeanSwe.Git.Proofs.ObeysBase
import LeanSwe.Git.Proofs.ParserProofs

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Step contract lemma `obeys_isRepo`. -/
theorem obeys_isRepo {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) :
    let r := (Impl.isRepoImpl (Impl.mkRawOpsM caps) p).run w
    allowedGuardedStep (proj w) (proj r.2) ((validateFsPathArg p).mapError (·.kind))
      [.notARepo, .parseError] (fun _ => True) r.1 := by
  unfold Impl.isRepoImpl Impl.validateRepoPath
  rw [validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, allowedGuardedStep]
    rw [stateM_bind_run]
    have hRaw := runGitRaw_caps_step hCaps { cwd := some p, args := #["rev-parse", "--git-dir"] } w hwf
    dsimp only at hRaw
    cases hr : ((Impl.runGitRaw (Impl.mkRawOpsM caps) _).run w).1 with
    | error e =>
      rw [hr] at hRaw
      simp only [stateM_pure_run]
      refine ⟨hRaw.1, hRaw.2.1, ?_⟩
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hRaw.2.2.1
      · exact hRaw.2.2.2.1
    | ok out =>
      dsimp only
      split
      · simp only [stateM_pure_run]; exact ⟨hRaw.1, trivial⟩
      · split
        · simp only [stateM_pure_run]; exact ⟨hRaw.1, trivial⟩
        · next hNe =>
          simp only [stateM_pure_run]
          have hc := classifyError_spec "rev-parse" out
          refine ⟨hRaw.1, hc.1, ?_⟩
          intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl
          · intro heq; exact hNe (by rw [heq]; decide)
          · exact hc.2.2

/-- Step contract lemma `obeys_repoRoot`. -/
theorem obeys_repoRoot {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) :
    let r := (Impl.repoRootImpl (Impl.mkRawOpsM caps) p).run w
    allowedGuardedStep (proj w) (proj r.2) ((validateFsPathArg p).mapError (·.kind))
      [] (fun _ => True) r.1 := by
  unfold Impl.repoRootImpl Impl.validateRepoPath
  rw [validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, allowedGuardedStep]
    rw [stateM_bind_run]
    have hChk := runGitChecked_caps_step hCaps "rev-parse"
      { cwd := some p, args := #["rev-parse", "--path-format=absolute", "--show-toplevel"] } w hwf
    dsimp only at hChk
    cases hr : ((Impl.runGitChecked (Impl.mkRawOpsM caps) "rev-parse" _).run w).1 with
    | error e =>
      rw [hr] at hChk
      simp only [stateM_pure_run]
      exact ⟨hChk.1, hChk.2.1, fun _ h => nomatch h⟩
    | ok out =>
      dsimp only
      cases hd : Impl.decodeUtf8Checked out.stdout with
      | error e =>
        simp only [stateM_pure_run]
        exact ⟨hChk.1, decodeUtf8Checked_err_nonEmpty hd, fun _ h => nomatch h⟩
      | ok s =>
        simp only [stateM_pure_run]
        exact ⟨hChk.1, trivial⟩

/-- Step contract lemma `obeys_commonDir`. -/
theorem obeys_commonDir {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) :
    let r := (Impl.commonDirImpl (Impl.mkRawOpsM caps) p).run w
    allowedGuardedStep (proj w) (proj r.2) ((validateFsPathArg p).mapError (·.kind))
      [] (fun _ => True) r.1 := by
  unfold Impl.commonDirImpl Impl.validateRepoPath
  rw [validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, allowedGuardedStep]
    rw [stateM_bind_run]
    have hChk := runGitChecked_caps_step hCaps "rev-parse"
      { cwd := some p, args := #["rev-parse", "--path-format=absolute", "--git-common-dir"] } w hwf
    dsimp only at hChk
    cases hr : ((Impl.runGitChecked (Impl.mkRawOpsM caps) "rev-parse" _).run w).1 with
    | error e =>
      rw [hr] at hChk
      simp only [stateM_pure_run]
      exact ⟨hChk.1, hChk.2.1, fun _ h => nomatch h⟩
    | ok out =>
      dsimp only
      cases hd : Impl.decodeUtf8Checked out.stdout with
      | error e =>
        simp only [stateM_pure_run]
        exact ⟨hChk.1, decodeUtf8Checked_err_nonEmpty hd, fun _ h => nomatch h⟩
      | ok s =>
        simp only [stateM_pure_run]
        exact ⟨hChk.1, trivial⟩

/-- Step contract lemma `obeys_headCommit`. -/
theorem obeys_headCommit {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) :
    let r := (Impl.headCommitImpl (Impl.mkRawOpsM caps) p).run w
    allowedGuardedStep (proj w) (proj r.2) ((validateFsPathArg p).mapError (·.kind))
      [] (fun c? => c?.all (fun c => isValidCommitIdStr c.hex) = true) r.1 := by
  unfold Impl.headCommitImpl Impl.validateRepoPath
  rw [validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, allowedGuardedStep]
    rw [stateM_bind_run]
    have hRaw := runGitRaw_caps_step hCaps
      { cwd := some p, args := #["rev-parse", "-q", "--verify", "HEAD^{commit}"] } w hwf
    dsimp only at hRaw
    cases hr : ((Impl.runGitRaw (Impl.mkRawOpsM caps) _).run w).1 with
    | error e =>
      rw [hr] at hRaw
      simp only [stateM_pure_run]
      exact ⟨hRaw.1, hRaw.2.1, fun _ h => nomatch h⟩
    | ok out =>
      dsimp only
      split
      · cases hd : Impl.decodeUtf8Checked out.stdout with
        | error e =>
          simp only [stateM_pure_run]
          exact ⟨hRaw.1, decodeUtf8Checked_err_nonEmpty hd, fun _ h => nomatch h⟩
        | ok s =>
          dsimp only
          have hCid := mkCommitId_spec (Impl.trimTrailingNewlines s)
          rw [mkCommitIdImpl_eq]
          cases hc : mkCommitId (Impl.trimTrailingNewlines s) with
          | error e =>
            rw [hc] at hCid
            simp only [stateM_pure_run]
            exact ⟨hRaw.1, hCid, fun _ h => nomatch h⟩
          | ok cid =>
            rw [hc] at hCid
            simp only [stateM_pure_run, Option.all_some]
            exact ⟨hRaw.1, hCid⟩
      · split
        · simp only [stateM_pure_run]
          exact ⟨hRaw.1, (classifyError_spec "rev-parse" out).1, fun _ h => nomatch h⟩
        · split
          · rw [stateM_bind_run]
            have hChk := runGitChecked_caps_step hCaps "rev-parse"
              { cwd := some p, args := #["rev-parse", "--git-dir"] }
              ((Impl.runGitRaw (Impl.mkRawOpsM caps) _).run w).2 hRaw.1.2.1
            have hTrans := allowedHostTransition_trans hRaw.1 hChk.1
            dsimp only at hChk
            cases hr2 : ((Impl.runGitChecked (Impl.mkRawOpsM caps) "rev-parse" _).run _).1 with
            | error e =>
              rw [hr2] at hChk
              simp only [stateM_pure_run]
              exact ⟨hTrans, hChk.2.1, fun _ h => nomatch h⟩
            | ok _ =>
              simp only [stateM_pure_run]
              exact ⟨hTrans, rfl⟩
          · simp only [stateM_pure_run]
            exact ⟨hRaw.1, (classifyError_spec "rev-parse" out).1, fun _ h => nomatch h⟩

/-- Step contract lemma `obeys_headBranch`. -/
theorem obeys_headBranch {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) :
    let r := (Impl.headBranchImpl (Impl.mkRawOpsM caps) p).run w
    allowedGuardedStep (proj w) (proj r.2) ((validateFsPathArg p).mapError (·.kind))
      [] (fun b? => b?.all (fun b => isValidRefNameStr b.raw) = true) r.1 := by
  unfold Impl.headBranchImpl Impl.validateRepoPath
  rw [validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, allowedGuardedStep]
    rw [stateM_bind_run]
    have hRaw := runGitRaw_caps_step hCaps
      { cwd := some p, args := #["symbolic-ref", "--quiet", "HEAD"] } w hwf
    dsimp only at hRaw
    cases hr : ((Impl.runGitRaw (Impl.mkRawOpsM caps) _).run w).1 with
    | error e =>
      rw [hr] at hRaw
      simp only [stateM_pure_run]
      exact ⟨hRaw.1, hRaw.2.1, fun _ h => nomatch h⟩
    | ok out =>
      dsimp only
      split
      · cases hd : Impl.decodeUtf8Checked out.stdout with
        | error e =>
          simp only [stateM_pure_run]
          exact ⟨hRaw.1, decodeUtf8Checked_err_nonEmpty hd, fun _ h => nomatch h⟩
        | ok s =>
          dsimp only
          let raw := Impl.trimTrailingNewlines s
          let stripped := if raw.startsWith "refs/heads/" then String.ofList (raw.toList.drop 11) else raw
          have hRef := mkRefName_spec stripped
          rw [mkRefNameImpl_eq]
          cases hc : mkRefName stripped with
          | error e =>
            rw [hc] at hRef
            simp only [stateM_pure_run]
            exact ⟨hRaw.1, hRef, fun _ h => nomatch h⟩
          | ok ref =>
            rw [hc] at hRef
            simp only [stateM_pure_run, Option.all_some]
            exact ⟨hRaw.1, hRef⟩
      · split
        · simp only [stateM_pure_run]
          exact ⟨hRaw.1, (classifyError_spec "symbolic-ref" out).1, fun _ h => nomatch h⟩
        · split
          · rw [stateM_bind_run]
            have hChk := runGitChecked_caps_step hCaps "rev-parse"
              { cwd := some p, args := #["rev-parse", "--git-dir"] }
              ((Impl.runGitRaw (Impl.mkRawOpsM caps) _).run w).2 hRaw.1.2.1
            have hTrans := allowedHostTransition_trans hRaw.1 hChk.1
            dsimp only at hChk
            cases hr2 : ((Impl.runGitChecked (Impl.mkRawOpsM caps) "rev-parse" _).run _).1 with
            | error e =>
              rw [hr2] at hChk
              simp only [stateM_pure_run]
              exact ⟨hTrans, hChk.2.1, fun _ h => nomatch h⟩
            | ok _ =>
              simp only [stateM_pure_run]
              exact ⟨hTrans, rfl⟩
          · simp only [stateM_pure_run]
            exact ⟨hRaw.1, (classifyError_spec "symbolic-ref" out).1, fun _ h => nomatch h⟩

/-- Step contract lemma `obeys_headState`. -/
theorem obeys_headState {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) :
    let r := (Impl.headStateImpl (Impl.mkRawOpsM caps) p).run w
    allowedGuardedStep (proj w) (proj r.2) ((validateFsPathArg p).mapError (·.kind))
      [] (fun hs => isValidHeadState hs = true) r.1 := by
  unfold Impl.headStateImpl
  rw [stateM_bind_run]
  have hBr := obeys_headBranch hCaps w hwf p
  dsimp only at hBr
  cases hv : validateFsPathArg p with
  | error e =>
    rw [hv] at hBr
    simp only [Except.mapError, allowedGuardedStep] at hBr ⊢
    rcases hBr with ⟨hEq, _, hRes⟩
    cases hBrRes : ((Impl.headBranchImpl (Impl.mkRawOpsM caps) p).run w).1 with
    | ok _ => rw [hBrRes] at hRes; exact False.elim hRes
    | error err =>
      rw [hBrRes] at hRes
      simp only [stateM_pure_run]
      exact ⟨hEq, hwf, hRes⟩
  | ok _ =>
    rw [hv] at hBr
    simp only [Except.mapError, allowedGuardedStep] at hBr ⊢
    cases hBrRes : ((Impl.headBranchImpl (Impl.mkRawOpsM caps) p).run w).1 with
    | error e =>
      rw [hBrRes] at hBr
      simp only [stateM_pure_run]
      exact hBr
    | ok b? =>
      rw [hBrRes] at hBr
      cases b? with
      | some b =>
        rw [stateM_bind_run]
        have hCm := obeys_headCommit hCaps ((Impl.headBranchImpl (Impl.mkRawOpsM caps) p).run w).2 hBr.1.2.1 p
        dsimp only at hCm
        rw [hv] at hCm
        simp only [Except.mapError, allowedGuardedStep] at hCm
        have hTrans := allowedHostTransition_trans hBr.1 hCm.1
        cases hCmRes : ((Impl.headCommitImpl (Impl.mkRawOpsM caps) p).run _).1 with
        | error e =>
          rw [hCmRes] at hCm
          simp only [stateM_pure_run]
          exact ⟨hTrans, hCm.2⟩
        | ok c? =>
          rw [hCmRes] at hCm
          simp only [stateM_pure_run, isValidHeadState, Bool.and_eq_true]
          exact ⟨hTrans, by simpa using hBr.2, hCm.2⟩
      | none =>
        rw [stateM_bind_run]
        have hCm := obeys_headCommit hCaps ((Impl.headBranchImpl (Impl.mkRawOpsM caps) p).run w).2 hBr.1.2.1 p
        dsimp only at hCm
        rw [hv] at hCm
        simp only [Except.mapError, allowedGuardedStep] at hCm
        have hTrans := allowedHostTransition_trans hBr.1 hCm.1
        cases hCmRes : ((Impl.headCommitImpl (Impl.mkRawOpsM caps) p).run _).1 with
        | error e =>
          rw [hCmRes] at hCm
          simp only [stateM_pure_run]
          exact ⟨hTrans, hCm.2⟩
        | ok c? =>
          rw [hCmRes] at hCm
          cases c? with
          | some c =>
            simp only [stateM_pure_run, isValidHeadState]
            exact ⟨hTrans, by simpa using hCm.2⟩
          | none =>
            simp only [stateM_pure_run]
            exact ⟨hTrans, by decide, fun _ h => nomatch h⟩

/-- Step contract for `Impl.revParseCommitImpl` (also reused by `commitImpl` and `showFileImpl`). -/
theorem obeys_revParseCommit {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p rev : String) :
    let r := (Impl.revParseCommitImpl (Impl.mkRawOpsM caps) p rev).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateRevParseCommit p rev)
      [] (fun cid => isValidCommitIdStr cid.hex = true) r.1 := by
  unfold Impl.revParseCommitImpl Impl.validateRepoPath preValidateRevParseCommit
  simp only [except_bind_eq, Except.bind, validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, isValidRevSpecImpl_eq]
    rcases (Bool.eq_false_or_eq_true (isValidRevSpec rev)).symm with hRev | hRev
    · simp only [hRev, Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
    · simp only [hRev, Bool.not_true, Bool.false_eq_true, ↓reduceIte, allowedGuardedStep]
      rw [stateM_bind_run]
      have hRaw := runGitRaw_caps_step hCaps
        { cwd := some p, args := #["rev-parse", "-q", "--verify", rev ++ "^{commit}"] } w hwf
      dsimp only at hRaw
      cases hr : ((Impl.runGitRaw (Impl.mkRawOpsM caps) _).run w).1 with
      | error e =>
        rw [hr] at hRaw
        simp only [stateM_pure_run]
        exact ⟨hRaw.1, hRaw.2.1, fun _ h => nomatch h⟩
      | ok out =>
        dsimp only
        split
        · cases hd : Impl.decodeUtf8Checked out.stdout with
          | error e =>
            simp only [stateM_pure_run]
            exact ⟨hRaw.1, decodeUtf8Checked_err_nonEmpty hd, fun _ h => nomatch h⟩
          | ok s =>
            dsimp only
            have hCid := mkCommitId_spec (Impl.trimTrailingNewlines s)
            rw [mkCommitIdImpl_eq]
            cases hc : mkCommitId (Impl.trimTrailingNewlines s) with
            | error e =>
              rw [hc] at hCid
              simp only [stateM_pure_run]
              exact ⟨hRaw.1, hCid, fun _ h => nomatch h⟩
            | ok cid =>
              rw [hc] at hCid
              simp only [stateM_pure_run]
              exact ⟨hRaw.1, hCid⟩
        · split
          · simp only [stateM_pure_run]
            exact ⟨hRaw.1, (classifyError_spec "rev-parse" out).1, fun _ h => nomatch h⟩
          · split
            · simp only [stateM_pure_run]
              exact ⟨hRaw.1, interp3_ne_empty _ _ _ (by decide), fun _ h => nomatch h⟩
            · simp only [stateM_pure_run]
              exact ⟨hRaw.1, (classifyError_spec "rev-parse" out).1, fun _ h => nomatch h⟩


end LeanSwe.Git.Proofs
