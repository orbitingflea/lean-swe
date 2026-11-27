import Core.Obeys
import LeanSwe.Git.Types
import LeanSweProofs.Git.Model
import LeanSweProofs.Git.Model.Refines
import LeanSwe.Git.Impl
import LeanSweProofs.Git.Proofs.ObeysBase
import LeanSweProofs.Git.Proofs.ObeysParsers
import LeanSweProofs.Git.Proofs.ObeysQueryOps1

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open LeanSwe.Git
open LeanSwe.Git.Model

private theorem obeys_isAncestor {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) (a d : CommitId) :
    let r := (Impl.isAncestorImpl (Impl.mkRawOpsM caps) p a d).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateCommitPair p a d)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.isAncestorImpl Impl.validateRepoPath preValidateCommitPair
  simp only [except_bind_eq, Except.bind, validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, isValidCommitIdStrImpl_eq]
    rcases (Bool.eq_false_or_eq_true (!isValidCommitIdStr a.hex || !isValidCommitIdStr d.hex)).symm with hPair | hPair
    · simp only [hPair, Bool.false_eq_true, ↓reduceIte, allowedGuardedStep]
      rw [stateM_bind_run]
      have hRaw := runGitRaw_caps_step hCaps
        { cwd := some p, args := #["merge-base", "--is-ancestor", a.hex, d.hex] } w hwf
      dsimp only at hRaw
      cases hr : ((Impl.runGitRaw (Impl.mkRawOpsM caps) _).run w).1 with
      | error e =>
        rw [hr] at hRaw
        simp only [stateM_pure_run]
        refine ⟨hRaw.1, hRaw.2.1, ?_⟩
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        subst hk; exact hRaw.2.2.2.1
      | ok out =>
        dsimp only
        split
        · simp only [stateM_pure_run]; exact ⟨hRaw.1, trivial⟩
        · split
          · simp only [stateM_pure_run]; exact ⟨hRaw.1, trivial⟩
          · simp only [stateM_pure_run]
            have hc := classifyError_spec "merge-base" out
            refine ⟨hRaw.1, hc.1, ?_⟩
            intro k hk
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
            subst hk; exact hc.2.2
    · simp only [hPair, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, by decide⟩

private theorem obeys_mergeBase {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) (a b : CommitId) :
    let r := (Impl.mergeBaseImpl (Impl.mkRawOpsM caps) p a b).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateCommitPair p a b)
      [] (fun c? => c?.all (fun c => isValidCommitIdStr c.hex) = true) r.1 := by
  unfold Impl.mergeBaseImpl Impl.validateRepoPath preValidateCommitPair
  simp only [except_bind_eq, Except.bind, validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, isValidCommitIdStrImpl_eq]
    rcases (Bool.eq_false_or_eq_true (!isValidCommitIdStr a.hex || !isValidCommitIdStr b.hex)).symm with hPair | hPair
    · simp only [hPair, Bool.false_eq_true, ↓reduceIte, allowedGuardedStep]
      rw [stateM_bind_run]
      have hRaw := runGitRaw_caps_step hCaps
        { cwd := some p, args := #["merge-base", a.hex, b.hex] } w hwf
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
          · simp only [stateM_pure_run]; exact ⟨hRaw.1, rfl⟩
          · simp only [stateM_pure_run]
            exact ⟨hRaw.1, (classifyError_spec "merge-base" out).1, fun _ h => nomatch h⟩
    · simp only [hPair, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, by decide⟩

private theorem obeys_status {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) :
    let r := (Impl.statusImpl (Impl.mkRawOpsM caps) p).run w
    allowedGuardedStep (proj w) (proj r.2) ((validateFsPathArg p).mapError (·.kind))
      [] (fun entries => entries.all (fun e => !e.path.isEmpty) = true) r.1 := by
  unfold Impl.statusImpl Impl.validateRepoPath
  rw [validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, allowedGuardedStep]
    rw [stateM_bind_run]
    have hChk := runGitChecked_caps_step hCaps "status"
      { cwd := some p, args := #["status", "--porcelain=v1", "--untracked-files=normal", "-z"] } w hwf
    dsimp only at hChk
    cases hr : ((Impl.runGitChecked (Impl.mkRawOpsM caps) "status" _).run w).1 with
    | error e =>
      rw [hr] at hChk
      simp only [stateM_pure_run]
      exact ⟨hChk.1, hChk.2.1, fun _ h => nomatch h⟩
    | ok out =>
      dsimp only
      have hSt := parsePorcelainStatusZ_spec out.stdout
      rw [parsePorcelainStatusZImpl_eq]
      cases hp : parsePorcelainStatusZ out.stdout with
      | error e =>
        rw [hp] at hSt
        simp only [stateM_pure_run]
        exact ⟨hChk.1, hSt, fun _ h => nomatch h⟩
      | ok entries =>
        rw [hp] at hSt
        simp only [stateM_pure_run]
        exact ⟨hChk.1, hSt⟩

private theorem obeys_diffNameStatus {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true)
    (p revA : String) (revB? : Option String) (paths : Array String) :
    let r := (Impl.diffNameStatusImpl (Impl.mkRawOpsM caps) p revA revB? paths).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateDiffNameStatus p revA revB? paths)
      [] (fun _ => True) r.1 := by
  unfold Impl.diffNameStatusImpl Impl.validateRepoPath preValidateDiffNameStatus
  simp only [except_bind_eq, Except.bind, validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, isValidStrictRevSpecImpl_eq]
    rcases (Bool.eq_false_or_eq_true (isValidStrictRevSpec revA)).symm with hA | hA
    · simp only [hA, Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
    · simp only [hA, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hAfterB : ∀ (rbArgs : Array String),
          let r :=
            (if !paths.all isValidPathArg then
              (pure (Except.error { kind := .invalidPath, message := "invalid diff path argument" }) :
                StateM W (Except GitError (Array DiffEntry)))
            else do
              match ← Impl.runGitChecked (Impl.mkRawOpsM caps) "diff"
                  { cwd := some p, args := #["diff", "--name-status", "-z", revA] ++ rbArgs ++ #["--"] ++ paths } with
              | .error e => return .error e
              | .ok out => return parseDiffNameStatusZ out.stdout).run w
          allowedGuardedStep (proj w) (proj r.2)
            (if !paths.all isValidPathArg then .error .invalidPath else .ok ())
            [] (fun _ => True) r.1 := by
        intro rbArgs
        cases hPs : paths.all isValidPathArg with
        | false =>
          simp only [Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
          exact ⟨trivial, hwf, trivial, by decide⟩
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, allowedGuardedStep]
          rw [stateM_bind_run]
          have hChk := runGitChecked_caps_step hCaps "diff"
            { cwd := some p, args := #["diff", "--name-status", "-z", revA] ++ rbArgs ++ #["--"] ++ paths } w hwf
          dsimp only at hChk
          cases hr : ((Impl.runGitChecked (Impl.mkRawOpsM caps) "diff" _).run w).1 with
          | error e =>
            rw [hr] at hChk
            simp only [stateM_pure_run]
            exact ⟨hChk.1, hChk.2.1, fun _ h => nomatch h⟩
          | ok out =>
            dsimp only
            cases hd : parseDiffNameStatusZ out.stdout with
            | error e =>
              simp only [stateM_pure_run]
              exact ⟨hChk.1, parseDiffNameStatusZ_err_nonEmpty hd, fun _ h => nomatch h⟩
            | ok _ =>
              simp only [stateM_pure_run]
              exact ⟨hChk.1, trivial⟩
      simp only [show Impl.isValidPathArgImpl = isValidPathArg from funext isValidPathArgImpl_eq,
        parseDiffNameStatusZImpl_eq]
      cases revB? with
      | none => exact hAfterB #[]
      | some rb =>
        dsimp only
        rcases (Bool.eq_false_or_eq_true (isValidStrictRevSpec rb)).symm with hB | hB
        · simp only [hB, Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
          exact ⟨trivial, hwf, rfl, interp3_ne_empty _ _ _ (by decide)⟩
        · simp only [hB, ↓reduceIte]
          exact hAfterB #[rb]

private theorem obeys_listWorktrees {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) :
    let r := (Impl.listWorktreesImpl (Impl.mkRawOpsM caps) p).run w
    allowedGuardedStep (proj w) (proj r.2) ((validateFsPathArg p).mapError (·.kind))
      [] (fun wts => wts.all isValidWorktreeInfo = true) r.1 := by
  unfold Impl.listWorktreesImpl Impl.validateRepoPath
  rw [validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError, allowedGuardedStep]
    rw [stateM_bind_run]
    have hChk := runGitChecked_caps_step hCaps "worktree"
      { cwd := some p, args := #["worktree", "list", "--porcelain", "-z"] } w hwf
    dsimp only at hChk
    cases hr : ((Impl.runGitChecked (Impl.mkRawOpsM caps) "worktree" _).run w).1 with
    | error e =>
      rw [hr] at hChk
      simp only [stateM_pure_run]
      exact ⟨hChk.1, hChk.2.1, fun _ h => nomatch h⟩
    | ok out =>
      dsimp only
      have hWt := parseWorktreeListPorcelain_spec out.stdout
      rw [parseWorktreeListPorcelainImpl_eq]
      cases hp : parseWorktreeListPorcelain out.stdout with
      | error e =>
        rw [hp] at hWt
        simp only [stateM_pure_run]
        exact ⟨hChk.1, hWt, fun _ h => nomatch h⟩
      | ok infos =>
        rw [hp] at hWt
        simp only [stateM_pure_run]
        exact ⟨hChk.1, hWt⟩

private theorem obeys_showFile {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p rev rel : String) :
    let r := (Impl.showFileImpl (Impl.mkRawOpsM caps) p rev rel).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateShowFile p rev rel)
      [] (fun _ => True) r.1 := by
  unfold Impl.showFileImpl Impl.validateRepoPath preValidateShowFile
  simp only [except_bind_eq, Except.bind, validateFsPathArgImpl_eq]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok u =>
    cases u
    simp only [Except.mapError, isValidStrictRevSpecImpl_eq]
    rcases (Bool.eq_false_or_eq_true (isValidStrictRevSpec rev)).symm with hRev | hRev
    · simp only [hRev, Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
    · simp only [hRev, Bool.not_true, Bool.false_eq_true, ↓reduceIte, validateRelRepoPathImpl_eq]
      cases hRel : validateRelRepoPath rel with
      | error e =>
        simp only [stateM_pure_run, allowedGuardedStep]
        exact ⟨trivial, hwf, trivial, validateRelRepoPath_err_nonEmpty hRel⟩
      | ok _ =>
        simp only [allowedGuardedStep]
        rw [stateM_bind_run]
        have hRevLoose : isValidRevSpec rev = true := by
          unfold isValidStrictRevSpec at hRev
          simp only [Bool.and_eq_true] at hRev
          exact hRev.1.1.1
        have hRp := obeys_revParseCommit hCaps w hwf p rev
        have hPreRp : preValidateRevParseCommit p rev = .ok () := by
          unfold preValidateRevParseCommit
          rw [hv]
          simp [except_bind_eq, Except.bind, Except.mapError, hRevLoose]
        dsimp only at hRp
        rw [hPreRp] at hRp
        simp only [allowedGuardedStep] at hRp
        cases hr1 : ((Impl.revParseCommitImpl (Impl.mkRawOpsM caps) p rev).run w).1 with
        | error e =>
          rw [hr1] at hRp
          simp only [stateM_pure_run]
          exact ⟨hRp.1, hRp.2⟩
        | ok cid =>
          dsimp only
          rw [stateM_bind_run]
          have hRaw := runGitRaw_caps_step hCaps
            { cwd := some p, args := #["cat-file", "-t", s!"{cid.hex}:{rel}"] }
            ((Impl.revParseCommitImpl (Impl.mkRawOpsM caps) p rev).run w).2 hRp.1.2.1
          have hTrans1 := allowedHostTransition_trans hRp.1 hRaw.1
          dsimp only at hRaw
          cases hr2 : ((Impl.runGitRaw (Impl.mkRawOpsM caps) _).run _).1 with
          | error e =>
            rw [hr2] at hRaw
            simp only [stateM_pure_run]
            exact ⟨hTrans1, hRaw.2.1, fun _ h => nomatch h⟩
          | ok typeOut =>
            dsimp only
            split
            · split
              · simp only [stateM_pure_run]; exact ⟨hTrans1, trivial⟩
              · split
                · simp only [stateM_pure_run]
                  exact ⟨hTrans1, (classifyError_spec "cat-file" typeOut).1, fun _ h => nomatch h⟩
                · simp only [stateM_pure_run]; exact ⟨hTrans1, trivial⟩
            · cases hd : Impl.decodeUtf8Checked typeOut.stdout with
              | error e =>
                simp only [stateM_pure_run]
                exact ⟨hTrans1, decodeUtf8Checked_err_nonEmpty hd, fun _ h => nomatch h⟩
              | ok objType =>
                dsimp only
                split
                · simp only [stateM_pure_run]; exact ⟨hTrans1, trivial⟩
                · rw [stateM_bind_run]
                  have hChk := runGitChecked_caps_step hCaps "cat-file"
                    { cwd := some p, args := #["cat-file", "blob", s!"{cid.hex}:{rel}"] }
                    ((Impl.runGitRaw (Impl.mkRawOpsM caps) _).run _).2 hRaw.1.2.1
                  have hTrans2 := allowedHostTransition_trans hTrans1 hChk.1
                  dsimp only at hChk
                  cases hr3 : ((Impl.runGitChecked (Impl.mkRawOpsM caps) "cat-file" _).run _).1 with
                  | error e =>
                    rw [hr3] at hChk
                    simp only [stateM_pure_run]
                    exact ⟨hTrans2, hChk.2.1, fun _ h => nomatch h⟩
                  | ok _ =>
                    simp only [stateM_pure_run]
                    exact ⟨hTrans2, trivial⟩

/-- Dispatch step proof covering all 13 query `PkgStepReq` variants. -/
theorem obeys_query_step {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) :
    (∀ p, allowedPkgStep (proj w) (.isRepo p)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.isRepo p)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.isRepo p)).run w).2)) ∧
    (∀ p, allowedPkgStep (proj w) (.repoRoot p)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.repoRoot p)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.repoRoot p)).run w).2)) ∧
    (∀ p, allowedPkgStep (proj w) (.commonDir p)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.commonDir p)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.commonDir p)).run w).2)) ∧
    (∀ p, allowedPkgStep (proj w) (.headCommit? p)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.headCommit? p)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.headCommit? p)).run w).2)) ∧
    (∀ p, allowedPkgStep (proj w) (.headBranch? p)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.headBranch? p)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.headBranch? p)).run w).2)) ∧
    (∀ p, allowedPkgStep (proj w) (.headState p)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.headState p)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.headState p)).run w).2)) ∧
    (∀ p rev, allowedPkgStep (proj w) (.revParseCommit p rev)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.revParseCommit p rev)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.revParseCommit p rev)).run w).2)) ∧
    (∀ p a d, allowedPkgStep (proj w) (.isAncestor p a d)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.isAncestor p a d)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.isAncestor p a d)).run w).2)) ∧
    (∀ p a b, allowedPkgStep (proj w) (.mergeBase? p a b)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.mergeBase? p a b)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.mergeBase? p a b)).run w).2)) ∧
    (∀ p, allowedPkgStep (proj w) (.status p)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.status p)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.status p)).run w).2)) ∧
    (∀ p rA rB? ps, allowedPkgStep (proj w) (.diffNameStatus p rA rB? ps)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.diffNameStatus p rA rB? ps)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.diffNameStatus p rA rB? ps)).run w).2)) ∧
    (∀ p, allowedPkgStep (proj w) (.listWorktrees p)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.listWorktrees p)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.listWorktrees p)).run w).2)) ∧
    (∀ p rev rel, allowedPkgStep (proj w) (.showFile? p rev rel)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.showFile? p rev rel)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.showFile? p rev rel)).run w).2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_isRepo hCaps w hwf p
  · intro p; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_repoRoot hCaps w hwf p
  · intro p; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_commonDir hCaps w hwf p
  · intro p; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_headCommit hCaps w hwf p
  · intro p; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_headBranch hCaps w hwf p
  · intro p; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_headState hCaps w hwf p
  · intro p rev; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_revParseCommit hCaps w hwf p rev
  · intro p a d; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_isAncestor hCaps w hwf p a d
  · intro p a b; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_mergeBase hCaps w hwf p a b
  · intro p; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_status hCaps w hwf p
  · intro p rA rB? ps; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_diffNameStatus hCaps w hwf p rA rB? ps
  · intro p; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_listWorktrees hCaps w hwf p
  · intro p rev rel; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_showFile hCaps w hwf p rev rel

end LeanSwe.Git.Proofs
