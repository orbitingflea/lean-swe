import Core.Obeys
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Model.Refines
import LeanSwe.Git.Impl
import LeanSwe.Git.Proofs.ObeysBase
import LeanSwe.Git.Proofs.ObeysMutOps1

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open LeanSwe.Git
open LeanSwe.Git.Model

private theorem obeys_switch {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true)
    (p : String) (b : RefName) (create : Bool) (sp? : Option String) (force : Bool) :
    let r := (Impl.switchImpl (Impl.mkRawOpsM caps) p b create sp? force).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateSwitch p b create sp?)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.switchImpl Impl.validateRepoPath preValidateSwitch
  simp only [except_bind_eq, Except.bind]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError]
    cases hb : isValidRefNameStr b.raw with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hCr : (!create && sp?.isSome) with
      | true =>
        simp only [↓reduceIte, stateM_pure_run, allowedGuardedStep]
        exact ⟨trivial, hwf, trivial, by decide⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases sp? with
        | none =>
          dsimp only
          apply bind_checked_unit_parse hCaps "switch"
            { cwd := some p
              args := #["switch"] ++ (if force then #["--force"] else #[]) ++
                (if create then #[if force then "-C" else "-c", b.raw] else #[b.raw]) ++ #[] } w hwf <;> (intro _; rfl)
        | some sp =>
          dsimp only
          cases hSp : isValidStrictRevSpec sp with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
            exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
          | true =>
            simp only [↓reduceIte]
            apply bind_checked_unit_parse hCaps "switch"
              { cwd := some p
                args := #["switch"] ++ (if force then #["--force"] else #[]) ++
                  (if create then #[if force then "-C" else "-c", b.raw] else #[b.raw]) ++ #[sp] } w hwf <;> (intro _; rfl)

private theorem obeys_reset {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) (mode : ResetMode) (rev : String) :
    let r := (Impl.resetImpl (Impl.mkRawOpsM caps) p mode rev).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateReset p rev)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.resetImpl Impl.validateRepoPath preValidateReset
  simp only [except_bind_eq, Except.bind]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError]
    cases hr : isValidStrictRevSpec rev with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      apply bind_checked_unit_parse hCaps "reset"
        { cwd := some p
          args := #["reset", match mode with | .soft => "--soft" | .mixed => "--mixed" | .hard => "--hard", rev, "--"] } w hwf <;> (intro _; rfl)

private theorem obeys_fetch {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true)
    (p rem : String) (ref? : Option String) (prune : Bool) :
    let r := (Impl.fetchImpl (Impl.mkRawOpsM caps) p rem ref? prune).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateFetch p rem ref?)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.fetchImpl Impl.validateRepoPath preValidateFetch
  simp only [except_bind_eq, Except.bind]
  cases hv : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv⟩
  | ok _ =>
    simp only [Except.mapError]
    cases hRem : isValidRemoteOrRefspec rem with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases ref? with
      | none =>
        dsimp only
        apply bind_checked_unit_parse hCaps "fetch"
          { cwd := some p, args := #["fetch"] ++ (if prune then #["--prune"] else #[]) ++ #[rem] ++ #[] } w hwf <;> (intro _; rfl)
      | some r =>
        dsimp only
        cases hR : isValidRemoteOrRefspec r with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
          exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
        | true =>
          simp only [↓reduceIte]
          apply bind_checked_unit_parse hCaps "fetch"
            { cwd := some p, args := #["fetch"] ++ (if prune then #["--prune"] else #[]) ++ #[rem] ++ #[r] } w hwf <;> (intro _; rfl)

private theorem obeys_worktreeAdd {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p : String) (opts : WorktreeAddOptions) :
    let r := (Impl.worktreeAddImpl (Impl.mkRawOpsM caps) p opts).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateWorktreeAdd p opts)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.worktreeAddImpl Impl.validateRepoPath preValidateWorktreeAdd
  simp only [except_bind_eq, Except.bind]
  cases hv1 : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv1⟩
  | ok _ =>
    simp only [Except.mapError]
    cases hv2 : validateFsPathArg opts.path with
    | error e =>
      simp only [stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv2⟩
    | ok _ =>
      cases hComb : (opts.detach && opts.newBranch?.isSome) with
      | true =>
        simp only [↓reduceIte, stateM_pure_run, allowedGuardedStep]
        exact ⟨trivial, hwf, trivial, by decide⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hAfterBranch : ∀ (bArgs : Array String),
            let r :=
              (match
                  (match opts.target? with
                  | none => Except.ok #[]
                  | some t =>
                    if isValidStrictRevSpec t then Except.ok #[t]
                    else Except.error { kind := .invalidInput, message := s!"invalid worktree target: '{t}'" }
                    : Except GitError (Array String)) with
                | .error e => (pure (.error e) : StateM W (Except GitError Unit))
                | .ok tArgs => do
                  match ← Impl.runGitChecked (Impl.mkRawOpsM caps) "worktree"
                      { cwd := some p
                        args := #["worktree", "add"] ++ (if opts.force then #["--force"] else #[]) ++
                          (if opts.detach then #["--detach"] else #[]) ++ bArgs ++ #["--", opts.path] ++ tArgs } with
                  | .error e => return .error e
                  | .ok _ => return .ok ()).run w
            allowedGuardedStep (proj w) (proj r.2)
              (match opts.target? with
                | none => .ok ()
                | some t => if isValidStrictRevSpec t then .ok () else .error .invalidInput)
              [.parseError] (fun _ => True) r.1 := by
          intro bArgs
          cases opts.target? with
          | none =>
            dsimp only
            apply bind_checked_unit_parse hCaps "worktree"
              { cwd := some p
                args := #["worktree", "add"] ++ (if opts.force then #["--force"] else #[]) ++
                  (if opts.detach then #["--detach"] else #[]) ++ bArgs ++ #["--", opts.path] ++ #[] } w hwf <;> (intro _; rfl)
          | some t =>
            dsimp only
            cases ht : isValidStrictRevSpec t with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
              exact ⟨trivial, hwf, trivial, interp3_ne_empty _ _ _ (by decide)⟩
            | true =>
              simp only [↓reduceIte]
              apply bind_checked_unit_parse hCaps "worktree"
                { cwd := some p
                  args := #["worktree", "add"] ++ (if opts.force then #["--force"] else #[]) ++
                    (if opts.detach then #["--detach"] else #[]) ++ bArgs ++ #["--", opts.path] ++ #[t] } w hwf <;> (intro _; rfl)
        cases opts.newBranch? with
        | none => exact hAfterBranch #[]
        | some b =>
          dsimp only
          cases hb : isValidRefNameStr b.raw with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run, allowedGuardedStep]
            exact ⟨trivial, hwf, rfl, interp3_ne_empty _ _ _ (by decide)⟩
          | true =>
            simp only [↓reduceIte]
            exact hAfterBranch #["-b", b.raw]

private theorem obeys_worktreeRemove {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) (p wt : String) (force : Bool) :
    let r := (Impl.worktreeRemoveImpl (Impl.mkRawOpsM caps) p wt force).run w
    allowedGuardedStep (proj w) (proj r.2) (preValidateWorktreeRemove p wt)
      [.parseError] (fun _ => True) r.1 := by
  unfold Impl.worktreeRemoveImpl Impl.validateRepoPath preValidateWorktreeRemove
  simp only [except_bind_eq, Except.bind]
  cases hv1 : validateFsPathArg p with
  | error e =>
    simp only [Except.mapError, stateM_pure_run, allowedGuardedStep]
    exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv1⟩
  | ok _ =>
    simp only [Except.mapError]
    cases hv2 : validateFsPathArg wt with
    | error e =>
      simp only [stateM_pure_run, allowedGuardedStep]
      exact ⟨trivial, hwf, trivial, validateFsPathArg_err_nonEmpty hv2⟩
    | ok _ =>
      apply bind_checked_unit_parse hCaps "worktree"
        { cwd := some p, args := #["worktree", "remove"] ++ (if force then #["--force"] else #[]) ++ #["--", wt] } w hwf <;> (intro _; rfl)

private theorem preValidateWorktreeAdd_implies_remove {p : String} {opts : WorktreeAddOptions}
    (h : preValidateWorktreeAdd p opts = .ok ()) :
    preValidateWorktreeRemove p opts.path = .ok () := by
  unfold preValidateWorktreeAdd at h
  unfold preValidateWorktreeRemove
  simp only [except_bind_eq, Except.bind] at h ⊢
  cases hv1 : validateFsPathArg p with
  | error _ => simp [hv1, Except.mapError] at h
  | ok _ =>
    cases hv2 : validateFsPathArg opts.path with
    | error _ => simp [hv1, hv2, Except.mapError] at h
    | ok _ => simp [Except.mapError]

private theorem obeys_withWorktree {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true)
    (p : String) (opts : WorktreeAddOptions) (actRes : Except GitError Nat) :
    let r := (Impl.withWorktreeImpl (Impl.mkRawOpsM caps) p opts (fun _ => pure actRes)).run w
    allowedPkgStep (proj w) (.withWorktree p opts actRes) (.withWt r.1) (proj r.2) := by
  unfold Impl.withWorktreeImpl allowedPkgStep
  dsimp only
  rw [stateM_bind_run]
  have hAdd := obeys_worktreeAdd hCaps w hwf p opts
  dsimp only at hAdd
  cases hPre : preValidateWorktreeAdd p opts with
  | error k =>
    rw [hPre] at hAdd
    simp only [allowedGuardedStep] at hAdd
    rcases hAdd with ⟨hEq, _, hRes⟩
    cases hAddR : ((Impl.worktreeAddImpl (Impl.mkRawOpsM caps) p opts).run w).1 with
    | ok _ => rw [hAddR] at hRes; exact False.elim hRes
    | error e =>
      rw [hAddR] at hRes
      simp only [stateM_pure_run]
      exact ⟨hEq, hwf, hRes⟩
  | ok u =>
    cases u
    rw [hPre] at hAdd
    simp only [allowedGuardedStep] at hAdd
    cases hAddR : ((Impl.worktreeAddImpl (Impl.mkRawOpsM caps) p opts).run w).1 with
    | error e =>
      rw [hAddR] at hAdd
      simp only [stateM_pure_run]
      refine ⟨hAdd.1, ?_⟩
      cases actRes with
      | ok _ => exact Or.inr ⟨e, rfl, hAdd.2⟩
      | error _ => exact Or.inr ⟨e, rfl, hAdd.2⟩
    | ok _ =>
      rw [hAddR] at hAdd
      dsimp only
      rw [stateM_bind_run, stateM_tryFinally'_run]
      simp only [stateM_pure_run]
      have hRem := obeys_worktreeRemove hCaps
        ((Impl.worktreeAddImpl (Impl.mkRawOpsM caps) p opts).run w).2 hAdd.1.2.1 p opts.path opts.force
      dsimp only at hRem
      rw [preValidateWorktreeAdd_implies_remove hPre] at hRem
      simp only [allowedGuardedStep] at hRem
      have hTrans := allowedHostTransition_trans hAdd.1 hRem.1
      cases actRes with
      | error ae =>
        cases hRemR : ((Impl.worktreeRemoveImpl (Impl.mkRawOpsM caps) p opts.path opts.force).run _).1 <;>
          (simp only [stateM_pure_run]; exact ⟨hTrans, Or.inl trivial⟩)
      | ok a =>
        cases hRemR : ((Impl.worktreeRemoveImpl (Impl.mkRawOpsM caps) p opts.path opts.force).run _).1 with
        | ok _ =>
          simp only [stateM_pure_run]
          exact ⟨hTrans, Or.inl trivial⟩
        | error ce =>
          rw [hRemR] at hRem
          simp only [stateM_pure_run]
          exact ⟨hTrans, Or.inr ⟨ce, rfl, hRem.2⟩⟩

/-- Dispatch step proof covering all 13 mutation and bracketed `PkgStepReq` variants. -/
theorem obeys_mut_step {W : Type} {proj : W → GitHostState} {caps : GitHostCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj hostStepWf (execCapsStep caps) allowedHostCapsStep)
    (w : W) (hwf : hostStepWf (proj w) = true) :
    (∀ p bare b?, allowedPkgStep (proj w) (.init p bare b?)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.init p bare b?)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.init p bare b?)).run w).2)) ∧
    (∀ src dst opts, allowedPkgStep (proj w) (.clone src dst opts)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.clone src dst opts)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.clone src dst opts)).run w).2)) ∧
    (∀ p ps all, allowedPkgStep (proj w) (.add p ps all)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.add p ps all)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.add p ps all)).run w).2)) ∧
    (∀ p opts, allowedPkgStep (proj w) (.commit p opts)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.commit p opts)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.commit p opts)).run w).2)) ∧
    (∀ p b sp? f, allowedPkgStep (proj w) (.createBranch p b sp? f)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.createBranch p b sp? f)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.createBranch p b sp? f)).run w).2)) ∧
    (∀ p b f, allowedPkgStep (proj w) (.deleteBranch p b f)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.deleteBranch p b f)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.deleteBranch p b f)).run w).2)) ∧
    (∀ p t f, allowedPkgStep (proj w) (.checkout p t f)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.checkout p t f)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.checkout p t f)).run w).2)) ∧
    (∀ p b c sp? f, allowedPkgStep (proj w) (.switch p b c sp? f)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.switch p b c sp? f)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.switch p b c sp? f)).run w).2)) ∧
    (∀ p m rev, allowedPkgStep (proj w) (.reset p m rev)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.reset p m rev)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.reset p m rev)).run w).2)) ∧
    (∀ p rem ref? pr, allowedPkgStep (proj w) (.fetch p rem ref? pr)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.fetch p rem ref? pr)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.fetch p rem ref? pr)).run w).2)) ∧
    (∀ p opts, allowedPkgStep (proj w) (.worktreeAdd p opts)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.worktreeAdd p opts)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.worktreeAdd p opts)).run w).2)) ∧
    (∀ p wt f, allowedPkgStep (proj w) (.worktreeRemove p wt f)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.worktreeRemove p wt f)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.worktreeRemove p wt f)).run w).2)) ∧
    (∀ p opts actRes, allowedPkgStep (proj w) (.withWorktree p opts actRes)
      ((execPkgStep (Impl.mkApiFromCapsM caps) (.withWorktree p opts actRes)).run w).1
      (proj ((execPkgStep (Impl.mkApiFromCapsM caps) (.withWorktree p opts actRes)).run w).2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p bare b?; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_init hCaps w hwf p bare b?
  · intro src dst opts; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_clone hCaps w hwf src dst opts
  · intro p ps all; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_add hCaps w hwf p ps all
  · intro p opts; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_commit hCaps w hwf p opts
  · intro p b sp? f; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_createBranch hCaps w hwf p b sp? f
  · intro p b f; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_deleteBranch hCaps w hwf p b f
  · intro p t f; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_checkout hCaps w hwf p t f
  · intro p b c sp? f; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_switch hCaps w hwf p b c sp? f
  · intro p m rev; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_reset hCaps w hwf p m rev
  · intro p rem ref? pr; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_fetch hCaps w hwf p rem ref? pr
  · intro p opts; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_worktreeAdd hCaps w hwf p opts
  · intro p wt f; dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]; rw [stateM_map_run]; exact obeys_worktreeRemove hCaps w hwf p wt f
  · intro p opts actRes
    dsimp only [execPkgStep, Impl.mkApiFromCapsM, Impl.mkApiM]
    rw [stateM_map_run]
    exact obeys_withWorktree hCaps w hwf p opts actRes

end LeanSwe.Git.Proofs
