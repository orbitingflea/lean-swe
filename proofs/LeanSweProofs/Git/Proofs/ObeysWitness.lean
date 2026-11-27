import Core.Obeys
import LeanSwe.EnvVars.Types
import LeanSweProofs.EnvVars.Model
import LeanSwe.Process.Types
import LeanSweProofs.Process.Model
import LeanSwe.Git.Types
import LeanSweProofs.Git.Model
import LeanSweProofs.Git.Model.Refines
import LeanSwe.Git.Impl
import LeanSweProofs.Git.Proofs.ObeysBase
import LeanSweProofs.Git.Proofs.ObeysParsers
import LeanSweProofs.Git.Proofs.ObeysQueryOps1
import LeanSweProofs.Git.Proofs.ObeysQueryOps2
import LeanSweProofs.Git.Proofs.ObeysMutOps1
import LeanSweProofs.Git.Proofs.ObeysMutOps2

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open LeanSwe.EnvVars
open LeanSwe.Process
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Full compositional `Core.ObeysStepFromFinally` proof for `Impl.mkApiFromCapsM` over all 26 `GitApiM` operations. -/
theorem obeysStepFromFinally_mkApiFromCapsM :
    Core.ObeysStepFromFinally id hostStepWf
      execCapsStep allowedHostCapsStep
      hostStepWf Impl.mkApiFromCapsM
      execPkgStep allowedPkgStep := by
  intro W proj caps hCaps w req hwf
  have hQ := obeys_query_step hCaps w hwf
  have hM := obeys_mut_step hCaps w hwf
  cases req with
  | isRepo p => exact hQ.1 p
  | repoRoot p => exact hQ.2.1 p
  | commonDir p => exact hQ.2.2.1 p
  | headCommit? p => exact hQ.2.2.2.1 p
  | headBranch? p => exact hQ.2.2.2.2.1 p
  | headState p => exact hQ.2.2.2.2.2.1 p
  | revParseCommit p rev => exact hQ.2.2.2.2.2.2.1 p rev
  | isAncestor p a d => exact hQ.2.2.2.2.2.2.2.1 p a d
  | mergeBase? p a b => exact hQ.2.2.2.2.2.2.2.2.1 p a b
  | status p => exact hQ.2.2.2.2.2.2.2.2.2.1 p
  | diffNameStatus p rA rB? ps => exact hQ.2.2.2.2.2.2.2.2.2.2.1 p rA rB? ps
  | listWorktrees p => exact hQ.2.2.2.2.2.2.2.2.2.2.2.1 p
  | showFile? p rev rel => exact hQ.2.2.2.2.2.2.2.2.2.2.2.2 p rev rel
  | init p bare b? => exact hM.1 p bare b?
  | clone src dst opts => exact hM.2.1 src dst opts
  | add p ps all => exact hM.2.2.1 p ps all
  | commit p opts => exact hM.2.2.2.1 p opts
  | createBranch p b sp? f => exact hM.2.2.2.2.1 p b sp? f
  | deleteBranch p b f => exact hM.2.2.2.2.2.1 p b f
  | checkout p t f => exact hM.2.2.2.2.2.2.1 p t f
  | switch p b c sp? f => exact hM.2.2.2.2.2.2.2.1 p b c sp? f
  | reset p m rev => exact hM.2.2.2.2.2.2.2.2.1 p m rev
  | fetch p rem ref? pr => exact hM.2.2.2.2.2.2.2.2.2.1 p rem ref? pr
  | worktreeAdd p opts => exact hM.2.2.2.2.2.2.2.2.2.2.1 p opts
  | worktreeRemove p wt f => exact hM.2.2.2.2.2.2.2.2.2.2.2.1 p wt f
  | withWorktree p opts actRes => exact hM.2.2.2.2.2.2.2.2.2.2.2.2 p opts actRes

private def modelEnvApi : EnvVarsApiM (StateM GitHostState) :=
  { mapRawError := LeanSwe.EnvVars.Model.mapRawErrorModel
    getEnv := fun k s => (LeanSwe.EnvVars.Model.getEnvModel s.env k, s)
    listEnv := fun s => (LeanSwe.EnvVars.Model.listEnvModel s.env, s)
    homeDir := fun s => (LeanSwe.EnvVars.Model.homeDirModel s.env, s)
    splitSearchPath := LeanSwe.EnvVars.Model.splitSearchPathModel }

private def emptyExecResult : ExecResult :=
  { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }

private def modelProcApi : ProcessApiM (StateM GitHostState) :=
  { mapRawError := LeanSwe.Process.Model.mapRawErrorModel
    validateRequest := LeanSwe.Process.Model.validateRequestModel
    mkCommandRequest := LeanSwe.Process.Model.mkCommandRequestModel
    withTextInput := LeanSwe.Process.Model.withTextInputModel
    spawn := fun req s =>
      match LeanSwe.Process.Model.validateSpawnRequestModel req with
      | .error e => (.error e, s)
      | .ok _ =>
        let hid := s.proc.nextHandleId
        let h : ProcessHandle := { handleId := hid, pid := 1, pgid := 1 }
        let entry : LeanSwe.Process.Model.ProcessHandleEntry :=
          { handleId := hid, pid := 1, pgid := 1, ioConsumed := false, waited := false }
        (.ok h, { s with proc := { nextHandleId := hid + 1, activeHandles := entry :: s.proc.activeHandles } })
    awaitOutput := fun h _ timeoutMs _ s =>
      if timeoutMs == some 0 then
        (.error { kind := .invalidInput, message := "timeoutMs must be greater than zero" }, s)
      else if (s.proc.activeHandles.map (·.handleId)).contains h.handleId then
        (.ok (.exited emptyExecResult), s)
      else
        (.error { kind := .invalidInput, message := "unknown process handle" }, s)
    killProcessGroup := fun _ s => (.ok (), s)
    reap := fun h s =>
      (.ok (), { s with proc := { s.proc with activeHandles := s.proc.activeHandles.filter (·.handleId != h.handleId) } })
    run := fun req s =>
      match LeanSwe.Process.Model.validateRequestModel req with
      | .error e => (.error e, s)
      | .ok _ => (.ok emptyExecResult, s)
    runChecked := fun req s =>
      match LeanSwe.Process.Model.validateRequestModel req with
      | .error e => (.error e, s)
      | .ok _ => (.ok emptyExecResult, s)
    runCommand := fun prog args s =>
      match LeanSwe.Process.Model.validateRequestModel (LeanSwe.Process.Model.mkCommandRequestModel prog args) with
      | .error e => (.error e, s)
      | .ok _ => (.ok emptyExecResult, s)
    runCommandChecked := fun prog args s =>
      match LeanSwe.Process.Model.validateRequestModel (LeanSwe.Process.Model.mkCommandRequestModel prog args) with
      | .error e => (.error e, s)
      | .ok _ => (.ok emptyExecResult, s)
    activeProcessCount := fun s => (s.proc.activeHandles.length, s) }

/-- Concrete `GitHostCapsM (StateM GitHostState)` witness inhabiting `allowedHostCapsStep`. -/
def modelHostCaps : GitHostCapsM (StateM GitHostState) :=
  { env := modelEnvApi, proc := modelProcApi }

private theorem list_not_contains_of_all_lt (xs : List LeanSwe.Process.Model.ProcessHandleEntry) (n : Nat)
    (hAll : ∀ e ∈ xs, e.handleId < n) :
    (xs.map (·.handleId)).contains n = false := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff]
    refine ⟨?_, ih (fun e he => hAll e (List.mem_cons_of_mem x he))⟩
    have hlt := hAll x List.mem_cons_self
    exact beq_false_of_ne (Nat.ne_of_gt hlt)

private theorem hasNoDupHandleIds_filter (xs : List LeanSwe.Process.Model.ProcessHandleEntry)
    (hid : Nat) (hNd : LeanSwe.Process.Model.hasNoDupHandleIds (xs.map (·.handleId)) = true) :
    LeanSwe.Process.Model.hasNoDupHandleIds ((xs.filter (·.handleId != hid)).map (·.handleId)) = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, LeanSwe.Process.Model.hasNoDupHandleIds, Bool.and_eq_true,
      Bool.not_eq_true'] at hNd
    simp only [List.filter_cons]
    split
    · simp only [List.map_cons, LeanSwe.Process.Model.hasNoDupHandleIds, Bool.and_eq_true,
        Bool.not_eq_true']
      refine ⟨?_, ih hNd.2⟩
      cases hc : ((rest.filter (·.handleId != hid)).map (·.handleId)).contains x.handleId with
      | false => rfl
      | true =>
        exfalso
        have hMem : x.handleId ∈ (rest.filter (·.handleId != hid)).map (·.handleId) :=
          List.contains_iff_mem.mp hc
        rcases List.mem_map.mp hMem with ⟨y, hy, hyEq⟩
        have hyRest : y ∈ rest := (List.mem_filter.mp hy).1
        have hInRest : x.handleId ∈ rest.map (·.handleId) := List.mem_map.mpr ⟨y, hyRest, hyEq⟩
        have hTrue : (rest.map (·.handleId)).contains x.handleId = true :=
          List.contains_iff_mem.mpr hInRest
        rw [hTrue] at hNd
        cases hNd.1
    · exact ih hNd.2

private theorem processStateWf_spawn (s : LeanSwe.Process.Model.ProcessModelState)
    (hwf : LeanSwe.Process.Model.processStateWf s = true) :
    LeanSwe.Process.Model.processStateWf
      { nextHandleId := s.nextHandleId + 1
        activeHandles :=
          { handleId := s.nextHandleId, pid := 1, pgid := 1, ioConsumed := false, waited := false } ::
            s.activeHandles } = true := by
  unfold LeanSwe.Process.Model.processStateWf at hwf ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf ⊢
  rcases hwf with ⟨⟨hGe, hNd⟩, hAll⟩
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · simp only [List.map_cons, LeanSwe.Process.Model.hasNoDupHandleIds, Bool.and_eq_true,
      Bool.not_eq_true']
    refine ⟨list_not_contains_of_all_lt s.activeHandles s.nextHandleId (fun e he => (hAll e he).1.1), hNd⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | hmem
    · exact ⟨⟨Nat.lt_succ_self _, by dsimp; decide⟩, by dsimp; decide⟩
    · have hE := hAll e hmem
      exact ⟨⟨Nat.lt_succ_of_lt hE.1.1, hE.1.2⟩, hE.2⟩

private theorem processStateWf_reap (s : LeanSwe.Process.Model.ProcessModelState) (hid : Nat)
    (hwf : LeanSwe.Process.Model.processStateWf s = true) :
    LeanSwe.Process.Model.processStateWf
      { s with activeHandles := s.activeHandles.filter (·.handleId != hid) } = true := by
  unfold LeanSwe.Process.Model.processStateWf at hwf ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf ⊢
  rcases hwf with ⟨⟨hGe, hNd⟩, hAll⟩
  refine ⟨⟨hGe, hasNoDupHandleIds_filter s.activeHandles hid hNd⟩, ?_⟩
  intro e he
  exact hAll e (List.mem_filter.mp he).1

/-- Proof that `modelHostCaps` obeys `allowedHostCapsStep` on every well-formed `GitHostState`. -/
theorem modelHostCaps_obeys_allowedHostCapsStep :
    Core.ObeysStep id hostStepWf (execCapsStep modelHostCaps) allowedHostCapsStep := by
  intro s req hwf
  cases req with
  | env er =>
    cases er <;>
      exact ⟨hwf, hwf, rfl, rfl, rfl⟩
  | proc pr =>
    cases pr with
    | spawn r =>
      dsimp only [execCapsStep, modelHostCaps, modelProcApi, LeanSwe.Process.Model.execPkgStep]
      rw [stateM_map_run, stateM_map_run]
      dsimp only [StateT.run, allowedHostCapsStep, LeanSwe.Process.Model.allowedPkgStep]
      cases hv : LeanSwe.Process.Model.validateSpawnRequestModel r with
      | error e => exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, rfl⟩
      | ok _ =>
        have hwf' := processStateWf_spawn s.proc hwf
        exact ⟨hwf, hwf', rfl, hwf, hwf', rfl, by dsimp; decide, by dsimp; decide, rfl⟩
    | awaitOutput h stdin timeoutMs maxOut =>
      dsimp only [execCapsStep, modelHostCaps, modelProcApi, LeanSwe.Process.Model.execPkgStep]
      rw [stateM_map_run, stateM_map_run]
      dsimp only [StateT.run, allowedHostCapsStep, LeanSwe.Process.Model.allowedPkgStep]
      cases ht : (timeoutMs == some 0) with
      | true =>
        simp only [↓reduceIte]
        exact ⟨hwf, hwf, trivial, hwf, hwf, trivial, trivial⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hc : (s.proc.activeHandles.map (·.handleId)).contains h.handleId with
        | true =>
          simp only [↓reduceIte]
          refine ⟨hwf, hwf, trivial, hwf, hwf, hwf, rfl, rfl, rfl, List.contains_iff_mem.mp hc, ?_⟩
          intro lim _
          exact Nat.zero_le lim
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hwf, hwf, trivial, hwf, hwf, hwf, rfl, rfl, rfl,
            by decide, by decide, by decide, by decide, by decide⟩
    | killProcessGroup _ =>
      exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, trivial⟩
    | reap h =>
      have hwf' := processStateWf_reap s.proc h.handleId hwf
      exact ⟨hwf, hwf', rfl, hwf, hwf', rfl, rfl, trivial⟩
    | run r =>
      dsimp only [execCapsStep, modelHostCaps, modelProcApi, LeanSwe.Process.Model.execPkgStep]
      rw [stateM_map_run, stateM_map_run]
      dsimp only [StateT.run, allowedHostCapsStep, LeanSwe.Process.Model.allowedPkgStep,
        LeanSwe.Process.Model.allowedPkgRun, LeanSwe.Process.Model.allowedExecResult]
      cases hv : LeanSwe.Process.Model.validateRequestModel r with
      | error e => exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, rfl⟩
      | ok _ =>
        exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, Or.inl rfl, fun h => Bool.noConfusion h, fun lim _ => Nat.zero_le lim⟩
    | runChecked r =>
      dsimp only [execCapsStep, modelHostCaps, modelProcApi, LeanSwe.Process.Model.execPkgStep]
      rw [stateM_map_run, stateM_map_run]
      dsimp only [StateT.run, allowedHostCapsStep, LeanSwe.Process.Model.allowedPkgStep,
        LeanSwe.Process.Model.allowedPkgRun, LeanSwe.Process.Model.allowedExecResult]
      cases hv : LeanSwe.Process.Model.validateRequestModel r with
      | error e => exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, rfl⟩
      | ok _ =>
        exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, Or.inl rfl, fun _ => rfl, fun lim _ => Nat.zero_le lim⟩
    | runCommand prog args =>
      dsimp only [execCapsStep, modelHostCaps, modelProcApi, LeanSwe.Process.Model.execPkgStep]
      rw [stateM_map_run, stateM_map_run]
      dsimp only [StateT.run, allowedHostCapsStep, LeanSwe.Process.Model.allowedPkgStep,
        LeanSwe.Process.Model.allowedPkgRun, LeanSwe.Process.Model.allowedExecResult]
      cases hv : LeanSwe.Process.Model.validateRequestModel (LeanSwe.Process.Model.mkCommandRequestModel prog args) with
      | error e => exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, rfl⟩
      | ok _ =>
        exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, Or.inl rfl, fun h => Bool.noConfusion h, fun lim _ => Nat.zero_le lim⟩
    | runCommandChecked prog args =>
      dsimp only [execCapsStep, modelHostCaps, modelProcApi, LeanSwe.Process.Model.execPkgStep]
      rw [stateM_map_run, stateM_map_run]
      dsimp only [StateT.run, allowedHostCapsStep, LeanSwe.Process.Model.allowedPkgStep,
        LeanSwe.Process.Model.allowedPkgRun, LeanSwe.Process.Model.allowedExecResult]
      cases hv : LeanSwe.Process.Model.validateRequestModel (LeanSwe.Process.Model.mkCommandRequestModel prog args) with
      | error e => exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, rfl⟩
      | ok _ =>
        exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, Or.inl rfl, fun _ => rfl, fun lim _ => Nat.zero_le lim⟩
    | activeProcessCount =>
      exact ⟨hwf, hwf, rfl, hwf, hwf, rfl, rfl⟩

end LeanSwe.Git.Proofs
