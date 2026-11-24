import LeanSwe.Process.Types
import LeanSwe.Process.Model.HealthySim
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Interface
import LeanSwe.Process.Impl
import LeanSwe.Process.SpecTests
import LeanSwe.Process.Proofs.EndToEnd
import LeanSwe.Process.Proofs.PureSpecs

namespace LeanSwe.Process.Proofs

open Core
open Core.NondetTest
open LeanSwe.Process

local notation "healthySimApiExpr" =>
  Internal.mkApiM
    (SysBridge.mkRawOpsM Model.Internal.healthySimDeps
      (SysBridge.stateProcTableOps Model.Internal.HealthySimState.tbl Model.Internal.setSimTbl)
      4 8)

/-- Proof of `test_process_run_invalidRequest_doesNotLeak` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_run_invalidRequest_doesNotLeak :
    AllPass (test_process_run_invalidRequest_doesNotLeak healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.1

/-- Non-vacuity `CanReach` witness for `test_process_run_invalidRequest_doesNotLeak`. -/
theorem reach_process_run_invalidRequest_doesNotLeak :
    CanReach (test_process_run_invalidRequest_doesNotLeak healthySimApiExpr) :=
  ⟨{}, { program := "" }, proof_process_run_invalidRequest_doesNotLeak {} { program := "" }⟩

/-- Proof of `test_process_run_usesNormalizedRequest` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_run_usesNormalizedRequest :
    AllPass (test_process_run_usesNormalizedRequest healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_usesNormalizedRequest`. -/
theorem reach_process_run_usesNormalizedRequest :
    CanReach (test_process_run_usesNormalizedRequest healthySimApiExpr) :=
  ⟨{}, { program := "/bin/true" }, proof_process_run_usesNormalizedRequest {} { program := "/bin/true" }⟩

/-- Proof of `test_process_runCommand_eq_runMkCommandRequest` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_runCommand_eq_runMkCommandRequest :
    AllPass (test_process_runCommand_eq_runMkCommandRequest healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runCommand_eq_runMkCommandRequest`. -/
theorem reach_process_runCommand_eq_runMkCommandRequest :
    CanReach (test_process_runCommand_eq_runMkCommandRequest healthySimApiExpr) :=
  ⟨{}, "/bin/true", #["a"], proof_process_runCommand_eq_runMkCommandRequest {} "/bin/true" #["a"]⟩

/-- Proof of `test_process_runCommandChecked_eq_runCheckedMkCommandRequest` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_runCommandChecked_eq_runCheckedMkCommandRequest :
    AllPass (test_process_runCommandChecked_eq_runCheckedMkCommandRequest healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runCommandChecked_eq_runCheckedMkCommandRequest`. -/
theorem reach_process_runCommandChecked_eq_runCheckedMkCommandRequest :
    CanReach (test_process_runCommandChecked_eq_runCheckedMkCommandRequest healthySimApiExpr) :=
  ⟨{}, "/bin/true", #["a"], proof_process_runCommandChecked_eq_runCheckedMkCommandRequest {} "/bin/true" #["a"]⟩

/-- Proof of `test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_run_allowsNonZeroExit_and_runChecked_rejectsIt :
    AllPass (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt`. -/
theorem reach_process_run_allowsNonZeroExit_and_runChecked_rejectsIt :
    CanReach (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt healthySimApiExpr) := by
  let req : ExecRequest := { program := "/bin/exit1", inheritEnv := false }
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_run_allowsNonZeroExit_and_runChecked_rejectsIt {} req
  dsimp only [AllPass, CanReach, test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt, nondet, bind] at hAll ⊢
  cases hRun : ((healthySimApiExpr).run req).run {} with
  | mk res s₁ =>
    cases res with
    | error _ =>
      have hOk : (((healthySimApiExpr).run req).run {}).1.isOk = true := by decide +kernel
      rw [hRun] at hOk; cases hOk
    | ok out =>
      have hNz : out.exitCode ≠ 0 := by
        have hb : (match (((healthySimApiExpr).run req).run {}).1 with | .ok o => o.exitCode != 0 | .error _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact bne_iff_ne.mp hb
      cases hChk : ((healthySimApiExpr).runChecked req).run {} with
      | mk cr s₂ =>
        rw [hRun, hChk] at hAll
        dsimp only [assume, assert] at hAll ⊢
        exact ⟨hNz, hAll hNz⟩

/-- Proof of `test_process_runChecked_zeroExit_matchesRun` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_runChecked_zeroExit_matchesRun :
    AllPass (test_process_runChecked_zeroExit_matchesRun healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_zeroExit_matchesRun`. -/
theorem reach_process_runChecked_zeroExit_matchesRun :
    CanReach (test_process_runChecked_zeroExit_matchesRun healthySimApiExpr) := by
  let req : ExecRequest := { program := "/bin/true", inheritEnv := false }
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_runChecked_zeroExit_matchesRun {} req
  dsimp only [AllPass, CanReach, test_process_runChecked_zeroExit_matchesRun, nondet, bind] at hAll ⊢
  cases hRun : ((healthySimApiExpr).run req).run {} with
  | mk res s₁ =>
    cases res with
    | error _ =>
      have hOk : (((healthySimApiExpr).run req).run {}).1.isOk = true := by decide +kernel
      rw [hRun] at hOk; cases hOk
    | ok out =>
      have hZ : out.exitCode = 0 := by
        have hb : (match (((healthySimApiExpr).run req).run {}).1 with | .ok o => o.exitCode == 0 | .error _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact beq_iff_eq.mp hb
      rw [hRun] at hAll
      dsimp only [assume, assert] at hAll ⊢
      exact ⟨hZ, hAll hZ⟩

/-- Proof of `test_process_runChecked_propagatesRunError` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_runChecked_propagatesRunError :
    AllPass (test_process_runChecked_propagatesRunError healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_propagatesRunError`. -/
theorem reach_process_runChecked_propagatesRunError :
    CanReach (test_process_runChecked_propagatesRunError healthySimApiExpr) :=
  ⟨{}, { program := "" }, proof_process_runChecked_propagatesRunError {} { program := "" }⟩

/-- Proof of `test_process_run_neverLeaksProcesses` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_run_neverLeaksProcesses :
    AllPass (test_process_run_neverLeaksProcesses healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_neverLeaksProcesses`. -/
theorem reach_process_run_neverLeaksProcesses :
    CanReach (test_process_run_neverLeaksProcesses healthySimApiExpr) :=
  ⟨{}, { program := "" }, proof_process_run_neverLeaksProcesses {} { program := "" }⟩

/-- Proof of `test_process_runChecked_neverLeaksProcesses` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_runChecked_neverLeaksProcesses :
    AllPass (test_process_runChecked_neverLeaksProcesses healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_neverLeaksProcesses`. -/
theorem reach_process_runChecked_neverLeaksProcesses :
    CanReach (test_process_runChecked_neverLeaksProcesses healthySimApiExpr) :=
  ⟨{}, { program := "" }, proof_process_runChecked_neverLeaksProcesses {} { program := "" }⟩

/-- Proof of `test_process_timeout_cleansUpAndErrors` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_timeout_cleansUpAndErrors :
    AllPass (test_process_timeout_cleansUpAndErrors healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_timeout_cleansUpAndErrors`. -/
theorem reach_process_timeout_cleansUpAndErrors :
    CanReach (test_process_timeout_cleansUpAndErrors healthySimApiExpr) := by
  let req : ExecRequest := { program := "/bin/hang", inheritEnv := false, timeoutMs := some 1 }
  have hNe : req.timeoutMs ≠ none := by decide
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_timeout_cleansUpAndErrors {} req hNe
  dsimp only [AllPass, CanReach, test_process_timeout_cleansUpAndErrors, nondet, bind] at hAll ⊢
  refine ⟨hNe, ?_⟩
  cases hRun : ((healthySimApiExpr).run req).run {} with
  | mk res s₁ =>
    cases res with
    | ok _ =>
      have hErr : (((healthySimApiExpr).run req).run {}).1.isOk = false := by decide +kernel
      rw [hRun] at hErr; cases hErr
    | error err =>
      have hK : err.kind = .timedOut := by
        have hb : (match (((healthySimApiExpr).run req).run {}).1 with | .error e => decide (e.kind = .timedOut) | .ok _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact of_decide_eq_true hb
      rw [hRun] at hAll
      dsimp only [assume, assert] at hAll ⊢
      exact ⟨hK, hAll hK⟩

/-- Proof of `test_process_run_noTimeout_neverTimesOut` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_run_noTimeout_neverTimesOut :
    AllPass (test_process_run_noTimeout_neverTimesOut healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_noTimeout_neverTimesOut`. -/
theorem reach_process_run_noTimeout_neverTimesOut :
    CanReach (test_process_run_noTimeout_neverTimesOut healthySimApiExpr) :=
  ⟨{}, { program := "", timeoutMs := none }, rfl,
    proof_process_run_noTimeout_neverTimesOut {} { program := "", timeoutMs := none } rfl⟩

/-- Proof of `test_process_outputLimit_cleansUpAndErrors` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_outputLimit_cleansUpAndErrors :
    AllPass (test_process_outputLimit_cleansUpAndErrors healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_outputLimit_cleansUpAndErrors`. -/
theorem reach_process_outputLimit_cleansUpAndErrors :
    CanReach (test_process_outputLimit_cleansUpAndErrors healthySimApiExpr) := by
  let req : ExecRequest := { program := "/bin/bigout", inheritEnv := false, maxOutputBytes := some 4 }
  have hNe : req.maxOutputBytes ≠ none := by decide
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_outputLimit_cleansUpAndErrors {} req hNe
  dsimp only [AllPass, CanReach, test_process_outputLimit_cleansUpAndErrors, nondet, bind] at hAll ⊢
  refine ⟨hNe, ?_⟩
  cases hRun : ((healthySimApiExpr).run req).run {} with
  | mk res s₁ =>
    cases res with
    | ok _ =>
      have hErr : (((healthySimApiExpr).run req).run {}).1.isOk = false := by decide +kernel
      rw [hRun] at hErr; cases hErr
    | error err =>
      have hK : err.kind = .outputLimitExceeded := by
        have hb : (match (((healthySimApiExpr).run req).run {}).1 with | .error e => decide (e.kind = .outputLimitExceeded) | .ok _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact of_decide_eq_true hb
      rw [hRun] at hAll
      dsimp only [assume, assert] at hAll ⊢
      exact ⟨hK, hAll hK⟩

/-- Proof of `test_process_run_noOutputLimit_neverExceedsLimit` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_run_noOutputLimit_neverExceedsLimit :
    AllPass (test_process_run_noOutputLimit_neverExceedsLimit healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_noOutputLimit_neverExceedsLimit`. -/
theorem reach_process_run_noOutputLimit_neverExceedsLimit :
    CanReach (test_process_run_noOutputLimit_neverExceedsLimit healthySimApiExpr) :=
  ⟨{}, { program := "", maxOutputBytes := none }, rfl,
    proof_process_run_noOutputLimit_neverExceedsLimit {} { program := "", maxOutputBytes := none } rfl⟩

/-- Proof of `test_process_run_respectsMaxOutputBytes` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_run_respectsMaxOutputBytes :
    AllPass (test_process_run_respectsMaxOutputBytes healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_respectsMaxOutputBytes`. -/
theorem reach_process_run_respectsMaxOutputBytes :
    CanReach (test_process_run_respectsMaxOutputBytes healthySimApiExpr) := by
  let req : ExecRequest := { program := "/bin/true", inheritEnv := false, maxOutputBytes := some 10 }
  refine ⟨{}, req, 10, rfl, ?_⟩
  have hAll := proof_process_run_respectsMaxOutputBytes {} req 10 rfl
  dsimp only [AllPass, CanReach, test_process_run_respectsMaxOutputBytes, nondet, bind] at hAll ⊢
  cases hRun : ((healthySimApiExpr).run req).run {} with
  | mk res s₁ =>
    cases res with
    | error _ =>
      have hOk : (((healthySimApiExpr).run req).run {}).1.isOk = true := by decide +kernel
      rw [hRun] at hOk; cases hOk
    | ok out =>
      rw [hRun] at hAll
      exact hAll

/-- Proof of `test_process_signaled_cleansUpAndErrors` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_signaled_cleansUpAndErrors :
    AllPass (test_process_signaled_cleansUpAndErrors healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_signaled_cleansUpAndErrors`. -/
theorem reach_process_signaled_cleansUpAndErrors :
    CanReach (test_process_signaled_cleansUpAndErrors healthySimApiExpr) := by
  let req : ExecRequest := { program := "/bin/sig9", inheritEnv := false }
  refine ⟨{}, req, ?_⟩
  have hAll := proof_process_signaled_cleansUpAndErrors {} req
  dsimp only [AllPass, CanReach, test_process_signaled_cleansUpAndErrors, nondet, bind] at hAll ⊢
  cases hRun : ((healthySimApiExpr).run req).run {} with
  | mk res s₁ =>
    cases res with
    | ok _ =>
      have hErr : (((healthySimApiExpr).run req).run {}).1.isOk = false := by decide +kernel
      rw [hRun] at hErr; cases hErr
    | error err =>
      have hK : err.kind = .terminatedBySignal := by
        have hb : (match (((healthySimApiExpr).run req).run {}).1 with | .error e => decide (e.kind = .terminatedBySignal) | .ok _ => false) = true := by
          decide +kernel
        rw [hRun] at hb; exact of_decide_eq_true hb
      rw [hRun] at hAll
      dsimp only [assume, assert] at hAll ⊢
      exact ⟨hK, hAll hK⟩

/-- Proof of `test_process_run_onError_returnsNonEmptyMessage` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_run_onError_returnsNonEmptyMessage :
    AllPass (test_process_run_onError_returnsNonEmptyMessage healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Non-vacuity `CanReach` witness for `test_process_run_onError_returnsNonEmptyMessage`. -/
theorem reach_process_run_onError_returnsNonEmptyMessage :
    CanReach (test_process_run_onError_returnsNonEmptyMessage healthySimApiExpr) :=
  ⟨{}, { program := "" }, proof_process_run_onError_returnsNonEmptyMessage {} { program := "" }⟩

/-- Proof of `test_process_runChecked_onError_returnsNonEmptyMessage` via `SysBridge.mkRawOpsM` (`healthySimApiExpr`). -/
theorem proof_process_runChecked_onError_returnsNonEmptyMessage :
    AllPass (test_process_runChecked_onError_returnsNonEmptyMessage healthySimApiExpr) :=
  healthySimApi_allStatefulSpecs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Non-vacuity `CanReach` witness for `test_process_runChecked_onError_returnsNonEmptyMessage`. -/
theorem reach_process_runChecked_onError_returnsNonEmptyMessage :
    CanReach (test_process_runChecked_onError_returnsNonEmptyMessage healthySimApiExpr) :=
  ⟨{}, { program := "" }, proof_process_runChecked_onError_returnsNonEmptyMessage {} { program := "" }⟩

/-- Proof of `test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules` for `SysBridge.resolveExecutablePath`. -/
theorem proof_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules :
    AllPass (test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules
      (@SysBridge.resolveExecutablePath (StateM PathProbeState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_validateWorkingDir_chdirSemantics` for `SysBridge.validateWorkingDir`. -/
theorem proof_process_sysBridge_validateWorkingDir_chdirSemantics :
    AllPass (test_process_sysBridge_validateWorkingDir_chdirSemantics
      SysBridge.probePathBytes
      (@SysBridge.validateWorkingDir (StateM PathProbeState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_streamPipes_shortReadWriteEagainEintrReassembly` for `SysBridge.streamPipesLoop`. -/
theorem proof_process_sysBridge_streamPipes_shortReadWriteEagainEintrReassembly :
    AllPass (test_process_sysBridge_streamPipes_shortReadWriteEagainEintrReassembly
      (@SysBridge.streamPipesLoop (StateM PipeScriptState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_streamPipes_drainsStdinAfterOutErrEof` for `SysBridge.streamPipesLoop`. -/
theorem proof_process_sysBridge_streamPipes_drainsStdinAfterOutErrEof :
    AllPass (test_process_sysBridge_streamPipes_drainsStdinAfterOutErrEof
      (@SysBridge.streamPipesLoop (StateM PipeScriptState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps` for `SysBridge.mkRawOpsM`. -/
theorem proof_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps :
    AllPass (test_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps
      (@SysBridge.stateProcTableOps CapSimState Nat)
      (@SysBridge.mkRawOpsM (StateM CapSimState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_partialPipe2Failure_cleansUpAllocatedFds` for `SysBridge.spawnPure`. -/
theorem proof_process_sysBridge_partialPipe2Failure_cleansUpAllocatedFds :
    AllPass (test_process_sysBridge_partialPipe2Failure_cleansUpAllocatedFds
      (@SysBridge.stateProcTableOps PipeFailSimState Nat)
      (@SysBridge.spawnPure (StateM PipeFailSimState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_mkApiM_preservesExactAwaitOutcomes` for `Internal.mkApiM`. -/
theorem proof_process_mkApiM_preservesExactAwaitOutcomes :
    AllPass (test_process_mkApiM_preservesExactAwaitOutcomes
      (@Internal.mkApiM (StateM OutcomeScriptState) _)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError` for `SysBridge.mkRawOpsM`. -/
theorem proof_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError :
    AllPass (test_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError
      (@SysBridge.stateProcTableOps SpawnAuditState Nat)
      (@SysBridge.mkRawOpsM (StateM SpawnAuditState) _ Nat)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

/-- Proof of `test_process_spawn_invalidRequest_doesNotCallRaw` for `Internal.mkApiM`. -/
theorem proof_process_spawn_invalidRequest_doesNotCallRaw :
    AllPass (test_process_spawn_invalidRequest_doesNotCallRaw
      (@Internal.mkApiM (StateM Nat) _)) := by
  intro s₀ req
  dsimp only [Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | ok _ => simp [assume]
  | error err =>
    have herr := validateRequest_err_spec req err hVal
    simp only [Internal.spawn, hVal, StateT.run, StateT.pure, pure, assert]
    exact ⟨⟨⟨err, rfl, herr⟩, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_process_spawn_invalidRequest_doesNotCallRaw`. -/
theorem reach_process_spawn_invalidRequest_doesNotCallRaw :
    CanReach (test_process_spawn_invalidRequest_doesNotCallRaw
      (@Internal.mkApiM (StateM Nat) _)) :=
  ⟨0, { program := "" }, proof_process_spawn_invalidRequest_doesNotCallRaw 0 { program := "" }⟩

/-- Proof of `test_process_spawn_usesNormalizedRequest` for `Internal.mkApiM`. -/
theorem proof_process_spawn_usesNormalizedRequest :
    AllPass (test_process_spawn_usesNormalizedRequest
      (@Internal.mkApiM (StateM (Option ExecRequest)) _)) := by
  intro req
  dsimp only [Internal.mkApiM]
  cases hVal : Internal.validateRequest req with
  | error _ => simp [assume]
  | ok norm =>
    have hIdem : Internal.validateRequest norm = .ok norm := by
      have hAll := proof_process_validateRequest_idempotent req
      simp only [defaultApi, Internal.mkApiM, hVal, assert] at hAll
      exact hAll.1
    simp [Internal.spawn, hVal, hIdem, StateT.run, bind, StateT.bind, pure, StateT.pure,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, assert]

/-- Non-vacuity `CanReach` witness for `test_process_spawn_usesNormalizedRequest`. -/
theorem reach_process_spawn_usesNormalizedRequest :
    CanReach (test_process_spawn_usesNormalizedRequest
      (@Internal.mkApiM (StateM (Option ExecRequest)) _)) :=
  ⟨{ program := "/bin/true" }, proof_process_spawn_usesNormalizedRequest { program := "/bin/true" }⟩

/-- Proof of `test_process_awaitOutput_rejectsZeroTimeout` for `Internal.mkApiM`. -/
theorem proof_process_awaitOutput_rejectsZeroTimeout :
    AllPass (test_process_awaitOutput_rejectsZeroTimeout
      (@Internal.mkApiM (StateM Nat) _)) := by
  intro s₀ h stdin maxOut
  simp only [Internal.mkApiM, Internal.awaitOutput, beq_self_eq_true, ↓reduceIte,
    StateT.run, StateT.pure, pure, assert]
  exact ⟨⟨⟨_, rfl, rfl, by decide⟩, trivial⟩, trivial⟩

/-- Proof of `test_process_lifecycle_delegatesAndNormalizesErrors` for `Internal.mkApiM`. -/
theorem proof_process_lifecycle_delegatesAndNormalizesErrors :
    AllPass (test_process_lifecycle_delegatesAndNormalizesErrors
      (@Internal.mkApiM (StateM LifecycleScriptState) _)) := by
  refine ⟨?_, trivial⟩
  decide +kernel

end LeanSwe.Process.Proofs
