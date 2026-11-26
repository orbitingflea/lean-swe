import LeanSwe.Process.Types
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Impl
import LeanSwe.Process.Interface
import LeanSwe.Process.SpecTests
import LeanSwe.Process.Proofs.HealthyStep
import LeanSwe.Process.Proofs.SysBridge
import LeanSwe.Process.Proofs.HealthySim
import LeanSwe.Process.Proofs.EndToEndLaws

namespace LeanSwe.Process.Proofs

open Core (AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.SysBridge

/-!
End-to-end `ProcessApiM` behavioral theorems over any `RawProcessOpsM` satisfying `RawProcessLaws`
(and hence over any syscall bundle refining relational `healthyStep`), `TimeRand.modelOps` healthy
refinement, concrete `SysBridge` simulation witness, and `IO` no-throw theorems for downstream callers.
-/

/-- Every `raw` satisfying `RawProcessLaws` satisfies all 17 stateful `ProcessApiM (StateM S)` promises in `LeanSwe/Process/SpecTests.lean`. -/
theorem mkApiM_allStatefulSpecs_of_RawProcessLaws {S fd : Type}
    {raw : RawProcessOpsM (StateM S)} (openFds : S → List fd) (hLaws : RawProcessLaws openFds raw) :
    let api := Internal.mkApiM raw
    AllPass (test_process_run_invalidRequest_doesNotLeak api) ∧
    AllPass (test_process_run_usesNormalizedRequest api) ∧
    AllPass (test_process_runCommand_eq_runMkCommandRequest api) ∧
    AllPass (test_process_runCommandChecked_eq_runCheckedMkCommandRequest api) ∧
    AllPass (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt api) ∧
    AllPass (test_process_runChecked_zeroExit_matchesRun api) ∧
    AllPass (test_process_runChecked_propagatesRunError api) ∧
    AllPass (test_process_run_neverLeaksProcesses api) ∧
    AllPass (test_process_runChecked_neverLeaksProcesses api) ∧
    AllPass (test_process_timeout_cleansUpAndErrors api) ∧
    AllPass (test_process_run_noTimeout_neverTimesOut api) ∧
    AllPass (test_process_outputLimit_cleansUpAndErrors api) ∧
    AllPass (test_process_run_noOutputLimit_neverExceedsLimit api) ∧
    AllPass (test_process_run_respectsMaxOutputBytes api) ∧
    AllPass (test_process_signaled_cleansUpAndErrors api) ∧
    AllPass (test_process_run_onError_returnsNonEmptyMessage api) ∧
    AllPass (test_process_runChecked_onError_returnsNonEmptyMessage api) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s₀ req
    dsimp only [Internal.mkApiM]
    cases hVal : Internal.validateRequest req with
    | ok _ => simp [assume]
    | error err =>
      have herr := validateRequest_err_spec req err hVal
      simp only [Internal.run, hVal, StateT.run, StateT.pure, pure, assert]
      exact ⟨⟨⟨err, rfl, herr⟩, trivial⟩, trivial⟩
  · intro s₀ req
    dsimp only [Internal.mkApiM]
    cases hVal : Internal.validateRequest req with
    | error _ => simp [assume]
    | ok norm =>
      have hIdem := validateRequest_idempotent_ok hVal
      simp [Internal.run, hVal, hIdem, assert]
  · intro s₀ prog args
    simp [Internal.mkApiM, assert]
  · intro s₀ prog args
    simp [Internal.mkApiM, assert]
  · intro s₀ req
    simp only [Internal.mkApiM, Internal.runChecked, stateT_bind_run]
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      cases res with
      | error _ => simp [assume]
      | ok out =>
        intro hnz
        have hbeq : (out.exitCode == 0) = false := beq_false_of_ne hnz
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, StateT.run, StateT.pure, pure, assert]
        refine ⟨⟨⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩, trivial⟩, trivial⟩
        simp [String.append_eq_empty_iff, toString]
  · intro s₀ req
    simp only [Internal.mkApiM, Internal.runChecked, stateT_bind_run]
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      cases res with
      | error _ => simp [assume]
      | ok out =>
        intro hz
        simp [hz, StateT.run, StateT.pure, pure, assert]
  · intro s₀ req
    simp only [Internal.mkApiM, Internal.runChecked, stateT_bind_run]
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      cases res with
      | ok _ => simp [assume]
      | error err =>
        simp [StateT.run, StateT.pure, pure, assert]
  · intro s₀ req
    dsimp only [Internal.mkApiM]
    have hCnt := (run_spec_of_RawProcessLaws openFds hLaws s₀ req).1
    simp only [assert]
    exact ⟨hCnt, trivial⟩
  · intro s₀ req
    dsimp only [Internal.mkApiM]
    have hCnt := (run_spec_of_RawProcessLaws openFds hLaws s₀ req).1
    simp only [Internal.runChecked, stateT_bind_run]
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      rw [hRun] at hCnt
      cases res with
      | error _ =>
        simp only [StateT.run, StateT.pure, pure, assert]
        exact ⟨hCnt, trivial⟩
      | ok out =>
        dsimp only
        split <;> (simp only [StateT.run, StateT.pure, pure, assert]; exact ⟨hCnt, trivial⟩)
  · intro s₀ req _
    dsimp only [Internal.mkApiM]
    have hProps := run_spec_of_RawProcessLaws openFds hLaws s₀ req
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      rw [hRun] at hProps
      cases res with
      | ok _ => simp [assume]
      | error err =>
        intro hk
        obtain ⟨hCnt, _, hErr, _⟩ := hProps
        obtain ⟨hMsg, hTo, _, _⟩ := hErr err rfl
        simp only [assert]
        exact ⟨⟨(hTo hk).2, hMsg, hCnt⟩, trivial⟩
  · intro s₀ req hNone
    dsimp only [Internal.mkApiM]
    have hProps := run_spec_of_RawProcessLaws openFds hLaws s₀ req
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      rw [hRun] at hProps
      cases res with
      | ok _ => trivial
      | error err =>
        simp only [assert]
        refine ⟨?_, trivial⟩
        intro hk
        have hSome := ((hProps.2.2.1 err rfl).2.1 hk).1
        simp [hNone] at hSome
  · intro s₀ req _
    dsimp only [Internal.mkApiM]
    have hProps := run_spec_of_RawProcessLaws openFds hLaws s₀ req
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      rw [hRun] at hProps
      cases res with
      | ok _ => simp [assume]
      | error err =>
        intro hk
        obtain ⟨hCnt, _, hErr, _⟩ := hProps
        obtain ⟨hMsg, _, hLim, _⟩ := hErr err rfl
        simp only [assert]
        exact ⟨⟨(hLim hk).2, hMsg, hCnt⟩, trivial⟩
  · intro s₀ req hNone
    dsimp only [Internal.mkApiM]
    have hProps := run_spec_of_RawProcessLaws openFds hLaws s₀ req
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      rw [hRun] at hProps
      cases res with
      | ok _ => trivial
      | error err =>
        simp only [assert]
        refine ⟨?_, trivial⟩
        intro hk
        have hSome := ((hProps.2.2.1 err rfl).2.2.1 hk).1
        simp [hNone] at hSome
  · intro s₀ req limit hLim
    dsimp only [Internal.mkApiM]
    have hProps := run_spec_of_RawProcessLaws openFds hLaws s₀ req
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      rw [hRun] at hProps
      cases res with
      | error _ => simp [assume]
      | ok out =>
        simp only [assert]
        exact ⟨hProps.2.2.2 out rfl limit hLim, trivial⟩
  · intro s₀ req
    dsimp only [Internal.mkApiM]
    have hProps := run_spec_of_RawProcessLaws openFds hLaws s₀ req
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      rw [hRun] at hProps
      cases res with
      | ok _ => simp [assume]
      | error err =>
        intro hk
        obtain ⟨hCnt, _, hErr, _⟩ := hProps
        obtain ⟨hMsg, _, _, hSig⟩ := hErr err rfl
        obtain ⟨hPrg, hSg⟩ := hSig hk
        simp only [assert]
        exact ⟨⟨hPrg, hSg, hMsg, hCnt⟩, trivial⟩
  · intro s₀ req
    dsimp only [Internal.mkApiM]
    have hProps := run_spec_of_RawProcessLaws openFds hLaws s₀ req
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      rw [hRun] at hProps
      cases res with
      | ok _ => simp [assume]
      | error err =>
        simp only [assert]
        exact ⟨(hProps.2.2.1 err rfl).1, trivial⟩
  · intro s₀ req
    simp only [Internal.mkApiM, Internal.runChecked, stateT_bind_run]
    have hProps := run_spec_of_RawProcessLaws openFds hLaws s₀ req
    cases hRun : (Internal.run raw req).run s₀ with
    | mk res s₁ =>
      rw [hRun] at hProps
      cases res with
      | error err =>
        simp only [StateT.run, StateT.pure, pure, assert]
        exact ⟨(hProps.2.2.1 err rfl).1, trivial⟩
      | ok out =>
        dsimp only
        split
        · simp [StateT.run, StateT.pure, pure, assume]
        · simp [StateT.run, StateT.pure, pure, String.append_eq_empty_iff, toString, assert]

/-- Universal end-to-end `healthyStep` bridge theorem: for **every** `deps` satisfying `RefinesHealthySysDeps`, `Internal.mkApiM (SysBridge.mkRawOpsM deps (stateProcTableOps getTbl setTbl) eintrFuel ioFuel)` satisfies all 17 stateful `Process` specification promises unconditionally, AND conserves `openFds` across every `run` execution. -/
theorem sysBridge_healthyStep_satisfies_allStatefulSpecs {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (deps : SysDepsM (StateM S) fd)
    (hDeps : RefinesHealthySysDeps getTbl setTbl openFds deps)
    (eintrFuel ioFuel : Nat) :
    let api := Internal.mkApiM
      (SysBridge.mkRawOpsM deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel ioFuel)
    AllPass (test_process_run_invalidRequest_doesNotLeak api) ∧
    AllPass (test_process_run_usesNormalizedRequest api) ∧
    AllPass (test_process_runCommand_eq_runMkCommandRequest api) ∧
    AllPass (test_process_runCommandChecked_eq_runCheckedMkCommandRequest api) ∧
    AllPass (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt api) ∧
    AllPass (test_process_runChecked_zeroExit_matchesRun api) ∧
    AllPass (test_process_runChecked_propagatesRunError api) ∧
    AllPass (test_process_run_neverLeaksProcesses api) ∧
    AllPass (test_process_runChecked_neverLeaksProcesses api) ∧
    AllPass (test_process_timeout_cleansUpAndErrors api) ∧
    AllPass (test_process_run_noTimeout_neverTimesOut api) ∧
    AllPass (test_process_outputLimit_cleansUpAndErrors api) ∧
    AllPass (test_process_run_noOutputLimit_neverExceedsLimit api) ∧
    AllPass (test_process_run_respectsMaxOutputBytes api) ∧
    AllPass (test_process_signaled_cleansUpAndErrors api) ∧
    AllPass (test_process_run_onError_returnsNonEmptyMessage api) ∧
    AllPass (test_process_runChecked_onError_returnsNonEmptyMessage api) :=
  mkApiM_allStatefulSpecs_of_RawProcessLaws openFds
    (mkRawOpsM_satisfies_RawProcessLaws getTbl setTbl openFds deps hDeps eintrFuel ioFuel)

/-- Universal OS pipe descriptor (`openFds`) conservation theorem for `SysBridge.mkRawOpsM` over any `RefinesHealthySysDeps` witness. -/
theorem sysBridge_healthyStep_conserves_openFds {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (deps : SysDepsM (StateM S) fd)
    (hDeps : RefinesHealthySysDeps getTbl setTbl openFds deps)
    (eintrFuel ioFuel : Nat) (s₀ : S) (req : ExecRequest) :
    let raw := SysBridge.mkRawOpsM deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel ioFuel
    openFds ((Internal.run raw req).run s₀).2 = openFds s₀ :=
  (run_spec_of_RawProcessLaws openFds
    (mkRawOpsM_satisfies_RawProcessLaws getTbl setTbl openFds deps hDeps eintrFuel ioFuel) s₀ req).2.1

local notation "healthySimApiExpr" =>
  Internal.mkApiM
    (SysBridge.mkRawOpsM Model.Internal.healthySimDeps
      (SysBridge.stateProcTableOps Model.Internal.HealthySimState.tbl Model.Internal.setSimTbl)
      4 8)

/-- All 17 stateful `Process` specification promises hold for `healthySimApiExpr` via `sysBridge_healthyStep_satisfies_allStatefulSpecs` and `refinesHealthySysDeps_of_components`. -/
theorem healthySimApi_allStatefulSpecs :
    AllPass (test_process_run_invalidRequest_doesNotLeak healthySimApiExpr) ∧
    AllPass (test_process_run_usesNormalizedRequest healthySimApiExpr) ∧
    AllPass (test_process_runCommand_eq_runMkCommandRequest healthySimApiExpr) ∧
    AllPass (test_process_runCommandChecked_eq_runCheckedMkCommandRequest healthySimApiExpr) ∧
    AllPass (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt healthySimApiExpr) ∧
    AllPass (test_process_runChecked_zeroExit_matchesRun healthySimApiExpr) ∧
    AllPass (test_process_runChecked_propagatesRunError healthySimApiExpr) ∧
    AllPass (test_process_run_neverLeaksProcesses healthySimApiExpr) ∧
    AllPass (test_process_runChecked_neverLeaksProcesses healthySimApiExpr) ∧
    AllPass (test_process_timeout_cleansUpAndErrors healthySimApiExpr) ∧
    AllPass (test_process_run_noTimeout_neverTimesOut healthySimApiExpr) ∧
    AllPass (test_process_outputLimit_cleansUpAndErrors healthySimApiExpr) ∧
    AllPass (test_process_run_noOutputLimit_neverExceedsLimit healthySimApiExpr) ∧
    AllPass (test_process_run_respectsMaxOutputBytes healthySimApiExpr) ∧
    AllPass (test_process_signaled_cleansUpAndErrors healthySimApiExpr) ∧
    AllPass (test_process_run_onError_returnsNonEmptyMessage healthySimApiExpr) ∧
    AllPass (test_process_runChecked_onError_returnsNonEmptyMessage healthySimApiExpr) := by
  have h := sysBridge_healthyStep_satisfies_allStatefulSpecs
    (fun s => s.tbl) (fun s t => { s with tbl := t })
    (fun s => (projSimFiles s).state.fds.map Prod.fst)
    healthySimDeps healthySimDeps_refinesHealthy 4 8
  dsimp only at h
  exact h

private theorem io_bind_ok {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

/-- `Core.ioConcOps.tryCatchMsg` converts every uncaught `IO.Error` into `.error` and never throws in `IO`. -/
theorem ioConcOps_tryCatchMsg_never_throws {α : Type} (act : IO α) (w : Void IO.RealWorld) :
    ∃ res w', Core.ioConcOps.tryCatchMsg act w = EST.Out.ok res w' := by
  have heq : Core.ioConcOps.tryCatchMsg act w =
      EST.tryCatch (EST.bind act (fun a => EST.pure (.ok a)))
        (fun err => EST.pure (.error (toString err))) w := rfl
  rw [heq]
  unfold EST.tryCatch EST.bind EST.pure
  cases act w with
  | ok a s => exact ⟨.ok a, s, rfl⟩
  | error e s => exact ⟨.error (toString e), s, rfl⟩

/-- `(Core.ioStateCell r).get` lifts `BaseIO` and never throws in `IO`. -/
theorem ioStateCell_get_never_throws {S : Type} (r : IO.Ref S) (w : Void IO.RealWorld) :
    ∃ s w', (Core.ioStateCell r).get w = EST.Out.ok s w' := by
  change ∃ s w', (r.get : BaseIO S).toEIO w = EST.Out.ok s w'
  unfold BaseIO.toEIO
  cases (r.get : BaseIO S) w with
  | mk a s => exact ⟨a, s, rfl⟩

/-- `(Core.ioStateCell r).modifyGet` lifts `BaseIO` and never throws in `IO`. -/
theorem ioStateCell_modifyGet_never_throws {S α : Type} (r : IO.Ref S)
    (f : S → α × S) (w : Void IO.RealWorld) :
    ∃ a w', (Core.ioStateCell r).modifyGet f w = EST.Out.ok a w' := by
  change ∃ a w', (r.modifyGet f : BaseIO α).toEIO w = EST.Out.ok a w'
  unfold BaseIO.toEIO
  cases (r.modifyGet f : BaseIO α) w with
  | mk a s => exact ⟨a, s, rfl⟩

/-- `SysBridge.spawnConc` over `Core.ioConcOps` and `Core.ioStateCell` never throws in `IO`. -/
theorem mkFullRawOps_spawn_never_throws (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState LinuxSyscall.RawFd)) (fuel : Nat)
    (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.spawnConc sys Core.ioConcOps (Core.ioStateCell r) fuel req w = EST.Out.ok res w' := by
  unfold SysBridge.spawnConc
  rcases ioConcOps_tryCatchMsg_never_throws _ w with ⟨tr, w1, h1⟩
  rw [io_bind_ok _ _ _ h1]
  cases tr with
  | error msg => exact ⟨_, w1, rfl⟩
  | ok osRes =>
    cases osRes with
    | error err => exact ⟨_, w1, rfl⟩
    | ok slot =>
      dsimp only
      rcases ioStateCell_modifyGet_never_throws r (fun st => SysBridge.insertSlotPure st slot) w1 with ⟨hid, w2, h2⟩
      rw [io_bind_ok _ _ _ h2]
      exact ⟨_, w2, rfl⟩

/-- `SysBridge.awaitOutputConc` over `Core.ioConcOps` and `Core.ioStateCell` never throws in `IO`. -/
theorem mkFullRawOps_awaitOutput_never_throws (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState LinuxSyscall.RawFd)) (ef iof : Nat)
    (h : ProcessHandle) (stdin : ByteArray) (timeoutMs? maxOutputBytes? : Option Nat)
    (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.awaitOutputConc sys Core.ioConcOps (Core.ioStateCell r) ef iof
      h stdin timeoutMs? maxOutputBytes? w = EST.Out.ok res w' := by
  unfold SysBridge.awaitOutputConc
  rcases ioStateCell_modifyGet_never_throws r (fun st => SysBridge.takeSlotIoPure st h.handleId) w with ⟨tk, w1, h1⟩
  rw [io_bind_ok _ _ _ h1]
  cases tk with
  | none => exact ⟨_, w1, rfl⟩
  | some tup =>
    rcases tup with ⟨pid, inFd0?, outFd0?, errFd0?⟩
    dsimp only
    rcases ioConcOps_tryCatchMsg_never_throws _ w1 with ⟨tr, w2, h2⟩
    rw [io_bind_ok _ _ _ h2]
    cases tr with
    | error msg => exact ⟨_, w2, rfl⟩
    | ok osRes =>
      cases osRes with
      | error err => exact ⟨_, w2, rfl⟩
      | ok pair =>
        rcases pair with ⟨waitedFlag, outcome⟩
        dsimp only
        rcases ioStateCell_modifyGet_never_throws r (fun st => SysBridge.markWaitedPure st h.handleId waitedFlag) w2 with
          ⟨okFlag, w3, h3⟩
        rw [io_bind_ok _ _ _ h3]
        cases okFlag <;> exact ⟨_, w3, rfl⟩

/-- `SysBridge.killProcessGroupConc` over `Core.ioConcOps` and `Core.ioStateCell` never throws in `IO`. -/
theorem mkFullRawOps_killProcessGroup_never_throws (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState LinuxSyscall.RawFd)) (ef : Nat)
    (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.killProcessGroupConc sys Core.ioConcOps (Core.ioStateCell r) ef h w = EST.Out.ok res w' := by
  unfold SysBridge.killProcessGroupConc
  rcases ioStateCell_get_never_throws r w with ⟨st, w1, h1⟩
  rw [io_bind_ok _ _ _ h1]
  cases (SysBridge.findSlotPure h.handleId st.slots).map (·.pgid) with
  | none => exact ⟨_, w1, rfl⟩
  | some pgid =>
    dsimp only
    rcases ioConcOps_tryCatchMsg_never_throws _ w1 with ⟨tr, w2, h2⟩
    rw [io_bind_ok _ _ _ h2]
    cases tr <;> exact ⟨_, w2, rfl⟩

/-- `SysBridge.reapConc` over `Core.ioConcOps` and `Core.ioStateCell` never throws in `IO`. -/
theorem mkFullRawOps_reap_never_throws (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState LinuxSyscall.RawFd)) (ef : Nat)
    (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.reapConc sys Core.ioConcOps (Core.ioStateCell r) ef h w = EST.Out.ok res w' := by
  unfold SysBridge.reapConc
  rcases ioStateCell_modifyGet_never_throws r (fun st => SysBridge.detachSlotPure st h.handleId) w with ⟨det, w1, h1⟩
  rw [io_bind_ok _ _ _ h1]
  cases det with
  | none => exact ⟨_, w1, rfl⟩
  | some slot =>
    dsimp only
    rcases ioConcOps_tryCatchMsg_never_throws _ w1 with ⟨tr, w2, h2⟩
    rw [io_bind_ok _ _ _ h2]
    cases tr <;> exact ⟨_, w2, rfl⟩

/-- `Internal.run (SysBridge.mkFullRawOpsM sys Core.ioConcOps (Core.ioStateCell r))` never throws in `IO`. -/
theorem mkFullRawOps_run_never_throws (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState LinuxSyscall.RawFd))
    (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', Internal.run (SysBridge.mkFullRawOpsM sys Core.ioConcOps (Core.ioStateCell r)) req w = EST.Out.ok res w' := by
  unfold Internal.run SysBridge.mkFullRawOpsM
  cases Internal.validateRequest req with
  | error err => exact ⟨.error err, w, rfl⟩
  | ok norm =>
    dsimp only
    rcases mkFullRawOps_spawn_never_throws sys r _ norm w with ⟨r1, w1, hw1⟩
    rw [io_bind_ok _ _ _ hw1]
    cases r1 with
    | error err => exact ⟨_, w1, rfl⟩
    | ok h =>
      dsimp only
      rcases mkFullRawOps_awaitOutput_never_throws sys r _ _ h norm.stdin norm.timeoutMs norm.maxOutputBytes w1 with
        ⟨r2, w2, hw2⟩
      rw [io_bind_ok _ _ _ hw2]
      cases r2 with
      | error err =>
        dsimp only
        rcases mkFullRawOps_killProcessGroup_never_throws sys r _ h w2 with ⟨_, wk, hwk⟩
        rw [io_bind_ok _ _ _ hwk]
        rcases mkFullRawOps_reap_never_throws sys r _ h wk with ⟨_, wr, hwr⟩
        rw [io_bind_ok _ _ _ hwr]
        exact ⟨_, wr, rfl⟩
      | ok outcome =>
        cases outcome with
        | exited res =>
          dsimp only
          rcases mkFullRawOps_reap_never_throws sys r _ h w2 with ⟨rr, wr, hwr⟩
          rw [io_bind_ok _ _ _ hwr]
          cases rr <;> exact ⟨_, wr, rfl⟩
        | signaled _ _ _ | timedOut _ _ | outputLimitExceeded _ _ =>
          dsimp only
          rcases mkFullRawOps_killProcessGroup_never_throws sys r _ h w2 with ⟨_, wk, hwk⟩
          rw [io_bind_ok _ _ _ hwk]
          rcases mkFullRawOps_reap_never_throws sys r _ h wk with ⟨_, wr, hwr⟩
          rw [io_bind_ok _ _ _ hwr]
          exact ⟨_, wr, rfl⟩

/-- `LeanSwe.Process.run` never throws an uncaught `IO.Error` on any `ExecRequest`. -/
theorem process_run_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.run req w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.run defaultApi Internal.mkFullApiM
  dsimp only
  exact mkFullRawOps_run_never_throws _ _ req w

/-- `LeanSwe.Process.spawn` never throws an uncaught `IO.Error` on any `SpawnRequest`. -/
theorem process_spawn_never_throws (req : SpawnRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.spawn req w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.spawn defaultApi Internal.mkFullApiM Internal.spawn SysBridge.mkFullRawOpsM
  dsimp only
  cases Internal.validateSpawnRequest req with
  | error err => exact ⟨.error err, w, rfl⟩
  | ok norm =>
    dsimp only
    rcases mkFullRawOps_spawn_never_throws _ _ _ { toSpawnRequest := norm } w with ⟨r1, w1, hw1⟩
    rw [io_bind_ok _ _ _ hw1]
    cases r1 <;> exact ⟨_, w1, rfl⟩

/-- `LeanSwe.Process.awaitOutput` never throws an uncaught `IO.Error`. -/
theorem process_awaitOutput_never_throws (h : ProcessHandle)
    (stdin : ByteArray) (timeoutMs? maxOutputBytes? : Option Nat) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.awaitOutput h stdin timeoutMs? maxOutputBytes? w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.awaitOutput defaultApi Internal.mkFullApiM Internal.awaitOutput SysBridge.mkFullRawOpsM
  dsimp only
  split
  · exact ⟨_, w, rfl⟩
  · rcases mkFullRawOps_awaitOutput_never_throws _ _ _ _ h stdin timeoutMs? maxOutputBytes? w with ⟨r1, w1, hw1⟩
    rw [io_bind_ok _ _ _ hw1]
    cases r1 <;> exact ⟨_, w1, rfl⟩

/-- `LeanSwe.Process.killProcessGroup` never throws an uncaught `IO.Error`. -/
theorem process_killProcessGroup_never_throws (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.killProcessGroup h w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.killProcessGroup defaultApi Internal.mkFullApiM Internal.killProcessGroup SysBridge.mkFullRawOpsM
  dsimp only
  rcases mkFullRawOps_killProcessGroup_never_throws _ _ _ h w with ⟨r1, w1, hw1⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r1 <;> exact ⟨_, w1, rfl⟩

/-- `LeanSwe.Process.reap` never throws an uncaught `IO.Error`. -/
theorem process_reap_never_throws (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.reap h w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.reap defaultApi Internal.mkFullApiM Internal.reap SysBridge.mkFullRawOpsM
  dsimp only
  rcases mkFullRawOps_reap_never_throws _ _ _ h w with ⟨r1, w1, hw1⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r1 <;> exact ⟨_, w1, rfl⟩

end LeanSwe.Process.Proofs
