import LeanSwe.Process.Types
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Impl
import LeanSwe.Process.Interface
import LeanSwe.Process.SpecTests
import LeanSwe.Process.Proofs.HealthyStep
import LeanSwe.Process.Proofs.SysBridge
import LeanSwe.Process.Proofs.HealthySim

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

private theorem stateT_bind_run {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := by
  dsimp only [StateT.run, Bind.bind, StateT.bind]
  cases x s
  rfl

private theorem validateRequest_err_spec (req : ExecRequest) (err : ProcessError)
    (h : Internal.validateRequest req = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Internal.validateRequest at h
  by_cases h1 : req.program.isEmpty = true
  · rw [ite_eq_left h1, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
  · rw [ite_eq_right h1] at h
    by_cases h2 : Internal.hasNul req.program = true
    · rw [ite_eq_left h2, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
    · rw [ite_eq_right h2] at h
      by_cases h3 : req.args.toList.any Internal.hasNul = true
      · rw [ite_eq_left h3, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
      · rw [ite_eq_right h3] at h
        cases hcwd : req.cwd with
        | none =>
          simp only [hcwd, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
          · rw [ite_eq_left h5, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
          · rw [ite_eq_right h5] at h
            by_cases h6 : (req.timeoutMs == some 0) = true
            · rw [ite_eq_left h6, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
            · rw [ite_eq_right h6] at h; cases h
        | some d =>
          simp only [hcwd] at h
          by_cases h4 : Internal.hasNul d = true
          · rw [ite_eq_left h4, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
          · rw [ite_eq_right h4] at h
            by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
            · rw [ite_eq_left h5, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
            · rw [ite_eq_right h5] at h
              by_cases h6 : (req.timeoutMs == some 0) = true
              · rw [ite_eq_left h6, Except.error.injEq] at h; subst h; exact ⟨rfl, by simp⟩
              · rw [ite_eq_right h6] at h; cases h

private theorem validateRequest_ok_fields_preserved {req norm : ExecRequest}
    (h : Internal.validateRequest req = .ok norm) :
    norm.program = req.program ∧
    norm.timeoutMs = req.timeoutMs ∧
    norm.maxOutputBytes = req.maxOutputBytes := by
  unfold Internal.validateRequest at h
  repeat (first | (rw [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩) | split at h | cases h)

private theorem ensureNonEmpty_msg_and_kind (fb : String) (err : ProcessError) (hfb : fb ≠ "") :
    (Internal.ensureNonEmptyMsg fb err).message ≠ "" ∧
    (Internal.ensureNonEmptyMsg fb err).kind = err.kind := by
  unfold Internal.ensureNonEmptyMsg
  split
  · exact ⟨hfb, rfl⟩
  · next h =>
    refine ⟨?_, rfl⟩
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

/-- Master behavioral and FD-conservation specification of `Internal.run raw` for any `raw` satisfying `RawProcessLaws openFds`. -/
theorem run_spec_of_RawProcessLaws {S fd : Type} {raw : RawProcessOpsM (StateM S)}
    (openFds : S → List fd) (hLaws : RawProcessLaws openFds raw) (s₀ : S) (req : ExecRequest) :
    let r := (Internal.run raw req).run s₀
    (raw.activeProcessCount.run r.2).1 = (raw.activeProcessCount.run s₀).1 ∧
    openFds r.2 = openFds s₀ ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      (err.kind = .timedOut → req.timeoutMs.isSome = true ∧ err.program = some req.program) ∧
      (err.kind = .outputLimitExceeded → req.maxOutputBytes.isSome = true ∧ err.program = some req.program) ∧
      (err.kind = .terminatedBySignal → err.program = some req.program ∧ err.signal ≠ none)) ∧
    (∀ out, r.1 = .ok out →
      ∀ lim, req.maxOutputBytes = some lim → out.stdout.size + out.stderr.size ≤ lim) := by
  dsimp only
  unfold Internal.run
  cases hVal : Internal.validateRequest req with
  | error verr =>
    dsimp only [pure, StateT.pure, StateT.run]
    obtain ⟨hk, hm⟩ := validateRequest_err_spec req verr hVal
    refine ⟨rfl, rfl, ?_, (by intro _ h; cases h)⟩
    intro err hEq; injection hEq with hE; rw [← hE]
    refine ⟨hm, ?_, ?_, ?_⟩ <;> (intro hBad; rw [hk] at hBad; cases hBad)
  | ok norm =>
    obtain ⟨hProg, hToEq, hMaxEq⟩ := validateRequest_ok_fields_preserved hVal
    dsimp only
    rw [stateT_bind_run]
    cases hSp : (raw.spawn norm).run s₀ with
    | mk spRes s₁ =>
      cases spRes with
      | error spErr =>
        dsimp only [pure, StateT.pure, StateT.run]
        have hSpE := hLaws.spawn_err s₀ norm spErr (by rw [hSp])
        rw [hSp] at hSpE
        obtain ⟨hCnt, hOpen, _, hk1, hk2, hk3⟩ := hSpE
        obtain ⟨hMsg', hKind'⟩ := ensureNonEmpty_msg_and_kind "process spawn failed" spErr (by decide)
        refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        refine ⟨hMsg', ?_, ?_, ?_⟩
        · intro hk; exact absurd (hKind'.symm.trans hk) hk1
        · intro hk; exact absurd (hKind'.symm.trans hk) hk2
        · intro hk; exact absurd (hKind'.symm.trans hk) hk3
      | ok h =>
        dsimp only
        obtain ⟨_, _, hAwErr, hAwEx, hAwSig, hAwTo, hAwLim⟩ := hLaws.spawn_lifecycle s₀ norm h s₁ hSp
        rw [stateT_bind_run]
        let aw := (raw.awaitOutput h norm.stdin norm.timeoutMs norm.maxOutputBytes).run s₁
        cases hAwFst : aw.1 with
        | error awErr =>
          dsimp only
          rw [stateT_bind_run, stateT_bind_run]
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hk1, hk2, hk3, hCnt, hOpen⟩ := hAwErr awErr hAwFst
          obtain ⟨hMsg', hKind'⟩ := ensureNonEmpty_msg_and_kind "process I/O failed" awErr (by decide)
          refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          refine ⟨hMsg', ?_, ?_, ?_⟩
          · intro hk; exact absurd (hKind'.symm.trans hk) hk1
          · intro hk; exact absurd (hKind'.symm.trans hk) hk2
          · intro hk; exact absurd (hKind'.symm.trans hk) hk3
        | ok outcome =>
          cases outcome with
          | exited res =>
            dsimp only
            rw [stateT_bind_run]
            obtain ⟨hCap, hCnt, hOpen, hRpErr⟩ := hAwEx res hAwFst
            cases hRp : ((raw.reap h).run aw.2).1 with
            | error rpErr =>
              dsimp only [pure, StateT.pure, StateT.run]
              obtain ⟨hk1, hk2, hk3⟩ := hRpErr rpErr hRp
              obtain ⟨hMsg', hKind'⟩ := ensureNonEmpty_msg_and_kind "process reap failed" rpErr (by decide)
              refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
              intro err hEq; injection hEq with hE; rw [← hE]
              refine ⟨hMsg', ?_, ?_, ?_⟩
              · intro hk; exact absurd (hKind'.symm.trans hk) hk1
              · intro hk; exact absurd (hKind'.symm.trans hk) hk2
              · intro hk; exact absurd (hKind'.symm.trans hk) hk3
            | ok u =>
              dsimp only [pure, StateT.pure, StateT.run]
              refine ⟨hCnt, hOpen, (by intro _ h; cases h), ?_⟩
              intro out hEq lim hLim
              injection hEq with hO; rw [← hO]
              exact hCap lim (hMaxEq.trans hLim)
          | signaled sig outB errB =>
            dsimp only
            rw [stateT_bind_run, stateT_bind_run]
            dsimp only [pure, StateT.pure, StateT.run]
            obtain ⟨hCnt, hOpen⟩ := hAwSig sig outB errB hAwFst
            refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
            intro err hEq; injection hEq with hE; rw [← hE]
            refine ⟨(by simp [String.append_eq_empty_iff, toString]),
              (by intro hk; cases hk),
              (by intro hk; cases hk),
              fun _ => ⟨by simp [hProg], by simp⟩⟩
          | timedOut outB errB =>
            dsimp only
            rw [stateT_bind_run, stateT_bind_run]
            dsimp only [pure, StateT.pure, StateT.run]
            obtain ⟨hSome, hCnt, hOpen⟩ := hAwTo outB errB hAwFst
            rw [hToEq] at hSome
            refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
            intro err hEq; injection hEq with hE; rw [← hE]
            refine ⟨(by simp [String.append_eq_empty_iff, toString]),
              fun _ => ⟨hSome, by simp [hProg]⟩,
              (by intro hk; cases hk),
              (by intro hk; cases hk)⟩
          | outputLimitExceeded outB errB =>
            dsimp only
            rw [stateT_bind_run, stateT_bind_run]
            dsimp only [pure, StateT.pure, StateT.run]
            obtain ⟨hSome, _, hCnt, hOpen⟩ := hAwLim outB errB hAwFst
            rw [hMaxEq] at hSome
            refine ⟨hCnt, hOpen, ?_, (by intro _ h; cases h)⟩
            intro err hEq; injection hEq with hE; rw [← hE]
            refine ⟨(by simp [String.append_eq_empty_iff, toString]),
              (by intro hk; cases hk),
              fun _ => ⟨hSome, by simp [hProg]⟩,
              (by intro hk; cases hk)⟩

private def noDupEnvKeys : List (String × Option String) → Prop
  | [] => True
  | kv :: rest => rest.any (fun p => p.1 == kv.1) = false ∧ noDupEnvKeys rest

private theorem mem_dedupEnv {xs : List (String × Option String)} {x : String × Option String}
    (hx : x ∈ Internal.dedupEnvList xs) : x ∈ xs := by
  induction xs with
  | nil => simp [Internal.dedupEnvList] at hx
  | cons kv rest ih =>
    simp only [Internal.dedupEnvList] at hx
    split at hx
    · exact List.mem_cons_of_mem kv (ih hx)
    · rcases List.mem_cons.mp hx with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem kv (ih hr)

private theorem noDupEnvKeys_dedup (xs : List (String × Option String)) :
    noDupEnvKeys (Internal.dedupEnvList xs) := by
  induction xs with
  | nil => trivial
  | cons kv rest ih =>
    simp only [Internal.dedupEnvList]
    split
    · exact ih
    · next h =>
      refine ⟨?_, ih⟩
      cases hAny : (Internal.dedupEnvList rest).any (fun p => p.1 == kv.1)
      · rfl
      · exact absurd hAny h

private theorem dedupEnv_idempotent (xs : List (String × Option String)) :
    Internal.dedupEnvList (Internal.dedupEnvList xs) = Internal.dedupEnvList xs := by
  suffices ∀ ys, noDupEnvKeys ys → Internal.dedupEnvList ys = ys from
    this _ (noDupEnvKeys_dedup xs)
  intro ys h
  induction ys with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨hnot, hrest⟩ := h
    simp [Internal.dedupEnvList, ih hrest, hnot]

private theorem validateRequest_idempotent_ok {req norm : ExecRequest}
    (h : Internal.validateRequest req = .ok norm) :
    Internal.validateRequest norm = .ok norm := by
  unfold Internal.validateRequest at h
  by_cases h1 : req.program.isEmpty = true
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    by_cases h2 : Internal.hasNul req.program = true
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h
      by_cases h3 : req.args.toList.any Internal.hasNul = true
      · rw [ite_eq_left h3] at h; cases h
      · rw [ite_eq_right h3] at h
        have h1f := Bool.eq_false_iff.mpr h1
        have h2f := Bool.eq_false_iff.mpr h2
        have h3f := Bool.eq_false_iff.mpr h3
        cases hcwd : req.cwd with
        | none =>
          simp only [hcwd, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
          · rw [ite_eq_left h5] at h; cases h
          · rw [ite_eq_right h5] at h
            by_cases h6 : (req.timeoutMs == some 0) = true
            · rw [ite_eq_left h6] at h; cases h
            · rw [ite_eq_right h6, Except.ok.injEq] at h
              subst h
              have h5f := Bool.eq_false_iff.mpr h5
              have h6f := Bool.eq_false_iff.mpr h6
              have h5' : ((Internal.dedupEnvList req.env.toList).toArray).toList.any Internal.isInvalidEnvEntry = false := by
                have hArr : ((Internal.dedupEnvList req.env.toList).toArray).toList =
                    Internal.dedupEnvList req.env.toList := by simp
                rw [hArr, List.any_eq_false]
                intro x hx
                exact List.any_eq_false.mp h5f x (mem_dedupEnv hx)
              simp [Internal.validateRequest, h1f, h2f, h3f, h5', h6f, dedupEnv_idempotent]
        | some d =>
          simp only [hcwd] at h
          by_cases h4 : Internal.hasNul d = true
          · rw [ite_eq_left h4] at h; cases h
          · rw [ite_eq_right h4] at h
            by_cases h5 : req.env.toList.any Internal.isInvalidEnvEntry = true
            · rw [ite_eq_left h5] at h; cases h
            · rw [ite_eq_right h5] at h
              by_cases h6 : (req.timeoutMs == some 0) = true
              · rw [ite_eq_left h6] at h; cases h
              · rw [ite_eq_right h6, Except.ok.injEq] at h
                subst h
                have h4f := Bool.eq_false_iff.mpr h4
                have h5f := Bool.eq_false_iff.mpr h5
                have h6f := Bool.eq_false_iff.mpr h6
                have h5' : ((Internal.dedupEnvList req.env.toList).toArray).toList.any Internal.isInvalidEnvEntry = false := by
                  have hArr : ((Internal.dedupEnvList req.env.toList).toArray).toList =
                      Internal.dedupEnvList req.env.toList := by simp
                  rw [hArr, List.any_eq_false]
                  intro x hx
                  exact List.any_eq_false.mp h5f x (mem_dedupEnv hx)
                simp [Internal.validateRequest, h1f, h2f, h3f, h4f, h5', h6f, dedupEnv_idempotent]

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

/-- `ProcessApiM (StateM HealthySimState)` constructed through `Internal.mkApiM healthySimRawOps` over genuine `healthySimDeps`. -/
def healthySimApi : ProcessApiM (StateM HealthySimState) :=
  Internal.mkApiM healthySimRawOps

/-- All 17 stateful `Process` specification promises hold for `healthySimApi` via `sysBridge_healthyStep_satisfies_allStatefulSpecs` and `refinesHealthySysDeps_of_components`. -/
theorem healthySimApi_allStatefulSpecs :
    AllPass (test_process_run_invalidRequest_doesNotLeak healthySimApi) ∧
    AllPass (test_process_run_usesNormalizedRequest healthySimApi) ∧
    AllPass (test_process_runCommand_eq_runMkCommandRequest healthySimApi) ∧
    AllPass (test_process_runCommandChecked_eq_runCheckedMkCommandRequest healthySimApi) ∧
    AllPass (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt healthySimApi) ∧
    AllPass (test_process_runChecked_zeroExit_matchesRun healthySimApi) ∧
    AllPass (test_process_runChecked_propagatesRunError healthySimApi) ∧
    AllPass (test_process_run_neverLeaksProcesses healthySimApi) ∧
    AllPass (test_process_runChecked_neverLeaksProcesses healthySimApi) ∧
    AllPass (test_process_timeout_cleansUpAndErrors healthySimApi) ∧
    AllPass (test_process_run_noTimeout_neverTimesOut healthySimApi) ∧
    AllPass (test_process_outputLimit_cleansUpAndErrors healthySimApi) ∧
    AllPass (test_process_run_noOutputLimit_neverExceedsLimit healthySimApi) ∧
    AllPass (test_process_run_respectsMaxOutputBytes healthySimApi) ∧
    AllPass (test_process_signaled_cleansUpAndErrors healthySimApi) ∧
    AllPass (test_process_run_onError_returnsNonEmptyMessage healthySimApi) ∧
    AllPass (test_process_runChecked_onError_returnsNonEmptyMessage healthySimApi) := by
  have h := sysBridge_healthyStep_satisfies_allStatefulSpecs
    (fun s => s.tbl) (fun s t => { s with tbl := t })
    (fun s => (projSimFiles s).state.fds.map Prod.fst)
    healthySimDeps healthySimDeps_refinesHealthy 4 8
  dsimp only at h
  unfold healthySimApi healthySimRawOps
  exact h

private theorem io_bind_ok {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

/-- `SysBridge.catchProc` converts every uncaught `IO.Error` into `.error` and never throws in `IO`. -/
theorem catchProc_never_throws {α : Type} (prog? : Option String)
    (act : IO (Except ProcessError α)) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.catchProc prog? act w = EST.Out.ok res w' := by
  have heq : SysBridge.catchProc prog? act w =
      EST.tryCatch act (fun err => EST.pure (.error (SysBridge.mapIoError prog? err))) w := rfl
  rw [heq]
  cases h : act w with
  | ok a s => exact ⟨a, s, by simp [EST.tryCatch, h]⟩
  | error e s => exact ⟨.error (SysBridge.mapIoError prog? e), s, by simp [EST.tryCatch, EST.pure, h]⟩

/-- `SysBridge.defaultOps.spawn` never throws an uncaught `IO.Error`. -/
theorem defaultOps_spawn_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.defaultOps.spawn req w = EST.Out.ok res w' :=
  catchProc_never_throws (some req.program) _ w

/-- `SysBridge.defaultOps.awaitOutput` never throws an uncaught `IO.Error`. -/
theorem defaultOps_awaitOutput_never_throws (h : ProcessHandle)
    (stdin : ByteArray) (timeoutMs? maxOutputBytes? : Option Nat) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.defaultOps.awaitOutput h stdin timeoutMs? maxOutputBytes? w = EST.Out.ok res w' :=
  catchProc_never_throws none _ w

/-- `SysBridge.defaultOps.killProcessGroup` never throws an uncaught `IO.Error`. -/
theorem defaultOps_killProcessGroup_never_throws (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.defaultOps.killProcessGroup h w = EST.Out.ok res w' :=
  catchProc_never_throws none _ w

/-- `SysBridge.defaultOps.reap` never throws an uncaught `IO.Error`. -/
theorem defaultOps_reap_never_throws (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.defaultOps.reap h w = EST.Out.ok res w' :=
  catchProc_never_throws none _ w

/-- `Internal.run SysBridge.defaultOps` never throws an uncaught `IO.Error` on any `ExecRequest`. -/
theorem process_defaultOps_run_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', Internal.run SysBridge.defaultOps req w = EST.Out.ok res w' := by
  unfold Internal.run
  cases Internal.validateRequest req with
  | error err => exact ⟨.error err, w, rfl⟩
  | ok norm =>
    dsimp only
    rcases defaultOps_spawn_never_throws norm w with ⟨r1, w1, hw1⟩
    rw [io_bind_ok _ _ _ hw1]
    cases r1 with
    | error err => exact ⟨_, w1, rfl⟩
    | ok h =>
      dsimp only
      rcases defaultOps_awaitOutput_never_throws h norm.stdin norm.timeoutMs norm.maxOutputBytes w1 with
        ⟨r2, w2, hw2⟩
      rw [io_bind_ok _ _ _ hw2]
      cases r2 with
      | error err =>
        dsimp only
        rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, wk, hwk⟩
        rw [io_bind_ok _ _ _ hwk]
        rcases defaultOps_reap_never_throws h wk with ⟨_, wr, hwr⟩
        rw [io_bind_ok _ _ _ hwr]
        exact ⟨_, wr, rfl⟩
      | ok outcome =>
        cases outcome with
        | exited res =>
          dsimp only
          rcases defaultOps_reap_never_throws h w2 with ⟨rr, wr, hwr⟩
          rw [io_bind_ok _ _ _ hwr]
          cases rr <;> exact ⟨_, wr, rfl⟩
        | signaled _ _ _ =>
          dsimp only
          rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, wk, hwk⟩
          rw [io_bind_ok _ _ _ hwk]
          rcases defaultOps_reap_never_throws h wk with ⟨_, wr, hwr⟩
          rw [io_bind_ok _ _ _ hwr]
          exact ⟨_, wr, rfl⟩
        | timedOut _ _ =>
          dsimp only
          rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, wk, hwk⟩
          rw [io_bind_ok _ _ _ hwk]
          rcases defaultOps_reap_never_throws h wk with ⟨_, wr, hwr⟩
          rw [io_bind_ok _ _ _ hwr]
          exact ⟨_, wr, rfl⟩
        | outputLimitExceeded _ _ =>
          dsimp only
          rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, wk, hwk⟩
          rw [io_bind_ok _ _ _ hwk]
          rcases defaultOps_reap_never_throws h wk with ⟨_, wr, hwr⟩
          rw [io_bind_ok _ _ _ hwr]
          exact ⟨_, wr, rfl⟩

/-- `LeanSwe.Process.run` never throws an uncaught `IO.Error` on any `ExecRequest`. -/
theorem process_run_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.run req w = EST.Out.ok res w' :=
  process_defaultOps_run_never_throws req w

end LeanSwe.Process.Proofs
