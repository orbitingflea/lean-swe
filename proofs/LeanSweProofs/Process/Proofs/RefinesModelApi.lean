import Core.Obeys
import LeanSwe.Process.Types
import LeanSweProofs.Process.Model
import LeanSwe.Process.Impl
import LeanSwe.Process.Interface
import LeanSweProofs.Process.Proofs.RefinesModelWitness

/-!
Pure and stateful `Core.Obeys` proofs for `LeanSwe.Process.Impl.mkApiM`,
providing `mkApiM_refines_of_rawWf` parameterized over an arbitrary world
well-formedness invariant `wf` stronger than `Model.processStateWf ∘ proj`,
together with `refinesStepFrom_mkApiM` and pure refinements.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.Process

private theorem stateT_bind_run' {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := by
  dsimp only [StateT.run, Bind.bind, StateT.bind]
  cases x s
  rfl

private theorem stateT_map_run' {σ α β : Type} (f : α → β) (x : StateM σ α) (s : σ) :
    (f <$> x).run s = (f (x.run s).1, (x.run s).2) := by
  dsimp only [Functor.map, StateT.map, StateT.run]
  cases x s
  rfl

private theorem stateT_pure_run' {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α).run s = (a, s) := rfl

/-- `LeanSwe.Process.mapRawError` refines `Model.mapRawErrorModel` with exact equality. -/
theorem refinesPure_mapRawError :
    Core.ObeysPureEq LeanSwe.Process.mapRawError Model.mapRawErrorModel := by
  intro raw
  cases raw <;> rfl

private theorem dedupEnvList_eq_model (xs : List (String × Option String)) :
    Internal.dedupEnvList xs = Model.dedupEnvListModel xs := by
  induction xs with
  | nil => rfl
  | cons kv rest ih =>
    simp only [Internal.dedupEnvList, Model.dedupEnvListModel, ih]

private theorem hasNul_eq_model : Internal.hasNul = Model.hasNulModel := rfl

private theorem isInvalidEnvEntry_eq_model :
    Internal.isInvalidEnvEntry = Model.isInvalidEnvEntryModel := rfl

private theorem validateSpawnRequest_eq_model (req : SpawnRequest) :
    Internal.validateSpawnRequest req = Model.validateSpawnRequestModel req := by
  unfold Internal.validateSpawnRequest Model.validateSpawnRequestModel
  simp only [hasNul_eq_model, isInvalidEnvEntry_eq_model, dedupEnvList_eq_model]
  cases req.cwd <;> rfl

private theorem validateRequest_eq_model (req : ExecRequest) :
    Internal.validateRequest req = Model.validateRequestModel req := by
  unfold Internal.validateRequest Model.validateRequestModel
  rw [validateSpawnRequest_eq_model]
  cases Model.validateSpawnRequestModel req.toSpawnRequest <;> rfl

/-- `LeanSwe.Process.validateRequest` refines `Model.validateRequestModel` with exact equality. -/
theorem refinesPure_validateRequest :
    Core.ObeysPureEq LeanSwe.Process.validateRequest Model.validateRequestModel :=
  validateRequest_eq_model

/-- `LeanSwe.Process.mkCommandRequest` refines `Model.mkCommandRequestModel` with exact equality. -/
theorem refinesPure_mkCommandRequest :
    @Core.ObeysPureEq2 String (Array String) ExecRequest
      (@LeanSwe.Process.mkCommandRequest) Model.mkCommandRequestModel := by
  intro _ _
  rfl

/-- `LeanSwe.Process.withTextInput` refines `Model.withTextInputModel` with exact equality. -/
theorem refinesPure_withTextInput :
    Core.ObeysPureEq2 LeanSwe.Process.withTextInput Model.withTextInputModel := by
  intro _ _
  rfl

private theorem validateSpawnRequest_ok_program {req norm : SpawnRequest}
    (h : Internal.validateSpawnRequest req = .ok norm) :
    norm.program = req.program := by
  unfold Internal.validateSpawnRequest at h
  repeat (first | (rw [Except.ok.injEq] at h; subst h; rfl) | split at h | cases h)

private theorem validateRequest_ok_fields {req norm : ExecRequest}
    (h : Internal.validateRequest req = .ok norm) :
    norm.program = req.program ∧
    norm.timeoutMs = req.timeoutMs ∧
    norm.maxOutputBytes = req.maxOutputBytes := by
  unfold Internal.validateRequest at h
  cases hS : Internal.validateSpawnRequest req.toSpawnRequest with
  | error _ => simp [hS] at h
  | ok sn =>
    simp only [hS] at h
    split at h
    · cases h
    · rw [Except.ok.injEq] at h
      subst h
      exact ⟨validateSpawnRequest_ok_program hS, rfl, rfl⟩

private theorem ensureNonEmpty_isNonOutcome (fb : String) (err : ProcessError)
    (hfb : fb ≠ "") (herr : Model.isNonOutcomeError err) :
    Model.isNonOutcomeError (Internal.ensureNonEmptyMsg fb err) := by
  obtain ⟨_, h1, h2, h3, h4⟩ := herr
  unfold Internal.ensureNonEmptyMsg
  split
  · exact ⟨hfb, h1, h2, h3, h4⟩
  · next h =>
    refine ⟨?_, h1, h2, h3, h4⟩
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

private theorem processStateWf_all_lt {s : Model.ProcessModelState}
    (hWf : Model.processStateWf s = true) :
    ∀ e ∈ s.activeHandles, e.handleId < s.nextHandleId ∧ e.pid > 0 ∧ e.pgid > 0 := by
  unfold Model.processStateWf at hWf
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hWf
  intro e he
  have h := hWf.2 e he
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem filter_fresh_eq_self {s : Model.ProcessModelState}
    (hWf : Model.processStateWf s = true) :
    s.activeHandles.filter (fun x => x.handleId != s.nextHandleId) = s.activeHandles := by
  rw [List.filter_eq_self]
  intro e he
  have hLt := (processStateWf_all_lt hWf e he).1
  exact bne_iff_ne.mpr (Nat.ne_of_lt hLt)

private theorem execResult_of_spawn {W : Type} (wf : W → Bool)
    (proj : W → Model.ProcessModelState) (raw : RawProcessOpsM (StateM W))
    (hRaw : ∀ w req, wf w = true →
      let (out, w') := (Model.execRawStep raw req).run w
      wf w' = true ∧ Model.allowedRawStep (proj w) req out (proj w'))
    (w : W) (hWf : wf w = true) (req : ExecRequest) :
    let r := (raw.spawn req).run w
    wf r.2 = true ∧
    Model.processStateWf (proj r.2) = true ∧
    Model.allowedRawSpawn (proj w) r.1 (proj r.2) := by
  have hStep := hRaw w (.spawn req) hWf
  dsimp only [Model.execRawStep, Functor.map, StateT.map, Bind.bind, StateT.bind,
    Pure.pure, StateT.pure, StateT.run, Model.allowedRawStep] at hStep ⊢
  cases hSp : raw.spawn req w with
  | mk res w' =>
    rw [hSp] at hStep
    exact ⟨hStep.1, hStep.2.2.1, hStep.2.2.2⟩

private theorem execResult_of_await {W : Type} (wf : W → Bool)
    (proj : W → Model.ProcessModelState) (raw : RawProcessOpsM (StateM W))
    (hRaw : ∀ w req, wf w = true →
      let (out, w') := (Model.execRawStep raw req).run w
      wf w' = true ∧ Model.allowedRawStep (proj w) req out (proj w'))
    (w : W) (hWf : wf w = true)
    (h : ProcessHandle) (stdin : ByteArray) (to? max? : Option Nat) :
    let r := (raw.awaitOutput h stdin to? max?).run w
    wf r.2 = true ∧
    Model.allowedAwaitCore (proj w) h to? max? r.1 (proj r.2) := by
  have hStep := hRaw w (.awaitOutput h stdin to? max?) hWf
  dsimp only [Model.execRawStep, Functor.map, StateT.map, Bind.bind, StateT.bind,
    Pure.pure, StateT.pure, StateT.run, Model.allowedRawStep] at hStep ⊢
  cases hAw : raw.awaitOutput h stdin to? max? w with
  | mk res w' =>
    rw [hAw] at hStep
    exact ⟨hStep.1, hStep.2.2.2⟩

private theorem execResult_of_kill {W : Type} (wf : W → Bool)
    (proj : W → Model.ProcessModelState) (raw : RawProcessOpsM (StateM W))
    (hRaw : ∀ w req, wf w = true →
      let (out, w') := (Model.execRawStep raw req).run w
      wf w' = true ∧ Model.allowedRawStep (proj w) req out (proj w'))
    (w : W) (hWf : wf w = true) (h : ProcessHandle) :
    let r := (raw.killProcessGroup h).run w
    wf r.2 = true ∧
    Model.allowedKillGroup (proj w) r.1 (proj r.2) := by
  have hStep := hRaw w (.killProcessGroup h) hWf
  dsimp only [Model.execRawStep, Functor.map, StateT.map, Bind.bind, StateT.bind,
    Pure.pure, StateT.pure, StateT.run, Model.allowedRawStep] at hStep ⊢
  cases hKl : raw.killProcessGroup h w with
  | mk res w' =>
    rw [hKl] at hStep
    exact ⟨hStep.1, hStep.2.2.2⟩

private theorem execResult_of_reap {W : Type} (wf : W → Bool)
    (proj : W → Model.ProcessModelState) (raw : RawProcessOpsM (StateM W))
    (hRaw : ∀ w req, wf w = true →
      let (out, w') := (Model.execRawStep raw req).run w
      wf w' = true ∧ Model.allowedRawStep (proj w) req out (proj w'))
    (w : W) (hWf : wf w = true) (h : ProcessHandle) :
    let r := (raw.reap h).run w
    wf r.2 = true ∧
    Model.processStateWf (proj r.2) = true ∧
    Model.allowedReap (proj w) h r.1 (proj r.2) := by
  have hStep := hRaw w (.reap h) hWf
  dsimp only [Model.execRawStep, Functor.map, StateT.map, Bind.bind, StateT.bind,
    Pure.pure, StateT.pure, StateT.run, Model.allowedRawStep] at hStep ⊢
  cases hRp : raw.reap h w with
  | mk res w' =>
    rw [hRp] at hStep
    exact ⟨hStep.1, hStep.2.2.1, hStep.2.2.2⟩

private theorem execResult_of_activeCount {W : Type} (wf : W → Bool)
    (proj : W → Model.ProcessModelState) (raw : RawProcessOpsM (StateM W))
    (hRaw : ∀ w req, wf w = true →
      let (out, w') := (Model.execRawStep raw req).run w
      wf w' = true ∧ Model.allowedRawStep (proj w) req out (proj w'))
    (w : W) (hWf : wf w = true) :
    let r := raw.activeProcessCount.run w
    wf r.2 = true ∧ proj r.2 = proj w ∧ r.1 = (proj w).activeHandles.length := by
  have hStep := hRaw w .activeProcessCount hWf
  dsimp only [Model.execRawStep, Functor.map, StateT.map, Bind.bind, StateT.bind,
    Pure.pure, StateT.pure, StateT.run, Model.allowedRawStep] at hStep ⊢
  cases hCnt : raw.activeProcessCount w with
  | mk n w' =>
    rw [hCnt] at hStep
    exact ⟨hStep.1, hStep.2.2.2⟩

private theorem run_refines_model {W : Type} (wf : W → Bool)
    (proj : W → Model.ProcessModelState) (raw : RawProcessOpsM (StateM W))
    (hImplies : ∀ w, wf w = true → Model.processStateWf (proj w) = true)
    (hRaw : ∀ w req, wf w = true →
      let (out, w') := (Model.execRawStep raw req).run w
      wf w' = true ∧ Model.allowedRawStep (proj w) req out (proj w'))
    (w : W) (hWf : wf w = true) (req : ExecRequest) :
    let r := (Internal.run raw req).run w
    wf r.2 = true ∧
    Model.allowedPkgRun false (proj w) req r.1 (proj r.2) := by
  dsimp only
  unfold Internal.run
  dsimp only [Model.allowedPkgRun]
  rw [← validateRequest_eq_model req]
  cases hVal : Internal.validateRequest req with
  | error verr =>
    rw [stateT_pure_run']
    exact ⟨hWf, rfl, rfl⟩
  | ok norm =>
    obtain ⟨hProg, hToEq, hMaxEq⟩ := validateRequest_ok_fields hVal
    dsimp only
    rw [stateT_bind_run']
    have hSp := execResult_of_spawn wf proj raw hRaw w hWf norm
    cases hSpRun : (raw.spawn norm).run w with
    | mk spRes w1 =>
      rw [hSpRun] at hSp
      obtain ⟨hWf1, _, hSpAllowed⟩ := hSp
      cases spRes with
      | error spErr =>
        rw [stateT_pure_run']
        obtain ⟨hS1Eq, hNonOut⟩ := hSpAllowed
        obtain ⟨hMsg, hNt, hNo, hNs, hNz⟩ := ensureNonEmpty_isNonOutcome "process spawn failed" spErr (by decide) hNonOut
        refine ⟨hWf1, ?_, Or.inl (congrArg Model.ProcessModelState.nextHandleId hS1Eq), ?_⟩
        · exact congrArg Model.ProcessModelState.activeHandles hS1Eq
        · refine ⟨hMsg, (fun h => absurd h hNt), (fun h => absurd h hNo), (fun h => absurd h hNs), (fun h => absurd h hNz)⟩
      | ok h =>
        obtain ⟨hHid, _, _, hS1Eq⟩ := hSpAllowed
        have hFilt1 : (proj w1).activeHandles.filter (·.handleId != h.handleId) = (proj w).activeHandles := by
          rw [hS1Eq, hHid]
          simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          exact filter_fresh_eq_self (hImplies w hWf)
        dsimp only
        rw [stateT_bind_run']
        have hAw := execResult_of_await wf proj raw hRaw w1 hWf1 h norm.stdin norm.timeoutMs norm.maxOutputBytes
        cases hAwRun : (raw.awaitOutput h norm.stdin norm.timeoutMs norm.maxOutputBytes).run w1 with
        | mk awRes w2 =>
          rw [hAwRun] at hAw
          obtain ⟨hWf2, _, hNext2, _, hFilt2, hAwBody⟩ := hAw
          have hNext2Eq : (proj w2).nextHandleId = (proj w).nextHandleId + 1 := by
            rw [hNext2, hS1Eq]
          have hFilt2Eq : (proj w2).activeHandles.filter (·.handleId != h.handleId) = (proj w).activeHandles :=
            hFilt2.trans hFilt1
          have killAndReapRestores : ∀ (wk : W), wf wk = true →
              (proj wk).nextHandleId = (proj w).nextHandleId + 1 →
              (proj wk).activeHandles.filter (·.handleId != h.handleId) = (proj w).activeHandles →
              wf ((raw.reap h).run ((raw.killProcessGroup h).run wk).2).2 = true ∧
              (proj ((raw.reap h).run ((raw.killProcessGroup h).run wk).2).2).activeHandles = (proj w).activeHandles ∧
              (proj ((raw.reap h).run ((raw.killProcessGroup h).run wk).2).2).nextHandleId = (proj w).nextHandleId + 1 := by
            intro wk hWfk hNextk hFiltk
            have hKl := execResult_of_kill wf proj raw hRaw wk hWfk h
            cases hKlRun : (raw.killProcessGroup h).run wk with
            | mk klRes wk2 =>
              rw [hKlRun] at hKl
              obtain ⟨hWfk2, hSk2Eq, _⟩ := hKl
              have hRp := execResult_of_reap wf proj raw hRaw wk2 hWfk2 h
              cases hRpRun : (raw.reap h).run wk2 with
              | mk rpRes wr =>
                rw [hRpRun] at hRp
                obtain ⟨hWfr, _, hNextr, hFiltr, _⟩ := hRp
                refine ⟨hWfr, ?_, ?_⟩
                · rw [hFiltr, hSk2Eq, hFiltk]
                · rw [hNextr, hSk2Eq, hNextk]
          cases awRes with
          | error awErr =>
            dsimp only
            rw [stateT_bind_run', stateT_bind_run', stateT_pure_run']
            obtain ⟨hWfr, hActr, hNextr⟩ := killAndReapRestores w2 hWf2 hNext2Eq hFilt2Eq
            obtain ⟨hMsg, hNt, hNo, hNs, hNz⟩ := ensureNonEmpty_isNonOutcome "process I/O failed" awErr (by decide) hAwBody
            refine ⟨hWfr, hActr, Or.inr hNextr, ?_⟩
            exact ⟨hMsg, (fun hk => absurd hk hNt), (fun hk => absurd hk hNo),
              (fun hk => absurd hk hNs), (fun hk => absurd hk hNz)⟩
          | ok outcome =>
            obtain ⟨_, hOutBody⟩ := hAwBody
            cases outcome with
            | exited res =>
              dsimp only
              rw [stateT_bind_run']
              have hRp := execResult_of_reap wf proj raw hRaw w2 hWf2 h
              cases hRpRun : (raw.reap h).run w2 with
              | mk rpRes wr =>
                rw [hRpRun] at hRp
                obtain ⟨hWfr, _, hNextr, hFiltr, hRpBody⟩ := hRp
                have hActr : (proj wr).activeHandles = (proj w).activeHandles := hFiltr.trans hFilt2Eq
                have hNextrEq : (proj wr).nextHandleId = (proj w).nextHandleId + 1 := hNextr.trans hNext2Eq
                cases rpRes with
                | error rpErr =>
                  rw [stateT_pure_run']
                  obtain ⟨hMsg, hNt, hNo, hNs, hNz⟩ := ensureNonEmpty_isNonOutcome "process reap failed" rpErr (by decide) hRpBody
                  refine ⟨hWfr, hActr, Or.inr hNextrEq, ?_⟩
                  exact ⟨hMsg, (fun hk => absurd hk hNt), (fun hk => absurd hk hNo),
                    (fun hk => absurd hk hNs), (fun hk => absurd hk hNz)⟩
                | ok _ =>
                  rw [stateT_pure_run']
                  refine ⟨hWfr, hActr, Or.inr hNextrEq, (fun h => by cases h), ?_⟩
                  intro lim hLim
                  exact hOutBody lim (hMaxEq.trans hLim)
            | signaled sig outB errB =>
              dsimp only
              rw [stateT_bind_run', stateT_bind_run', stateT_pure_run']
              obtain ⟨hWfr, hActr, hNextr⟩ := killAndReapRestores w2 hWf2 hNext2Eq hFilt2Eq
              refine ⟨hWfr, hActr, Or.inr hNextr, ?_⟩
              refine ⟨by simp [String.append_eq_empty_iff, toString],
                (fun hk => by cases hk), (fun hk => by cases hk),
                (fun _ => ⟨by simp [hProg], by simp⟩), (fun hk => by cases hk)⟩
            | timedOut outB errB =>
              dsimp only
              rw [stateT_bind_run', stateT_bind_run', stateT_pure_run']
              obtain ⟨hWfr, hActr, hNextr⟩ := killAndReapRestores w2 hWf2 hNext2Eq hFilt2Eq
              rw [hToEq] at hOutBody
              refine ⟨hWfr, hActr, Or.inr hNextr, ?_⟩
              refine ⟨by simp [String.append_eq_empty_iff, toString],
                (fun _ => ⟨hOutBody, by simp [hProg]⟩), (fun hk => by cases hk),
                (fun hk => by cases hk), (fun hk => by cases hk)⟩
            | outputLimitExceeded outB errB =>
              dsimp only
              rw [stateT_bind_run', stateT_bind_run', stateT_pure_run']
              obtain ⟨hWfr, hActr, hNextr⟩ := killAndReapRestores w2 hWf2 hNext2Eq hFilt2Eq
              obtain ⟨hMaxSome, hMaxBound⟩ := hOutBody
              rw [hMaxEq] at hMaxSome
              refine ⟨hWfr, hActr, Or.inr hNextr, ?_⟩
              refine ⟨by simp [String.append_eq_empty_iff, toString],
                (fun hk => by cases hk), ?_, (fun hk => by cases hk), (fun hk => by cases hk)⟩
              intro _
              refine ⟨hMaxSome, by simp [hProg], ?_⟩
              intro lim hLim
              rw [Option.map_some, Option.map_some, Option.getD_some, Option.getD_some]
              exact hMaxBound lim (hMaxEq.trans hLim)

private theorem runChecked_refines_model {W : Type} (wf : W → Bool)
    (proj : W → Model.ProcessModelState) (raw : RawProcessOpsM (StateM W))
    (hImplies : ∀ w, wf w = true → Model.processStateWf (proj w) = true)
    (hRaw : ∀ w req, wf w = true →
      let (out, w') := (Model.execRawStep raw req).run w
      wf w' = true ∧ Model.allowedRawStep (proj w) req out (proj w'))
    (w : W) (hWf : wf w = true) (req : ExecRequest) :
    let r := (Internal.runChecked raw req).run w
    wf r.2 = true ∧
    Model.allowedPkgRun true (proj w) req r.1 (proj r.2) := by
  dsimp only
  unfold Internal.runChecked
  rw [stateT_bind_run']
  have hRun := run_refines_model wf proj raw hImplies hRaw w hWf req
  cases hRunRes : (Internal.run raw req).run w with
  | mk res w1 =>
    rw [hRunRes] at hRun
    obtain ⟨hWf1, hPkg⟩ := hRun
    dsimp only [Model.allowedPkgRun] at hPkg ⊢
    cases hVal : Model.validateRequestModel req with
    | error verr =>
      rw [hVal] at hPkg
      obtain ⟨hErr, hState⟩ := hPkg
      subst hErr
      rw [stateT_pure_run']
      exact ⟨hWf1, rfl, hState⟩
    | ok norm =>
      rw [hVal] at hPkg
      obtain ⟨hAct, hNext, hExec⟩ := hPkg
      cases res with
      | error err =>
        rw [stateT_pure_run']
        exact ⟨hWf1, hAct, hNext, hExec.1, hExec.2.1, hExec.2.2.1, hExec.2.2.2.1,
          fun hk => absurd (hExec.2.2.2.2 hk).1 (by decide)⟩
      | ok out =>
        dsimp only
        by_cases hZero : (out.exitCode == 0) = true
        · rw [ite_eq_left hZero, stateT_pure_run']
          exact ⟨hWf1, hAct, hNext, fun _ => beq_iff_eq.mp hZero, hExec.2⟩
        · rw [ite_eq_right hZero, stateT_pure_run']
          have hNz : out.exitCode ≠ 0 := fun hz => hZero (beq_iff_eq.mpr hz)
          refine ⟨hWf1, hAct, hNext, ?_⟩
          refine ⟨by simp [String.append_eq_empty_iff, toString],
            (fun hk => by cases hk), (fun hk => by cases hk), (fun hk => by cases hk), ?_⟩
          intro _
          exact ⟨rfl, rfl, (by simp), (by simp [hNz]), (by simp), (by simp)⟩

/-- Generalized `Internal.mkApiM` refinement theorem parameterized over any world invariant `wf` stronger than `Model.processStateWf ∘ proj`. -/
theorem mkApiM_refines_of_rawWf {W : Type} (wf : W → Bool)
    (proj : W → Model.ProcessModelState)
    (raw : RawProcessOpsM (StateM W))
    (hImplies : ∀ w, wf w = true → Model.processStateWf (proj w) = true)
    (hRaw : ∀ w req, wf w = true →
      let (out, w') := (Model.execRawStep raw req).run w
      wf w' = true ∧ Model.allowedRawStep (proj w) req out (proj w'))
    (w : W) (req : Model.PkgStepReq) (hWf : wf w = true) :
    let (out, w') := (Model.execPkgStep (Internal.mkApiM raw) req).run w
    wf w' = true ∧ Model.allowedPkgStep (proj w) req out (proj w') := by
  have hS : Model.processStateWf (proj w) = true := hImplies w hWf
  cases req with
  | spawn sreq =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp]
    rw [stateT_map_run']
    dsimp only [Internal.spawn]
    rw [validateSpawnRequest_eq_model]
    cases hVal : Model.validateSpawnRequestModel sreq with
    | error err =>
      rw [stateT_pure_run']
      exact ⟨hWf, hS, hS, rfl, rfl⟩
    | ok norm =>
      rw [stateT_bind_run']
      have hSp := execResult_of_spawn wf proj raw hRaw w hWf { toSpawnRequest := norm }
      cases hSpRun : (raw.spawn { toSpawnRequest := norm }).run w with
      | mk spRes w1 =>
        rw [hSpRun] at hSp
        obtain ⟨hWf1, hS1, hSpAllowed⟩ := hSp
        cases spRes with
        | error spErr =>
          rw [stateT_pure_run']
          refine ⟨hWf1, hS, hS1, ?_⟩
          exact ⟨hSpAllowed.1, ensureNonEmpty_isNonOutcome "process spawn failed" spErr (by decide) hSpAllowed.2⟩
        | ok h =>
          rw [stateT_pure_run']
          exact ⟨hWf1, hS, hS1, hSpAllowed⟩
  | awaitOutput h stdin timeoutMs maxOutputBytes =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp]
    rw [stateT_map_run']
    dsimp only [Internal.awaitOutput]
    by_cases hZero : (timeoutMs == some 0) = true
    · rw [ite_eq_left hZero, stateT_pure_run']
      simp only [hZero, ↓reduceIte]
      exact ⟨hWf, hS, hS, trivial, trivial⟩
    · rw [ite_eq_right hZero, stateT_bind_run']
      have hZeroF : (timeoutMs == some 0) = false := Bool.eq_false_iff.mpr hZero
      simp only [hZeroF, Bool.false_eq_true, ↓reduceIte]
      have hAw := execResult_of_await wf proj raw hRaw w hWf h stdin timeoutMs maxOutputBytes
      cases hAwRun : (raw.awaitOutput h stdin timeoutMs maxOutputBytes).run w with
      | mk awRes w1 =>
        rw [hAwRun] at hAw
        obtain ⟨hWf1, hS1, hNext1, hMap1, hFilt1, hAwBody⟩ := hAw
        cases awRes with
        | error awErr =>
          rw [stateT_pure_run']
          refine ⟨hWf1, hS, hImplies w1 hWf1, hS1, hNext1, hMap1, hFilt1, ?_⟩
          exact ensureNonEmpty_isNonOutcome "process I/O failed" awErr (by decide) hAwBody
        | ok outcome =>
          rw [stateT_pure_run']
          exact ⟨hWf1, hS, hImplies w1 hWf1, hS1, hNext1, hMap1, hFilt1, hAwBody⟩
  | killProcessGroup h =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp]
    rw [stateT_map_run']
    dsimp only [Internal.killProcessGroup]
    rw [stateT_bind_run']
    have hKl := execResult_of_kill wf proj raw hRaw w hWf h
    cases hKlRun : (raw.killProcessGroup h).run w with
    | mk klRes w1 =>
      rw [hKlRun] at hKl
      obtain ⟨hWf1, hS1Eq, hKlBody⟩ := hKl
      have hS1 : Model.processStateWf (proj w1) = true := hS1Eq ▸ hS
      cases klRes with
      | error klErr =>
        rw [stateT_pure_run']
        exact ⟨hWf1, hS, hS1, hS1Eq, ensureNonEmpty_isNonOutcome "process group termination failed" klErr (by decide) hKlBody⟩
      | ok _ =>
        rw [stateT_pure_run']
        exact ⟨hWf1, hS, hS1, hS1Eq, trivial⟩
  | reap h =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp]
    rw [stateT_map_run']
    dsimp only [Internal.reap]
    rw [stateT_bind_run']
    have hRp := execResult_of_reap wf proj raw hRaw w hWf h
    cases hRpRun : (raw.reap h).run w with
    | mk rpRes w1 =>
      rw [hRpRun] at hRp
      obtain ⟨hWf1, hS1, hNext1, hFilt1, hRpBody⟩ := hRp
      cases rpRes with
      | error rpErr =>
        rw [stateT_pure_run']
        exact ⟨hWf1, hS, hS1, hNext1, hFilt1, ensureNonEmpty_isNonOutcome "process reap failed" rpErr (by decide) hRpBody⟩
      | ok _ =>
        rw [stateT_pure_run']
        exact ⟨hWf1, hS, hS1, hNext1, hFilt1, trivial⟩
  | run r =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp]
    rw [stateT_map_run']
    have hR := run_refines_model wf proj raw hImplies hRaw w hWf r
    cases hRun : (Internal.run raw r).run w with
    | mk res w1 =>
      rw [hRun] at hR
      exact ⟨hR.1, hS, hImplies w1 hR.1, hR.2⟩
  | runChecked r =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp]
    rw [stateT_map_run']
    have hR := runChecked_refines_model wf proj raw hImplies hRaw w hWf r
    cases hRun : (Internal.runChecked raw r).run w with
    | mk res w1 =>
      rw [hRun] at hR
      exact ⟨hR.1, hS, hImplies w1 hR.1, hR.2⟩
  | runCommand prog args =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp]
    rw [stateT_map_run']
    have hR := run_refines_model wf proj raw hImplies hRaw w hWf (Model.mkCommandRequestModel prog args)
    cases hRun : (Internal.run raw (Internal.mkCommandRequest prog args)).run w with
    | mk res w1 =>
      change (Internal.run raw (Model.mkCommandRequestModel prog args)).run w = (res, w1) at hRun
      rw [hRun] at hR
      exact ⟨hR.1, hS, hImplies w1 hR.1, hR.2⟩
  | runCommandChecked prog args =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp]
    rw [stateT_map_run']
    have hR := runChecked_refines_model wf proj raw hImplies hRaw w hWf (Model.mkCommandRequestModel prog args)
    cases hRun : (Internal.runChecked raw (Internal.mkCommandRequest prog args)).run w with
    | mk res w1 =>
      change (Internal.runChecked raw (Model.mkCommandRequestModel prog args)).run w = (res, w1) at hRun
      rw [hRun] at hR
      exact ⟨hR.1, hS, hImplies w1 hR.1, hR.2⟩
  | activeProcessCount =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp]
    rw [stateT_map_run']
    have hCnt := execResult_of_activeCount wf proj raw hRaw w hWf
    cases hCntRun : raw.activeProcessCount.run w with
    | mk n w1 =>
      rw [hCntRun] at hCnt
      exact ⟨hCnt.1, hS, hCnt.2.1 ▸ hS, hCnt.2.1, hCnt.2.2⟩

/-- Compositional capability-refinement theorem lifting `RawProcessOpsM` contracts to `Internal.mkApiM`. -/
theorem refinesStepFrom_mkApiM :
    Core.ObeysStepFrom id Model.processStateWf
      Model.execRawStep Model.allowedRawStep
      Model.processStateWf Internal.mkApiM
      Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hWf
  have hRes := mkApiM_refines_of_rawWf (fun x => Model.processStateWf (proj x)) proj raw
    (fun _ h => h)
    (fun x r hx =>
      let step := hRaw x r hx
      ⟨step.2.1, step⟩)
    w req hWf
  exact hRes.2

end LeanSwe.Process.Proofs
