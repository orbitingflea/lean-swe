import Core.Refines
import LeanSwe.Process.Types
import LeanSwe.Process.Model

/-!
Non-vacuity witness for `LeanSwe.Process.Model.allowedRawStep`, proving that
`modelRawOps : RawProcessOpsM (StateM Model.ProcessModelState)` genuinely satisfies
`Core.RefinesStep id Model.processStateWf (Model.execRawStep modelRawOps) Model.allowedRawStep`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.Process

private theorem hasNoDupHandleIds_filter {xs : List Nat} (p : Nat → Bool)
    (h : Model.hasNoDupHandleIds xs = true) :
    Model.hasNoDupHandleIds (xs.filter p) = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    unfold Model.hasNoDupHandleIds at h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hNotIn, hRest⟩ := h
    simp only [List.filter_cons]
    cases hp : p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih hRest
    · simp only [↓reduceIte]
      unfold Model.hasNoDupHandleIds
      rw [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, ih hRest⟩
      cases hC : (rest.filter p).contains x
      · rfl
      · have hMem : x ∈ rest.filter p := List.contains_iff_mem.mp hC
        have hMemRest : x ∈ rest := (List.mem_filter.mp hMem).1
        rw [List.contains_iff_mem.mpr hMemRest] at hNotIn
        cases hNotIn

private theorem hasNoDupHandleIds_map_filter {α : Type} (xs : List α) (f : α → Nat) (p : α → Bool)
    (q : Nat → Bool) (hEq : ∀ a, p a = q (f a))
    (h : Model.hasNoDupHandleIds (xs.map f) = true) :
    Model.hasNoDupHandleIds ((xs.filter p).map f) = true := by
  have hMap : ∀ xs : List α, (xs.filter p).map f = (xs.map f).filter q := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.filter_cons, List.map_cons, hEq a]
      cases hq : q (f a)
      · simp only [Bool.false_eq_true, ↓reduceIte, ih]
      · simp only [↓reduceIte, List.map_cons, ih]
  rw [hMap xs]
  exact hasNoDupHandleIds_filter q h

private theorem processStateWf_cons_fresh {s : Model.ProcessModelState}
    (hWf : Model.processStateWf s = true) (pid pgid : Int) (hPid : pid > 0) (hPgid : pgid > 0) :
    Model.processStateWf
      { nextHandleId := s.nextHandleId + 1
        activeHandles :=
          { handleId := s.nextHandleId
            pid := pid
            pgid := pgid
            ioConsumed := false
            waited := false } :: s.activeHandles } = true := by
  unfold Model.processStateWf at hWf ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hWf ⊢
  have hNotMem : s.nextHandleId ∉ s.activeHandles.map (·.handleId) := by
    intro hMem
    rw [List.mem_map] at hMem
    obtain ⟨e, he, heId⟩ := hMem
    have hLt := (hWf.2 e he).1.1
    omega
  have hNotCont : (s.activeHandles.map (·.handleId)).contains s.nextHandleId = false := by
    cases hC : (s.activeHandles.map (·.handleId)).contains s.nextHandleId
    · rfl
    · exact absurd (List.contains_iff_mem.mp hC) hNotMem
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · simp only [List.map_cons]
    unfold Model.hasNoDupHandleIds
    rw [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hNotCont, hWf.1.2⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | hTail
    · exact ⟨⟨Nat.lt_succ_self _, hPid⟩, hPgid⟩
    · have hE := hWf.2 e hTail
      exact ⟨⟨Nat.lt_succ_of_lt hE.1.1, hE.1.2⟩, hE.2⟩

private theorem processStateWf_await_update {s : Model.ProcessModelState}
    (hWf : Model.processStateWf s = true) (hid : Nat) (wFlag : Bool) :
    let handles' := s.activeHandles.map fun e =>
      if e.handleId == hid then { e with ioConsumed := true, waited := wFlag } else e
    Model.processStateWf { nextHandleId := s.nextHandleId, activeHandles := handles' } = true ∧
    handles'.map (·.handleId) = s.activeHandles.map (·.handleId) ∧
    handles'.filter (·.handleId != hid) = s.activeHandles.filter (·.handleId != hid) := by
  dsimp only
  have hMapId : ∀ xs : List Model.ProcessHandleEntry,
      (xs.map fun e => if e.handleId == hid then { e with ioConsumed := true, waited := wFlag } else e).map (·.handleId) =
        xs.map (·.handleId) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.map_cons]
      by_cases hEq : a.handleId = hid
      · have hb : (a.handleId == hid) = true := beq_iff_eq.mpr hEq
        simp only [hb, ↓reduceIte, ih]
      · have hb : (a.handleId == hid) = false := beq_false_of_ne hEq
        simp only [hb, Bool.false_eq_true, ↓reduceIte, ih]
  have hFiltId : ∀ xs : List Model.ProcessHandleEntry,
      (xs.map fun e => if e.handleId == hid then { e with ioConsumed := true, waited := wFlag } else e).filter (·.handleId != hid) =
        xs.filter (·.handleId != hid) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.map_cons]
      by_cases hEq : a.handleId = hid
      · have hb : (a.handleId == hid) = true := beq_iff_eq.mpr hEq
        have hNe : (a.handleId != hid) = false := by simp [hEq]
        simp only [hb, ↓reduceIte, List.filter_cons, hNe, Bool.false_eq_true, ih]
      · have hb : (a.handleId == hid) = false := beq_false_of_ne hEq
        have hNe : (a.handleId != hid) = true := bne_iff_ne.mpr hEq
        simp only [hb, Bool.false_eq_true, ↓reduceIte, List.filter_cons, hNe, ih]
  refine ⟨?_, hMapId s.activeHandles, hFiltId s.activeHandles⟩
  unfold Model.processStateWf at hWf ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hWf ⊢
  rw [hMapId]
  refine ⟨hWf.1, fun e he => ?_⟩
  rw [List.mem_map] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  have hE := hWf.2 e₀ he₀
  by_cases hEq : e₀.handleId = hid
  · have hb : (e₀.handleId == hid) = true := beq_iff_eq.mpr hEq
    simp only [hb, ↓reduceIte]
    exact ⟨⟨hE.1.1, hE.1.2⟩, hE.2⟩
  · have hb : (e₀.handleId == hid) = false := beq_false_of_ne hEq
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact ⟨⟨hE.1.1, hE.1.2⟩, hE.2⟩

private def modelRawOps : RawProcessOpsM (StateM Model.ProcessModelState) where
  mapRawError := Model.mapRawErrorModel
  spawn req := modifyGet fun s =>
    if req.program == "/bin/fail" then
      (.error { kind := .notFound, program := some req.program, message := "not found" }, s)
    else
      let h : ProcessHandle := { handleId := s.nextHandleId, pid := 100, pgid := 100 }
      (.ok h,
       { nextHandleId := s.nextHandleId + 1
         activeHandles :=
           { handleId := h.handleId
             pid := h.pid
             pgid := h.pgid
             ioConsumed := false
             waited := false } :: s.activeHandles })
  awaitOutput h _stdin timeoutMs? maxOutputBytes? := modifyGet fun s =>
    match s.activeHandles.find? (·.handleId == h.handleId) with
    | none => (.error { kind := .ioError, message := "invalid process handle" }, s)
    | some _ =>
      let out : ExecOutcome :=
        if timeoutMs?.isSome then .timedOut ByteArray.empty ByteArray.empty
        else if maxOutputBytes?.isSome then .outputLimitExceeded ByteArray.empty ByteArray.empty
        else .exited { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
      let handles' := s.activeHandles.map fun e =>
        if e.handleId == h.handleId then
          { e with ioConsumed := true, waited := !timeoutMs?.isSome && !maxOutputBytes?.isSome }
        else e
      (.ok out, { s with activeHandles := handles' })
  killProcessGroup _ := pure (.ok ())
  reap h := modifyGet fun s =>
    (.ok (), { s with activeHandles := s.activeHandles.filter (·.handleId != h.handleId) })
  activeProcessCount := do
    return (← get).activeHandles.length

/-- Non-vacuity witness proving `Model.allowedRawStep` is genuinely satisfiable over `ProcessModelState`. -/
theorem modelRawOps_refines_allowedRawStep :
    Core.RefinesStep id Model.processStateWf
      (Model.execRawStep modelRawOps) Model.allowedRawStep := by
  intro s req hWf
  cases req with
  | mapRawError err =>
    exact ⟨hWf, hWf, rfl, rfl⟩
  | spawn r =>
    dsimp only [Model.execRawStep, modelRawOps, Functor.map, StateT.map, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run,
      Model.allowedRawStep, Model.allowedRawSpawn, id]
    by_cases hF : (r.program == "/bin/fail") = true
    · rw [ite_eq_left hF]
      refine ⟨hWf, hWf, rfl, (by simp), ?_, ?_, ?_, ?_⟩ <;> simp
    · rw [ite_eq_right hF]
      have h100 : (100 : Int) > 0 := by decide
      have hWf' := processStateWf_cons_fresh hWf 100 100 h100 h100
      exact ⟨hWf, hWf', rfl, h100, h100, rfl⟩
  | awaitOutput h stdin timeoutMs? maxOutputBytes? =>
    dsimp only [Model.execRawStep, modelRawOps, Functor.map, StateT.map, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run,
      Model.allowedRawStep, Model.allowedAwaitCore, id]
    cases hFind : s.activeHandles.find? (·.handleId == h.handleId) with
    | none =>
      refine ⟨hWf, hWf, hWf, rfl, rfl, rfl, ?_⟩
      simp [Model.isNonOutcomeError]
    | some found =>
      have hUpd := processStateWf_await_update hWf h.handleId (!timeoutMs?.isSome && !maxOutputBytes?.isSome)
      have hMem : h.handleId ∈ s.activeHandles.map (·.handleId) := by
        have hP := List.find?_some hFind
        have hMemF := List.mem_of_find?_eq_some hFind
        rw [List.mem_map]
        exact ⟨found, hMemF, beq_iff_eq.mp hP⟩
      refine ⟨hWf, hUpd.1, hUpd.1, rfl, hUpd.2.1, hUpd.2.2, hMem, ?_⟩
      cases hTo : timeoutMs?.isSome
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hMax : maxOutputBytes?.isSome
        · simp only [Bool.false_eq_true, ↓reduceIte, Model.allowedAwaitOutcome]
          intro lim hLim
          simp [hLim] at hMax
        · simp only [↓reduceIte, Model.allowedAwaitOutcome]
          refine ⟨hMax, fun lim hLim => ?_⟩
          simp
      · simp only [↓reduceIte, Model.allowedAwaitOutcome, hTo]
  | killProcessGroup h =>
    exact ⟨hWf, hWf, rfl, trivial⟩
  | reap h =>
    dsimp only [Model.execRawStep, modelRawOps, Functor.map, StateT.map, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run,
      Model.allowedRawStep, Model.allowedReap, id]
    have hWf' : Model.processStateWf
        { nextHandleId := s.nextHandleId, activeHandles := s.activeHandles.filter (·.handleId != h.handleId) } = true := by
      unfold Model.processStateWf at hWf ⊢
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hWf ⊢
      refine ⟨⟨hWf.1.1, ?_⟩, fun e he => hWf.2 e (List.mem_filter.mp he).1⟩
      exact hasNoDupHandleIds_map_filter s.activeHandles (·.handleId) (·.handleId != h.handleId)
        (· != h.handleId) (fun _ => rfl) hWf.1.2
    exact ⟨hWf, hWf', rfl, rfl, trivial⟩
  | activeProcessCount =>
    exact ⟨hWf, hWf, rfl, rfl⟩

end LeanSwe.Process.Proofs
