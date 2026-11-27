import Core.Obeys
import Core.ConcOps
import LeanSwe.Process.Impl
import LeanSwe.Process.Proofs.RefinesModelApi
import LeanSwe.Process.Proofs.FullObeysPhases

/-!
Compositional `Core.ObeysStepFromConcCell` proof for `LeanSwe.Process.Internal.mkFullApiM`
over `Internal.ProcessSysCapsM`, `Core.ConcOpsM`, and `Core.StateCellM`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

private theorem map_rawSlotToEntry_fst {fd : Type} (xs : List (Nat × Internal.ProcSlotM fd)) :
    (xs.map Model.rawSlotToEntry).map (·.handleId) = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨_, _⟩; simp [Model.rawSlotToEntry, ih]

private theorem procCellWf_elim {fd : Type} {t : Internal.ProcTableState fd}
    (hWf : Model.procCellWf t = true) :
    t.slots.all (fun p => Model.procSlotWf p.2) = true ∧
    Model.processStateWf (Model.rawTableToState t) = true ∧
    t.nextId ≥ 1 ∧
    Model.hasNoDupHandleIds (t.slots.map Prod.fst) = true ∧
    ∀ p ∈ t.slots, p.1 < t.nextId := by
  have h0 := hWf
  unfold Model.procCellWf at hWf
  simp only [Bool.and_eq_true] at hWf
  obtain ⟨hSlots, hPs⟩ := hWf
  have hPs0 := hPs
  unfold Model.processStateWf Model.rawTableToState at hPs
  simp only [Bool.and_eq_true, map_rawSlotToEntry_fst, decide_eq_true_eq] at hPs
  obtain ⟨⟨hNext, hNoDup⟩, hAll⟩ := hPs
  refine ⟨hSlots, hPs0, hNext, hNoDup, ?_⟩
  intro p hp
  have hE := (List.all_eq_true.mp hAll) (Model.rawSlotToEntry p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  simp only [decide_eq_true_eq] at hE
  exact hE.1.1

private theorem procCellWf_intro {fd : Type} {t : Internal.ProcTableState fd}
    (hSlots : t.slots.all (fun p => Model.procSlotWf p.2) = true)
    (hNext : t.nextId ≥ 1)
    (hNoDup : Model.hasNoDupHandleIds (t.slots.map Prod.fst) = true)
    (hLt : ∀ p ∈ t.slots, p.1 < t.nextId) :
    Model.procCellWf t = true := by
  unfold Model.procCellWf Model.processStateWf Model.rawTableToState
  simp only [hSlots, Bool.true_and, map_rawSlotToEntry_fst, hNoDup, Bool.and_true]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map]
  refine ⟨hNext, ?_⟩
  intro e ⟨p, hp, he⟩
  subst he
  have hpWf : Model.procSlotWf p.2 = true := (List.all_eq_true.mp hSlots) p hp
  unfold Model.procSlotWf at hpWf
  simp only [decide_eq_true_eq] at hpWf
  have hPidPos : (1 : Nat) ≤ p.2.pid.toNat := hpWf.1
  have hPgidPos : (1 : Nat) ≤ p.2.pgid.toNat := hpWf.2.2.1
  exact ⟨⟨hLt p hp, by simpa [Model.rawSlotToEntry] using Int.ofNat_lt.mpr hPidPos⟩,
    by simpa [Model.rawSlotToEntry] using Int.ofNat_lt.mpr hPgidPos⟩

private theorem findSlotPure_some_mem {fd : Type} (hid : Nat)
    (xs : List (Nat × Internal.ProcSlotM fd)) (slot : Internal.ProcSlotM fd)
    (h : SysBridge.findSlotPure hid xs = some slot) :
    hid ∈ xs.map Prod.fst := by
  induction xs with
  | nil => simp [SysBridge.findSlotPure] at h
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    unfold SysBridge.findSlotPure at h
    by_cases hEq : (k == hid) = true
    · simp only [List.map_cons, List.mem_cons]; exact Or.inl (beq_iff_eq.mp hEq).symm
    · rw [ite_eq_right hEq] at h; exact List.mem_cons_of_mem _ (ih h)

private theorem bool_and_mp {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp at h ⊢

private theorem bool_and_mpr {a b : Bool} (h : a = true ∧ b = true) : (a && b) = true := by
  rw [h.1, h.2]; rfl

private theorem map_fst_update_slot {fd : Type} (xs : List (Nat × Internal.ProcSlotM fd))
    (hid : Nat) (f : Internal.ProcSlotM fd → Internal.ProcSlotM fd) :
    (xs.map fun x => if x.1 == hid then (x.1, f x.2) else (x.1, x.2)).map Prod.fst = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    by_cases hEq : (hd.1 == hid) = true
    · simp only [List.map_cons, hEq, ↓reduceIte, ih]
    · simp only [List.map_cons, hEq, Bool.false_eq_true, ↓reduceIte, ih]

private theorem filter_update_slot {fd : Type} (xs : List (Nat × Internal.ProcSlotM fd))
    (hid : Nat) (f : Internal.ProcSlotM fd → Internal.ProcSlotM fd) :
    ((xs.map fun x => if x.1 == hid then (x.1, f x.2) else (x.1, x.2)).map
        Model.rawSlotToEntry).filter (·.handleId != hid) =
      (xs.map Model.rawSlotToEntry).filter (·.handleId != hid) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    by_cases hEq : (hd.1 == hid) = true
    · have hNeF : (hd.1 != hid) = false := by simp [beq_iff_eq.mp hEq]
      simp only [List.map_cons, hEq, ↓reduceIte, List.filter_cons, Model.rawSlotToEntry, hNeF, Bool.false_eq_true, ih]
    · have hNeT : (hd.1 != hid) = true := bne_iff_ne.mpr (fun h => hEq (beq_iff_eq.mpr h))
      simp only [List.map_cons, hEq, Bool.false_eq_true, ↓reduceIte, List.filter_cons, Model.rawSlotToEntry, hNeT, ih]

private theorem removeSlotList_mem {fd : Type} (hid : Nat) (xs : List (Nat × Internal.ProcSlotM fd))
    (p : Nat × Internal.ProcSlotM fd) (hp : p ∈ (SysBridge.removeSlotList hid xs).2) :
    p ∈ xs := by
  induction xs with
  | nil => simp [SysBridge.removeSlotList] at hp
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    unfold SysBridge.removeSlotList at hp
    by_cases hEq : (k == hid) = true
    · rw [ite_eq_left hEq] at hp; exact List.mem_cons_of_mem _ hp
    · rw [ite_eq_right hEq] at hp; dsimp only at hp
      rcases List.mem_cons.mp hp with rfl | hTl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hTl)

private theorem hasNoDupHandleIds_removeSlot {fd : Type} (hid : Nat)
    (xs : List (Nat × Internal.ProcSlotM fd))
    (hNoDup : Model.hasNoDupHandleIds (xs.map Prod.fst) = true) :
    Model.hasNoDupHandleIds ((SysBridge.removeSlotList hid xs).2.map Prod.fst) = true := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, Model.hasNoDupHandleIds, Bool.and_eq_true, Bool.not_eq_true'] at hNoDup
    unfold SysBridge.removeSlotList
    by_cases hEq : (k == hid) = true
    · rw [ite_eq_left hEq]; exact hNoDup.2
    · rw [ite_eq_right hEq]; dsimp only
      simp only [List.map_cons, Model.hasNoDupHandleIds, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, ih hNoDup.2⟩
      rw [Bool.eq_false_iff]; intro hCont
      rcases List.mem_map.mp (List.contains_iff_mem.mp hCont) with ⟨⟨k', v'⟩, hp, hk⟩
      dsimp only at hk; subst hk
      have hContTl : (tl.map Prod.fst).contains k' = true :=
        List.contains_iff_mem.mpr (List.mem_map.mpr ⟨(k', v'), removeSlotList_mem hid tl (k', v') hp, rfl⟩)
      rw [hContTl] at hNoDup; cases hNoDup.1

private theorem map_removeSlotList_eq_filter {fd : Type} (xs : List (Nat × Internal.ProcSlotM fd))
    (hid : Nat) (hNoDup : Model.hasNoDupHandleIds (xs.map Prod.fst) = true) :
    (SysBridge.removeSlotList hid xs).2.map Model.rawSlotToEntry =
      (xs.map Model.rawSlotToEntry).filter (·.handleId != hid) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, Model.hasNoDupHandleIds, Bool.and_eq_true, Bool.not_eq_true'] at hNoDup
    unfold SysBridge.removeSlotList
    by_cases hEq : (k == hid) = true
    · have hkHid : k = hid := beq_iff_eq.mp hEq; subst hkHid
      simp only [beq_self_eq_true, ↓reduceIte, List.map_cons, List.filter_cons, Model.rawSlotToEntry, bne_self_eq_false, Bool.false_eq_true]
      symm; rw [List.filter_eq_self]
      intro e he
      rcases List.mem_map.mp he with ⟨⟨k', v'⟩, hkv, rfl⟩
      dsimp only [Model.rawSlotToEntry]; rw [bne_iff_ne]; intro hKe; subst hKe
      have hCont : (tl.map Prod.fst).contains k' = true :=
        List.contains_iff_mem.mpr (List.mem_map.mpr ⟨(k', v'), hkv, rfl⟩)
      rw [hCont] at hNoDup; cases hNoDup.1
    · have hNeT : (k != hid) = true := bne_iff_ne.mpr (fun h => hEq (beq_iff_eq.mpr h))
      simp only [hEq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.filter_cons, Model.rawSlotToEntry, hNeT, ih hNoDup.2]

private theorem insertSlotPure_step {fd : Type} {t : Internal.ProcTableState fd}
    (hWf : Model.procCellWf t = true) (slot : Internal.ProcSlotM fd)
    (hSlot : Model.procSlotWf slot = true)
    (hInSome : slot.stdinFd?.isNone = false) (hWaitF : slot.waited = false) :
    let (hid, t') := SysBridge.insertSlotPure t slot
    Model.procCellWf t' = true ∧
    Model.allowedRawSpawn (Model.rawTableToState t)
      (.ok { handleId := hid, pid := Int.ofNat slot.pid.toNat, pgid := Int.ofNat slot.pgid.toNat })
      (Model.rawTableToState t') := by
  obtain ⟨hSlots, _, _, hNoDup, hLt⟩ := procCellWf_elim hWf
  have hSwf := hSlot
  unfold Model.procSlotWf at hSwf; simp only [decide_eq_true_eq] at hSwf
  have hPidNat : (1 : Nat) ≤ slot.pid.toNat := hSwf.1
  have hPgidNat : (1 : Nat) ≤ slot.pgid.toNat := hSwf.2.2.1
  dsimp only [SysBridge.insertSlotPure]
  refine ⟨procCellWf_intro ?_ ?_ ?_ ?_, rfl, Int.ofNat_lt.mpr hPidNat, Int.ofNat_lt.mpr hPgidNat, ?_⟩
  · simp only [List.all_cons, Bool.and_eq_true]; exact ⟨hSlot, hSlots⟩
  · exact Nat.le_add_left 1 t.nextId
  · simp only [List.map_cons, Model.hasNoDupHandleIds, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, hNoDup⟩
    rw [Bool.eq_false_iff]; intro hCont
    rcases List.mem_map.mp (List.contains_iff_mem.mp hCont) with ⟨p, hp, hEq⟩
    have := hLt p hp; omega
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hpRest
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hLt p hpRest)
  · dsimp only [Model.rawTableToState]
    simp only [List.map_cons, Model.rawSlotToEntry, hInSome, Bool.false_and, hWaitF]

private theorem takeSlotIoPure_step {fd : Type} {t : Internal.ProcTableState fd}
    (hWf : Model.procCellWf t = true) (hid : Nat) :
    let (res, t') := SysBridge.takeSlotIoPure t hid
    Model.procCellWf t' = true ∧
    (Model.rawTableToState t').nextHandleId = (Model.rawTableToState t).nextHandleId ∧
    (Model.rawTableToState t').activeHandles.map (·.handleId) =
      (Model.rawTableToState t).activeHandles.map (·.handleId) ∧
    (Model.rawTableToState t').activeHandles.filter (·.handleId != hid) =
      (Model.rawTableToState t).activeHandles.filter (·.handleId != hid) ∧
    (∀ tup, res = some tup → hid ∈ (Model.rawTableToState t).activeHandles.map (·.handleId)) := by
  obtain ⟨hSlots, _, hNext, hNoDup, hLt⟩ := procCellWf_elim hWf
  dsimp only [SysBridge.takeSlotIoPure]
  cases hFind : SysBridge.findSlotPure hid t.slots with
  | none =>
    exact ⟨hWf, rfl, rfl, rfl, fun _ h => by cases h⟩
  | some slot =>
    dsimp only
    refine ⟨procCellWf_intro ?_ hNext ?_ ?_, rfl, ?_, ?_, ?_⟩
    · dsimp only; rw [List.all_eq_true]
      intro p hp
      rcases List.mem_map.mp hp with ⟨⟨k, v⟩, hkv, hpEq⟩
      have hvWf := (List.all_eq_true.mp hSlots) (k, v) hkv
      by_cases hEq : (k == hid) = true
      · rw [ite_eq_left hEq] at hpEq; rw [← hpEq]; simpa [Model.procSlotWf] using hvWf
      · rw [ite_eq_right hEq] at hpEq; rw [← hpEq]; exact hvWf
    · dsimp only
      rw [map_fst_update_slot t.slots hid (fun s => { s with stdinFd? := none, stdoutFd? := none, stderrFd? := none })]
      exact hNoDup
    · dsimp only; intro p hp
      rcases List.mem_map.mp hp with ⟨⟨k, v⟩, hkv, hpEq⟩
      have hkLt := hLt (k, v) hkv
      by_cases hEq : (k == hid) = true
      · rw [ite_eq_left hEq] at hpEq; rw [← hpEq]; exact hkLt
      · rw [ite_eq_right hEq] at hpEq; rw [← hpEq]; exact hkLt
    · dsimp only [Model.rawTableToState]
      rw [map_rawSlotToEntry_fst, map_rawSlotToEntry_fst]
      exact map_fst_update_slot t.slots hid (fun s => { s with stdinFd? := none, stdoutFd? := none, stderrFd? := none })
    · dsimp only [Model.rawTableToState]
      exact filter_update_slot t.slots hid (fun s => { s with stdinFd? := none, stdoutFd? := none, stderrFd? := none })
    · intro _ _; dsimp only [Model.rawTableToState]; rw [map_rawSlotToEntry_fst]
      exact findSlotPure_some_mem hid t.slots slot hFind

private theorem markWaitedPure_step {fd : Type} {t : Internal.ProcTableState fd}
    (hWf : Model.procCellWf t = true) (hid : Nat) (waited : Bool) :
    let (_, t') := SysBridge.markWaitedPure t hid waited
    Model.procCellWf t' = true ∧
    (Model.rawTableToState t').nextHandleId = (Model.rawTableToState t).nextHandleId ∧
    (Model.rawTableToState t').activeHandles.map (·.handleId) =
      (Model.rawTableToState t).activeHandles.map (·.handleId) ∧
    (Model.rawTableToState t').activeHandles.filter (·.handleId != hid) =
      (Model.rawTableToState t).activeHandles.filter (·.handleId != hid) := by
  obtain ⟨hSlots, _, hNext, hNoDup, hLt⟩ := procCellWf_elim hWf
  dsimp only [SysBridge.markWaitedPure]
  cases SysBridge.findSlotPure hid t.slots with
  | none => exact ⟨hWf, rfl, rfl, rfl⟩
  | some _ =>
    dsimp only
    refine ⟨procCellWf_intro ?_ hNext ?_ ?_, rfl, ?_, ?_⟩
    · dsimp only; rw [List.all_eq_true]
      intro p hp
      rcases List.mem_map.mp hp with ⟨⟨k, v⟩, hkv, hpEq⟩
      have hvWf := (List.all_eq_true.mp hSlots) (k, v) hkv
      by_cases hEq : (k == hid) = true
      · rw [ite_eq_left hEq] at hpEq; rw [← hpEq]; simpa [Model.procSlotWf] using hvWf
      · rw [ite_eq_right hEq] at hpEq; rw [← hpEq]; exact hvWf
    · dsimp only
      rw [map_fst_update_slot t.slots hid (fun s => { s with waited := s.waited || waited })]
      exact hNoDup
    · dsimp only; intro p hp
      rcases List.mem_map.mp hp with ⟨⟨k, v⟩, hkv, hpEq⟩
      have hkLt := hLt (k, v) hkv
      by_cases hEq : (k == hid) = true
      · rw [ite_eq_left hEq] at hpEq; rw [← hpEq]; exact hkLt
      · rw [ite_eq_right hEq] at hpEq; rw [← hpEq]; exact hkLt
    · dsimp only [Model.rawTableToState]
      rw [map_rawSlotToEntry_fst, map_rawSlotToEntry_fst]
      exact map_fst_update_slot t.slots hid (fun s => { s with waited := s.waited || waited })
    · dsimp only [Model.rawTableToState]
      exact filter_update_slot t.slots hid (fun s => { s with waited := s.waited || waited })

private theorem detachSlotPure_step {fd : Type} {t : Internal.ProcTableState fd}
    (hWf : Model.procCellWf t = true) (hid : Nat) :
    let (_, t') := SysBridge.detachSlotPure t hid
    Model.procCellWf t' = true ∧
    (Model.rawTableToState t').nextHandleId = (Model.rawTableToState t).nextHandleId ∧
    (Model.rawTableToState t').activeHandles =
      (Model.rawTableToState t).activeHandles.filter (·.handleId != hid) := by
  obtain ⟨hSlots, _, hNext, hNoDup, hLt⟩ := procCellWf_elim hWf
  dsimp only [SysBridge.detachSlotPure]
  refine ⟨procCellWf_intro ?_ hNext (hasNoDupHandleIds_removeSlot hid _ hNoDup) ?_, rfl, ?_⟩
  · rw [List.all_eq_true]
    intro p hp; exact (List.all_eq_true.mp hSlots) p (removeSlotList_mem hid _ p hp)
  · intro p hp; exact hLt p (removeSlotList_mem hid _ p hp)
  · dsimp only [Model.rawTableToState]; exact map_removeSlotList_eq_filter t.slots hid hNoDup

private theorem mapCaughtMsg_isNonOutcome (prog? : Option String) (msg : String) :
    Model.isNonOutcomeError (SysBridge.mapCaughtMsg prog? msg) := by
  have h := mapRawError_userError_isNonOutcome msg
  unfold SysBridge.mapCaughtMsg
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

private theorem tryCatchMsg_frame_post {W CellT α : Type}
    {inv : W → Prop} {projCell : W → CellT} {conc : Core.ConcOpsM (StateM W)}
    (hConc : Core.ObeysConcFrame inv (fun w₁ w₂ => projCell w₂ = projCell w₁) conc)
    (act : StateM W α) (P : α → Prop)
    (hAct : ∀ w, inv w → let (a, w') := act.run w; inv w' ∧ projCell w' = projCell w ∧ P a)
    (w : W) (hw : inv w) :
    let (res, w') := (conc.tryCatchMsg act).run w
    inv w' ∧ projCell w' = projCell w ∧
    match res with
    | .ok a => P a
    | .error msg => msg ≠ "" := by
  rcases hConc with ⟨_, _, _, _, _, _, _, _, _, _, _, hTry⟩
  have hT := hTry act
    (fun w0 a w1 => projCell w1 = projCell w0 ∧ P a)
    (fun w0 w1 => projCell w1 = projCell w0)
    (fun _ _ => rfl)
    (fun w0 hw0 => by
      have ha := hAct w0 hw0
      cases hR : act.run w0 with
      | mk a w1 => rw [hR] at ha; exact ⟨ha.1, ⟨ha.2.1, ha.2.2⟩, ha.2.1⟩)
    w hw
  cases hR : (conc.tryCatchMsg act).run w with
  | mk res w' =>
    rw [hR] at hT
    cases res with
    | ok a => exact ⟨hT.1, hT.2.1, hT.2.2⟩
    | error msg => exact ⟨hT.1, hT.2.2, hT.2.1⟩

private theorem mapFullWorldToState_wf_iff {Ref TaskH : Type → Type}
    (rw : Model.FullHostWorld) (tbl : Internal.ProcCellS Ref TaskH) :
    Model.processStateWf (Model.mapFullWorldToState rw (Model.procCellToState tbl)) = true ↔
      Model.fullRawWf rw = true ∧ Model.procCellWf tbl = true := by
  unfold Model.mapFullWorldToState Model.procCellToState
  cases hr : Model.fullRawWf rw with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, false_and, iff_false]; decide
  | true =>
    cases hc : Model.procCellWf tbl with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, and_false, iff_false]; decide
    | true => simp only [↓reduceIte, and_self, iff_true]; exact (procCellWf_elim hc).2.1

private theorem mapFullWorldToState_eq_rawTable {Ref TaskH : Type → Type}
    {rw : Model.FullHostWorld} {tbl : Internal.ProcCellS Ref TaskH}
    (hr : Model.fullRawWf rw = true) (hc : Model.procCellWf tbl = true) :
    Model.mapFullWorldToState rw (Model.procCellToState tbl) = Model.rawTableToState tbl := by
  unfold Model.mapFullWorldToState Model.procCellToState; simp [hr, hc]

private theorem mkFullRawOpsM_refines_full {W : Type}
    (projRaw : W → Model.FullHostWorld)
    (raw : Internal.ProcessSysCapsM (StateM W))
    (conc : Core.ConcOpsM (StateM W))
    (projCell : W → Internal.ProcCellS conc.Ref conc.TaskHandle)
    (cell : Core.StateCellM (StateM W) (Internal.ProcCellS conc.Ref conc.TaskHandle))
    (hRaw : Core.ObeysStep projRaw Model.fullRawWf (Model.execFullRawStep raw) Model.allowedFullRawStep)
    (hFrame : ∀ w req, Model.fullRawWf (projRaw w) = true →
      projCell ((Model.execFullRawStep raw req).run w).2 = projCell w)
    (hConc : Core.ObeysConcFrame (fun w => Model.fullRawWf (projRaw w) = true)
      (fun w₁ w₂ => projCell w₂ = projCell w₁) conc)
    (hCell : Core.ObeysStateCell projRaw projCell cell)
    (w : W) (req : Model.RawStepReq)
    (hWf : (Model.fullRawWf (projRaw w) && Model.procCellWf (projCell w)) = true) :
    let (out, w') := (Model.execRawStep (SysBridge.mkFullRawOpsM raw conc cell) req).run w
    (Model.fullRawWf (projRaw w') && Model.procCellWf (projCell w')) = true ∧
    Model.allowedRawStep
      (Model.mapFullWorldToState (projRaw w) (Model.procCellToState (projCell w)))
      req out
      (Model.mapFullWorldToState (projRaw w') (Model.procCellToState (projCell w'))) := by
  obtain ⟨hRw, hCw⟩ := bool_and_mp hWf
  have hSys := sysPreservesFrame_of_obeysStep projRaw projCell raw hRaw hFrame
  have hrefl : ∀ x : W, projCell x = projCell x := fun _ => rfl
  have htrans : ∀ x y z : W, projCell y = projCell x → projCell z = projCell y → projCell z = projCell x :=
    fun _ _ _ h1 h2 => h2.trans h1
  have hPsW : Model.processStateWf (Model.rawTableToState (projCell w)) = true :=
    (procCellWf_elim hCw).2.1
  rw [mapFullWorldToState_eq_rawTable hRw hCw]
  cases req with
  | mapRawError err =>
    dsimp only [Model.execRawStep, SysBridge.mkFullRawOpsM]
    simp only [hostStateT_pure_run]; rw [mapFullWorldToState_eq_rawTable hRw hCw]
    exact ⟨hWf, hPsW, hPsW, rfl, (refinesPure_mapRawError err).symm⟩
  | spawn sreq =>
    dsimp only [Model.execRawStep, SysBridge.mkFullRawOpsM]
    rw [hostStateT_map_run]
    unfold SysBridge.spawnConc
    rw [hostStateT_bind_run]
    have hTry := tryCatchMsg_frame_post hConc
      (SysBridge.spawnOsPhase (SysBridge.sysDepsOfCaps raw) DEFAULT_EINTR_FUEL sreq)
      (fun res => match res with
        | .error err => Model.isNonOutcomeError err
        | .ok slot => Model.procSlotWf slot = true ∧ slot.stdinFd?.isNone = false ∧ slot.waited = false)
      (fun x hx => spawnOsPhase_full_spec hrefl htrans hSys sreq x hx)
      w hRw
    cases hTRun : (conc.tryCatchMsg (SysBridge.spawnOsPhase (SysBridge.sysDepsOfCaps raw) DEFAULT_EINTR_FUEL sreq)).run w with
    | mk tr w1 =>
      rw [hTRun] at hTry
      obtain ⟨hRw1, hCell1, hPost1⟩ := hTry
      have hCw1 : Model.procCellWf (projCell w1) = true := hCell1 ▸ hCw
      cases tr with
      | error msg =>
        simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw1, hCw1⟩, ?_⟩
        rw [mapFullWorldToState_eq_rawTable hRw1 hCw1, hCell1]
        exact ⟨hPsW, hPsW, rfl, mapCaughtMsg_isNonOutcome (some sreq.program) msg⟩
      | ok osRes =>
        cases osRes with
        | error err =>
          simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw1, hCw1⟩, ?_⟩
          rw [mapFullWorldToState_eq_rawTable hRw1 hCw1, hCell1]
          exact ⟨hPsW, hPsW, rfl, hPost1⟩
        | ok slot =>
          dsimp only; rw [hostStateT_bind_run]
          have hMod := hCell.2 (fun st => SysBridge.insertSlotPure st slot) w1
          cases hMRun : (cell.modifyGet (fun st => SysBridge.insertSlotPure st slot)).run w1 with
          | mk hid w2 =>
            rw [hMRun] at hMod; simp only [hostStateT_pure_run]
            obtain ⟨hHidEq, hCell2, hRaw2⟩ := hMod
            have hRw2 : Model.fullRawWf (projRaw w2) = true := hRaw2 ▸ hRw1
            have hIns := insertSlotPure_step hCw1 slot hPost1.1 hPost1.2.1 hPost1.2.2
            have hInsEq : SysBridge.insertSlotPure (projCell w1) slot = (hid, projCell w2) := Prod.ext hHidEq.symm hCell2.symm
            rw [hInsEq] at hIns; dsimp only at hIns
            have hPs2 := (procCellWf_elim hIns.1).2.1
            refine ⟨bool_and_mpr ⟨hRw2, hIns.1⟩, ?_⟩
            rw [mapFullWorldToState_eq_rawTable hRw2 hIns.1]
            have hSpawned := hIns.2; rw [hCell1] at hSpawned
            exact ⟨hPsW, hPs2, hSpawned⟩
  | awaitOutput h stdin to? max? =>
    dsimp only [Model.execRawStep, SysBridge.mkFullRawOpsM]; rw [hostStateT_map_run]
    unfold SysBridge.awaitOutputConc; rw [hostStateT_bind_run]
    have hMod1 := hCell.2 (fun st => SysBridge.takeSlotIoPure st h.handleId) w
    cases hM1 : (cell.modifyGet (fun st => SysBridge.takeSlotIoPure st h.handleId)).run w with
    | mk tk w1 =>
      rw [hM1] at hMod1; obtain ⟨hTkEq, hCell1, hRaw1⟩ := hMod1
      have hRw1 : Model.fullRawWf (projRaw w1) = true := hRaw1 ▸ hRw
      have hTake := takeSlotIoPure_step hCw h.handleId
      have hTakeEq : SysBridge.takeSlotIoPure (projCell w) h.handleId = (tk, projCell w1) := Prod.ext hTkEq.symm hCell1.symm
      rw [hTakeEq] at hTake; dsimp only at hTake
      obtain ⟨hCw1, hNext1, hMap1, hFilt1, hMem1⟩ := hTake
      have hPs1 := (procCellWf_elim hCw1).2.1
      cases tk with
      | none =>
        simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw1, hCw1⟩, ?_⟩
        rw [mapFullWorldToState_eq_rawTable hRw1 hCw1]
        exact ⟨hPsW, hPs1, hPs1, hNext1, hMap1, hFilt1, mapRawError_userError_isNonOutcome _⟩
      | some tup =>
        rcases tup with ⟨pid, inFd0?, outFd0?, errFd0?⟩; have hMem := hMem1 _ rfl
        dsimp only; rw [hostStateT_bind_run]
        have hTry := tryCatchMsg_frame_post hConc
          (SysBridge.awaitOsPhase (SysBridge.sysDepsOfCaps raw) DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL pid inFd0? outFd0? errFd0? stdin to? max?)
          (fun res => match res with | .error err => Model.isNonOutcomeError err | .ok (_, outcome) => Model.allowedAwaitOutcome to? max? outcome)
          (fun x hx => awaitOsPhase_full_spec hrefl htrans hSys pid inFd0? outFd0? errFd0? stdin to? max? x hx) w1 hRw1
        cases hTRun : (conc.tryCatchMsg (SysBridge.awaitOsPhase (SysBridge.sysDepsOfCaps raw)
            DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL pid inFd0? outFd0? errFd0? stdin to? max?)).run w1 with
        | mk tr w2 =>
          rw [hTRun] at hTry; obtain ⟨hRw2, hCell2, hPost2⟩ := hTry
          have hCw2 : Model.procCellWf (projCell w2) = true := hCell2 ▸ hCw1
          cases tr with
          | error msg =>
            simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw2, hCw2⟩, ?_⟩
            rw [mapFullWorldToState_eq_rawTable hRw2 hCw2, hCell2]
            exact ⟨hPsW, hPs1, hPs1, hNext1, hMap1, hFilt1, mapCaughtMsg_isNonOutcome none msg⟩
          | ok osRes =>
            cases osRes with
            | error _ =>
              simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw2, hCw2⟩, ?_⟩
              rw [mapFullWorldToState_eq_rawTable hRw2 hCw2, hCell2]
              exact ⟨hPsW, hPs1, hPs1, hNext1, hMap1, hFilt1, hPost2⟩
            | ok pair =>
              rcases pair with ⟨waitedFlag, _⟩; dsimp only; rw [hostStateT_bind_run]
              have hMod2 := hCell.2 (fun st => SysBridge.markWaitedPure st h.handleId waitedFlag) w2
              cases hM2 : (cell.modifyGet (fun st => SysBridge.markWaitedPure st h.handleId waitedFlag)).run w2 with
              | mk okFlag w3 =>
                rw [hM2] at hMod2; obtain ⟨hOkEq, hCell3, hRaw3⟩ := hMod2
                have hRw3 : Model.fullRawWf (projRaw w3) = true := hRaw3 ▸ hRw2
                have hMark := markWaitedPure_step hCw2 h.handleId waitedFlag
                have hMarkEq : SysBridge.markWaitedPure (projCell w2) h.handleId waitedFlag = (okFlag, projCell w3) := Prod.ext hOkEq.symm hCell3.symm
                rw [hMarkEq] at hMark; dsimp only at hMark
                obtain ⟨hCw3, hNext3, hMap3, hFilt3⟩ := hMark
                have hPs3 := (procCellWf_elim hCw3).2.1
                have hNext3' : (Model.rawTableToState (projCell w3)).nextHandleId = (Model.rawTableToState (projCell w)).nextHandleId := by rw [hNext3, hCell2, hNext1]
                have hMap3' : (Model.rawTableToState (projCell w3)).activeHandles.map (·.handleId) = (Model.rawTableToState (projCell w)).activeHandles.map (·.handleId) := by rw [hMap3, hCell2, hMap1]
                have hFilt3' : (Model.rawTableToState (projCell w3)).activeHandles.filter (·.handleId != h.handleId) = (Model.rawTableToState (projCell w)).activeHandles.filter (·.handleId != h.handleId) := by rw [hFilt3, hCell2, hFilt1]
                cases okFlag with
                | false =>
                  simp only [Bool.not_false, ↓reduceIte, hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw3, hCw3⟩, ?_⟩
                  rw [mapFullWorldToState_eq_rawTable hRw3 hCw3]
                  exact ⟨hPsW, hPs3, hPs3, hNext3', hMap3', hFilt3', mapRawError_userError_isNonOutcome _⟩
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw3, hCw3⟩, ?_⟩
                  rw [mapFullWorldToState_eq_rawTable hRw3 hCw3]
                  exact ⟨hPsW, hPs3, hPs3, hNext3', hMap3', hFilt3', hMem, hPost2⟩
  | killProcessGroup h =>
    dsimp only [Model.execRawStep, SysBridge.mkFullRawOpsM]; rw [hostStateT_map_run]
    unfold SysBridge.killProcessGroupConc; rw [hostStateT_bind_run]
    have hGet := hCell.1 w
    cases hG : cell.get.run w with
    | mk st w1 =>
      rw [hG] at hGet; obtain ⟨rfl, hCell1, hRaw1⟩ := hGet
      have hRw1 : Model.fullRawWf (projRaw w1) = true := hRaw1 ▸ hRw
      have hCw1 : Model.procCellWf (projCell w1) = true := hCell1 ▸ hCw
      dsimp only
      cases (SysBridge.findSlotPure h.handleId (projCell w).slots).map (·.pgid) with
      | none =>
        simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw1, hCw1⟩, ?_⟩
        rw [mapFullWorldToState_eq_rawTable hRw1 hCw1, hCell1]
        exact ⟨hPsW, hPsW, rfl, trivial⟩
      | some pgid =>
        dsimp only; rw [hostStateT_bind_run]
        have hTry := tryCatchMsg_frame_post hConc
          (SysBridge.killGroupOsPhase (SysBridge.sysDepsOfCaps raw) DEFAULT_EINTR_FUEL pgid)
          (fun res => match res with | .ok () => True | .error err => Model.isNonOutcomeError err)
          (fun x hx => killGroupOsPhase_full_spec hrefl htrans hSys pgid x hx) w1 hRw1
        cases hTRun : (conc.tryCatchMsg (SysBridge.killGroupOsPhase (SysBridge.sysDepsOfCaps raw) DEFAULT_EINTR_FUEL pgid)).run w1 with
        | mk tr w2 =>
          rw [hTRun] at hTry; obtain ⟨hRw2, hCell2, hPost2⟩ := hTry
          have hCw2 : Model.procCellWf (projCell w2) = true := (hCell2.trans hCell1) ▸ hCw
          cases tr with
          | error msg =>
            simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw2, hCw2⟩, ?_⟩
            rw [mapFullWorldToState_eq_rawTable hRw2 hCw2, hCell2, hCell1]
            exact ⟨hPsW, hPsW, rfl, mapCaughtMsg_isNonOutcome none msg⟩
          | ok _ =>
            simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw2, hCw2⟩, ?_⟩
            rw [mapFullWorldToState_eq_rawTable hRw2 hCw2, hCell2, hCell1]
            exact ⟨hPsW, hPsW, rfl, hPost2⟩
  | reap h =>
    dsimp only [Model.execRawStep, SysBridge.mkFullRawOpsM]; rw [hostStateT_map_run]
    unfold SysBridge.reapConc; rw [hostStateT_bind_run]
    have hMod := hCell.2 (fun st => SysBridge.detachSlotPure st h.handleId) w
    cases hM : (cell.modifyGet (fun st => SysBridge.detachSlotPure st h.handleId)).run w with
    | mk det w1 =>
      rw [hM] at hMod; obtain ⟨hDetEq, hCell1, hRaw1⟩ := hMod
      have hRw1 : Model.fullRawWf (projRaw w1) = true := hRaw1 ▸ hRw
      have hDet := detachSlotPure_step hCw h.handleId
      have hDetEqP : SysBridge.detachSlotPure (projCell w) h.handleId = (det, projCell w1) := Prod.ext hDetEq.symm hCell1.symm
      rw [hDetEqP] at hDet; dsimp only at hDet
      obtain ⟨hCw1, hNext1, hAct1⟩ := hDet; have hPs1 := (procCellWf_elim hCw1).2.1
      cases det with
      | none =>
        simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw1, hCw1⟩, ?_⟩
        rw [mapFullWorldToState_eq_rawTable hRw1 hCw1]
        exact ⟨hPsW, hPs1, hNext1, hAct1, trivial⟩
      | some slot =>
        dsimp only; rw [hostStateT_bind_run]
        have hTry := tryCatchMsg_frame_post hConc
          (SysBridge.reapOsPhase (SysBridge.sysDepsOfCaps raw) DEFAULT_EINTR_FUEL slot)
          (fun res => match res with | .ok () => True | .error err => Model.isNonOutcomeError err)
          (fun x hx => reapOsPhase_full_spec hrefl htrans hSys slot x hx) w1 hRw1
        cases hTRun : (conc.tryCatchMsg (SysBridge.reapOsPhase (SysBridge.sysDepsOfCaps raw) DEFAULT_EINTR_FUEL slot)).run w1 with
        | mk tr w2 =>
          rw [hTRun] at hTry; obtain ⟨hRw2, hCell2, hPost2⟩ := hTry
          have hCw2 : Model.procCellWf (projCell w2) = true := hCell2 ▸ hCw1
          cases tr with
          | error msg =>
            simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw2, hCw2⟩, ?_⟩
            rw [mapFullWorldToState_eq_rawTable hRw2 hCw2, hCell2]
            exact ⟨hPsW, hPs1, hNext1, hAct1, mapCaughtMsg_isNonOutcome none msg⟩
          | ok _ =>
            simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw2, hCw2⟩, ?_⟩
            rw [mapFullWorldToState_eq_rawTable hRw2 hCw2, hCell2]
            exact ⟨hPsW, hPs1, hNext1, hAct1, hPost2⟩
  | activeProcessCount =>
    dsimp only [Model.execRawStep, SysBridge.mkFullRawOpsM]
    rw [hostStateT_map_run, hostStateT_bind_run]
    have hGet := hCell.1 w
    cases hG : cell.get.run w with
    | mk st w1 =>
      rw [hG] at hGet; obtain ⟨rfl, hCell1, hRaw1⟩ := hGet
      have hRw1 : Model.fullRawWf (projRaw w1) = true := hRaw1 ▸ hRw
      have hCw1 : Model.procCellWf (projCell w1) = true := hCell1 ▸ hCw
      simp only [hostStateT_pure_run]; refine ⟨bool_and_mpr ⟨hRw1, hCw1⟩, ?_⟩
      rw [mapFullWorldToState_eq_rawTable hRw1 hCw1, hCell1]
      exact ⟨hPsW, hPsW, rfl, by dsimp only [Model.rawTableToState]; rw [List.length_map]⟩

/-- Canonical `Core.ObeysStepFromConcCell` contract for `LeanSwe.Process.Internal.mkFullApiM`
    over `Internal.ProcessSysCapsM`, `Core.ConcOpsM`, and `Core.StateCellM`. -/
theorem obeysStepFromConcCell_mkFullApiM :
    Core.ObeysStepFromConcCell (CellS := Internal.ProcCellS)
      Model.mapFullWorldToState Model.procCellToState
      Model.fullRawWf Model.execFullRawStep Model.allowedFullRawStep
      Model.processStateWf Internal.mkFullApiM
      Model.execPkgStep Model.allowedPkgStep := by
  intro W projRaw raw conc projCell cell hRaw hFrame hConc hCell w req hPkgWf
  have hPair := (mapFullWorldToState_wf_iff (projRaw w) (projCell w)).mp hPkgWf
  have hWf : (Model.fullRawWf (projRaw w) && Model.procCellWf (projCell w)) = true :=
    bool_and_mpr hPair
  dsimp only [Core.ObeysStep]
  have hEqApi : Internal.mkFullApiM raw conc cell =
      Internal.mkApiM (SysBridge.mkFullRawOpsM raw conc cell) := rfl
  rw [hEqApi]
  have hRes := mkApiM_refines_of_rawWf
    (fun x => Model.fullRawWf (projRaw x) && Model.procCellWf (projCell x))
    (fun x => Model.mapFullWorldToState (projRaw x) (Model.procCellToState (projCell x)))
    (SysBridge.mkFullRawOpsM raw conc cell)
    (fun x hx => (mapFullWorldToState_wf_iff (projRaw x) (projCell x)).mpr (bool_and_mp hx))
    (mkFullRawOpsM_refines_full projRaw raw conc projCell cell hRaw hFrame hConc hCell)
    w req hWf
  exact hRes.2

end LeanSwe.Process.Proofs
