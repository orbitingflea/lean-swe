import LeanSweProofs.PostFork.Proofs.PureAndWire

/-!
# PostFork FD Operations Proofs

Reusable `OkPost` specifications for the 10 Rust FD operations in
`LeanSwe.PostFork.Aeneas.postfork.fd_ops`, plus zero-hypothesis `AllPass`
and `CanReach` proofs for the three core `fd_ops` theorems in
`LeanSwe.PostFork.SpecTests`.
-/

namespace LeanSwe.PostFork.Proofs

open _root_.Aeneas _root_.Aeneas.Std
open LeanSwe.PostFork
open LeanSwe.PostFork.Aeneas.Internal
open LeanSwe.PostFork.Aeneas.Internal.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model

private theorem usize_max_ge_4294967295 : 4294967295 ≤ Usize.max := by
  have h1 := Usize.cMax_bound.1
  have h2 : UScalar.cMax UScalarTy.Usize = 4294967295 := by decide
  omega

private theorem slice_index_usize_ok {α : Type} (s : Slice α) (i : Usize) (hi : i.val < s.val.length) :
    s.index_usize i = Result.ok (s.val[i.val]'hi) := by
  have hLen : i.val < s.length := hi
  obtain ⟨x, hx, hEq⟩ := (okPost_iff_wp_spec _ _).mpr (Slice.index_usize_spec s i hLen)
  rw [hx, hEq]

private theorem usize_add_one_ok_of_lt (i : Usize) (hi : i.val < Usize.max) :
    ∃ i1 : Usize, i + 1#usize = Result.ok i1 ∧ i1.val = i.val + 1 := by
  have hBound : i.val + (1#usize).val ≤ Usize.max := by
    change i.val + 1 ≤ Usize.max
    omega
  obtain ⟨z, hz, hzVal⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.add_spec hBound)
  exact ⟨z, hz, by simpa using hzVal⟩

/-! ## Pigeonhole Lemma for `findLowestFreeFd` -/

private theorem findLowestFreeFdAux_some_of_card_lt (s : ChildState) :
    ∀ (n : Nat) (cur : Int) (bound : List Int),
      bound.length < n →
      (∀ x, cur ≤ x → x < cur + Int.ofNat n → s.isOpen x = true → x ∈ bound) →
      ∃ dst, findLowestFreeFdAux s cur n = some dst
  | 0, _, bound, hlt, _ => by omega
  | n + 1, cur, bound, hlt, hmem => by
    by_cases hopen : s.isOpen cur = true
    · have hcur : cur ∈ bound :=
        hmem cur (le_refl cur)
          (by simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]; omega) hopen
      have hlen : (bound.erase cur).length < n := by
        have hpos : 0 < bound.length := List.length_pos_of_mem hcur
        have heq := List.length_erase_of_mem hcur
        omega
      have hmem' :
          ∀ x, cur + 1 ≤ x → x < (cur + 1) + Int.ofNat n → s.isOpen x = true →
            x ∈ bound.erase cur := by
        intro x hx1 hx2 hxopen
        exact (List.mem_erase_of_ne (by omega)).mpr
          (hmem x (by omega)
            (by simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at *; omega) hxopen)
      obtain ⟨dst, hdst⟩ :=
        findLowestFreeFdAux_some_of_card_lt s n (cur + 1) (bound.erase cur) hlen hmem'
      refine ⟨dst, ?_⟩
      simpa [findLowestFreeFdAux, hopen] using hdst
    · have hfalse : s.isOpen cur = false := Bool.eq_false_iff.mpr hopen
      exact ⟨cur, by simp [findLowestFreeFdAux, hfalse]⟩

/-- When `0 ≤ minFd`, `min s.fdLimit 2147483648 > minFd + bound.length`, and every open FD
at or above `minFd` belongs to `bound`, `findLowestFreeFd s minFd` succeeds. -/
theorem findLowestFreeFd_some_of_card_lt (s : ChildState) (minFd : Int) (bound : List Int)
    (h0 : 0 ≤ minFd)
    (hcap : minFd + Int.ofNat bound.length < min s.fdLimit 2147483648)
    (hmem : ∀ x, minFd ≤ x → s.isOpen x = true → x ∈ bound) :
    ∃ dst, findLowestFreeFd s minFd = some dst := by
  simp only [Int.ofNat_eq_natCast] at hcap
  have hcap1 : minFd + ↑bound.length < s.fdLimit :=
    lt_of_lt_of_le hcap (Int.min_le_left _ _)
  have hcap2 : minFd + ↑bound.length < 2147483648 :=
    lt_of_lt_of_le hcap (Int.min_le_right _ _)
  unfold findLowestFreeFd
  have hlt1 : ¬ minFd < 0 := by omega
  have hlt2 : ¬ minFd ≥ min s.fdLimit 2147483648 := by omega
  simp only [hlt1, hlt2, decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  apply findLowestFreeFdAux_some_of_card_lt s (min s.fdLimit 2147483648 - minFd).toNat minFd bound
  · omega
  · intro x hx1 _ hxopen
    exact hmem x hx1 hxopen

private theorem mem_map_fst_of_isOpen {s : ChildState} {x : Int} (hx : s.isOpen x = true) :
    x ∈ s.fds.map Prod.fst := by
  rw [isOpen_iff_isSome] at hx
  unfold ChildState.getFd at hx
  cases hfind : s.fds.find? (fun p => p.1 == x) with
  | none => rw [hfind] at hx; simp at hx
  | some p =>
    have hfst : p.1 = x :=
      beq_iff_eq.mp (List.find?_some (p := fun q : Int × FdEntry => q.1 == x) hfind)
    have hmem : p ∈ s.fds := List.mem_of_find?_eq_some hfind
    exact hfst ▸ List.mem_map.mpr ⟨p, hmem, rfl⟩

private theorem getFd_eq_of_fds_eq {s1 s2 : ChildState} (h : s1.fds = s2.fds) (k : Int) :
    s1.getFd k = s2.getFd k := by
  unfold ChildState.getFd
  rw [h]

/-! ## Pure Slice Helpers -/

private theorem list_any_take_succ {α : Type} (l : List α) (p : α → Bool) (i : Nat)
    (hi : i < l.length) :
    (l.take (i + 1)).any p = ((l.take i).any p || p l[i]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.any_append,
    List.any_cons, List.any_nil, Bool.or_false]

/-- `postfork.fd_ops.slice_contains_nonneg` computes `Model.sliceContainsNonnegSpec`. -/
theorem slice_contains_nonneg_spec (fds : Slice I32) (target : I32) :
    OkPost (postfork.fd_ops.slice_contains_nonneg fds target)
      (fun b => b = sliceContainsNonnegSpec fds.val target.val) := by
  unfold postfork.fd_ops.slice_contains_nonneg
  by_cases hneg : target < 0#i32
  · have ht : target.val < 0 := hneg
    simp only [hneg, ↓reduceIte]
    refine okPost_ok _ _ ?_
    have hdec : decide (0 ≤ target.val) = false := decide_eq_false (by omega)
    simp [sliceContainsNonnegSpec, hdec]
  · have ht : 0 ≤ target.val := by change ¬ target.val < 0 at hneg; omega
    simp only [hneg, ↓reduceIte]
    have hdec : decide (0 ≤ target.val) = true := decide_eq_true ht
    let measure : Usize → Nat := fun i => fds.val.length - i.val
    let inv : Usize → Prop := fun i =>
      i.val ≤ fds.val.length ∧ (fds.val.take i.val).any (fun x => x.val == target.val) = false
    refine okPost_loop_decr_nat measure inv
      (fun b => b = sliceContainsNonnegSpec fds.val target.val)
      (postfork.fd_ops.slice_contains_nonneg_loop.body fds target fds.len) 0#usize ?_
      ⟨Nat.zero_le _, rfl⟩
    · intro i ⟨hiLe, hNone⟩
      unfold postfork.fd_ops.slice_contains_nonneg_loop.body
      by_cases hlt : i < fds.len
      · have hiLen : i.val < fds.val.length := hlt
        simp only [hlt, ↓reduceIte]
        rw [slice_index_usize_ok fds i hiLen, bind_ok]
        have hiMax : i.val < Usize.max := Nat.lt_of_lt_of_le hiLen fds.length_ineq
        by_cases heq : fds.val[i.val] = target
        · simp only [heq, ↓reduceIte]
          refine ⟨ControlFlow.done true, rfl, ?_⟩
          have hmem : fds.val[i.val] ∈ fds.val := List.getElem_mem hiLen
          have hany : fds.val.any (fun x => x.val == target.val) = true :=
            List.any_eq_true.mpr ⟨fds.val[i.val], hmem, by simp [heq]⟩
          simp [sliceContainsNonnegSpec, hdec, hany]
        · simp only [heq, ↓reduceIte]
          obtain ⟨i1, hi1Eq, hi1Val⟩ := usize_add_one_ok_of_lt i hiMax
          rw [hi1Eq, bind_ok]
          refine ⟨ControlFlow.cont i1, rfl, ⟨?_, ?_⟩, ?_⟩
          · omega
          · rw [hi1Val, list_any_take_succ _ _ _ hiLen, hNone, Bool.false_or]
            exact beq_false_of_ne (fun h => heq (IScalar.eq_of_val_eq h))
          · simp only [measure]; omega
      · have hiEq : i.val = fds.val.length := by
          change ¬ i.val < fds.val.length at hlt
          omega
        simp only [hlt, ↓reduceIte]
        refine ⟨ControlFlow.done false, rfl, ?_⟩
        rw [hiEq, List.take_length] at hNone
        simp [sliceContainsNonnegSpec, hdec, hNone]

/-- `postfork.fd_ops.slice_has_stdio_slot` computes `Model.sliceHasStdioSlotSpec`. -/
theorem slice_has_stdio_slot_spec (fds : Slice I32) :
    OkPost (postfork.fd_ops.slice_has_stdio_slot fds)
      (fun b => b = sliceHasStdioSlotSpec fds.val) := by
  unfold postfork.fd_ops.slice_has_stdio_slot
  let measure : Usize → Nat := fun i => fds.val.length - i.val
  let inv : Usize → Prop := fun i =>
    i.val ≤ fds.val.length ∧
    (fds.val.take i.val).any (fun x => decide (0 ≤ x.val ∧ x.val ≤ 2)) = false
  refine okPost_loop_decr_nat measure inv
    (fun b => b = sliceHasStdioSlotSpec fds.val)
    (postfork.fd_ops.slice_has_stdio_slot_loop.body fds fds.len) 0#usize ?_
    ⟨Nat.zero_le _, rfl⟩
  · intro i ⟨hiLe, hNone⟩
    unfold postfork.fd_ops.slice_has_stdio_slot_loop.body
    by_cases hlt : i < fds.len
    · have hiLen : i.val < fds.val.length := hlt
      simp only [hlt, ↓reduceIte]
      rw [slice_index_usize_ok fds i hiLen, bind_ok]
      have hiMax : i.val < Usize.max := Nat.lt_of_lt_of_le hiLen fds.length_ineq
      by_cases h0 : 0#i32 ≤ fds.val[i.val]
      · by_cases h2 : fds.val[i.val] ≤ 2#i32
        · simp only [h0, h2, ↓reduceIte]
          refine ⟨ControlFlow.done true, rfl, ?_⟩
          have h0' : 0 ≤ fds.val[i.val].val := h0
          have h2' : fds.val[i.val].val ≤ 2 := h2
          have hmem : fds.val[i.val] ∈ fds.val := List.getElem_mem hiLen
          have hany : fds.val.any (fun x => decide (0 ≤ x.val ∧ x.val ≤ 2)) = true :=
            List.any_eq_true.mpr ⟨fds.val[i.val], hmem, decide_eq_true ⟨h0', h2'⟩⟩
          simpa [sliceHasStdioSlotSpec] using hany.symm
        · simp only [h0, h2, ↓reduceIte]
          obtain ⟨i1, hi1Eq, hi1Val⟩ := usize_add_one_ok_of_lt i hiMax
          rw [hi1Eq, bind_ok]
          refine ⟨ControlFlow.cont i1, rfl, ⟨?_, ?_⟩, ?_⟩
          · omega
          · rw [hi1Val, list_any_take_succ _ _ _ hiLen, hNone, Bool.false_or]
            have hnot2 : ¬ (fds.val[i.val].val ≤ 2) := h2
            exact decide_eq_false (fun h => hnot2 h.2)
          · simp only [measure]; omega
      · simp only [h0, ↓reduceIte]
        obtain ⟨i1, hi1Eq, hi1Val⟩ := usize_add_one_ok_of_lt i hiMax
        rw [hi1Eq, bind_ok]
        refine ⟨ControlFlow.cont i1, rfl, ⟨?_, ?_⟩, ?_⟩
        · omega
        · rw [hi1Val, list_any_take_succ _ _ _ hiLen, hNone, Bool.false_or]
          have hnot0 : ¬ (0 ≤ fds.val[i.val].val) := h0
          exact decide_eq_false (fun h => hnot0 h.1)
        · simp only [measure]; omega
    · have hiEq : i.val = fds.val.length := by
        change ¬ i.val < fds.val.length at hlt
        omega
      simp only [hlt, ↓reduceIte]
      refine ⟨ControlFlow.done false, rfl, ?_⟩
      rw [hiEq, List.take_length] at hNone
      simpa [sliceHasStdioSlotSpec] using hNone.symm

/-- `postfork.fd_ops.slices_overlap_nonneg` computes `Model.slicesOverlapNonnegSpec`. -/
theorem slices_overlap_nonneg_spec (lhs rhs : Slice I32) :
    OkPost (postfork.fd_ops.slices_overlap_nonneg lhs rhs)
      (fun b => b = slicesOverlapNonnegSpec lhs.val rhs.val) := by
  unfold postfork.fd_ops.slices_overlap_nonneg
  let measure : Usize → Nat := fun i => lhs.val.length - i.val
  let inv : Usize → Prop := fun i =>
    i.val ≤ lhs.val.length ∧
    (lhs.val.take i.val).any
      (fun x => decide (0 ≤ x.val) && sliceContainsNonnegSpec rhs.val x.val) = false
  refine okPost_loop_decr_nat measure inv
    (fun b => b = slicesOverlapNonnegSpec lhs.val rhs.val)
    (postfork.fd_ops.slices_overlap_nonneg_loop.body lhs rhs lhs.len) 0#usize ?_
    ⟨Nat.zero_le _, rfl⟩
  · intro i ⟨hiLe, hNone⟩
    unfold postfork.fd_ops.slices_overlap_nonneg_loop.body
    by_cases hlt : i < lhs.len
    · have hiLen : i.val < lhs.val.length := hlt
      simp only [hlt, ↓reduceIte]
      rw [slice_index_usize_ok lhs i hiLen, bind_ok]
      have hiMax : i.val < Usize.max := Nat.lt_of_lt_of_le hiLen lhs.length_ineq
      by_cases h0 : 0#i32 ≤ lhs.val[i.val]
      · simp only [h0, ↓reduceIte]
        obtain ⟨c, hcEq, hcVal⟩ := slice_contains_nonneg_spec rhs lhs.val[i.val]
        rw [hcEq, bind_ok]
        subst hcVal
        by_cases hmem : sliceContainsNonnegSpec rhs.val lhs.val[i.val].val = true
        · simp only [hmem, ↓reduceIte]
          refine ⟨ControlFlow.done true, rfl, ?_⟩
          have h0' : 0 ≤ lhs.val[i.val].val := h0
          have hElem : lhs.val[i.val] ∈ lhs.val := List.getElem_mem hiLen
          have hany : lhs.val.any
              (fun x => decide (0 ≤ x.val) && sliceContainsNonnegSpec rhs.val x.val) = true :=
            List.any_eq_true.mpr ⟨lhs.val[i.val], hElem, by simp [h0', hmem]⟩
          simpa [slicesOverlapNonnegSpec] using hany.symm
        · have hfalse : sliceContainsNonnegSpec rhs.val lhs.val[i.val].val = false :=
            Bool.eq_false_iff.mpr hmem
          simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨i1, hi1Eq, hi1Val⟩ := usize_add_one_ok_of_lt i hiMax
          rw [hi1Eq, bind_ok]
          refine ⟨ControlFlow.cont i1, rfl, ⟨?_, ?_⟩, ?_⟩
          · omega
          · rw [hi1Val, list_any_take_succ _ _ _ hiLen, hNone, Bool.false_or, hfalse,
              Bool.and_false]
          · simp only [measure]; omega
      · simp only [h0, ↓reduceIte]
        obtain ⟨i1, hi1Eq, hi1Val⟩ := usize_add_one_ok_of_lt i hiMax
        rw [hi1Eq, bind_ok]
        refine ⟨ControlFlow.cont i1, rfl, ⟨?_, ?_⟩, ?_⟩
        · omega
        · rw [hi1Val, list_any_take_succ _ _ _ hiLen, hNone, Bool.false_or]
          have hnot0 : ¬ (0 ≤ lhs.val[i.val].val) := h0
          rw [decide_eq_false hnot0, Bool.false_and]
        · simp only [measure]; omega
    · have hiEq : i.val = lhs.val.length := by
        change ¬ i.val < lhs.val.length at hlt
        omega
      simp only [hlt, ↓reduceIte]
      refine ⟨ControlFlow.done false, rfl, ?_⟩
      rw [hiEq, List.take_length] at hNone
      simpa [slicesOverlapNonnegSpec] using hNone.symm

/-! ## Syscall Totality Helpers -/

private theorem sys_close_total (s : ChildState) (fd : I32) :
    OkPost (sys.close s fd) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_close_running s hrun fd
    exact ⟨(r, s'), h, trivial⟩
  · have h := sys_close_not_running s hrun fd
    exact ⟨(.Ok (), s), h, trivial⟩

private theorem sys_dup2_total (s : ChildState) (oldfd newfd : I32) :
    OkPost (sys.dup2 s oldfd newfd) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_dup2_running s hrun oldfd newfd
    exact ⟨(r, s'), h, trivial⟩
  · unfold sys.dup2 LeanSwe.PostFork.Aeneas.Internal.Sys.dup2
    rw [runUnitSyscall_not_running s hrun]
    exact okPost_ok _ _ trivial

private theorem sys_fcntl_getfd_total (s : ChildState) (fd : I32) :
    OkPost (sys.fcntl_getfd s fd) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_fcntl_getfd_running s hrun fd
    exact ⟨(r, s'), h, trivial⟩
  · unfold sys.fcntl_getfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_getfd
    cases s.getFd fd.val <;>
      (dsimp only; rw [runI32Syscall_not_running s hrun]; exact ⟨_, rfl, trivial⟩)

private theorem sys_fcntl_setfd_total (s : ChildState) (fd flags : I32) :
    OkPost (sys.fcntl_setfd s fd flags) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_fcntl_setfd_running s hrun fd flags
    exact ⟨(r, s'), h, trivial⟩
  · unfold sys.fcntl_setfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_setfd
    rw [runUnitSyscall_not_running s hrun]
    exact okPost_ok _ _ trivial

private theorem sys_fcntl_dupfd_cloexec_total (s : ChildState) (fd minFd : I32) :
    OkPost (sys.fcntl_dupfd_cloexec s fd minFd) (fun _ => True) := by
  by_cases hrun : s.status = .running
  · obtain ⟨r, s', h, _⟩ := sys_fcntl_dupfd_cloexec_running s hrun fd minFd
    exact ⟨(r, s'), h, trivial⟩
  · unfold sys.fcntl_dupfd_cloexec LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_dupfd_cloexec
    cases s.getFd fd.val with
    | none =>
      dsimp only
      rw [runI32Syscall_not_running s hrun]
      exact ⟨_, rfl, trivial⟩
    | some e =>
      dsimp only
      by_cases hlim : (decide (minFd.val < 0) || decide (minFd.val ≥ s.fdLimit)) = true
      · simp only [hlim, ↓reduceIte]
        rw [runI32Syscall_not_running s hrun]
        exact ⟨_, rfl, trivial⟩
      · simp only [hlim, Bool.false_eq_true, ↓reduceIte]
        cases findLowestFreeFd s minFd.val <;>
          (dsimp only; rw [runI32Syscall_not_running s hrun]; exact ⟨_, rfl, trivial⟩)

/-! ## `clear_cloexec`, `set_cloexec`, and `relocate_rep_above2` -/

/-- `postfork.fd_ops.clear_cloexec` always terminates cleanly on any `ChildState`. -/
theorem clear_cloexec_total (s : ChildState) (fd : I32) :
    OkPost (postfork.fd_ops.clear_cloexec s fd) (fun _ => True) := by
  unfold postfork.fd_ops.clear_cloexec
  obtain ⟨⟨r1, s1⟩, h1, _⟩ := sys_fcntl_getfd_total s fd
  rw [h1, bind_ok]
  cases r1 with
  | Err e => exact okPost_ok _ _ trivial
  | Ok flags =>
    simp only [lift, bind_ok]
    exact sys_fcntl_setfd_total s1 fd _

/-- `postfork.fd_ops.set_cloexec` always terminates cleanly on any `ChildState`. -/
theorem set_cloexec_total (s : ChildState) (fd : I32) :
    OkPost (postfork.fd_ops.set_cloexec s fd) (fun _ => True) := by
  unfold postfork.fd_ops.set_cloexec
  obtain ⟨⟨r1, s1⟩, h1, _⟩ := sys_fcntl_getfd_total s fd
  rw [h1, bind_ok]
  cases r1 with
  | Err e => exact okPost_ok _ _ trivial
  | Ok flags =>
    simp only [lift, bind_ok]
    exact sys_fcntl_setfd_total s1 fd _

/-- `postfork.fd_ops.relocate_rep_above2` always terminates cleanly on any `ChildState`. -/
theorem relocate_rep_above2_total (s : ChildState) (fd : I32) :
    OkPost (postfork.fd_ops.relocate_rep_above2 s fd) (fun _ => True) := by
  unfold postfork.fd_ops.relocate_rep_above2
  by_cases hneg : fd < 0#i32
  · simp [hneg]
    exact okPost_ok _ _ trivial
  · simp only [hneg, ↓reduceIte]
    by_cases hle : fd ≤ 2#i32
    · simp only [hle, ↓reduceIte]
      obtain ⟨⟨r1, s1⟩, h1, _⟩ := sys_fcntl_dupfd_cloexec_total s fd 3#i32
      rw [h1, bind_ok]
      cases r1 with
      | Err e => exact okPost_ok _ _ trivial
      | Ok dst =>
        obtain ⟨⟨r2, s2⟩, h2, _⟩ := sys_close_total s1 fd
        change OkPost (do let (_, s2) ← sys.close s1 fd; Result.ok (core.result.Result.Ok dst, s2)) _
        rw [h2, bind_ok]
        exact okPost_ok _ _ trivial
    · simp only [hle, ↓reduceIte]
      obtain ⟨⟨r1, s1⟩, h1, _⟩ := set_cloexec_total s fd
      rw [h1, bind_ok]
      cases r1 <;> exact okPost_ok _ _ trivial

private theorem sys_fcntl_getfd_run_spec (s : ChildState) (hRun : s.status = .running)
    (hOr : s.oracle = []) (fd : I32) :
    ∃ r1 s1, sys.fcntl_getfd s fd = Result.ok (r1, s1) ∧
      SameChildConfig s1 s ∧ s1.pgid = s.pgid ∧ s1.cwd = s.cwd ∧
      s1.sig = s.sig ∧ s1.descs = s.descs ∧ s1.writeLog = s.writeLog ∧
      s1.fds = s.fds ∧
      match s.getFd fd.val with
      | none => r1 = .Err EBADF
      | some e => r1 = .Ok (fdFlagsWord e) := by
  have hf := currentFault_oracle_nil s hOr
  unfold sys.fcntl_getfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_getfd runI32Syscall
  rw [hRun, hf]
  cases hget : s.getFd fd.val with
  | none =>
    refine ⟨.Err EBADF, _, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, hRun.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some e =>
    refine ⟨.Ok (fdFlagsWord e), _, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Fault-free specification of `postfork.fd_ops.clear_cloexec`. -/
theorem clear_cloexec_spec (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (fd : I32) :
    OkPost (postfork.fd_ops.clear_cloexec s fd)
      (fun p => CloexecTogglePost false s fd p.1 p.2 ∧ SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog) := by
  unfold postfork.fd_ops.clear_cloexec
  obtain ⟨r1, s1, h1, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hsfds, hfd1⟩ :=
    sys_fcntl_getfd_run_spec s hRun hOr fd
  rw [h1, bind_ok]
  cases hget : s.getFd fd.val with
  | none =>
    simp only [hget] at hfd1
    subst hfd1
    refine okPost_ok _ _ ⟨?_, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1⟩
    simp [CloexecTogglePost, hget, hsfds]
  | some e =>
    simp only [hget] at hfd1
    subst hfd1
    simp only [lift, bind_ok]
    have hs1Run : s1.status = .running := hcfg1.status.symm ▸ hRun
    have hs1Or : s1.oracle = [] := hcfg1.oracle.symm ▸ hOr
    have hs1F := currentFault_oracle_nil s1 hs1Or
    have hs1Get : s1.getFd fd.val = some e := by
      unfold ChildState.getFd; rw [hsfds]; exact hget
    obtain ⟨r2, s2, h2, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, _, _, hok2, hfd2⟩ :=
      sys_fcntl_setfd_running s1 hs1Run fd (fdFlagsWord e &&& ~~~postfork.fd_ops.FD_CLOEXEC)
    change OkPost (sys.fcntl_setfd s1 fd (fdFlagsWord e &&& ~~~postfork.fd_ops.FD_CLOEXEC)) _
    rw [h2]
    rw [hs1Get, hs1F] at hfd2
    subst hfd2
    refine okPost_ok _ _ ⟨?_, hcfg2.trans hcfg1, hpg2.trans hpg1, hcw2.trans hcw1,
      hsi2.trans hsi1, hde2.trans hde1, hwl2.trans hwl1⟩
    have hs2Fds := hok2 rfl
    rw [hs1Get] at hs2Fds
    simp only [CloexecTogglePost, hget, true_and]
    dsimp only at hs2Fds
    refine ⟨?_, ?_⟩
    · rw [getFd_eq_of_fds_eq hs2Fds, getFd_putSlot_self, postfork.fd_ops.FD_CLOEXEC,
        hcfg1.kernelMasksSetfd, updateFdFlags_clear_cloexec]
    · intro k hne
      simp [getFd_eq_of_fds_eq hs2Fds, getFd_putSlot_ne, hne, getFd_eq_of_fds_eq hsfds]

/-- Fault-free specification of `postfork.fd_ops.set_cloexec`. -/
theorem set_cloexec_spec (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (fd : I32) :
    OkPost (postfork.fd_ops.set_cloexec s fd)
      (fun p => CloexecTogglePost true s fd p.1 p.2 ∧ SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog) := by
  unfold postfork.fd_ops.set_cloexec
  obtain ⟨r1, s1, h1, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hsfds, hfd1⟩ :=
    sys_fcntl_getfd_run_spec s hRun hOr fd
  rw [h1, bind_ok]
  cases hget : s.getFd fd.val with
  | none =>
    simp only [hget] at hfd1
    subst hfd1
    refine okPost_ok _ _ ⟨?_, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1⟩
    simp [CloexecTogglePost, hget, hsfds]
  | some e =>
    simp only [hget] at hfd1
    subst hfd1
    simp only [lift, bind_ok]
    have hs1Run : s1.status = .running := hcfg1.status.symm ▸ hRun
    have hs1Or : s1.oracle = [] := hcfg1.oracle.symm ▸ hOr
    have hs1F := currentFault_oracle_nil s1 hs1Or
    have hs1Get : s1.getFd fd.val = some e := by
      unfold ChildState.getFd; rw [hsfds]; exact hget
    obtain ⟨r2, s2, h2, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, _, _, hok2, hfd2⟩ :=
      sys_fcntl_setfd_running s1 hs1Run fd (fdFlagsWord e ||| postfork.fd_ops.FD_CLOEXEC)
    change OkPost (sys.fcntl_setfd s1 fd (fdFlagsWord e ||| postfork.fd_ops.FD_CLOEXEC)) _
    rw [h2]
    rw [hs1Get, hs1F] at hfd2
    subst hfd2
    refine okPost_ok _ _ ⟨?_, hcfg2.trans hcfg1, hpg2.trans hpg1, hcw2.trans hcw1,
      hsi2.trans hsi1, hde2.trans hde1, hwl2.trans hwl1⟩
    have hs2Fds := hok2 rfl
    rw [hs1Get] at hs2Fds
    simp only [CloexecTogglePost, hget, true_and]
    dsimp only at hs2Fds
    refine ⟨?_, ?_⟩
    · rw [getFd_eq_of_fds_eq hs2Fds, getFd_putSlot_self, postfork.fd_ops.FD_CLOEXEC,
        hcfg1.kernelMasksSetfd, updateFdFlags_set_cloexec]
    · intro k hne
      simp [getFd_eq_of_fds_eq hs2Fds, getFd_putSlot_ne, hne, getFd_eq_of_fds_eq hsfds]

/-- Fault-free specification of `postfork.fd_ops.relocate_rep_above2`. -/
theorem relocate_rep_above2_spec (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (fd : I32) :
    OkPost (postfork.fd_ops.relocate_rep_above2 s fd)
      (fun p => RelocateRepPost s fd p.1 p.2 ∧ SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog) := by
  unfold postfork.fd_ops.relocate_rep_above2
  by_cases hneg : fd < 0#i32
  · simp only [hneg, ↓reduceIte]
    refine okPost_ok _ _ ⟨?_, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl⟩
    simp [RelocateRepPost, hneg, postfork.fd_ops.EBADF, EBADF]
  · have hnonneg : 0 ≤ fd.val := by change ¬ fd.val < 0 at hneg; omega
    simp only [hneg, ↓reduceIte]
    by_cases hle : fd ≤ 2#i32
    · have hleInt : fd.val ≤ 2 := hle
      simp only [hle, ↓reduceIte]
      obtain ⟨r1, s1, h1, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, _, herr1, hok1, hfd1⟩ :=
        sys_fcntl_dupfd_cloexec_running s hRun fd 3#i32
      rw [h1, bind_ok]
      have hfd1' := hfd1 hOr
      have h3 : (3#i32).val = 3 := rfl
      cases hget : s.getFd fd.val with
      | none =>
        rw [hget] at hfd1'
        subst hfd1'
        refine okPost_ok _ _ ⟨?_, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1⟩
        have hsfds := herr1 _ rfl
        simp [RelocateRepPost, hneg, hsfds, hget]
      | some e =>
        cases hlow : findLowestFreeFd s 3 with
        | none =>
          rw [hget, h3, hlow] at hfd1'
          split_ifs at hfd1' with hlim
          · subst hfd1'
            refine okPost_ok _ _ ⟨?_, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1⟩
            have hsfds := herr1 _ rfl
            have hlim' : s.fdLimit ≤ 3 := by simp at hlim; omega
            simp [RelocateRepPost, hneg, hleInt, hsfds, hget, hlim']
          · subst hfd1'
            refine okPost_ok _ _ ⟨?_, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1⟩
            have hsfds := herr1 _ rfl
            have hnotlim : ¬ s.fdLimit ≤ 3 := by simp at hlim; omega
            simp [RelocateRepPost, hneg, hleInt, hlow, hsfds, hget, hnotlim]
        | some dst =>
          rw [hget, h3, hlow] at hfd1'
          split_ifs at hfd1' with hlim
          · have hlowSpec := findLowestFreeFd_spec s 3 dst hlow
            simp at hlim
            omega
          · rcases hfd1' with ⟨dstI, hdstEq, hdstVal⟩
            subst hdstEq
            have hs1Run : s1.status = .running := hcfg1.status.symm ▸ hRun
            have hs1Or : s1.oracle = [] := hcfg1.oracle.symm ▸ hOr
            obtain ⟨r2, s2, h2, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, _, hfds2, _⟩ :=
              sys_close_running s1 hs1Run fd
            have hfds2' : s2.fds = (s1.closeSlot fd.val).fds := by
              have htmp := hfds2
              rw [currentFault_oracle_nil s1 hs1Or] at htmp
              exact htmp
            change OkPost (do let (_, s2) ← sys.close s1 fd; Result.ok (core.result.Result.Ok dstI, s2)) _
            rw [h2, bind_ok]
            refine okPost_ok _ _ ⟨?_, hcfg2.trans hcfg1, hpg2.trans hpg1, hcw2.trans hcw1,
              hsi2.trans hsi1, hde2.trans hde1, hwl2.trans hwl1⟩
            have hlowSpec := findLowestFreeFd_spec s 3 dst hlow
            have hs1Fds := hok1 dstI rfl
            rcases hs1Fds with ⟨e', dst', hget', hlow', hdstVal', _, _, _, hs1FdsEq⟩
            rw [hget] at hget'; cases hget'
            rw [h3, hlow] at hlow'; cases hlow'
            simp only [RelocateRepPost, hneg, hget, hleInt, ↓reduceIte, hlow]
            have hnotlim : ¬ s.fdLimit ≤ 3 := by simp at hlim; omega
            simp only [hnotlim, ↓reduceIte]
            have hdstNe : dst ≠ fd.val := by omega
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · congr 1
              exact IScalar.eq_of_val_eq (by
                rw [hdstVal']
                unfold mkI32
                simp only [IScalar.val, IScalarTy.numBits]
                erw [BitVec.toInt_ofInt, Int.bmod_eq_of_le] <;> omega)
            · omega
            · rw [getFd_eq_of_fds_eq hfds2', getFd_closeSlot_self]
            · rw [getFd_eq_of_fds_eq hfds2', getFd_closeSlot_ne (s := s1) (fd := fd.val) (k := dst) hdstNe,
                getFd_eq_of_fds_eq hs1FdsEq, getFd_putSlot_self]
            · intro k hne1 hne2
              simp [getFd_eq_of_fds_eq hfds2', getFd_closeSlot_ne, getFd_eq_of_fds_eq hs1FdsEq,
                getFd_putSlot_ne, hne1, hne2]
    · have hgt : 2 < fd.val := by change ¬ fd.val ≤ 2 at hle; omega
      simp only [hle, ↓reduceIte]
      obtain ⟨⟨r1, s1⟩, h1, hspec, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1⟩ :=
        set_cloexec_spec s hRun hOr fd
      rw [h1, bind_ok]
      simp only [CloexecTogglePost] at hspec
      cases r1 with
      | Err e =>
        refine okPost_ok _ _ ⟨?_, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1⟩
        cases hget : s.getFd fd.val with
        | none =>
          rw [hget] at hspec
          rcases hspec with ⟨heEq, hs1Fds⟩
          cases heEq
          simp [RelocateRepPost, hneg, hget, hs1Fds]
        | some e' =>
          rw [hget] at hspec
          exact False.elim (by cases hspec.1)
      | Ok u =>
        refine okPost_ok _ _ ⟨?_, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1⟩
        cases hget : s.getFd fd.val with
        | none =>
          rw [hget] at hspec
          exact False.elim (by cases hspec.1)
        | some e' =>
          rw [hget] at hspec
          have hnotle : ¬ fd.val ≤ 2 := by omega
          simpa [RelocateRepPost, hneg, hget, hnotle] using hspec.2

/-- Zero-hypothesis `AllPass` proof for `test_postfork_cloexecAndRelocate_preserveFlagsAndBounds`. -/
theorem test_postfork_cloexecAndRelocate_preserveFlagsAndBounds_allPass :
    Core.AllPass (test_postfork_cloexecAndRelocate_preserveFlagsAndBounds rustAeneasApi) := by
  intro s fd
  dsimp [rustAeneasApi, Core.AllPassRun, Core.NondetTest.assert, Bind.bind, Pure.pure]
  refine ⟨clear_cloexec_total s fd, set_cloexec_total s fd, relocate_rep_above2_total s fd, ?_⟩
  rintro ⟨hRun, hOr⟩
  refine ⟨?_, ?_, ?_, trivial⟩
  · exact okPost_mono (clear_cloexec_spec s hRun hOr fd) (fun _ hp => hp.1)
  · exact okPost_mono (set_cloexec_spec s hRun hOr fd) (fun _ hp => hp.1)
  · exact okPost_mono (relocate_rep_above2_spec s hRun hOr fd) (fun _ hp => hp.1)

/-- Zero-hypothesis `CanReach` proof for `test_postfork_cloexecAndRelocate_preserveFlagsAndBounds`. -/
theorem test_postfork_cloexecAndRelocate_preserveFlagsAndBounds_canReach :
    Core.CanReach (test_postfork_cloexecAndRelocate_preserveFlagsAndBounds rustAeneasApi) := by
  let s0 : ChildState :=
    { pid := 1, sid := 1, pgid := 1, status := .running, fds := [], descs := [],
      fdLimit := 64, kernelMasksSetfd := false, closeRangeSupported := false,
      closeRangeErrno := 0#i32, procSelfFdAvailable := false, procOpenErrno := 0#i32,
      cwd := [], sig := [], writeLog := [], trace := [], oracle := [] }
  refine ⟨s0, 0#i32, ?_⟩
  dsimp [rustAeneasApi, Core.CanReachRun, Core.NondetTest.assert, Bind.bind, Pure.pure]
  refine ⟨clear_cloexec_total s0 0#i32, set_cloexec_total s0 0#i32,
    relocate_rep_above2_total s0 0#i32, ⟨rfl, rfl⟩, ?_, ?_, ?_, trivial⟩
  · exact okPost_mono (clear_cloexec_spec s0 rfl rfl 0#i32) (fun _ hp => hp.1)
  · exact okPost_mono (set_cloexec_spec s0 rfl rfl 0#i32) (fun _ hp => hp.1)
  · exact okPost_mono (relocate_rep_above2_spec s0 rfl rfl 0#i32) (fun _ hp => hp.1)

private theorem slice_idx_succ {α : Type} (s : Slice α) {j : Usize} (hlt : j < s.len) :
    ∃ hjlt : j.val < s.val.length,
      s.index_usize j = .ok s.val[j.val] ∧
      ∃ z : Usize, j + 1#usize = Result.ok z ∧ z.val = j.val + 1 := by
  have hjlt : j.val < s.val.length := by simpa [Slice.len] using hlt
  have hlen : s.val.length ≤ Usize.max := s.property
  have h1 : (1#usize : Usize).val = 1 := rfl
  have hmax : j.val + 1 ≤ Usize.max := by omega
  have hidx : s.index_usize j = .ok s.val[j.val] := by
    simp [Slice.index_usize, hjlt]
  have hlt2 : j.val + 1 < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
  have hchk : UScalar.check_bounds .Usize (j.val + 1) = true := decide_eq_true hlt2
  have hadd : j + 1#usize = UScalar.tryMk .Usize (j.val + 1) := by
    change UScalar.tryMk .Usize (j.val + (1#usize : Usize).val) = _
    rw [h1]
  rw [hadd]
  unfold UScalar.tryMk UScalar.tryMkOpt
  simp only [hchk, ↓reduceDIte, Result.ofOption]
  exact ⟨hjlt, hidx, UScalar.ofNatCore (j.val + 1) hlt2, rfl, rfl⟩

private theorem probe_open_slice_loop_total (fds : Slice I32) (i : Usize)
    (hi : i.val ≤ fds.val.length) (s : ChildState) :
    OkPost (postfork.fd_ops.probe_open_slice_loop s fds i fds.len) (fun _ => True) := by
  unfold postfork.fd_ops.probe_open_slice_loop
  refine okPost_loop_decr_nat
    (fun (p : ChildState × Usize) => fds.val.length - p.2.val)
    (fun p => p.2.val ≤ fds.val.length)
    (fun _ => True)
    (fun p => match p with | (s1, i1) => postfork.fd_ops.probe_open_slice_loop.body fds fds.len s1 i1)
    (s, i) ?_ hi
  intro ⟨s1, j⟩ hj
  unfold postfork.fd_ops.probe_open_slice_loop.body
  by_cases hlt : j < fds.len
  · rcases slice_idx_succ fds hlt with ⟨hjlt, hidx, z, hinc, hval⟩
    simp only [hlt, ↓reduceIte]
    rw [hidx, bind_ok]
    by_cases hnonneg : fds.val[j.val] ≥ 0#i32
    · simp only [hnonneg, ↓reduceIte]
      refine okPost_bind (sys_fcntl_getfd_total s1 fds.val[j.val]) ?_
      intro ⟨r, s2⟩ _
      cases r with
      | Ok _ =>
        change OkPost (do
          let i1 ← j + 1#usize
          Result.ok (ControlFlow.cont (s2, i1))) _
        rw [hinc, bind_ok]
        exact okPost_ok _ _ ⟨by dsimp; rw [hval]; exact hjlt, by dsimp; rw [hval]; omega⟩
      | Err e =>
        exact okPost_ok _ _ trivial
    · simp only [hnonneg, ↓reduceIte]
      rw [hinc, bind_ok]
      exact okPost_ok _ _ ⟨by dsimp; rw [hval]; exact hjlt, by dsimp; rw [hval]; omega⟩
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok _ _ trivial

/-- `probe_open_slice` always terminates cleanly on any child state. -/
theorem probe_open_slice_total (s : ChildState) (fds : Slice I32) :
    OkPost (postfork.fd_ops.probe_open_slice s fds) (fun _ => True) := by
  unfold postfork.fd_ops.probe_open_slice
  refine okPost_bind (probe_open_slice_loop_total fds 0#usize (Nat.zero_le _) s) ?_
  intro ⟨s1, err, failed⟩ _
  by_cases h : failed = true <;> simp [h, okPost_ok]

private theorem probe_open_slice_loop_spec (s0 : ChildState) (hRun0 : s0.status = .running)
    (hOr0 : s0.oracle = []) (fds : Slice I32) :
    OkPost (postfork.fd_ops.probe_open_slice_loop s0 fds 0#usize fds.len)
      (fun (s1, err, failed) =>
        SameChildConfig s1 s0 ∧ s1.fds = s0.fds ∧
          s1.pgid = s0.pgid ∧ s1.cwd = s0.cwd ∧ s1.sig = s0.sig ∧
          s1.descs = s0.descs ∧ s1.writeLog = s0.writeLog ∧
          (failed = false →
            ∀ j (hj : j < fds.val.length), 0 ≤ fds.val[j].val →
              s0.isOpen fds.val[j].val = true) ∧
          (failed = true →
            err = EBADF ∧
              ∃ j, ∃ hj : j < fds.val.length, 0 ≤ fds.val[j].val ∧
                s0.isOpen fds.val[j].val = false)) := by
  unfold postfork.fd_ops.probe_open_slice_loop
  have hz0 : (0#usize : Usize).val = 0 := rfl
  have hInv0 :
      SameChildConfig s0 s0 ∧ s0.fds = s0.fds ∧
        s0.pgid = s0.pgid ∧ s0.cwd = s0.cwd ∧ s0.sig = s0.sig ∧
        s0.descs = s0.descs ∧ s0.writeLog = s0.writeLog ∧
        (0#usize : Usize).val ≤ fds.val.length ∧
        (∀ j (hj : j < fds.val.length), j < (0#usize : Usize).val → 0 ≤ fds.val[j].val →
          s0.isOpen fds.val[j].val = true) :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, fun _ _ hlt _ => absurd hlt (by omega)⟩
  refine okPost_loop_decr_nat
    (fun (p : ChildState × Usize) => fds.val.length - p.2.val)
    (fun p =>
      SameChildConfig p.1 s0 ∧ p.1.fds = s0.fds ∧
        p.1.pgid = s0.pgid ∧ p.1.cwd = s0.cwd ∧ p.1.sig = s0.sig ∧
        p.1.descs = s0.descs ∧ p.1.writeLog = s0.writeLog ∧
        p.2.val ≤ fds.val.length ∧
        (∀ j (hj : j < fds.val.length), j < p.2.val → 0 ≤ fds.val[j].val →
          s0.isOpen fds.val[j].val = true))
    (fun (s1, err, failed) =>
      SameChildConfig s1 s0 ∧ s1.fds = s0.fds ∧
        s1.pgid = s0.pgid ∧ s1.cwd = s0.cwd ∧ s1.sig = s0.sig ∧
        s1.descs = s0.descs ∧ s1.writeLog = s0.writeLog ∧
        (failed = false →
          ∀ j (hj : j < fds.val.length), 0 ≤ fds.val[j].val →
            s0.isOpen fds.val[j].val = true) ∧
        (failed = true →
          err = EBADF ∧
            ∃ j, ∃ hj : j < fds.val.length, 0 ≤ fds.val[j].val ∧
              s0.isOpen fds.val[j].val = false))
    (fun p => match p with | (s1, i1) => postfork.fd_ops.probe_open_slice_loop.body fds fds.len s1 i1)
    (s0, 0#usize) ?_ hInv0
  intro ⟨s1, j⟩ ⟨hcfg1, hfds1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hjle, hprev⟩
  unfold postfork.fd_ops.probe_open_slice_loop.body
  by_cases hlt : j < fds.len
  · rcases slice_idx_succ fds hlt with ⟨hjlt, hidx, z, hinc, hval⟩
    simp only [hlt, ↓reduceIte]
    rw [hidx, bind_ok]
    by_cases hnonneg : fds.val[j.val] ≥ 0#i32
    · have hj_nonneg : 0 ≤ fds.val[j.val].val := by
        change (0#i32 : I32).val ≤ fds.val[j.val].val at hnonneg
        exact hnonneg
      simp only [hnonneg, ↓reduceIte]
      have hRun1 : s1.status = .running := hcfg1.status.trans hRun0
      have hOr1 : s1.oracle = [] := hcfg1.oracle.trans hOr0
      rcases sys_fcntl_getfd_run_spec s1 hRun1 hOr1 fds.val[j.val] with
        ⟨r, s2, hcall, hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hfds2, hres2⟩
      rw [hcall, bind_ok]
      have hfds20 : s2.fds = s0.fds := hfds2.trans hfds1
      have hopen_eq : s1.isOpen fds.val[j.val].val = s0.isOpen fds.val[j.val].val := by
        simp [ChildState.isOpen, getFd_eq_of_fds_eq hfds1]
      cases hget1 : s1.getFd fds.val[j.val].val with
      | none =>
        have hopen1 : s1.isOpen fds.val[j.val].val = false := by
          simp [ChildState.isOpen, hget1]
        have hopen0 : s0.isOpen fds.val[j.val].val = false := hopen_eq.symm.trans hopen1
        rw [hget1] at hres2
        subst hres2
        refine okPost_ok _ _ ⟨hcfg2.trans hcfg1, hfds20, hpg2.trans hpg1, hcwd2.trans hcwd1,
          hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1,
          (fun h => by contradiction), fun _ => ⟨rfl, j.val, hjlt, hj_nonneg, hopen0⟩⟩
      | some e1 =>
        have hopen1 : s1.isOpen fds.val[j.val].val = true := by
          simp [ChildState.isOpen, hget1]
        have hopen0 : s0.isOpen fds.val[j.val].val = true := hopen_eq.symm.trans hopen1
        rw [hget1] at hres2
        subst hres2
        change OkPost (do
          let i1 ← j + 1#usize
          Result.ok (ControlFlow.cont (s2, i1))) _
        rw [hinc, bind_ok]
        refine okPost_ok _ _ ⟨⟨hcfg2.trans hcfg1, hfds20, hpg2.trans hpg1, hcwd2.trans hcwd1,
          hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1, ?_, ?_⟩, ?_⟩
        · rw [hval]; exact hjlt
        · intro k hk hkj hk0
          have hkj' : k < j.val + 1 := by dsimp only at hkj; rw [hval] at hkj; exact hkj
          by_cases hkeq : k = j.val
          · subst hkeq; exact hopen0
          · have hltj : k < j.val := by omega
            exact hprev k hk hltj hk0
        · dsimp; rw [hval]; omega
    · simp only [hnonneg, ↓reduceIte]
      rw [hinc, bind_ok]
      refine okPost_ok _ _ ⟨⟨hcfg1, hfds1, hpg1, hcwd1, hsig1, hdescs1, hwl1, ?_, ?_⟩, ?_⟩
      · rw [hval]; exact hjlt
      · intro k hk hkj hk0
        have hkj' : k < j.val + 1 := by dsimp only at hkj; rw [hval] at hkj; exact hkj
        by_cases hkeq : k = j.val
        · subst hkeq
          exfalso
          apply hnonneg
          change (0#i32 : I32).val ≤ fds.val[j.val].val
          exact hk0
        · have hltj : k < j.val := by omega
          exact hprev k hk hltj hk0
      · dsimp; rw [hval]; omega
  · simp only [hlt, ↓reduceIte]
    have hj_ge : fds.val.length ≤ j.val := by
      have hlen : ¬ j.val < fds.val.length := by simpa [Slice.len] using hlt
      omega
    exact okPost_ok _ _ ⟨hcfg1, hfds1, hpg1, hcwd1, hsig1, hdescs1, hwl1,
      fun _ k hk hk0 => hprev k hk (Nat.lt_of_lt_of_le hk hj_ge) hk0,
      fun h => by contradiction⟩

/-- Specification of `probe_open_slice` on a running, fault-free child state: preserves all
non-trace state and succeeds iff every non-negative entry in `fds` is currently open. -/
theorem probe_open_slice_spec (s : ChildState) (hRun : s.status = .running) (hOr : s.oracle = [])
    (fds : Slice I32) :
    OkPost (postfork.fd_ops.probe_open_slice s fds) fun p =>
      SameChildConfig p.2 s ∧ p.2.fds = s.fds ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        match p.1 with
        | .Ok () => ∀ fd ∈ fds.val, 0 ≤ fd.val → s.isOpen fd.val = true
        | .Err e => e = EBADF ∧ ∃ fd ∈ fds.val, 0 ≤ fd.val ∧ s.isOpen fd.val = false := by
  unfold postfork.fd_ops.probe_open_slice
  refine okPost_bind (probe_open_slice_loop_spec s hRun hOr fds) ?_
  intro ⟨s1, err, failed⟩ ⟨hcfg, hfds, hpg, hcwd, hsig, hdescs, hwl, hok, herr⟩
  by_cases hfail : failed = true
  · simp only [hfail]
    rcases herr hfail with ⟨rfl, j, hj, hj0, hjclosed⟩
    exact okPost_ok _ _ ⟨hcfg, hfds, hpg, hcwd, hsig, hdescs, hwl,
      rfl, fds.val[j], List.getElem_mem hj, hj0, hjclosed⟩
  · have hfalse : failed = false := Bool.eq_false_iff.mpr hfail
    simp only [hfail]
    refine okPost_ok _ _ ⟨hcfg, hfds, hpg, hcwd, hsig, hdescs, hwl, ?_⟩
    intro fd hmem h0
    rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, rfl⟩
    exact hok hfalse j hj h0

private theorem clear_cloexec_slice_loop_total (fds : Slice I32) (i : Usize)
    (hi : i.val ≤ fds.val.length) (s : ChildState) :
    OkPost (postfork.fd_ops.clear_cloexec_slice_loop s fds i fds.len) (fun _ => True) := by
  unfold postfork.fd_ops.clear_cloexec_slice_loop
  refine okPost_loop_decr_nat
    (fun (p : ChildState × Usize) => fds.val.length - p.2.val)
    (fun p => p.2.val ≤ fds.val.length)
    (fun _ => True)
    (fun p => match p with
      | (s1, i1) => postfork.fd_ops.clear_cloexec_slice_loop.body fds fds.len s1 i1)
    (s, i) ?_ hi
  intro ⟨s1, j⟩ hj
  unfold postfork.fd_ops.clear_cloexec_slice_loop.body
  by_cases hlt : j < fds.len
  · rcases slice_idx_succ fds hlt with ⟨hjlt, hidx, z, hinc, hval⟩
    simp only [hlt, ↓reduceIte]
    rw [hidx, bind_ok]
    by_cases hnonneg : fds.val[j.val] ≥ 0#i32
    · simp only [hnonneg, ↓reduceIte]
      refine okPost_bind (clear_cloexec_total s1 fds.val[j.val]) ?_
      intro ⟨r, s2⟩ _
      cases r with
      | Ok _ =>
        change OkPost (do
          let i1 ← j + 1#usize
          Result.ok (ControlFlow.cont (s2, i1))) _
        rw [hinc, bind_ok]
        exact okPost_ok _ _ ⟨by dsimp; rw [hval]; exact hjlt, by dsimp; rw [hval]; omega⟩
      | Err e =>
        exact okPost_ok _ _ trivial
    · simp only [hnonneg, ↓reduceIte]
      rw [hinc, bind_ok]
      exact okPost_ok _ _ ⟨by dsimp; rw [hval]; exact hjlt, by dsimp; rw [hval]; omega⟩
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok _ _ trivial

/-- `clear_cloexec_slice` always terminates cleanly on any child state. -/
theorem clear_cloexec_slice_total (s : ChildState) (fds : Slice I32) :
    OkPost (postfork.fd_ops.clear_cloexec_slice s fds) (fun _ => True) := by
  unfold postfork.fd_ops.clear_cloexec_slice
  refine okPost_bind (clear_cloexec_slice_loop_total fds 0#usize (Nat.zero_le _) s) ?_
  intro ⟨s1, err, failed⟩ _
  by_cases h : failed = true <;> simp [h, okPost_ok]

private theorem band_mask_props (x : I32) :
    let y : I32 := x &&& 2147483646#i32
    0 ≤ y.val ∧ y.val % 2 = 0 ∧
      mkI32 y.val = y ∧
      mkI32 (y.val + 1) &&& 2147483646#i32 = y ∧
      y &&& 2147483646#i32 = y := by
  intro y
  have hbv_eq : y.bv = x.bv &&& 2147483646#32 := rfl
  have hle_nat : y.bv.toNat ≤ 2147483646 := by
    rw [hbv_eq, BitVec.toNat_and]
    exact Nat.and_le_right
  have hlsb : y.bv &&& 1#32 = 0#32 := by
    have hm : (2147483646#32 &&& 1#32) = 0#32 := rfl
    rw [hbv_eq, BitVec.and_assoc, hm, BitVec.and_zero]
  have hand : y.bv &&& 2147483646#32 = y.bv := by
    have hm : (2147483646#32 &&& 2147483646#32) = 2147483646#32 := rfl
    rw [hbv_eq, BitVec.and_assoc, hm]
  have htoInt : y.val = (y.bv.toNat : Int) := by
    change y.bv.toInt = _
    rw [BitVec.toInt_eq_toNat_cond]
    simp [show 2 * y.bv.toNat < 4294967296 by omega]
  have hy_nonneg : 0 ≤ y.val := by omega
  have hy_even : y.val % 2 = 0 := by
    have hb := congrArg BitVec.toNat hlsb
    rw [BitVec.toNat_and] at hb
    change y.bv.toNat &&& 1 = 0 at hb
    have hmod : y.bv.toNat % 2 = 0 := by
      have := Nat.and_one_is_mod y.bv.toNat
      omega
    omega
  have hmk0 : mkI32 y.val = y := by
    apply congrArg IScalar.mk
    change BitVec.ofInt 32 y.bv.toInt = y.bv
    simp
  have hmk1 : mkI32 (y.val + 1) = ⟨y.bv + 1#32⟩ := by
    apply congrArg IScalar.mk
    change BitVec.ofInt 32 (y.val + 1) = y.bv + 1#32
    rw [htoInt]
    have : BitVec.ofInt 32 ((y.bv.toNat : Int) + 1) = BitVec.ofNat 32 (y.bv.toNat + 1) := rfl
    rw [this, BitVec.ofNat_add, BitVec.ofNat_toNat]
    rfl
  have hadd : (y.bv + 1#32) &&& 2147483646#32 = y.bv := by
    have hy_mod : y.bv.toNat % 2 = 0 := by omega
    have hsum : (y.bv + 1#32).toNat = y.bv.toNat + 1 := by
      rw [BitVec.toNat_add]
      simp [Nat.mod_eq_of_lt (show y.bv.toNat + 1 < 4294967296 by omega)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hm0 : (2147483646#32).getLsbD 0 = false := rfl
      have hy0 : y.bv.getLsbD 0 = false := by
        simp [BitVec.getLsbD, Nat.testBit_zero, hy_mod]
      rw [BitVec.getLsbD_and, hm0, Bool.and_false, hy0]
    · have hy_bit : (y.bv + 1#32).getLsbD i = y.bv.getLsbD i := by
        simp only [BitVec.getLsbD, hsum]
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        simp [Nat.testBit_succ, show (y.bv.toNat + 1) / 2 = y.bv.toNat / 2 by omega]
      rw [BitVec.getLsbD_and, hy_bit]
      have handi := congrArg (fun v => v.getLsbD i) hand
      simpa [BitVec.getLsbD_and] using handi
  refine ⟨hy_nonneg, hy_even, hmk0, ?_, ?_⟩
  · rw [hmk1]
    exact congrArg IScalar.mk hadd
  · exact congrArg IScalar.mk hand

private theorem fdFlagsWord_mk_band (desc : Desc) (b : Bool) (w : I32)
    (hw0 : 0 ≤ w.val) (hw2 : w.val % 2 = 0) (hmk : mkI32 w.val = w) :
    fdFlagsWord { desc := desc, cloexec := b, extraFdFlags := w } =
      if b = true then mkI32 (w.val + 1) else w := by
  unfold fdFlagsWord
  dsimp only
  rw [hw2, Int.sub_zero, hmk]
  have hnot : ¬ w.val < 0 := by omega
  simp only [hnot, ↓reduceIte]

private theorem expectedExtraFlags_idemp (s1 s2 : ChildState)
    (hmask : s1.kernelMasksSetfd = s2.kernelMasksSetfd) (e : FdEntry) (b : Bool) :
    expectedExtraFlagsAfterSetfd s1
        { desc := e.desc, cloexec := b, extraFdFlags := expectedExtraFlagsAfterSetfd s2 e } =
      expectedExtraFlagsAfterSetfd s2 e := by
  cases h2 : s2.kernelMasksSetfd
  · rcases band_mask_props (fdFlagsWord e) with ⟨hnonneg, heven, hmk0, hadd, hand⟩
    simp only [expectedExtraFlagsAfterSetfd, hmask, h2, Bool.false_eq_true, ↓reduceIte]
    rw [fdFlagsWord_mk_band e.desc b (fdFlagsWord e &&& 2147483646#i32) hnonneg heven hmk0]
    cases b <;> simp [hadd, hand]
  · simp [expectedExtraFlagsAfterSetfd, hmask, h2]

private theorem clear_cloexec_slice_loop_spec (s0 : ChildState) (hRun0 : s0.status = .running)
    (hOr0 : s0.oracle = []) (fds : Slice I32) :
    OkPost (postfork.fd_ops.clear_cloexec_slice_loop s0 fds 0#usize fds.len)
      (fun (s1, err, failed) =>
        SameChildConfig s1 s0 ∧
          s1.pgid = s0.pgid ∧ s1.cwd = s0.cwd ∧ s1.sig = s0.sig ∧
          s1.descs = s0.descs ∧ s1.writeLog = s0.writeLog ∧
          (∀ k : Int, s1.isOpen k = s0.isOpen k) ∧
          (∀ k : Int, (∀ j (hj : j < fds.val.length), 0 ≤ fds.val[j].val →
            k ≠ fds.val[j].val) → s1.getFd k = s0.getFd k) ∧
          (failed = false →
            (∀ j (hj : j < fds.val.length), 0 ≤ fds.val[j].val →
              ∃ e, s0.getFd fds.val[j].val = some e ∧
                s1.getFd fds.val[j].val = some
                  { desc := e.desc, cloexec := false,
                    extraFdFlags := expectedExtraFlagsAfterSetfd s0 e })) ∧
          (failed = true →
            err = EBADF ∧
              ∃ j, ∃ hj : j < fds.val.length, 0 ≤ fds.val[j].val ∧
                s0.isOpen fds.val[j].val = false)) := by
  unfold postfork.fd_ops.clear_cloexec_slice_loop
  have hz0 : (0#usize : Usize).val = 0 := rfl
  let inv : ChildState × Usize → Prop := fun (s1, p) =>
    SameChildConfig s1 s0 ∧
      s1.pgid = s0.pgid ∧ s1.cwd = s0.cwd ∧ s1.sig = s0.sig ∧
      s1.descs = s0.descs ∧ s1.writeLog = s0.writeLog ∧
      p.val ≤ fds.val.length ∧
      (∀ k : Int, s1.isOpen k = s0.isOpen k) ∧
      (∀ k : Int, (∀ j (hj : j < fds.val.length), j < p.val →
        0 ≤ fds.val[j].val → k ≠ fds.val[j].val) → s1.getFd k = s0.getFd k) ∧
      (∀ j (hj : j < fds.val.length), j < p.val → 0 ≤ fds.val[j].val →
        ∃ e, s0.getFd fds.val[j].val = some e ∧
          s1.getFd fds.val[j].val = some
            { desc := e.desc, cloexec := false,
              extraFdFlags := expectedExtraFlagsAfterSetfd s0 e })
  have hInv0 : inv (s0, 0#usize) :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, fun _ => rfl, fun _ _ => rfl,
      fun _ _ hlt _ => absurd hlt (by omega)⟩
  refine okPost_loop_decr_nat
    (fun (p : ChildState × Usize) => fds.val.length - p.2.val)
    inv
    (fun (s1, err, failed) =>
      SameChildConfig s1 s0 ∧
        s1.pgid = s0.pgid ∧ s1.cwd = s0.cwd ∧ s1.sig = s0.sig ∧
        s1.descs = s0.descs ∧ s1.writeLog = s0.writeLog ∧
        (∀ k : Int, s1.isOpen k = s0.isOpen k) ∧
        (∀ k : Int, (∀ j (hj : j < fds.val.length), 0 ≤ fds.val[j].val →
          k ≠ fds.val[j].val) → s1.getFd k = s0.getFd k) ∧
        (failed = false →
          (∀ j (hj : j < fds.val.length), 0 ≤ fds.val[j].val →
            ∃ e, s0.getFd fds.val[j].val = some e ∧
              s1.getFd fds.val[j].val = some
                { desc := e.desc, cloexec := false,
                  extraFdFlags := expectedExtraFlagsAfterSetfd s0 e })) ∧
        (failed = true →
          err = EBADF ∧
            ∃ j, ∃ hj : j < fds.val.length, 0 ≤ fds.val[j].val ∧
              s0.isOpen fds.val[j].val = false))
    (fun p => match p with
      | (s1, i1) => postfork.fd_ops.clear_cloexec_slice_loop.body fds fds.len s1 i1)
    (s0, 0#usize) ?_ hInv0
  intro ⟨s1, j⟩ ⟨hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hjle, hopen1, hother1, hprev1⟩
  unfold postfork.fd_ops.clear_cloexec_slice_loop.body
  by_cases hlt : j < fds.len
  · rcases slice_idx_succ fds hlt with ⟨hjlt, hidx, z, hinc, hval⟩
    simp only [hlt, ↓reduceIte]
    rw [hidx, bind_ok]
    by_cases hnonneg : fds.val[j.val] ≥ 0#i32
    · have hj_nonneg : 0 ≤ fds.val[j.val].val := by
        change (0#i32 : I32).val ≤ fds.val[j.val].val at hnonneg
        exact hnonneg
      simp only [hnonneg, ↓reduceIte]
      have hRun1 : s1.status = .running := hcfg1.status.trans hRun0
      have hOr1 : s1.oracle = [] := hcfg1.oracle.trans hOr0
      refine okPost_bind (clear_cloexec_spec s1 hRun1 hOr1 fds.val[j.val]) ?_
      intro ⟨r, s2⟩ ⟨hpost2, hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2⟩
      cases hget1 : s1.getFd fds.val[j.val].val with
      | none =>
        have hpost2' : r = .Err EBADF ∧ s2.fds = s1.fds := by
          simpa [CloexecTogglePost, hget1] using hpost2
        rcases hpost2' with ⟨rfl, hfds2⟩
        have hopen_s1 : s1.isOpen fds.val[j.val].val = false := by
          simp [ChildState.isOpen, hget1]
        have hopen_s0 : s0.isOpen fds.val[j.val].val = false := by
          rw [← hopen1 fds.val[j.val].val]; exact hopen_s1
        have hopen2 : ∀ k : Int, s2.isOpen k = s0.isOpen k := by
          intro k
          simp only [ChildState.isOpen, getFd_eq_of_fds_eq hfds2]
          exact hopen1 k
        have hother2 : ∀ k : Int, (∀ m (hm : m < fds.val.length),
            0 ≤ fds.val[m].val → k ≠ fds.val[m].val) → s2.getFd k = s0.getFd k := by
          intro k hk
          rw [getFd_eq_of_fds_eq hfds2 k]
          exact hother1 k (fun m hm _ hm0 => hk m hm hm0)
        exact okPost_ok _ _ ⟨hcfg2.trans hcfg1, hpg2.trans hpg1, hcwd2.trans hcwd1,
          hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1, hopen2, hother2,
          (fun h => by contradiction), fun _ => ⟨rfl, j.val, hjlt, hj_nonneg, hopen_s0⟩⟩
      | some e1 =>
        have hpost2' :
            r = .Ok () ∧
              s2.getFd fds.val[j.val].val = some
                { desc := e1.desc, cloexec := false,
                  extraFdFlags := expectedExtraFlagsAfterSetfd s1 e1 } ∧
              ∀ k : Int, k ≠ fds.val[j.val].val → s2.getFd k = s1.getFd k := by
          simpa [CloexecTogglePost, hget1] using hpost2
        rcases hpost2' with ⟨rfl, hget2_self, hget2_ne⟩
        change OkPost (do
          let i1 ← j + 1#usize
          Result.ok (ControlFlow.cont (s2, i1))) _
        rw [hinc, bind_ok]
        have hopen2 : ∀ k : Int, s2.isOpen k = s0.isOpen k := by
          intro k
          by_cases hk : k = fds.val[j.val].val
          · subst hk
            rw [← hopen1 fds.val[j.val].val]
            simp [ChildState.isOpen, hget1, hget2_self]
          · simp only [ChildState.isOpen, hget2_ne k hk]
            exact hopen1 k
        have hother2 : ∀ k : Int, (∀ m (hm : m < fds.val.length), m < j.val + 1 →
            0 ≤ fds.val[m].val → k ≠ fds.val[m].val) → s2.getFd k = s0.getFd k := by
          intro k hk
          have hne_j : k ≠ fds.val[j.val].val := hk j.val hjlt (Nat.lt_succ_self _) hj_nonneg
          rw [hget2_ne k hne_j]
          exact hother1 k (fun m hm hmj hm0 => hk m hm (by omega) hm0)
        have hprev2 : ∀ m (hm : m < fds.val.length), m < j.val + 1 →
            0 ≤ fds.val[m].val →
            ∃ e, s0.getFd fds.val[m].val = some e ∧
              s2.getFd fds.val[m].val = some
                { desc := e.desc, cloexec := false,
                  extraFdFlags := expectedExtraFlagsAfterSetfd s0 e } := by
          intro m hm hmj hm0
          by_cases hmeq : fds.val[m].val = fds.val[j.val].val
          · by_cases hseen : ∃ m0, ∃ hm0lt : m0 < fds.val.length,
                m0 < j.val ∧ 0 ≤ fds.val[m0].val ∧
                fds.val[m0].val = fds.val[j.val].val
            · rcases hseen with ⟨m0, hm0lt, hm0j, hm0_nonneg, hm0_eq⟩
              rcases hprev1 m0 hm0lt hm0j hm0_nonneg with ⟨e0, h0, h1⟩
              rw [hm0_eq] at h0 h1
              rw [hget1] at h1
              cases h1
              refine ⟨e0, ?_, ?_⟩
              · rw [hmeq]; exact h0
              · rw [hmeq, hget2_self]
                congr 2
                exact expectedExtraFlags_idemp s1 s0 hcfg1.kernelMasksSetfd e0 false
            · have hnot : ∀ m0 (hm0lt : m0 < fds.val.length), m0 < j.val →
                  0 ≤ fds.val[m0].val → fds.val[j.val].val ≠ fds.val[m0].val :=
                fun m0 hm0lt hm0j hm0_nonneg heq =>
                  hseen ⟨m0, hm0lt, hm0j, hm0_nonneg, heq.symm⟩
              have hs1_eq_s0 : s1.getFd fds.val[j.val].val = s0.getFd fds.val[j.val].val :=
                hother1 fds.val[j.val].val hnot
              rw [hget1] at hs1_eq_s0
              refine ⟨e1, ?_, ?_⟩
              · rw [hmeq]; exact hs1_eq_s0.symm
              · rw [hmeq, hget2_self]
                congr 2
                cases hms : s0.kernelMasksSetfd <;>
                  simp [expectedExtraFlagsAfterSetfd, hcfg1.kernelMasksSetfd, hms]
          · have hmne : m ≠ j.val := fun h => hmeq (by subst h; rfl)
            rcases hprev1 m hm (by omega) hm0 with ⟨e0, h0, h1⟩
            refine ⟨e0, h0, ?_⟩
            rw [hget2_ne fds.val[m].val hmeq]
            exact h1
        refine okPost_ok _ _ ⟨⟨hcfg2.trans hcfg1, hpg2.trans hpg1, hcwd2.trans hcwd1,
          hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1, ?_, hopen2, ?_, ?_⟩, ?_⟩
        · rw [hval]; exact hjlt
        · intro k hk
          apply hother2 k
          intro m hm hmj hm0
          rw [hval] at hk
          exact hk m hm (by omega) hm0
        · intro m hm hmj hm0
          rw [hval] at hmj
          exact hprev2 m hm hmj hm0
        · dsimp; rw [hval]; omega
    · simp only [hnonneg, ↓reduceIte]
      rw [hinc, bind_ok]
      have hnot_nonneg : ¬ 0 ≤ fds.val[j.val].val := fun h =>
        hnonneg (by change (0#i32 : I32).val ≤ fds.val[j.val].val; exact h)
      refine okPost_ok _ _ ⟨⟨hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, ?_, hopen1, ?_, ?_⟩, ?_⟩
      · rw [hval]; exact hjlt
      · intro k hk
        apply hother1 k
        intro m hm hmj hm0
        rw [hval] at hk
        exact hk m hm (by omega) hm0
      · intro m hm hmj hm0
        rw [hval] at hmj
        have hmj' : m < j.val := by
          by_cases hmeq : m = j.val
          · subst hmeq; exact absurd hm0 hnot_nonneg
          · omega
        exact hprev1 m hm hmj' hm0
      · dsimp; rw [hval]; omega
  · simp only [hlt, ↓reduceIte]
    have hj_ge : fds.val.length ≤ j.val := by
      have hlen : ¬ j.val < fds.val.length := by simpa [Slice.len] using hlt
      omega
    exact okPost_ok _ _ ⟨hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hopen1,
      (fun k hk => hother1 k (fun m hm _ hm0 => hk m hm hm0)),
      (fun _ m hm hm0 => hprev1 m hm (Nat.lt_of_lt_of_le hm hj_ge) hm0),
      fun h => by contradiction⟩

/-- Specification of `clear_cloexec_slice` on a running, fault-free child state: succeeds iff all
non-negative entries of `fds` are open in `s`, clears `cloexec` on each of them while preserving
all other slots, open-FD sets, descriptors, and non-fd/trace configuration. -/
theorem clear_cloexec_slice_spec (s : ChildState) (hRun : s.status = .running)
    (hOr : s.oracle = []) (fds : Slice I32) :
    OkPost (postfork.fd_ops.clear_cloexec_slice s fds) fun p =>
      SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        (∀ k : Int, p.2.isOpen k = s.isOpen k) ∧
        (∀ k : Int, (∀ fd ∈ fds.val, 0 ≤ fd.val → k ≠ fd.val) → p.2.getFd k = s.getFd k) ∧
        match p.1 with
        | .Ok () =>
          ∀ fd ∈ fds.val, 0 ≤ fd.val →
            ∃ e, s.getFd fd.val = some e ∧
              p.2.getFd fd.val = some
                { desc := e.desc, cloexec := false,
                  extraFdFlags := expectedExtraFlagsAfterSetfd s e }
        | .Err e =>
          e = EBADF ∧ ∃ fd ∈ fds.val, 0 ≤ fd.val ∧ s.isOpen fd.val = false := by
  unfold postfork.fd_ops.clear_cloexec_slice
  refine okPost_bind (clear_cloexec_slice_loop_spec s hRun hOr fds) ?_
  intro ⟨s1, err, failed⟩ ⟨hcfg, hpg, hcwd, hsig, hdescs, hwl, hopen, hother, hok, herr⟩
  have hother' : ∀ k : Int, (∀ fd ∈ fds.val, 0 ≤ fd.val → k ≠ fd.val) →
      s1.getFd k = s.getFd k := by
    intro k hk
    apply hother k
    intro j hj hj0
    exact hk fds.val[j] (List.getElem_mem hj) hj0
  by_cases hfail : failed = true
  · simp only [hfail]
    rcases herr hfail with ⟨rfl, j, hj, hj0, hjclosed⟩
    exact okPost_ok _ _ ⟨hcfg, hpg, hcwd, hsig, hdescs, hwl, hopen, hother',
      rfl, fds.val[j], List.getElem_mem hj, hj0, hjclosed⟩
  · have hfalse : failed = false := Bool.eq_false_iff.mpr hfail
    simp only [hfail]
    refine okPost_ok _ _ ⟨hcfg, hpg, hcwd, hsig, hdescs, hwl, hopen, hother', ?_⟩
    intro fd hmem h0
    rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, rfl⟩
    exact hok hfalse j hj h0

/-- `probe_stdio_open` always terminates cleanly on any child state. -/
theorem probe_stdio_open_total (s : ChildState) (stdin_fd stdout_fd stderr_fd : I32) :
    OkPost (postfork.fd_ops.probe_stdio_open s stdin_fd stdout_fd stderr_fd) (fun _ => True) := by
  unfold postfork.fd_ops.probe_stdio_open
  by_cases h0 : stdin_fd < 0#i32
  · simp [h0, okPost_ok]
  · by_cases h1 : stdout_fd < 0#i32
    · simp [h0, h1, okPost_ok]
    · by_cases h2 : stderr_fd < 0#i32
      · simp [h0, h1, h2, okPost_ok]
      · simp only [h0, h1, h2, ↓reduceIte]
        refine okPost_bind (sys_fcntl_getfd_total s stdin_fd) ?_
        intro ⟨r0, s1⟩ _
        cases r0 with
        | Err _ => exact okPost_ok _ _ trivial
        | Ok _ =>
          refine okPost_bind (sys_fcntl_getfd_total s1 stdout_fd) ?_
          intro ⟨r1, s2⟩ _
          cases r1 with
          | Err _ => exact okPost_ok _ _ trivial
          | Ok _ =>
            refine okPost_bind (sys_fcntl_getfd_total s2 stderr_fd) ?_
            intro ⟨r2, s3⟩ _
            cases r2 <;> exact okPost_ok _ _ trivial

/-- Specification of `probe_stdio_open` on a running, fault-free child state. -/
theorem probe_stdio_open_spec (s : ChildState) (hRun : s.status = .running)
    (hOr : s.oracle = []) (stdin_fd stdout_fd stderr_fd : I32) :
    OkPost (postfork.fd_ops.probe_stdio_open s stdin_fd stdout_fd stderr_fd) fun p =>
      SameChildConfig p.2 s ∧ p.2.fds = s.fds ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        if stdin_fd < 0#i32 || stdout_fd < 0#i32 || stderr_fd < 0#i32 then
          p.1 = .Err EBADF ∧ p.2 = s
        else if s.isOpen stdin_fd.val && s.isOpen stdout_fd.val && s.isOpen stderr_fd.val then
          p.1 = .Ok ()
        else
          p.1 = .Err EBADF := by
  unfold postfork.fd_ops.probe_stdio_open
  have hcfg0 : SameChildConfig s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hebadf : postfork.fd_ops.EBADF = EBADF := by
    simp [postfork.fd_ops.EBADF, EBADF]
  by_cases h0 : stdin_fd < 0#i32
  · simp only [h0, ↓reduceIte]
    exact okPost_ok _ _ ⟨hcfg0, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hebadf]⟩
  · by_cases h1 : stdout_fd < 0#i32
    · simp only [h0, h1, ↓reduceIte]
      exact okPost_ok _ _ ⟨hcfg0, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hebadf]⟩
    · by_cases h2 : stderr_fd < 0#i32
      · simp only [h0, h1, h2, ↓reduceIte]
        exact okPost_ok _ _ ⟨hcfg0, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hebadf]⟩
      · simp only [h0, h1, h2, ↓reduceIte]
        rcases sys_fcntl_getfd_run_spec s hRun hOr stdin_fd with
          ⟨r0, s1, hcall0, hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hfds1, hres1⟩
        rw [hcall0, bind_ok]
        cases hget0 : s.getFd stdin_fd.val with
        | none =>
          have ho0 : s.isOpen stdin_fd.val = false := by simp [ChildState.isOpen, hget0]
          rw [hget0] at hres1
          subst hres1
          exact okPost_ok _ _ ⟨hcfg1, hfds1, hpg1, hcwd1, hsig1, hdescs1, hwl1,
            by simp [ho0]⟩
        | some e0 =>
          have ho0 : s.isOpen stdin_fd.val = true := by simp [ChildState.isOpen, hget0]
          rw [hget0] at hres1
          subst hres1
          change OkPost (do
            let (r1, s2) ← sys.fcntl_getfd s1 stdout_fd
            match r1 with
            | core.result.Result.Ok _ => do
              let (r2, s3) ← sys.fcntl_getfd s2 stderr_fd
              match r2 with
              | core.result.Result.Ok _ => Result.ok (core.result.Result.Ok (), s3)
              | core.result.Result.Err e => Result.ok (core.result.Result.Err e, s3)
            | core.result.Result.Err e => Result.ok (core.result.Result.Err e, s2)) _
          have hRun1 : s1.status = .running := hcfg1.status.trans hRun
          have hOr1 : s1.oracle = [] := hcfg1.oracle.trans hOr
          rcases sys_fcntl_getfd_run_spec s1 hRun1 hOr1 stdout_fd with
            ⟨r1, s2, hcall1, hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hfds2, hres2⟩
          rw [hcall1, bind_ok]
          have hget1_eq : s1.getFd stdout_fd.val = s.getFd stdout_fd.val :=
            getFd_eq_of_fds_eq hfds1 stdout_fd.val
          cases hget1 : s.getFd stdout_fd.val with
          | none =>
            have ho1 : s.isOpen stdout_fd.val = false := by simp [ChildState.isOpen, hget1]
            rw [hget1_eq, hget1] at hres2
            subst hres2
            exact okPost_ok _ _ ⟨hcfg2.trans hcfg1, hfds2.trans hfds1, hpg2.trans hpg1,
              hcwd2.trans hcwd1, hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1,
              by simp [ho0, ho1]⟩
          | some e1 =>
            have ho1 : s.isOpen stdout_fd.val = true := by simp [ChildState.isOpen, hget1]
            rw [hget1_eq, hget1] at hres2
            subst hres2
            change OkPost (do
              let (r2, s3) ← sys.fcntl_getfd s2 stderr_fd
              match r2 with
              | core.result.Result.Ok _ => Result.ok (core.result.Result.Ok (), s3)
              | core.result.Result.Err e => Result.ok (core.result.Result.Err e, s3)) _
            have hRun2 : s2.status = .running := hcfg2.status.trans hRun1
            have hOr2 : s2.oracle = [] := hcfg2.oracle.trans hOr1
            rcases sys_fcntl_getfd_run_spec s2 hRun2 hOr2 stderr_fd with
              ⟨r2, s3, hcall2, hcfg3, hpg3, hcwd3, hsig3, hdescs3, hwl3, hfds3, hres3⟩
            rw [hcall2, bind_ok]
            have hget2_eq : s2.getFd stderr_fd.val = s.getFd stderr_fd.val :=
              getFd_eq_of_fds_eq (hfds2.trans hfds1) stderr_fd.val
            cases hget2 : s.getFd stderr_fd.val with
            | none =>
              have ho2 : s.isOpen stderr_fd.val = false := by simp [ChildState.isOpen, hget2]
              rw [hget2_eq, hget2] at hres3
              subst hres3
              exact okPost_ok _ _ ⟨hcfg3.trans (hcfg2.trans hcfg1),
                hfds3.trans (hfds2.trans hfds1), hpg3.trans (hpg2.trans hpg1),
                hcwd3.trans (hcwd2.trans hcwd1), hsig3.trans (hsig2.trans hsig1),
                hdescs3.trans (hdescs2.trans hdescs1), hwl3.trans (hwl2.trans hwl1),
                by simp [ho0, ho1, ho2]⟩
            | some e2 =>
              have ho2 : s.isOpen stderr_fd.val = true := by simp [ChildState.isOpen, hget2]
              rw [hget2_eq, hget2] at hres3
              subst hres3
              exact okPost_ok _ _ ⟨hcfg3.trans (hcfg2.trans hcfg1),
                hfds3.trans (hfds2.trans hfds1), hpg3.trans (hpg2.trans hpg1),
                hcwd3.trans (hcwd2.trans hcwd1), hsig3.trans (hsig2.trans hsig1),
                hdescs3.trans (hdescs2.trans hdescs1), hwl3.trans (hwl2.trans hwl1),
                by simp [ho0, ho1, ho2]⟩

private theorem fdOpsMkI32Val (x : ℤ) (hx0 : 0 ≤ x) (hx1 : x < 2147483648) : (mkI32 x).val = x := by
  simp only [mkI32]
  have h : (BitVec.ofInt 32 x#iscalar : I32) = I32.ofInt x (by scalar_tac) := rfl
  rw [h]
  simp

private theorem probe_stdio_open_neg_spec (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (hNeg : (decide (stdin_fd < 0#i32) || decide (stdout_fd < 0#i32) || decide (stderr_fd < 0#i32)) = true) :
    OkPost (postfork.fd_ops.probe_stdio_open s stdin_fd stdout_fd stderr_fd)
      (fun p => p.1 = .Err EBADF ∧ p.2 = s) := by
  unfold postfork.fd_ops.probe_stdio_open
  by_cases h0 : stdin_fd < 0#i32
  · simp only [h0, ↓reduceIte]
    exact okPost_ok _ _ ⟨by simp [postfork.fd_ops.EBADF, EBADF], rfl⟩
  · by_cases h1 : stdout_fd < 0#i32
    · simp only [h0, h1, ↓reduceIte]
      exact okPost_ok _ _ ⟨by simp [postfork.fd_ops.EBADF, EBADF], rfl⟩
    · have hb0 : decide (stdin_fd < 0#i32) = false := decide_eq_false h0
      have hb1 : decide (stdout_fd < 0#i32) = false := decide_eq_false h1
      simp only [hb0, hb1, Bool.false_or] at hNeg
      have h2 : stderr_fd < 0#i32 := of_decide_eq_true hNeg
      simp only [h0, h1, h2, ↓reduceIte]
      exact okPost_ok _ _ ⟨by simp [postfork.fd_ops.EBADF, EBADF], rfl⟩

private theorem sys_close_spec (s : sys.Sys) (hRun : s.status = .running) (hOr : s.oracle = [])
    (fd : I32) :
    OkPost (sys.close s fd) fun p =>
      SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        ∀ k, p.2.getFd k = if k = fd.val then none else s.getFd k := by
  unfold sys.close LeanSwe.PostFork.Aeneas.Internal.Sys.close runUnitSyscall
  rw [hRun]
  have hF : currentFault s = .normal := currentFault_oracle_nil s hOr
  by_cases hOpen : s.isOpen fd.val = true
  · simp only [hOpen, ↓reduceIte, hF]
    refine okPost_ok _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, fun k => ?_⟩
    by_cases hk : k = fd.val
    · subst hk; simp only [↓reduceIte]; exact getFd_closeSlot_self s _
    · simp only [hk, ↓reduceIte]; exact getFd_closeSlot_ne s hk
  · simp only [hOpen, hF]
    refine okPost_ok _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, fun k => ?_⟩
    by_cases hk : k = fd.val
    · subst hk; simp only [↓reduceIte]; exact getFd_closeSlot_self s _
    · simp only [hk, ↓reduceIte]; exact getFd_closeSlot_ne s hk

private theorem sys_dup2_spec (s : sys.Sys) (hRun : s.status = .running) (hOr : s.oracle = [])
    (oldfd newfd : I32) {e : FdEntry} (hOpen : s.getFd oldfd.val = some e)
    (h0 : 0 ≤ newfd.val) (hLim : newfd.val < s.fdLimit) :
    OkPost (sys.dup2 s oldfd newfd) fun p =>
      p.1 = .Ok () ∧ SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        (∃ f, p.2.getFd newfd.val = some f ∧ f.desc = e.desc) ∧
        (∀ k, k ≠ newfd.val → p.2.getFd k = s.getFd k) := by
  unfold sys.dup2 LeanSwe.PostFork.Aeneas.Internal.Sys.dup2 runUnitSyscall
  have ho : s.isOpen oldfd.val = true := by simp [ChildState.isOpen, hOpen]
  have hoNot : (!s.isOpen oldfd.val) = false := by simp [ho]
  have hF : currentFault s = .normal := currentFault_oracle_nil s hOr
  have hBounds : (decide (newfd.val < 0) || decide (newfd.val ≥ s.fdLimit)) = false := by
    simp [show ¬(newfd.val < 0) by omega, show ¬(newfd.val ≥ s.fdLimit) by omega]
  by_cases hEq : oldfd.val = newfd.val
  · have hEqb : (oldfd.val == newfd.val) = true := beq_iff_eq.mpr hEq
    have hcfg : SameChildConfig
        { pid := s.pid, sid := s.sid, pgid := s.pgid, fds := s.fds, descs := s.descs, fdLimit := s.fdLimit,
          kernelMasksSetfd := s.kernelMasksSetfd, closeRangeSupported := s.closeRangeSupported,
          closeRangeErrno := s.closeRangeErrno, procSelfFdAvailable := s.procSelfFdAvailable,
          procOpenErrno := s.procOpenErrno, cwd := s.cwd, chdirResolved := s.chdirResolved, sig := s.sig,
          blockedSigs := s.blockedSigs, procMaxFds := s.procMaxFds, writeLog := s.writeLog,
          trace := s.trace ++ [{ req := Req.dup2 oldfd newfd, out := EventOutcome.okVal 0 }],
          oracle := s.oracle, status := s.status } s :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [hoNot, Bool.false_eq_true, ↓reduceIte, hEqb, hRun, hF]
    refine okPost_ok _ _ ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ⟨e, ?_, rfl⟩, fun k _ => rfl⟩
    · simpa [SameChildConfig, hRun] using hcfg
    · change s.getFd newfd.val = some e
      rw [← hEq]; exact hOpen
  · have hEqb : (oldfd.val == newfd.val) = false := beq_false_of_ne hEq
    simp only [hoNot, Bool.false_eq_true, ↓reduceIte, hEqb, hBounds, hRun, hF, hOpen]
    refine okPost_ok _ _ ⟨rfl, ⟨rfl, by simp [ChildState.putSlot, hRun], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, ⟨{ desc := e.desc, cloexec := false }, ?_, rfl⟩, fun k hk => ?_⟩
    · exact getFd_putSlot_self s newfd.val { desc := e.desc, cloexec := false }
    · exact getFd_putSlot_ne s hk { desc := e.desc, cloexec := false }

private theorem sys_fcntl_dupfd_cloexec_spec (s : sys.Sys) (hRun : s.status = .running)
    (hOr : s.oracle = []) (fd minFd : I32) {e : FdEntry} {dst : ℤ}
    (hOpen : s.getFd fd.val = some e) (hMin0 : 0 ≤ minFd.val) (hMinLim : minFd.val < s.fdLimit)
    (hFree : findLowestFreeFd s minFd.val = some dst) :
    OkPost (sys.fcntl_dupfd_cloexec s fd minFd) fun p =>
      ∃ tmp, p.1 = .Ok tmp ∧ tmp.val = dst ∧ minFd.val ≤ tmp.val ∧
        tmp.val < min s.fdLimit 2147483648 ∧ s.getFd tmp.val = none ∧
        SameChildConfig p.2 s ∧ p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        (∃ f, p.2.getFd tmp.val = some f ∧ f.desc = e.desc) ∧
        (∀ k, k ≠ tmp.val → p.2.getFd k = s.getFd k) := by
  rcases findLowestFreeFd_spec s minFd.val dst hFree with ⟨hfd0, hfdLim, _, _, hfdNone⟩
  have hdst0 : 0 ≤ dst := by omega
  have hdstLim : dst < 2147483648 := by omega
  have htmpVal : (mkI32 dst).val = dst := fdOpsMkI32Val dst hdst0 hdstLim
  have hBounds : (decide (minFd.val < 0) || decide (minFd.val ≥ s.fdLimit)) = false := by
    simp [show ¬(minFd.val < 0) by omega, show ¬(minFd.val ≥ s.fdLimit) by omega]
  have hF : currentFault s = .normal := currentFault_oracle_nil s hOr
  unfold sys.fcntl_dupfd_cloexec LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_dupfd_cloexec runI32Syscall
  simp only [hOpen, hBounds, Bool.false_eq_true, ↓reduceIte, hFree, hRun, hF]
  refine okPost_ok _ _ ⟨mkI32 dst, rfl, htmpVal, by omega, by omega, by rw [htmpVal]; exact hfdNone.2,
    ⟨rfl, by simp [ChildState.putSlot, hRun], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
    ⟨{ desc := e.desc, cloexec := true }, ?_, rfl⟩, fun k hk => ?_⟩
  · change (s.putSlot dst { desc := e.desc, cloexec := true }).getFd (mkI32 dst).val = _
    rw [htmpVal]
    exact getFd_putSlot_self s dst { desc := e.desc, cloexec := true }
  · change (s.putSlot dst { desc := e.desc, cloexec := true }).getFd k = s.getFd k
    rw [htmpVal] at hk
    exact getFd_putSlot_ne s hk { desc := e.desc, cloexec := true }

private def setupStdioClear012 (s : sys.Sys) :
    Result (core.result.Result Unit I32 × sys.Sys) := do
  let (r6, s10) ← postfork.fd_ops.clear_cloexec s 0#i32
  match r6 with
  | .Ok _ => do
    let (r7, s12) ← postfork.fd_ops.clear_cloexec s10 1#i32
    match r7 with
    | .Ok _ => postfork.fd_ops.clear_cloexec s12 2#i32
    | .Err _ => Result.ok (r7, s12)
  | .Err _ => Result.ok (r6, s10)

private def setupStdioCloseAbove2 (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32) :
    Result sys.Sys := do
  let s10 ←
    if stdin_fd > 2#i32 then do
      let (_, s12) ← sys.close s stdin_fd
      Result.ok s12
    else Result.ok s
  let s12 ←
    if stdout_fd > 2#i32 then
      if (stdout_fd != stdin_fd) = true then do
        let (_, s13) ← sys.close s10 stdout_fd
        Result.ok s13
      else Result.ok s10
    else Result.ok s10
  if stderr_fd > 2#i32 then
    if (stderr_fd != stdin_fd) = true then
      if (stderr_fd != stdout_fd) = true then do
        let (_, s13) ← sys.close s12 stderr_fd
        Result.ok s13
      else Result.ok s12
    else Result.ok s12
  else Result.ok s12

private def setupStdioFinish (s : sys.Sys) (tmp0 tmp1 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) : Result (core.result.Result Unit I32 × sys.Sys) := do
  let s7 ←
    if tmp1 ≥ 0#i32 then do
      let (_, s8) ← sys.close s tmp1
      Result.ok s8
    else Result.ok s
  let s8 ←
    if tmp0 ≥ 0#i32 then do
      let (_, s9) ← sys.close s7 tmp0
      Result.ok s9
    else Result.ok s7
  let s9 ←
    if close_sources_above2 = true then
      setupStdioCloseAbove2 s8 stdin_fd stdout_fd stderr_fd
    else Result.ok s8
  setupStdioClear012 s9

private def setupStdioCloseTmpsErr (s : sys.Sys) (tmp0 tmp1 : I32)
    (r : core.result.Result Unit I32) : Result (core.result.Result Unit I32 × sys.Sys) := do
  let s7 ←
    if tmp1 ≥ 0#i32 then do
      let (_, s8) ← sys.close s tmp1
      Result.ok s8
    else Result.ok s
  if tmp0 ≥ 0#i32 then do
    let (_, s8) ← sys.close s7 tmp0
    Result.ok (r, s8)
  else Result.ok (r, s7)

private def setupStdioDup12Direct (s : sys.Sys) (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) : Result (core.result.Result Unit I32 × sys.Sys) := do
  let (r3, s4) ← sys.dup2 s s11 1#i32
  match r3 with
  | .Ok _ => do
    let (r4, s5) ← sys.dup2 s4 s21 2#i32
    match r4 with
    | .Ok _ => setupStdioFinish s5 tmp0 (-1)#i32 stdin_fd stdout_fd stderr_fd close_sources_above2
    | .Err _ => setupStdioCloseTmpsErr s5 tmp0 (-1)#i32 r4
  | .Err _ => setupStdioCloseTmpsErr s4 tmp0 (-1)#i32 r3

private def setupStdioAfterDup0 (s : sys.Sys) (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) : Result (core.result.Result Unit I32 × sys.Sys) :=
  if (s11 != 1#i32) = true then
    if s21 = 1#i32 then do
      let (r3, s4) ← sys.fcntl_dupfd_cloexec s 1#i32 3#i32
      match r3 with
      | .Ok fd1 => do
        let (r4, s5) ← sys.dup2 s4 s11 1#i32
        match r4 with
        | .Ok _ => do
          let (r5, s6) ← sys.dup2 s5 fd1 2#i32
          match r5 with
          | .Ok _ => setupStdioFinish s6 tmp0 fd1 stdin_fd stdout_fd stderr_fd close_sources_above2
          | .Err _ => setupStdioCloseTmpsErr s6 tmp0 fd1 r5
        | .Err _ => setupStdioCloseTmpsErr s5 tmp0 fd1 r4
      | .Err e =>
        if tmp0 ≥ 0#i32 then do
          let (_, s5) ← sys.close s4 tmp0
          Result.ok (core.result.Result.Err e, s5)
        else Result.ok (core.result.Result.Err e, s4)
    else setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
  else setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2

private def setupStdioSave0 (s1 : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) : Result (core.result.Result Unit I32 × sys.Sys) := do
  let (r1, s2) ← sys.fcntl_dupfd_cloexec s1 0#i32 3#i32
  match r1 with
  | .Ok fd => do
    let s11 ← if stdout_fd = 0#i32 then Result.ok fd else Result.ok stdout_fd
    let s21 ← if stderr_fd = 0#i32 then Result.ok fd else Result.ok stderr_fd
    let (r2, s3) ← sys.dup2 s2 stdin_fd 0#i32
    match r2 with
    | .Ok _ => setupStdioAfterDup0 s3 fd s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
    | .Err _ =>
      if fd ≥ 0#i32 then do
        let (_, s4) ← sys.close s3 fd
        Result.ok (r2, s4)
      else Result.ok (r2, s3)
  | .Err e => Result.ok (core.result.Result.Err e, s2)

private def setupStdioNoSave0 (s1 : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) : Result (core.result.Result Unit I32 × sys.Sys) := do
  let (r1, s2) ← sys.dup2 s1 stdin_fd 0#i32
  match r1 with
  | .Ok _ => setupStdioAfterDup0 s2 (-1)#i32 stdout_fd stderr_fd stdin_fd stdout_fd stderr_fd close_sources_above2
  | .Err _ =>
    if (-1)#i32 ≥ 0#i32 then do
      let (_, s3) ← sys.close s2 (-1)#i32
      Result.ok (r1, s3)
    else Result.ok (r1, s2)

private theorem setup_stdio_eq_factored (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    postfork.fd_ops.setup_stdio s stdin_fd stdout_fd stderr_fd close_sources_above2 =
      (do
        let (r, s1) ← postfork.fd_ops.probe_stdio_open s stdin_fd stdout_fd stderr_fd
        match r with
        | .Ok _ =>
          if (stdin_fd != 0#i32) = true then
            if stdout_fd = 0#i32 then setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
            else if stderr_fd = 0#i32 then setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
            else setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
          else setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
        | .Err _ => Result.ok (r, s1)) := rfl

private theorem setupStdioClear012_total (s : sys.Sys) :
    OkPost (setupStdioClear012 s) (fun _ => True) := by
  unfold setupStdioClear012
  refine okPost_bind (clear_cloexec_total s 0#i32) fun ⟨r6, s10⟩ _ => ?_
  cases r6 with
  | Ok _ =>
    refine okPost_bind (clear_cloexec_total s10 1#i32) fun ⟨r7, s12⟩ _ => ?_
    cases r7 with
    | Ok _ => exact clear_cloexec_total s12 2#i32
    | Err _ => exact okPost_ok _ _ trivial
  | Err _ => exact okPost_ok _ _ trivial

private theorem setupStdioCloseAbove2_total (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32) :
    OkPost (setupStdioCloseAbove2 s stdin_fd stdout_fd stderr_fd) (fun _ => True) := by
  unfold setupStdioCloseAbove2
  refine okPost_bind (P := fun _ => True) (by split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]) fun s10 _ => ?_
  refine okPost_bind (P := fun _ => True) (by split <;> [split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]; exact okPost_ok _ _ trivial]) fun s12 _ => ?_
  split <;> [split <;> [split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]; exact okPost_ok _ _ trivial]; exact okPost_ok _ _ trivial]

private theorem setupStdioFinish_total (s : sys.Sys) (tmp0 tmp1 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioFinish s tmp0 tmp1 stdin_fd stdout_fd stderr_fd close_sources_above2) (fun _ => True) := by
  unfold setupStdioFinish
  refine okPost_bind (P := fun _ => True) (by split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]) fun s7 _ => ?_
  refine okPost_bind (P := fun _ => True) (by split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]) fun s8 _ => ?_
  refine okPost_bind (P := fun _ => True) (by split <;> [exact setupStdioCloseAbove2_total _ _ _ _; exact okPost_ok _ _ trivial]) fun s9 _ => ?_
  exact setupStdioClear012_total s9

private theorem setupStdioCloseTmpsErr_total (s : sys.Sys) (tmp0 tmp1 : I32)
    (r : core.result.Result Unit I32) :
    OkPost (setupStdioCloseTmpsErr s tmp0 tmp1 r) (fun _ => True) := by
  unfold setupStdioCloseTmpsErr
  refine okPost_bind (P := fun _ => True) (by split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]) fun s7 _ => ?_
  split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]

private theorem setupStdioDup12Direct_total (s : sys.Sys) (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2)
      (fun _ => True) := by
  unfold setupStdioDup12Direct
  refine okPost_bind (sys_dup2_total s s11 1#i32) fun ⟨r3, s4⟩ _ => ?_
  cases r3 with
  | Ok _ =>
    refine okPost_bind (sys_dup2_total s4 s21 2#i32) fun ⟨r4, s5⟩ _ => ?_
    cases r4 with
    | Ok _ => exact setupStdioFinish_total s5 tmp0 (-1)#i32 stdin_fd stdout_fd stderr_fd close_sources_above2
    | Err _ => exact setupStdioCloseTmpsErr_total s5 tmp0 (-1)#i32 _
  | Err _ => exact setupStdioCloseTmpsErr_total s4 tmp0 (-1)#i32 _

private theorem setupStdioAfterDup0_total (s : sys.Sys) (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioAfterDup0 s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2)
      (fun _ => True) := by
  unfold setupStdioAfterDup0
  split
  · split
    · refine okPost_bind (sys_fcntl_dupfd_cloexec_total s 1#i32 3#i32) fun ⟨r3, s4⟩ _ => ?_
      cases r3 with
      | Ok fd1 =>
        refine okPost_bind (sys_dup2_total s4 s11 1#i32) fun ⟨r4, s5⟩ _ => ?_
        cases r4 with
        | Ok _ =>
          refine okPost_bind (sys_dup2_total s5 fd1 2#i32) fun ⟨r5, s6⟩ _ => ?_
          cases r5 with
          | Ok _ => exact setupStdioFinish_total s6 tmp0 fd1 stdin_fd stdout_fd stderr_fd close_sources_above2
          | Err _ => exact setupStdioCloseTmpsErr_total s6 tmp0 fd1 _
        | Err _ => exact setupStdioCloseTmpsErr_total s5 tmp0 fd1 _
      | Err _ =>
        split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]
    · exact setupStdioDup12Direct_total s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
  · exact setupStdioDup12Direct_total s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2

private theorem setupStdioSave0_total (s1 : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) (fun _ => True) := by
  unfold setupStdioSave0
  refine okPost_bind (sys_fcntl_dupfd_cloexec_total s1 0#i32 3#i32) fun ⟨r1, s2⟩ _ => ?_
  cases r1 with
  | Ok fd =>
    refine okPost_bind (P := fun _ => True) (by split <;> exact okPost_ok _ _ trivial) fun s11 _ => ?_
    refine okPost_bind (P := fun _ => True) (by split <;> exact okPost_ok _ _ trivial) fun s21 _ => ?_
    refine okPost_bind (sys_dup2_total s2 stdin_fd 0#i32) fun ⟨r2, s3⟩ _ => ?_
    cases r2 with
    | Ok _ => exact setupStdioAfterDup0_total s3 fd s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
    | Err _ => split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]
  | Err _ => exact okPost_ok _ _ trivial

private theorem setupStdioNoSave0_total (s1 : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) (fun _ => True) := by
  unfold setupStdioNoSave0
  refine okPost_bind (sys_dup2_total s1 stdin_fd 0#i32) fun ⟨r1, s2⟩ _ => ?_
  cases r1 with
  | Ok _ => exact setupStdioAfterDup0_total s2 (-1)#i32 stdout_fd stderr_fd stdin_fd stdout_fd stderr_fd close_sources_above2
  | Err _ => split <;> [exact okPost_bind (sys_close_total _ _) fun _ _ => okPost_ok _ _ trivial; exact okPost_ok _ _ trivial]

/-- Total safety for `postfork.fd_ops.setup_stdio`. -/
theorem setup_stdio_total (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (postfork.fd_ops.setup_stdio s stdin_fd stdout_fd stderr_fd close_sources_above2)
      (fun _ => True) := by
  rw [setup_stdio_eq_factored]
  refine okPost_bind (probe_stdio_open_total s stdin_fd stdout_fd stderr_fd) fun ⟨r, s1⟩ _ => ?_
  cases r with
  | Ok _ =>
    split
    · split
      · exact setupStdioSave0_total s1 stdin_fd stdout_fd stderr_fd close_sources_above2
      · split
        · exact setupStdioSave0_total s1 stdin_fd stdout_fd stderr_fd close_sources_above2
        · exact setupStdioNoSave0_total s1 stdin_fd stdout_fd stderr_fd close_sources_above2
    · exact setupStdioNoSave0_total s1 stdin_fd stdout_fd stderr_fd close_sources_above2
  | Err _ => exact okPost_ok _ _ trivial

/-- Trace extension relation asserting `s'.trace` preserves `s.trace` as a prefix. -/
def TraceExtends (s s' : ChildState) : Prop :=
  ∃ suf, s'.trace = s.trace ++ suf

/-- Reflexivity of `TraceExtends`. -/
theorem traceExtends_refl (s : ChildState) : TraceExtends s s :=
  ⟨[], by simp⟩

/-- Transitivity of `TraceExtends`. -/
theorem traceExtends_trans {s1 s2 s3 : ChildState}
    (h12 : TraceExtends s1 s2) (h23 : TraceExtends s2 s3) : TraceExtends s1 s3 := by
  rcases h12 with ⟨t1, ht1⟩
  rcases h23 with ⟨t2, ht2⟩
  exact ⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩

private theorem runUnitSyscall_trace (s : ChildState) (req : Req) (forcedErr? : Option I32)
    (onOk onErr : ChildState → ChildState)
    (hOkTr : (onOk s).trace = s.trace) (hErrTr : (onErr s).trace = s.trace) :
    OkPost (runUnitSyscall s req forcedErr? onOk onErr) fun p => TraceExtends s p.2 := by
  by_cases hs : s.status = Status.running
  · obtain ⟨r, s', hEq, hSpec⟩ := runUnitSyscall_running s hs req forcedErr? onOk onErr
    rw [hEq]
    cases hf : currentFault s with
    | seccomp rawE =>
      simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
      exact okPost_ok _ _ ⟨_, rfl⟩
    | fail rawE =>
      cases forcedErr? with
      | some e =>
        simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, congrArg (· ++ _) hErrTr⟩
      | none =>
        simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, congrArg (· ++ _) hErrTr⟩
    | normal | partialWrite _ | dentsBatch _ =>
      cases forcedErr? with
      | some e =>
        simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, congrArg (· ++ _) hErrTr⟩
      | none =>
        simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, congrArg (· ++ _) hOkTr⟩
  · rw [runUnitSyscall_not_running s hs]; exact okPost_ok _ _ (traceExtends_refl s)

private theorem runI32Syscall_trace (s : ChildState) (req : Req) (forcedErr? : Option I32)
    (onOk : ChildState → I32 × ChildState) (hOkTr : (onOk s).2.trace = s.trace) :
    OkPost (runI32Syscall s req forcedErr? onOk) fun p => TraceExtends s p.2 := by
  by_cases hs : s.status = Status.running
  · obtain ⟨r, s', hEq, hSpec⟩ := runI32Syscall_running s hs req forcedErr? onOk
    rw [hEq]
    cases hf : currentFault s with
    | seccomp rawE =>
      simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
      exact okPost_ok _ _ ⟨_, rfl⟩
    | fail rawE =>
      cases forcedErr? with
      | some e =>
        simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, rfl⟩
      | none =>
        simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, rfl⟩
    | normal | partialWrite _ | dentsBatch _ =>
      cases forcedErr? with
      | some e =>
        simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, rfl⟩
      | none =>
        simp only [hf] at hSpec; rcases hSpec with ⟨_, rfl⟩
        exact okPost_ok _ _ ⟨_, congrArg (· ++ _) hOkTr⟩
  · rw [runI32Syscall_not_running s hs]; exact okPost_ok _ _ (traceExtends_refl s)

/-- Trace-extension specification for `sys.close`. -/
theorem sys_close_trace (s : ChildState) (fd : I32) :
    OkPost (sys.close s fd) fun p => TraceExtends s p.2 :=
  runUnitSyscall_trace s _ _ _ _ rfl rfl

private theorem sys_dup2_trace (s : ChildState) (oldfd newfd : I32) :
    OkPost (sys.dup2 s oldfd newfd) fun p => TraceExtends s p.2 := by
  unfold sys.dup2 LeanSwe.PostFork.Aeneas.Internal.Sys.dup2
  exact runUnitSyscall_trace s _ _ _ _ (by split <;> [rfl; cases s.getFd ↑oldfd <;> rfl]) rfl

/-- Trace-extension specification for `sys.fcntl_getfd`. -/
theorem sys_fcntl_getfd_trace (s : ChildState) (fd : I32) :
    OkPost (sys.fcntl_getfd s fd) fun p => TraceExtends s p.2 := by
  unfold sys.fcntl_getfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_getfd
  cases s.getFd ↑fd <;> exact runI32Syscall_trace s _ _ _ rfl

private theorem sys_fcntl_setfd_trace (s : ChildState) (fd flags : I32) :
    OkPost (sys.fcntl_setfd s fd flags) fun p => TraceExtends s p.2 := by
  unfold sys.fcntl_setfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_setfd
  cases s.getFd ↑fd <;>
    exact runUnitSyscall_trace s _ _ _ _ (by cases s.getFd ↑fd <;> rfl) rfl

/-- Trace-extension specification for `sys.fcntl_dupfd_cloexec`. -/
theorem sys_fcntl_dupfd_cloexec_trace (s : ChildState) (fd minFd : I32) :
    OkPost (sys.fcntl_dupfd_cloexec s fd minFd) fun p => TraceExtends s p.2 := by
  unfold sys.fcntl_dupfd_cloexec LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_dupfd_cloexec
  cases s.getFd ↑fd with
  | none => exact runI32Syscall_trace s _ _ _ rfl
  | some e =>
    dsimp only
    split
    · exact runI32Syscall_trace s _ _ _ rfl
    · cases findLowestFreeFd s ↑minFd <;> exact runI32Syscall_trace s _ _ _ rfl

/-- Trace-extension specification for `postfork.fd_ops.clear_cloexec`. -/
theorem clear_cloexec_trace (s : ChildState) (fd : I32) :
    OkPost (postfork.fd_ops.clear_cloexec s fd) fun p => TraceExtends s p.2 := by
  unfold postfork.fd_ops.clear_cloexec
  refine okPost_bind (sys_fcntl_getfd_trace s fd) fun p h1 => ?_
  rcases p with ⟨r, s1⟩
  dsimp only at h1
  cases r with
  | Err _ => exact okPost_ok _ _ h1
  | Ok flags =>
    refine okPost_bind (okPost_lift _ _ rfl) fun i _ => ?_
    refine okPost_bind (okPost_lift _ _ rfl) fun i1 _ => ?_
    exact okPost_mono (sys_fcntl_setfd_trace s1 fd i1) fun q hq => traceExtends_trans h1 hq

/-- Trace-extension specification for `postfork.fd_ops.probe_stdio_open`. -/
theorem probe_stdio_open_trace (s : ChildState) (stdin_fd stdout_fd stderr_fd : I32) :
    OkPost (postfork.fd_ops.probe_stdio_open s stdin_fd stdout_fd stderr_fd) fun p => TraceExtends s p.2 := by
  unfold postfork.fd_ops.probe_stdio_open
  split
  · exact okPost_ok _ _ (traceExtends_refl s)
  · split
    · exact okPost_ok _ _ (traceExtends_refl s)
    · split
      · exact okPost_ok _ _ (traceExtends_refl s)
      · refine okPost_bind (sys_fcntl_getfd_trace s stdin_fd) fun p1 h1 => ?_
        rcases p1 with ⟨r0, s1⟩
        dsimp only at h1
        cases r0 with
        | Err _ => exact okPost_ok _ _ h1
        | Ok _ =>
          refine okPost_bind (sys_fcntl_getfd_trace s1 stdout_fd) fun p2 h2 => ?_
          rcases p2 with ⟨r1, s2⟩
          dsimp only at h2
          cases r1 with
          | Err _ => exact okPost_ok _ _ (traceExtends_trans h1 h2)
          | Ok _ =>
            refine okPost_bind (sys_fcntl_getfd_trace s2 stderr_fd) fun p3 h3 => ?_
            rcases p3 with ⟨r2, s3⟩
            dsimp only at h3
            cases r2 <;> exact okPost_ok _ _ (traceExtends_trans (traceExtends_trans h1 h2) h3)

private theorem setupStdioClear012_trace (s : sys.Sys) :
    OkPost (setupStdioClear012 s) fun p => TraceExtends s p.2 := by
  unfold setupStdioClear012
  refine okPost_bind (clear_cloexec_trace s 0#i32) fun p1 h1 => ?_
  rcases p1 with ⟨r6, s10⟩
  dsimp only at h1
  cases r6 with
  | Ok _ =>
    refine okPost_bind (clear_cloexec_trace s10 1#i32) fun p2 h2 => ?_
    rcases p2 with ⟨r7, s12⟩
    dsimp only at h2
    cases r7 with
    | Ok _ => exact okPost_mono (clear_cloexec_trace s12 2#i32) fun q hq => traceExtends_trans (traceExtends_trans h1 h2) hq
    | Err _ => exact okPost_ok _ _ (traceExtends_trans h1 h2)
  | Err _ => exact okPost_ok _ _ h1

private theorem setupStdioCloseAbove2_trace (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32) :
    OkPost (setupStdioCloseAbove2 s stdin_fd stdout_fd stderr_fd) fun s' => TraceExtends s s' := by
  unfold setupStdioCloseAbove2
  refine okPost_bind (P := fun s' => TraceExtends s s')
    (by split <;> [exact okPost_bind (sys_close_trace s _) fun _ hp => okPost_ok _ _ hp; exact okPost_ok _ _ (traceExtends_refl s)])
    fun s10 h1 => ?_
  refine okPost_bind (P := fun s' => TraceExtends s s')
    (by split <;> [split <;> [exact okPost_bind (sys_close_trace s10 _) fun _ hp => okPost_ok _ _ (traceExtends_trans h1 hp); exact okPost_ok _ _ h1]; exact okPost_ok _ _ h1])
    fun s12 h2 => ?_
  split <;> [split <;> [split <;> [exact okPost_bind (sys_close_trace s12 _) fun _ hp => okPost_ok _ _ (traceExtends_trans h2 hp); exact okPost_ok _ _ h2]; exact okPost_ok _ _ h2]; exact okPost_ok _ _ h2]

private theorem setupStdioFinish_trace (s : sys.Sys) (tmp0 tmp1 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioFinish s tmp0 tmp1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      TraceExtends s p.2 := by
  unfold setupStdioFinish
  refine okPost_bind (P := fun s' => TraceExtends s s')
    (by split <;> [exact okPost_bind (sys_close_trace s _) fun _ hp => okPost_ok _ _ hp; exact okPost_ok _ _ (traceExtends_refl s)])
    fun s7 h1 => ?_
  refine okPost_bind (P := fun s' => TraceExtends s s')
    (by split <;> [exact okPost_bind (sys_close_trace s7 _) fun _ hp => okPost_ok _ _ (traceExtends_trans h1 hp); exact okPost_ok _ _ h1])
    fun s8 h2 => ?_
  refine okPost_bind (P := fun s' => TraceExtends s s')
    (by split <;> [exact okPost_mono (setupStdioCloseAbove2_trace s8 _ _ _) fun s' hs' => traceExtends_trans h2 hs'; exact okPost_ok _ _ h2])
    fun s9 h3 => ?_
  exact okPost_mono (setupStdioClear012_trace s9) fun q hq => traceExtends_trans h3 hq

private theorem setupStdioCloseTmpsErr_trace (s : sys.Sys) (tmp0 tmp1 : I32)
    (r : core.result.Result Unit I32) :
    OkPost (setupStdioCloseTmpsErr s tmp0 tmp1 r) fun p => TraceExtends s p.2 := by
  unfold setupStdioCloseTmpsErr
  refine okPost_bind (P := fun s' => TraceExtends s s')
    (by split <;> [exact okPost_bind (sys_close_trace s _) fun _ hp => okPost_ok _ _ hp; exact okPost_ok _ _ (traceExtends_refl s)])
    fun s7 h1 => ?_
  split <;> [exact okPost_bind (sys_close_trace s7 _) fun _ hp => okPost_ok _ _ (traceExtends_trans h1 hp); exact okPost_ok _ _ h1]

private theorem setupStdioDup12Direct_trace (s : sys.Sys) (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2)
      fun p => TraceExtends s p.2 := by
  unfold setupStdioDup12Direct
  refine okPost_bind (sys_dup2_trace s s11 1#i32) fun p1 h1 => ?_
  rcases p1 with ⟨r3, s4⟩
  dsimp only at h1
  cases r3 with
  | Ok _ =>
    refine okPost_bind (sys_dup2_trace s4 s21 2#i32) fun p2 h2 => ?_
    rcases p2 with ⟨r4, s5⟩
    dsimp only at h2
    have h12 := traceExtends_trans h1 h2
    cases r4 with
    | Ok _ => exact okPost_mono (setupStdioFinish_trace s5 tmp0 (-1)#i32 stdin_fd stdout_fd stderr_fd close_sources_above2) fun q hq => traceExtends_trans h12 hq
    | Err _ => exact okPost_mono (setupStdioCloseTmpsErr_trace s5 tmp0 (-1)#i32 _) fun q hq => traceExtends_trans h12 hq
  | Err _ => exact okPost_mono (setupStdioCloseTmpsErr_trace s4 tmp0 (-1)#i32 _) fun q hq => traceExtends_trans h1 hq

private theorem setupStdioAfterDup0_trace (s : sys.Sys) (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioAfterDup0 s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2)
      fun p => TraceExtends s p.2 := by
  unfold setupStdioAfterDup0
  split
  · split
    · refine okPost_bind (sys_fcntl_dupfd_cloexec_trace s 1#i32 3#i32) fun p1 h1 => ?_
      rcases p1 with ⟨r3, s4⟩
      dsimp only at h1
      cases r3 with
      | Ok fd1 =>
        refine okPost_bind (sys_dup2_trace s4 s11 1#i32) fun p2 h2 => ?_
        rcases p2 with ⟨r4, s5⟩
        dsimp only at h2
        have h12 := traceExtends_trans h1 h2
        cases r4 with
        | Ok _ =>
          refine okPost_bind (sys_dup2_trace s5 fd1 2#i32) fun p3 h3 => ?_
          rcases p3 with ⟨r5, s6⟩
          dsimp only at h3
          have h13 := traceExtends_trans h12 h3
          cases r5 with
          | Ok _ => exact okPost_mono (setupStdioFinish_trace s6 tmp0 fd1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun q hq => traceExtends_trans h13 hq
          | Err _ => exact okPost_mono (setupStdioCloseTmpsErr_trace s6 tmp0 fd1 _) fun q hq => traceExtends_trans h13 hq
        | Err _ => exact okPost_mono (setupStdioCloseTmpsErr_trace s5 tmp0 fd1 _) fun q hq => traceExtends_trans h12 hq
      | Err _ =>
        split <;> [exact okPost_bind (sys_close_trace s4 _) fun _ hp => okPost_ok _ _ (traceExtends_trans h1 hp); exact okPost_ok _ _ h1]
    · exact setupStdioDup12Direct_trace s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
  · exact setupStdioDup12Direct_trace s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2

private theorem setupStdioSave0_trace (s1 : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      TraceExtends s1 p.2 := by
  unfold setupStdioSave0
  refine okPost_bind (sys_fcntl_dupfd_cloexec_trace s1 0#i32 3#i32) fun p1 h1 => ?_
  rcases p1 with ⟨r1, s2⟩
  dsimp only at h1
  cases r1 with
  | Ok fd =>
    refine okPost_bind (P := fun _ => True) (by split <;> exact okPost_ok _ _ trivial) fun s11 _ => ?_
    refine okPost_bind (P := fun _ => True) (by split <;> exact okPost_ok _ _ trivial) fun s21 _ => ?_
    refine okPost_bind (sys_dup2_trace s2 stdin_fd 0#i32) fun p2 h2 => ?_
    rcases p2 with ⟨r2, s3⟩
    dsimp only at h2
    have h12 := traceExtends_trans h1 h2
    cases r2 with
    | Ok _ => exact okPost_mono (setupStdioAfterDup0_trace s3 fd s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2) fun q hq => traceExtends_trans h12 hq
    | Err _ => split <;> [exact okPost_bind (sys_close_trace s3 _) fun _ hp => okPost_ok _ _ (traceExtends_trans h12 hp); exact okPost_ok _ _ h12]
  | Err _ => exact okPost_ok _ _ h1

private theorem setupStdioNoSave0_trace (s1 : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      TraceExtends s1 p.2 := by
  unfold setupStdioNoSave0
  refine okPost_bind (sys_dup2_trace s1 stdin_fd 0#i32) fun p1 h1 => ?_
  rcases p1 with ⟨r1, s2⟩
  dsimp only at h1
  cases r1 with
  | Ok _ => exact okPost_mono (setupStdioAfterDup0_trace s2 (-1)#i32 stdout_fd stderr_fd stdin_fd stdout_fd stderr_fd close_sources_above2) fun q hq => traceExtends_trans h1 hq
  | Err _ => split <;> [exact okPost_bind (sys_close_trace s2 _) fun _ hp => okPost_ok _ _ (traceExtends_trans h1 hp); exact okPost_ok _ _ h1]

/-- Trace-extension specification for `postfork.fd_ops.setup_stdio`. -/
theorem setup_stdio_trace (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    OkPost (postfork.fd_ops.setup_stdio s stdin_fd stdout_fd stderr_fd close_sources_above2)
      (fun p => ∃ suf, p.2.trace = s.trace ++ suf) := by
  rw [setup_stdio_eq_factored]
  refine okPost_bind (probe_stdio_open_trace s stdin_fd stdout_fd stderr_fd) fun p1 h1 => ?_
  rcases p1 with ⟨r, s1⟩
  dsimp only at h1
  cases r with
  | Ok _ =>
    split
    · split
      · exact okPost_mono (setupStdioSave0_trace s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun q hq => traceExtends_trans h1 hq
      · split
        · exact okPost_mono (setupStdioSave0_trace s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun q hq => traceExtends_trans h1 hq
        · exact okPost_mono (setupStdioNoSave0_trace s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun q hq => traceExtends_trans h1 hq
    · exact okPost_mono (setupStdioNoSave0_trace s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun q hq => traceExtends_trans h1 hq
  | Err _ => exact okPost_ok _ _ h1

private theorem setupStdioClear012_spec (s : sys.Sys) (hRun : s.status = .running) (hOr : s.oracle = [])
    {e0 e1 e2 : FdEntry} (h0 : s.getFd 0 = some e0) (h1 : s.getFd 1 = some e1)
    (h2 : s.getFd 2 = some e2) :
    OkPost (setupStdioClear012 s) fun p =>
      p.1 = .Ok () ∧ SameChildConfig p.2 s ∧
        (∃ f0, p.2.getFd 0 = some f0 ∧ f0.desc = e0.desc ∧ f0.cloexec = false) ∧
        (∃ f1, p.2.getFd 1 = some f1 ∧ f1.desc = e1.desc ∧ f1.cloexec = false) ∧
        (∃ f2, p.2.getFd 2 = some f2 ∧ f2.desc = e2.desc ∧ f2.cloexec = false) ∧
        (∀ k > 2, p.2.getFd k = s.getFd k) := by
  unfold setupStdioClear012
  refine okPost_bind (clear_cloexec_spec s hRun hOr 0#i32) fun ⟨r6, s10⟩ ⟨hct0, hcfg0, _⟩ => ?_
  change CloexecTogglePost false s 0#i32 r6 s10 at hct0
  simp only [CloexecTogglePost, show (0#i32 : I32).val = 0 by decide, h0] at hct0
  rcases hct0 with ⟨hr6, hs10_0, hs10_ne⟩
  subst hr6
  refine okPost_bind (clear_cloexec_spec s10 (hcfg0.status ▸ hRun) (hcfg0.oracle ▸ hOr) 1#i32)
    fun ⟨r7, s12⟩ ⟨hct1, hcfg1, _⟩ => ?_
  change CloexecTogglePost false s10 1#i32 r7 s12 at hct1
  have hs10_1 : s10.getFd 1 = some e1 := by rw [hs10_ne 1 (by omega), h1]
  simp only [CloexecTogglePost, show (1#i32 : I32).val = 1 by decide, hs10_1] at hct1
  rcases hct1 with ⟨hr7, hs12_1, hs12_ne⟩
  subst hr7
  refine okPost_mono (clear_cloexec_spec s12 ((hcfg1.trans hcfg0).status ▸ hRun) ((hcfg1.trans hcfg0).oracle ▸ hOr) 2#i32) ?_
  rintro ⟨r8, s13⟩ ⟨hct2, hcfg2, _⟩
  change CloexecTogglePost false s12 2#i32 r8 s13 at hct2
  have hs12_2 : s12.getFd 2 = some e2 := by
    rw [hs12_ne 2 (by omega), hs10_ne 2 (by omega), h2]
  simp only [CloexecTogglePost, show (2#i32 : I32).val = 2 by decide, hs12_2] at hct2
  rcases hct2 with ⟨hr8, hs13_2, hs13_ne⟩
  have hs13_0 : s13.getFd 0 = some { desc := e0.desc, cloexec := false, extraFdFlags := expectedExtraFlagsAfterSetfd s e0 } := by
    rw [hs13_ne 0 (by omega), hs12_ne 0 (by omega), hs10_0]
  have hs13_1 : s13.getFd 1 = some { desc := e1.desc, cloexec := false, extraFdFlags := expectedExtraFlagsAfterSetfd s10 e1 } := by
    rw [hs13_ne 1 (by omega), hs12_1]
  refine ⟨hr8, hcfg2.trans (hcfg1.trans hcfg0),
    ⟨_, hs13_0, rfl, rfl⟩, ⟨_, hs13_1, rfl, rfl⟩, ⟨_, hs13_2, rfl, rfl⟩, fun k hk => ?_⟩
  rw [hs13_ne k (by omega), hs12_ne k (by omega), hs10_ne k (by omega)]

private theorem setupStdioCloseAbove2_spec (s : sys.Sys) (hRun : s.status = .running) (hOr : s.oracle = [])
    (stdin_fd stdout_fd stderr_fd : I32) :
    OkPost (setupStdioCloseAbove2 s stdin_fd stdout_fd stderr_fd) fun s' =>
      SameChildConfig s' s ∧
        (∀ k ≤ 2, s'.getFd k = s.getFd k) ∧
        (∀ k > 2, s'.getFd k =
          if (k == stdin_fd.val || k == stdout_fd.val || k == stderr_fd.val) = true then none else s.getFd k) := by
  unfold setupStdioCloseAbove2
  have h1 : OkPost (if stdin_fd > 2#i32 then do let (_, s12) ← sys.close s stdin_fd; Result.ok s12 else Result.ok s)
      fun s10 => SameChildConfig s10 s ∧
        (∀ k ≤ 2, s10.getFd k = s.getFd k) ∧
        (∀ k > 2, s10.getFd k = if (k == stdin_fd.val) = true then none else s.getFd k) := by
    by_cases hgt : stdin_fd > 2#i32
    · simp only [hgt, ↓reduceIte]
      refine okPost_bind (sys_close_spec s hRun hOr stdin_fd) fun ⟨_, s12⟩ ⟨hcfg, _, _, _, _, _, hget⟩ => ?_
      refine okPost_ok _ _ ⟨hcfg, fun k hk => ?_, fun k _ => ?_⟩
      · rw [hget k]; simp [show k ≠ stdin_fd.val by scalar_tac]
      · rw [hget k]; by_cases hke : k = stdin_fd.val <;> simp [hke]
    · simp only [hgt, ↓reduceIte]
      refine okPost_ok _ _ ⟨SameChildConfig.refl s, fun _ _ => rfl, fun k hk => ?_⟩
      have hne : (k == stdin_fd.val) = false := beq_false_of_ne (by scalar_tac)
      simp [hne]
  refine okPost_bind h1 fun s10 ⟨hcfg1, hle1, hgt1⟩ => ?_
  have h2 : OkPost (if stdout_fd > 2#i32 then if (stdout_fd != stdin_fd) = true then do let (_, s13) ← sys.close s10 stdout_fd; Result.ok s13 else Result.ok s10 else Result.ok s10)
      fun s12 => SameChildConfig s12 s ∧
        (∀ k ≤ 2, s12.getFd k = s.getFd k) ∧
        (∀ k > 2, s12.getFd k = if (k == stdin_fd.val || k == stdout_fd.val) = true then none else s.getFd k) := by
    by_cases hgt : stdout_fd > 2#i32
    · by_cases hne : (stdout_fd != stdin_fd) = true
      · simp only [hgt, ↓reduceIte, hne]
        refine okPost_bind (sys_close_spec s10 (hcfg1.status ▸ hRun) (hcfg1.oracle ▸ hOr) stdout_fd)
          fun ⟨_, s13⟩ ⟨hcfg2, _, _, _, _, _, hget2⟩ => ?_
        refine okPost_ok _ _ ⟨hcfg2.trans hcfg1, fun k hk => ?_, fun k hk => ?_⟩
        · rw [hget2 k, ite_eq_right (by scalar_tac)]; exact hle1 k hk
        · rw [hget2 k, hgt1 k hk]
          by_cases hk2 : k = stdout_fd.val <;> simp [hk2]
      · have heq : stdout_fd.val = stdin_fd.val := by
          have : ¬(stdout_fd ≠ stdin_fd) := by simpa using hne
          rw [not_not] at this
          rw [this]
        simp only [hgt, ↓reduceIte, hne]
        refine okPost_ok _ _ ⟨hcfg1, hle1, fun k hk => ?_⟩
        rw [hgt1 k hk, heq]; simp
    · simp only [hgt, ↓reduceIte]
      refine okPost_ok _ _ ⟨hcfg1, hle1, fun k hk => ?_⟩
      have hne : (k == stdout_fd.val) = false := beq_false_of_ne (by scalar_tac)
      simp [hgt1 k hk, hne]
  refine okPost_bind h2 fun s12 ⟨hcfg2, hle2, hgt2⟩ => ?_
  by_cases hgt : stderr_fd > 2#i32
  · by_cases hne1 : (stderr_fd != stdin_fd) = true
    · by_cases hne2 : (stderr_fd != stdout_fd) = true
      · simp only [hgt, ↓reduceIte, hne1, hne2]
        refine okPost_bind (sys_close_spec s12 (hcfg2.status ▸ hRun) (hcfg2.oracle ▸ hOr) stderr_fd)
          fun ⟨_, s13⟩ ⟨hcfg3, _, _, _, _, _, hget3⟩ => ?_
        refine okPost_ok _ _ ⟨hcfg3.trans hcfg2, fun k hk => ?_, fun k hk => ?_⟩
        · rw [hget3 k, ite_eq_right (by scalar_tac)]; exact hle2 k hk
        · rw [hget3 k, hgt2 k hk]
          by_cases hk3 : k = stderr_fd.val <;> simp [hk3]
      · have heq : stderr_fd.val = stdout_fd.val := by
          have : ¬(stderr_fd ≠ stdout_fd) := by simpa using hne2
          rw [not_not] at this; rw [this]
        simp only [hgt, ↓reduceIte, hne1, hne2]
        refine okPost_ok _ _ ⟨hcfg2, hle2, fun k hk => ?_⟩
        rw [hgt2 k hk, heq]; simp
    · have heq : stderr_fd.val = stdin_fd.val := by
        have : ¬(stderr_fd ≠ stdin_fd) := by simpa using hne1
        rw [not_not] at this; rw [this]
      simp only [hgt, ↓reduceIte, hne1]
      refine okPost_ok _ _ ⟨hcfg2, hle2, fun k hk => ?_⟩
      rw [hgt2 k hk, heq]; simp [Bool.or_comm]
  · simp only [hgt, ↓reduceIte]
    refine okPost_ok _ _ ⟨hcfg2, hle2, fun k hk => ?_⟩
    have hne : (k == stderr_fd.val) = false := beq_false_of_ne (by scalar_tac)
    simp [hgt2 k hk, hne]

private theorem setupStdioFinish_spec (s sOrig : sys.Sys) (tmp0 tmp1 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool)
    (hRun : s.status = .running) (hOr : s.oracle = [])
    {e0 e1 e2 f0 f1 f2 : FdEntry}
    (hs0 : s.getFd 0 = some f0) (hd0 : f0.desc = e0.desc)
    (hs1 : s.getFd 1 = some f1) (hd1 : f1.desc = e1.desc)
    (hs2 : s.getFd 2 = some f2) (hd2 : f2.desc = e2.desc)
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2)
    (ht0 : tmp0 < 0#i32 ∨ (3 ≤ tmp0.val ∧ sOrig.getFd tmp0.val = none))
    (ht1 : tmp1 < 0#i32 ∨ (3 ≤ tmp1.val ∧ sOrig.getFd tmp1.val = none))
    (hAbove : ∀ k > 2, k ≠ tmp0.val → k ≠ tmp1.val → s.getFd k = sOrig.getFd k) :
    OkPost (setupStdioFinish s tmp0 tmp1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.1 = .Ok () ∧ SetupStdioPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2 := by
  unfold setupStdioFinish
  have hClose1 : OkPost (if tmp1 ≥ 0#i32 then do let (_, s8) ← sys.close s tmp1; Result.ok s8 else Result.ok s)
      fun s7 => SameChildConfig s7 s ∧
        (∀ k ≤ 2, s7.getFd k = s.getFd k) ∧
        (∀ k > 2, k ≠ tmp0.val → s7.getFd k = sOrig.getFd k) := by
    by_cases h1 : tmp1 ≥ 0#i32
    · rcases ht1 with ht1neg | ⟨ht1_3, ht1_none⟩
      · exfalso; scalar_tac
      · simp only [h1, ↓reduceIte]
        refine okPost_bind (sys_close_spec s hRun hOr tmp1) fun ⟨_, s8⟩ ⟨hcfg, _, _, _, _, _, hget⟩ => ?_
        refine okPost_ok _ _ ⟨hcfg, fun k hk => ?_, fun k hk hne0 => ?_⟩
        · rw [hget k, ite_eq_right (by omega)]
        · rw [hget k]
          by_cases hke : k = tmp1.val
          · subst hke; simp [ht1_none]
          · simp only [hke, ↓reduceIte]; exact hAbove k hk hne0 hke
    · simp only [h1, ↓reduceIte]
      refine okPost_ok _ _ ⟨SameChildConfig.refl s, fun _ _ => rfl, fun k hk hne0 => ?_⟩
      have hne1 : k ≠ tmp1.val := by
        rcases ht1 with ht1neg | ⟨ht1_3, _⟩
        · scalar_tac
        · exfalso; apply h1; scalar_tac
      exact hAbove k hk hne0 hne1
  refine okPost_bind hClose1 fun s7 ⟨hcfg7, hle7, hgt7⟩ => ?_
  have hClose0 : OkPost (if tmp0 ≥ 0#i32 then do let (_, s9) ← sys.close s7 tmp0; Result.ok s9 else Result.ok s7)
      fun s8 => SameChildConfig s8 s ∧
        (∀ k ≤ 2, s8.getFd k = s.getFd k) ∧
        (∀ k > 2, s8.getFd k = sOrig.getFd k) := by
    by_cases h0 : tmp0 ≥ 0#i32
    · rcases ht0 with ht0neg | ⟨ht0_3, ht0_none⟩
      · exfalso; scalar_tac
      · simp only [h0, ↓reduceIte]
        refine okPost_bind (sys_close_spec s7 (hcfg7.status ▸ hRun) (hcfg7.oracle ▸ hOr) tmp0)
          fun ⟨_, s9⟩ ⟨hcfg, _, _, _, _, _, hget⟩ => ?_
        refine okPost_ok _ _ ⟨hcfg.trans hcfg7, fun k hk => ?_, fun k hk => ?_⟩
        · rw [hget k, ite_eq_right (by omega)]; exact hle7 k hk
        · rw [hget k]
          by_cases hke : k = tmp0.val
          · subst hke; simp [ht0_none]
          · simp only [hke, ↓reduceIte]; exact hgt7 k hk hke
    · simp only [h0, ↓reduceIte]
      refine okPost_ok _ _ ⟨hcfg7, hle7, fun k hk => ?_⟩
      have hne0 : k ≠ tmp0.val := by
        rcases ht0 with ht0neg | ⟨ht0_3, _⟩
        · scalar_tac
        · exfalso; apply h0; scalar_tac
      exact hgt7 k hk hne0
  refine okPost_bind hClose0 fun s8 ⟨hcfg8, hle8, hgt8⟩ => ?_
  have hCA2 : OkPost (if close_sources_above2 = true then setupStdioCloseAbove2 s8 stdin_fd stdout_fd stderr_fd else Result.ok s8)
      fun s9 => SameChildConfig s9 s ∧
        (∀ k ≤ 2, s9.getFd k = s.getFd k) ∧
        (∀ k > 2, s9.getFd k =
          if (close_sources_above2 && (k == stdin_fd.val || k == stdout_fd.val || k == stderr_fd.val)) = true then none else sOrig.getFd k) := by
    by_cases hca : close_sources_above2 = true
    · simp only [hca, ↓reduceIte]
      refine okPost_mono (setupStdioCloseAbove2_spec s8 (hcfg8.status ▸ hRun) (hcfg8.oracle ▸ hOr) stdin_fd stdout_fd stderr_fd) ?_
      rintro s9 ⟨hcfg9, hle9, hgt9⟩
      refine ⟨hcfg9.trans hcfg8, fun k hk => (hle9 k hk).trans (hle8 k hk), fun k hk => ?_⟩
      rw [hgt9 k hk, hgt8 k hk]; simp
    · have hcaf : close_sources_above2 = false := Bool.eq_false_iff.mpr hca
      simp only [hcaf, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      exact okPost_ok _ _ ⟨hcfg8, hle8, fun k hk => by simp [hgt8 k hk]⟩
  refine okPost_bind hCA2 fun s9 ⟨hcfg9, hle9, hgt9⟩ => ?_
  have hs9_0 : s9.getFd 0 = some f0 := by rw [hle9 0 (by omega), hs0]
  have hs9_1 : s9.getFd 1 = some f1 := by rw [hle9 1 (by omega), hs1]
  have hs9_2 : s9.getFd 2 = some f2 := by rw [hle9 2 (by omega), hs2]
  refine okPost_mono (setupStdioClear012_spec s9 (hcfg9.status ▸ hRun) (hcfg9.oracle ▸ hOr) hs9_0 hs9_1 hs9_2) ?_
  rintro ⟨r, s10⟩ ⟨hr, _, ⟨g0, hg0, hg0d, hg0c⟩, ⟨g1, hg1, hg1d, hg1c⟩, ⟨g2, hg2, hg2d, hg2c⟩, hs10_gt⟩
  refine ⟨hr, ⟨e0, g0, hOrig0, hg0, hg0d.trans hd0, hg0c⟩,
    ⟨e1, g1, hOrig1, hg1, hg1d.trans hd1, hg1c⟩,
    ⟨e2, g2, hOrig2, hg2, hg2d.trans hd2, hg2c⟩, fun k hk => ?_⟩
  rw [hs10_gt k hk, hgt9 k hk]

private theorem setupStdioDup12Direct_spec (s sOrig : sys.Sys)
    (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32) (close_sources_above2 : Bool)
    (hRun : s.status = .running) (hOr : s.oracle = [])
    (hNotCycle : ¬((s11 != 1#i32) = true ∧ s21 = 1#i32))
    (hLim : min sOrig.fdLimit 2147483648 ≥ 5 + Int.ofNat sOrig.fds.length)
    (hCfg : SameChildConfig s sOrig)
    {e0 e1 e2 f0 f1 f2 : FdEntry}
    (hs0 : s.getFd 0 = some f0) (hd0 : f0.desc = e0.desc)
    (hs11 : s.getFd s11.val = some f1) (hd1 : f1.desc = e1.desc)
    (hs21 : s.getFd s21.val = some f2) (hd2 : f2.desc = e2.desc)
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2)
    (ht0 : tmp0 < 0#i32 ∨ (3 ≤ tmp0.val ∧ sOrig.getFd tmp0.val = none))
    (hAbove : ∀ k > 2, k ≠ tmp0.val → s.getFd k = sOrig.getFd k) :
    OkPost (setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.1 = .Ok () ∧ SetupStdioPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2 := by
  unfold setupStdioDup12Direct
  have hLim' : min sOrig.fdLimit 2147483648 ≥ 5 + (sOrig.fds.length : ℤ) := by
    simpa [Int.ofNat_eq_natCast] using hLim
  have hsLim : 5 ≤ s.fdLimit := by rw [hCfg.fdLimit]; omega
  refine okPost_bind (sys_dup2_spec s hRun hOr s11 1#i32 hs11 (by decide) (by scalar_tac))
    fun p3 hp3 => ?_
  rcases p3 with ⟨r3, s4⟩
  rcases hp3 with ⟨hr3, hcfg4, _, _, _, _, _, ⟨g1, hg1, hg1d⟩, hne4⟩
  dsimp only at hr3 hcfg4 hg1 hg1d hne4
  rw [hr3]
  have hs4_0 : s4.getFd 0 = some f0 := by rw [hne4 0 (by decide), hs0]
  have hs4_21 : ∃ g2, s4.getFd s21.val = some g2 ∧ g2.desc = e2.desc := by
    by_cases h21_1 : s21.val = 1
    · have hs11_eq : s11 = 1#i32 := by
        by_contra hne
        apply hNotCycle
        refine ⟨by simpa using hne, ?_⟩
        apply Aeneas.Std.IScalar.eq_of_val_eq
        exact h21_1
      have hs11_1 : s11.val = 1 := congrArg Aeneas.Std.IScalar.val hs11_eq
      rw [h21_1]
      refine ⟨g1, hg1, ?_⟩
      have heq : f1 = f2 := Option.some.inj (by rw [← hs11, hs11_1, ← h21_1, hs21])
      rw [hg1d, heq, hd2]
    · refine ⟨f2, ?_, hd2⟩
      rw [hne4 s21.val h21_1, hs21]
  rcases hs4_21 with ⟨g2, hs4_s21, hg2d⟩
  refine okPost_bind (sys_dup2_spec s4 (hcfg4.status ▸ hRun) (hcfg4.oracle ▸ hOr) s21 2#i32 hs4_s21 (by decide) (by rw [hcfg4.fdLimit]; scalar_tac))
    fun p4 hp4 => ?_
  rcases p4 with ⟨r4, s5⟩
  rcases hp4 with ⟨hr4, hcfg5, _, _, _, _, _, ⟨g2', hg2', hg2'd⟩, hne5⟩
  dsimp only at hr4 hcfg5 hg2' hg2'd hne5
  rw [hr4]
  have hs5_0 : s5.getFd 0 = some f0 := by rw [hne5 0 (by decide), hs4_0]
  have hs5_1 : s5.getFd 1 = some g1 := by rw [hne5 1 (by decide)]; exact hg1
  refine setupStdioFinish_spec s5 sOrig tmp0 (-1)#i32 stdin_fd stdout_fd stderr_fd close_sources_above2
    ((hcfg5.trans hcfg4).status ▸ hRun) ((hcfg5.trans hcfg4).oracle ▸ hOr)
    hs5_0 hd0 hs5_1 (hg1d.trans hd1) hg2' (hg2'd.trans hg2d) hOrig0 hOrig1 hOrig2
    ht0 (Or.inl (by decide)) fun k hk hne0 _ => ?_
  rw [hne5 k (by scalar_tac), hne4 k (by scalar_tac), hAbove k hk hne0]

private theorem setupStdioAfterDup0_spec (s sOrig : sys.Sys)
    (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32) (close_sources_above2 : Bool)
    (hRun : s.status = .running) (hOr : s.oracle = [])
    (hLim : min sOrig.fdLimit 2147483648 ≥ 5 + Int.ofNat sOrig.fds.length)
    (hCfg : SameChildConfig s sOrig)
    {e0 e1 e2 f0 f1 f2 : FdEntry}
    (hs0 : s.getFd 0 = some f0) (hd0 : f0.desc = e0.desc)
    (hs11 : s.getFd s11.val = some f1) (hd1 : f1.desc = e1.desc)
    (hs21 : s.getFd s21.val = some f2) (hd2 : f2.desc = e2.desc)
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2)
    (ht0 : tmp0 < 0#i32 ∨ (3 ≤ tmp0.val ∧ sOrig.getFd tmp0.val = none))
    (hAbove : ∀ k > 2, k ≠ tmp0.val → s.getFd k = sOrig.getFd k) :
    OkPost (setupStdioAfterDup0 s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.1 = .Ok () ∧ SetupStdioPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2 := by
  unfold setupStdioAfterDup0
  have hLim' : min sOrig.fdLimit 2147483648 ≥ 5 + (sOrig.fds.length : ℤ) := by
    simpa [Int.ofNat_eq_natCast] using hLim
  by_cases h11 : (s11 != 1#i32) = true
  · by_cases h21 : s21 = 1#i32
    · simp only [h11, ↓reduceIte, h21]
      have h1_open : s.getFd (1#i32 : I32).val = some f2 := by
        simpa [h21] using hs21
      let bound : List ℤ := if tmp0 ≥ 0#i32 then tmp0.val :: sOrig.fds.map Prod.fst else sOrig.fds.map Prod.fst
      have hbound_len : bound.length ≤ sOrig.fds.length + 1 := by
        dsimp [bound]; split <;> simp
      have hcap : (3 : ℤ) + Int.ofNat bound.length < min s.fdLimit 2147483648 := by
        rw [hCfg.fdLimit]; simp only [Int.ofNat_eq_natCast]; omega
      have hmem : ∀ x, (3 : ℤ) ≤ x → s.isOpen x = true → x ∈ bound := by
        intro x hx3 hxopen
        dsimp [bound]
        by_cases hxt : x = tmp0.val
        · have ht0_nonneg : tmp0 ≥ 0#i32 := by
            rcases ht0 with ht0neg | ⟨ht0_3, _⟩
            · exfalso; scalar_tac
            · scalar_tac
          simp only [ht0_nonneg, ↓reduceIte, List.mem_cons]
          exact Or.inl hxt
        · have hsx : sOrig.isOpen x = true := by
            simpa [ChildState.isOpen, hAbove x (by omega) hxt] using hxopen
          have hmemOrig : x ∈ sOrig.fds.map Prod.fst := mem_map_fst_of_isOpen hsx
          split
          · exact List.mem_cons_of_mem _ hmemOrig
          · exact hmemOrig
      obtain ⟨dst, hFree⟩ := findLowestFreeFd_some_of_card_lt s 3 bound (by omega) hcap hmem
      have hsLim : 3 < s.fdLimit := by rw [hCfg.fdLimit]; omega
      refine okPost_bind (sys_fcntl_dupfd_cloexec_spec s hRun hOr 1#i32 3#i32 h1_open (by decide) hsLim hFree)
        fun p hp => ?_
      rcases p with ⟨r3, s4⟩
      rcases hp with ⟨fd1, hr3, _, hfd1_3, _, hnone_fd1, hcfg4, _, _, _, _, _, ⟨g2, hg2, hg2d⟩, hne4⟩
      dsimp only at hr3 hfd1_3 hnone_fd1 hcfg4 hg2 hg2d hne4
      rw [hr3]
      have hs4_0 : s4.getFd 0 = some f0 := by rw [hne4 0 (by scalar_tac), hs0]
      have hs4_11 : s4.getFd s11.val = some f1 := by
        have hne11 : s11.val ≠ fd1.val := by
          intro heq
          rw [heq, hnone_fd1] at hs11
          cases hs11
        rw [hne4 s11.val hne11, hs11]
      refine okPost_bind (sys_dup2_spec s4 (hcfg4.status ▸ hRun) (hcfg4.oracle ▸ hOr) s11 1#i32 hs4_11 (by decide) (by rw [hcfg4.fdLimit, hCfg.fdLimit]; scalar_tac))
        fun p4 hp4 => ?_
      rcases p4 with ⟨r4, s5⟩
      rcases hp4 with ⟨hr4, hcfg5, _, _, _, _, _, ⟨g1, hg1, hg1d⟩, hne5⟩
      dsimp only at hr4 hcfg5 hg1 hg1d hne5
      rw [hr4]
      have hs5_0 : s5.getFd 0 = some f0 := by rw [hne5 0 (by scalar_tac), hs4_0]
      have hs5_fd1 : s5.getFd fd1.val = some g2 := by rw [hne5 fd1.val (by scalar_tac), hg2]
      refine okPost_bind (sys_dup2_spec s5 ((hcfg5.trans hcfg4).status ▸ hRun) ((hcfg5.trans hcfg4).oracle ▸ hOr) fd1 2#i32 hs5_fd1 (by decide) (by rw [(hcfg5.trans hcfg4).fdLimit, hCfg.fdLimit]; scalar_tac))
        fun p5 hp5 => ?_
      rcases p5 with ⟨r5, s6⟩
      rcases hp5 with ⟨hr5, hcfg6, _, _, _, _, _, ⟨g2', hg2', hg2'd⟩, hne6⟩
      dsimp only at hr5 hcfg6 hg2' hg2'd hne6
      rw [hr5]
      have hs6_0 : s6.getFd 0 = some f0 := by rw [hne6 0 (by scalar_tac), hs5_0]
      have hs6_1 : s6.getFd 1 = some g1 := by rw [hne6 1 (by scalar_tac)]; simpa using hg1
      have hfd1OrigNone : sOrig.getFd fd1.val = none := by
        by_cases heqt0 : fd1.val = tmp0.val
        · rcases ht0 with ht0neg | ⟨_, ht0_none⟩
          · exfalso; scalar_tac
          · rw [heqt0]; exact ht0_none
        · rw [← hAbove fd1.val (by scalar_tac) heqt0, hnone_fd1]
      refine setupStdioFinish_spec s6 sOrig tmp0 fd1 stdin_fd stdout_fd stderr_fd close_sources_above2
        ((hcfg6.trans (hcfg5.trans hcfg4)).status ▸ hRun) ((hcfg6.trans (hcfg5.trans hcfg4)).oracle ▸ hOr)
        hs6_0 hd0 hs6_1 (hg1d.trans hd1) hg2' (hg2'd.trans (hg2d.trans hd2))
        hOrig0 hOrig1 hOrig2 ht0 (Or.inr ⟨by scalar_tac, hfd1OrigNone⟩) fun k hk hne0 hnefd1 => ?_
      rw [hne6 k (by scalar_tac), hne5 k (by scalar_tac), hne4 k hnefd1, hAbove k hk hne0]
    · simp only [h11, ↓reduceIte, h21]
      exact setupStdioDup12Direct_spec s sOrig tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
        hRun hOr (fun ⟨_, h⟩ => h21 h) hLim hCfg hs0 hd0 hs11 hd1 hs21 hd2 hOrig0 hOrig1 hOrig2 ht0 hAbove
  · simp only [h11]
    exact setupStdioDup12Direct_spec s sOrig tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
      hRun hOr (fun ⟨h, _⟩ => h11 h) hLim hCfg hs0 hd0 hs11 hd1 hs21 hd2 hOrig0 hOrig1 hOrig2 ht0 hAbove

private theorem setupStdioSave0_spec (s1 sOrig : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool)
    (hRun : s1.status = .running) (hOr : s1.oracle = [])
    (hFds : s1.fds = sOrig.fds)
    (hCfg : SameChildConfig s1 sOrig)
    (hZero : stdout_fd = 0#i32 ∨ stderr_fd = 0#i32)
    {e0 e1 e2 : FdEntry}
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2)
    (hLim : min sOrig.fdLimit 2147483648 ≥ 5 + Int.ofNat sOrig.fds.length) :
    OkPost (setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.1 = .Ok () ∧ SetupStdioPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2 := by
  unfold setupStdioSave0
  have hLim' : min sOrig.fdLimit 2147483648 ≥ 5 + (sOrig.fds.length : ℤ) := by
    simpa [Int.ofNat_eq_natCast] using hLim
  have heZero : ∃ eZ, s1.getFd (0#i32 : I32).val = some eZ ∧
      (stdout_fd = 0#i32 → eZ = e1) ∧ (stderr_fd = 0#i32 → eZ = e2) := by
    rcases hZero with h0 | h0
    · refine ⟨e1, ?_, fun _ => rfl, fun h0' => ?_⟩
      · change s1.getFd 0 = some e1
        rw [getFd_eq_of_fds_eq hFds, ← show stdout_fd.val = 0 by simp [h0]]
        exact hOrig1
      · have : some e1 = some e2 := by rw [← hOrig1, h0, ← h0', hOrig2]
        cases this; rfl
    · refine ⟨e2, ?_, fun h0' => ?_, fun _ => rfl⟩
      · change s1.getFd 0 = some e2
        rw [getFd_eq_of_fds_eq hFds, ← show stderr_fd.val = 0 by simp [h0]]
        exact hOrig2
      · have : some e2 = some e1 := by rw [← hOrig2, h0, ← h0', hOrig1]
        cases this; rfl
  rcases heZero with ⟨eZ, hs1_0, hz1, hz2⟩
  let bound := sOrig.fds.map Prod.fst
  have hcap : (3 : ℤ) + Int.ofNat bound.length < min s1.fdLimit 2147483648 := by
    dsimp [bound]; rw [hCfg.fdLimit]; simp; omega
  have hmem : ∀ x, (3 : ℤ) ≤ x → s1.isOpen x = true → x ∈ bound := by
    intro x _ hxopen
    have hsOrigOpen : sOrig.isOpen x = true := by
      simpa [ChildState.isOpen, getFd_eq_of_fds_eq hFds] using hxopen
    exact mem_map_fst_of_isOpen hsOrigOpen
  obtain ⟨dst, hFree⟩ := findLowestFreeFd_some_of_card_lt s1 3 bound (by omega) hcap hmem
  have hs1Lim : 3 < s1.fdLimit := by rw [hCfg.fdLimit]; omega
  refine okPost_bind (sys_fcntl_dupfd_cloexec_spec s1 hRun hOr 0#i32 3#i32 hs1_0 (by decide) hs1Lim hFree)
    fun p1 hp1 => ?_
  rcases p1 with ⟨r1, s2⟩
  rcases hp1 with ⟨fd, hr1, _, hfd_3, _, hnone_fd, hcfg2, _, _, _, _, _, ⟨gZ, hgZ, hgZd⟩, hne2⟩
  dsimp only at hr1 hfd_3 hnone_fd hcfg2 hgZ hgZd hne2
  rw [hr1]
  have hs1OrigNone : sOrig.getFd fd.val = none := by
    rw [← getFd_eq_of_fds_eq hFds]; exact hnone_fd
  have hs2_in : s2.getFd stdin_fd.val = some e0 := by
    have hne : stdin_fd.val ≠ fd.val := by
      intro heq
      rw [heq, hs1OrigNone] at hOrig0
      cases hOrig0
    rw [hne2 stdin_fd.val hne, getFd_eq_of_fds_eq hFds, hOrig0]
  have hs11Post : OkPost (if stdout_fd = 0#i32 then Result.ok fd else Result.ok stdout_fd)
      (fun v => v = if stdout_fd = 0#i32 then fd else stdout_fd) := by
    by_cases h : stdout_fd = 0#i32 <;> simp [h, okPost_ok]
  refine okPost_bind hs11Post fun s11 hs11eq => ?_
  have hs21Post : OkPost (if stderr_fd = 0#i32 then Result.ok fd else Result.ok stderr_fd)
      (fun v => v = if stderr_fd = 0#i32 then fd else stderr_fd) := by
    by_cases h : stderr_fd = 0#i32 <;> simp [h, okPost_ok]
  refine okPost_bind hs21Post fun s21 hs21eq => ?_
  subst hs11eq; subst hs21eq
  have hs2Lim : (0 : ℤ) < s2.fdLimit := by rw [hcfg2.fdLimit, hCfg.fdLimit]; omega
  refine okPost_bind (sys_dup2_spec s2 (hcfg2.status ▸ hRun) (hcfg2.oracle ▸ hOr) stdin_fd 0#i32 hs2_in (by decide) hs2Lim)
    fun p2 hp2 => ?_
  rcases p2 with ⟨r2, s3⟩
  rcases hp2 with ⟨hr2, hcfg3, _, _, _, _, _, ⟨f0, hf0, hf0d⟩, hne3⟩
  dsimp only at hr2 hcfg3 hf0 hf0d hne3
  rw [hr2]
  have hs3_11 : ∃ f1, s3.getFd (if stdout_fd = 0#i32 then fd else stdout_fd).val = some f1 ∧ f1.desc = e1.desc := by
    by_cases h : stdout_fd = 0#i32
    · simp only [h, ↓reduceIte]
      rw [hne3 fd.val (by scalar_tac)]
      exact ⟨gZ, hgZ, by rw [hgZd, hz1 h]⟩
    · simp only [h, ↓reduceIte]
      have hne0 : stdout_fd.val ≠ 0 := by
        intro hv; apply h; apply Aeneas.Std.IScalar.eq_of_val_eq; exact hv
      have hnefd : stdout_fd.val ≠ fd.val := by
        intro heq; rw [heq, hs1OrigNone] at hOrig1; cases hOrig1
      rw [hne3 stdout_fd.val hne0, hne2 stdout_fd.val hnefd, getFd_eq_of_fds_eq hFds]
      exact ⟨e1, hOrig1, rfl⟩
  have hs3_21 : ∃ f2, s3.getFd (if stderr_fd = 0#i32 then fd else stderr_fd).val = some f2 ∧ f2.desc = e2.desc := by
    by_cases h : stderr_fd = 0#i32
    · simp only [h, ↓reduceIte]
      rw [hne3 fd.val (by scalar_tac)]
      exact ⟨gZ, hgZ, by rw [hgZd, hz2 h]⟩
    · simp only [h, ↓reduceIte]
      have hne0 : stderr_fd.val ≠ 0 := by
        intro hv; apply h; apply Aeneas.Std.IScalar.eq_of_val_eq; exact hv
      have hnefd : stderr_fd.val ≠ fd.val := by
        intro heq; rw [heq, hs1OrigNone] at hOrig2; cases hOrig2
      rw [hne3 stderr_fd.val hne0, hne2 stderr_fd.val hnefd, getFd_eq_of_fds_eq hFds]
      exact ⟨e2, hOrig2, rfl⟩
  rcases hs3_11 with ⟨f1, hs3_f1, hf1d⟩
  rcases hs3_21 with ⟨f2, hs3_f2, hf2d⟩
  refine setupStdioAfterDup0_spec s3 sOrig fd _ _ stdin_fd stdout_fd stderr_fd close_sources_above2
    ((hcfg3.trans hcfg2).status ▸ hRun) ((hcfg3.trans hcfg2).oracle ▸ hOr) hLim
    (hcfg3.trans (hcfg2.trans hCfg)) hf0 hf0d hs3_f1 hf1d hs3_f2 hf2d hOrig0 hOrig1 hOrig2
    (Or.inr ⟨by scalar_tac, hs1OrigNone⟩) fun k hk hnefd => ?_
  rw [hne3 k (by scalar_tac), hne2 k hnefd, getFd_eq_of_fds_eq hFds]

private theorem setupStdioNoSave0_spec (s1 sOrig : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool)
    (hRun : s1.status = .running) (hOr : s1.oracle = [])
    (hFds : s1.fds = sOrig.fds)
    (hCfg : SameChildConfig s1 sOrig)
    (hNoSave : stdin_fd = 0#i32 ∨ (stdout_fd ≠ 0#i32 ∧ stderr_fd ≠ 0#i32))
    {e0 e1 e2 : FdEntry}
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2)
    (hLim : min sOrig.fdLimit 2147483648 ≥ 5 + Int.ofNat sOrig.fds.length) :
    OkPost (setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.1 = .Ok () ∧ SetupStdioPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2 := by
  unfold setupStdioNoSave0
  have hLim' : min sOrig.fdLimit 2147483648 ≥ 5 + (sOrig.fds.length : ℤ) := by
    simpa [Int.ofNat_eq_natCast] using hLim
  have hs1_in : s1.getFd stdin_fd.val = some e0 := by
    rw [getFd_eq_of_fds_eq hFds]; exact hOrig0
  have hs1Lim : (0 : ℤ) < s1.fdLimit := by rw [hCfg.fdLimit]; omega
  refine okPost_bind (sys_dup2_spec s1 hRun hOr stdin_fd 0#i32 hs1_in (by decide) hs1Lim)
    fun p1 hp1 => ?_
  rcases p1 with ⟨r1, s2⟩
  rcases hp1 with ⟨hr1, hcfg2, _, _, _, _, _, ⟨f0, hf0, hf0d⟩, hne2⟩
  dsimp only at hr1 hcfg2 hf0 hf0d hne2
  rw [hr1]
  have hs2_out : ∃ f1, s2.getFd stdout_fd.val = some f1 ∧ f1.desc = e1.desc := by
    by_cases h0 : stdout_fd.val = 0
    · have hstin : stdin_fd = 0#i32 := by
        rcases hNoSave with h | ⟨hneq, _⟩
        · exact h
        · exfalso; apply hneq; apply Aeneas.Std.IScalar.eq_of_val_eq; exact h0
      have he01 : e0 = e1 := by
        have : some e0 = some e1 := by
          rw [← hOrig0, hstin, show (0#i32 : I32).val = 0 by decide, ← h0, hOrig1]
        cases this; rfl
      rw [h0]
      exact ⟨f0, hf0, by rw [hf0d, he01]⟩
    · rw [hne2 stdout_fd.val h0, getFd_eq_of_fds_eq hFds]
      exact ⟨e1, hOrig1, rfl⟩
  have hs2_err : ∃ f2, s2.getFd stderr_fd.val = some f2 ∧ f2.desc = e2.desc := by
    by_cases h0 : stderr_fd.val = 0
    · have hstin : stdin_fd = 0#i32 := by
        rcases hNoSave with h | ⟨_, hneq⟩
        · exact h
        · exfalso; apply hneq; apply Aeneas.Std.IScalar.eq_of_val_eq; exact h0
      have he02 : e0 = e2 := by
        have : some e0 = some e2 := by
          rw [← hOrig0, hstin, show (0#i32 : I32).val = 0 by decide, ← h0, hOrig2]
        cases this; rfl
      rw [h0]
      exact ⟨f0, hf0, by rw [hf0d, he02]⟩
    · rw [hne2 stderr_fd.val h0, getFd_eq_of_fds_eq hFds]
      exact ⟨e2, hOrig2, rfl⟩
  rcases hs2_out with ⟨f1, hs2_f1, hf1d⟩
  rcases hs2_err with ⟨f2, hs2_f2, hf2d⟩
  refine setupStdioAfterDup0_spec s2 sOrig (-1)#i32 stdout_fd stderr_fd stdin_fd stdout_fd stderr_fd
    close_sources_above2 (hcfg2.status ▸ hRun) (hcfg2.oracle ▸ hOr) hLim (hcfg2.trans hCfg)
    hf0 hf0d hs2_f1 hf1d hs2_f2 hf2d hOrig0 hOrig1 hOrig2 (Or.inl (by decide)) fun k hk _ => ?_
  rw [hne2 k (by scalar_tac), getFd_eq_of_fds_eq hFds]

/-- Error specification for `postfork.fd_ops.setup_stdio` on negative input FDs. -/
theorem setup_stdio_neg_spec (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool)
    (hNeg : (decide (stdin_fd < 0#i32) || decide (stdout_fd < 0#i32) || decide (stderr_fd < 0#i32)) = true) :
    OkPost (postfork.fd_ops.setup_stdio s stdin_fd stdout_fd stderr_fd close_sources_above2)
      (fun p => p.1 = .Err EBADF ∧ p.2 = s) := by
  rw [setup_stdio_eq_factored]
  refine okPost_bind (probe_stdio_open_neg_spec s stdin_fd stdout_fd stderr_fd hNeg) fun p hp => ?_
  rcases p with ⟨r, s1⟩
  rcases hp with ⟨hr, hs1⟩
  dsimp only at hr hs1
  rw [hr, hs1]
  exact okPost_ok _ _ ⟨rfl, rfl⟩

/-- Error specification for `postfork.fd_ops.setup_stdio` when a non-negative input FD is closed. -/
theorem setup_stdio_not_open_spec (s : sys.Sys) (hRun : s.status = .running) (hOr : s.oracle = [])
    (stdin_fd stdout_fd stderr_fd : I32) (close_sources_above2 : Bool)
    (hNonNeg : 0#i32 ≤ stdin_fd ∧ 0#i32 ≤ stdout_fd ∧ 0#i32 ≤ stderr_fd)
    (hClosed : (!s.isOpen stdin_fd.val || !s.isOpen stdout_fd.val || !s.isOpen stderr_fd.val) = true) :
    OkPost (postfork.fd_ops.setup_stdio s stdin_fd stdout_fd stderr_fd close_sources_above2)
      (fun p => p.1 = .Err EBADF ∧ p.2.fds = s.fds) := by
  rw [setup_stdio_eq_factored]
  refine okPost_bind (probe_stdio_open_spec s hRun hOr stdin_fd stdout_fd stderr_fd) fun p hp => ?_
  rcases p with ⟨r, s1⟩
  rcases hp with ⟨_, hfds1, _, _, _, _, _, hres⟩
  dsimp only at hfds1 hres
  have hNegFalse : (decide (stdin_fd < 0#i32) || decide (stdout_fd < 0#i32) || decide (stderr_fd < 0#i32)) = false := by
    simp [show ¬(stdin_fd < 0#i32) by scalar_tac, show ¬(stdout_fd < 0#i32) by scalar_tac,
      show ¬(stderr_fd < 0#i32) by scalar_tac]
  have hOpenFalse : (s.isOpen stdin_fd.val && s.isOpen stdout_fd.val && s.isOpen stderr_fd.val) = false := by
    cases ho0 : s.isOpen stdin_fd.val <;> cases ho1 : s.isOpen stdout_fd.val <;>
      cases ho2 : s.isOpen stderr_fd.val <;> simp_all
  simp only [hNegFalse, Bool.false_eq_true, ↓reduceIte, hOpenFalse] at hres
  rw [hres]
  exact okPost_ok _ _ ⟨rfl, hfds1⟩

/-- Functional specification for `postfork.fd_ops.setup_stdio` on valid open inputs. -/
theorem setup_stdio_spec (s : sys.Sys) (hRun : s.status = .running) (hOr : s.oracle = [])
    (stdin_fd stdout_fd stderr_fd : I32) (close_sources_above2 : Bool)
    (hNonNeg : 0#i32 ≤ stdin_fd ∧ 0#i32 ≤ stdout_fd ∧ 0#i32 ≤ stderr_fd)
    (hOpen : s.isOpen stdin_fd.val = true ∧ s.isOpen stdout_fd.val = true ∧ s.isOpen stderr_fd.val = true)
    (hLim : min s.fdLimit 2147483648 ≥ 5 + Int.ofNat s.fds.length) :
    OkPost (postfork.fd_ops.setup_stdio s stdin_fd stdout_fd stderr_fd close_sources_above2)
      (fun p => p.1 = .Ok () ∧ SetupStdioPost s stdin_fd stdout_fd stderr_fd close_sources_above2 p.2) := by
  rw [setup_stdio_eq_factored]
  refine okPost_bind (probe_stdio_open_spec s hRun hOr stdin_fd stdout_fd stderr_fd) fun p hp => ?_
  rcases p with ⟨r, s1⟩
  rcases hp with ⟨hcfg1, hfds1, _, _, _, _, _, hres⟩
  dsimp only at hcfg1 hfds1 hres
  have hNegFalse : (decide (stdin_fd < 0#i32) || decide (stdout_fd < 0#i32) || decide (stderr_fd < 0#i32)) = false := by
    simp [show ¬(stdin_fd < 0#i32) by scalar_tac, show ¬(stdout_fd < 0#i32) by scalar_tac,
      show ¬(stderr_fd < 0#i32) by scalar_tac]
  have hOpenTrue : (s.isOpen stdin_fd.val && s.isOpen stdout_fd.val && s.isOpen stderr_fd.val) = true := by
    simp [hOpen.1, hOpen.2.1, hOpen.2.2]
  simp only [hNegFalse, Bool.false_eq_true, ↓reduceIte, hOpenTrue] at hres
  rw [hres]
  obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp (by simpa [isOpen_iff_isSome] using hOpen.1)
  obtain ⟨e1, he1⟩ := Option.isSome_iff_exists.mp (by simpa [isOpen_iff_isSome] using hOpen.2.1)
  obtain ⟨e2, he2⟩ := Option.isSome_iff_exists.mp (by simpa [isOpen_iff_isSome] using hOpen.2.2)
  have hRun1 : s1.status = .running := hcfg1.status ▸ hRun
  have hOr1 : s1.oracle = [] := hcfg1.oracle ▸ hOr
  by_cases hstin : (stdin_fd != 0#i32) = true
  · by_cases hstout : stdout_fd = 0#i32
    · have hs := setupStdioSave0_spec s1 s stdin_fd stdout_fd stderr_fd close_sources_above2
        hRun1 hOr1 hfds1 hcfg1 (Or.inl hstout) he0 he1 he2 hLim
      simp only [hstin, ↓reduceIte, hstout] at hs ⊢
      exact hs
    · by_cases hsterr : stderr_fd = 0#i32
      · have hs := setupStdioSave0_spec s1 s stdin_fd stdout_fd stderr_fd close_sources_above2
          hRun1 hOr1 hfds1 hcfg1 (Or.inr hsterr) he0 he1 he2 hLim
        simp only [hstin, ↓reduceIte, eq_false hstout, hsterr] at hs ⊢
        exact hs
      · simp only [hstin, ↓reduceIte, eq_false hstout, eq_false hsterr]
        exact setupStdioNoSave0_spec s1 s stdin_fd stdout_fd stderr_fd close_sources_above2
          hRun1 hOr1 hfds1 hcfg1 (Or.inr ⟨hstout, hsterr⟩) he0 he1 he2 hLim
  · have heq0 : stdin_fd = 0#i32 := Aeneas.Std.IScalar.eq_of_val_eq (by simpa using hstin)
    simp only [hstin, Bool.false_eq_true, ↓reduceIte]
    exact setupStdioNoSave0_spec s1 s stdin_fd stdout_fd stderr_fd close_sources_above2
      hRun1 hOr1 hfds1 hcfg1 (Or.inl heq0) he0 he1 he2 hLim

/-- Zero-hypothesis verification of `test_postfork_setupStdio_clobberFreePermutationsAndCycles` for `rustAeneasApi`. -/
theorem test_postfork_setupStdio_clobberFreePermutationsAndCycles_allPass :
    Core.AllPass (test_postfork_setupStdio_clobberFreePermutationsAndCycles rustAeneasApi) := by
  dsimp [Core.AllPass, test_postfork_setupStdio_clobberFreePermutationsAndCycles, rustAeneasApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, Bind.bind]
  intro s inFd outFd errFd closeAbove2
  by_cases hNeg : (decide (inFd < 0#i32) || decide (outFd < 0#i32) || decide (errFd < 0#i32)) = true
  · simp only [hNeg, ↓reduceIte]
    refine ⟨setup_stdio_neg_spec s inFd outFd errFd closeAbove2 hNeg, fun ⟨_, _⟩ hNonNeg => ?_⟩
    exfalso
    rcases hNonNeg with ⟨h0, h1, h2⟩
    simp [show ¬(inFd < 0#i32) by scalar_tac, show ¬(outFd < 0#i32) by scalar_tac,
      show ¬(errFd < 0#i32) by scalar_tac] at hNeg
  · simp only [hNeg, Bool.false_eq_true, ↓reduceIte]
    intro ⟨hRun, hOr⟩ hNonNeg
    by_cases hClosed : (!s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val) = true
    · simp only [hClosed, ↓reduceIte]
      refine ⟨setup_stdio_not_open_spec s hRun hOr inFd outFd errFd closeAbove2 hNonNeg hClosed,
        fun ⟨ho0, ho1, ho2⟩ _ => ?_⟩
      exfalso
      simp [ho0, ho1, ho2] at hClosed
    · simp only [hClosed, Bool.false_eq_true, ↓reduceIte]
      intro hOpen hLim
      exact ⟨setup_stdio_spec s hRun hOr inFd outFd errFd closeAbove2 hNonNeg hOpen hLim, trivial⟩

/-- Zero-hypothesis reachability of `test_postfork_setupStdio_clobberFreePermutationsAndCycles` for `rustAeneasApi`. -/
theorem test_postfork_setupStdio_clobberFreePermutationsAndCycles_canReach :
    Core.CanReach (test_postfork_setupStdio_clobberFreePermutationsAndCycles rustAeneasApi) := by
  let s : ChildState :=
    { fds := [(0, { desc := 10, cloexec := true }), (1, { desc := 11, cloexec := true }), (2, { desc := 12, cloexec := true })],
      fdLimit := 16 }
  dsimp [Core.CanReach, test_postfork_setupStdio_clobberFreePermutationsAndCycles, rustAeneasApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, Bind.bind]
  refine ⟨s, 2#i32, 0#i32, 1#i32, false, ?_⟩
  have hNeg : (decide (2#i32 < 0#i32) || decide (0#i32 < 0#i32) || decide (1#i32 < 0#i32)) = false := by decide
  have hClosed : (!s.isOpen (2#i32 : I32).val || !s.isOpen (0#i32 : I32).val || !s.isOpen (1#i32 : I32).val) = false := by
    simp [s, ChildState.isOpen, ChildState.getFd]
  simp only [hNeg, Bool.false_eq_true, ↓reduceIte, hClosed]
  refine ⟨⟨rfl, rfl⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by simp [s, ChildState.isOpen, ChildState.getFd],
     by simp [s, ChildState.isOpen, ChildState.getFd],
     by simp [s, ChildState.isOpen, ChildState.getFd]⟩,
    by simp [s], ?_, trivial⟩
  exact setup_stdio_spec s rfl rfl 2#i32 0#i32 1#i32 false ⟨by decide, by decide, by decide⟩
    ⟨by simp [s, ChildState.isOpen, ChildState.getFd],
     by simp [s, ChildState.isOpen, ChildState.getFd],
     by simp [s, ChildState.isOpen, ChildState.getFd]⟩ (by simp [s])

section CloseUnusedSlice

private theorem sys_close_step_total (s : sys.Sys) (fd : I32) :
    OkPost (sys.close s fd) fun p =>
      SameChildConfig p.2 s ∧
        p.2.descs = s.descs ∧
        p.2.trace.length ≤ s.trace.length + 1 ∧
        (∀ k, k ≠ fd.val → p.2.getFd k = s.getFd k) ∧
        (p.2.getFd fd.val = none ∨ p.2.getFd fd.val = s.getFd fd.val) := by
  unfold sys.close LeanSwe.PostFork.Aeneas.Internal.Sys.close runUnitSyscall
  cases hst : s.status with
  | running =>
    dsimp only
    cases currentFault s with
    | seccomp _ =>
      dsimp only
      exact okPost_ok _ _ ⟨⟨rfl, by simp [hst], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, by simp,
        fun _ _ => rfl, Or.inr rfl⟩
    | normal | partialWrite _ | dentsBatch _ | fail _ =>
      dsimp only
      split <;>
        exact okPost_ok _ _ ⟨⟨rfl, by simp [ChildState.closeSlot, hst], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, by simp [ChildState.closeSlot],
          fun k hk => getFd_closeSlot_ne s hk, Or.inl (getFd_closeSlot_self s _)⟩
  | exited _ =>
    exact okPost_ok _ _ ⟨SameChildConfig.refl s, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inr rfl⟩
  | signaled _ =>
    exact okPost_ok _ _ ⟨SameChildConfig.refl s, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inr rfl⟩
  | execd _ =>
    exact okPost_ok _ _ ⟨SameChildConfig.refl s, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inr rfl⟩

/-- Unconditional totality for `postfork.fd_ops.close_unused_slice`. -/
theorem close_unused_slice_total (s : sys.Sys) (fds : Slice I32) :
    OkPost (postfork.fd_ops.close_unused_slice s fds) (fun _ => True) := by
  unfold postfork.fd_ops.close_unused_slice postfork.fd_ops.close_unused_slice_loop
  refine okPost_loop_decr_nat
    (fun p => fds.len.val - p.2.val)
    (fun p => p.2 ≤ fds.len)
    (fun _ => True)
    (fun p => postfork.fd_ops.close_unused_slice_loop.body fds fds.len p.1 p.2)
    (s, 0#usize) ?_ (by scalar_tac)
  intro ⟨s1, idx⟩ hIdx
  unfold postfork.fd_ops.close_unused_slice_loop.body
  by_cases hlt : idx < fds.len
  · rcases slice_idx_succ fds hlt with ⟨hjlt, hidx, idx1, hinc, hval⟩
    simp only [hlt, ↓reduceIte]
    rw [hidx, bind_ok]
    have hstep : OkPost (if fds.val[idx.val] ≥ 0#i32 then do let (_, s2) ← sys.close s1 fds.val[idx.val]; Result.ok s2
        else Result.ok s1) (fun _ => True) := by
      by_cases hnonneg : fds.val[idx.val] ≥ 0#i32
      · simp only [hnonneg, ↓reduceIte]
        exact okPost_bind (sys_close_step_total s1 fds.val[idx.val]) fun _ _ => okPost_ok _ _ trivial
      · simp only [hnonneg, ↓reduceIte]
        exact okPost_ok _ _ trivial
    refine okPost_bind hstep fun s2 _ => ?_
    rw [hinc, bind_ok]
    refine okPost_ok _ _ ⟨?_, ?_⟩
    · change idx1.val ≤ fds.len.val; rw [hval]; exact hjlt
    · dsimp; rw [hval]; exact Nat.sub_succ_lt_self fds.len.val idx.val hjlt
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok _ _ trivial

private theorem sliceContainsNonnegSpec_eq_any (xs : List I32) (k : ℤ) :
    Model.sliceContainsNonnegSpec xs k = true ↔ (0 ≤ k ∧ ∃ x ∈ xs, x.val = k) := by
  simp [Model.sliceContainsNonnegSpec]

/-- Functional specification for `postfork.fd_ops.close_unused_slice`. -/
theorem close_unused_slice_spec (s : sys.Sys) (hRun : s.status = .running) (hOr : s.oracle = [])
    (fds : Slice I32) :
    OkPost (postfork.fd_ops.close_unused_slice s fds) fun s' =>
      SameChildConfig s' s ∧
        s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
        s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
        ∀ k, s'.getFd k = if Model.sliceContainsNonnegSpec fds.val k = true then none else s.getFd k := by
  unfold postfork.fd_ops.close_unused_slice postfork.fd_ops.close_unused_slice_loop
  let inv : sys.Sys × Usize → Prop := fun p =>
    SameChildConfig p.1 s ∧ p.1.pgid = s.pgid ∧ p.1.cwd = s.cwd ∧ p.1.sig = s.sig ∧
      p.1.descs = s.descs ∧ p.1.writeLog = s.writeLog ∧ p.2 ≤ fds.len ∧
      ∀ k, p.1.getFd k =
        if Model.sliceContainsNonnegSpec (fds.val.take p.2.val) k = true then none else s.getFd k
  refine okPost_loop_decr_nat (fun p => fds.len.val - p.2.val) inv
    (fun s' => SameChildConfig s' s ∧ s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      ∀ k, s'.getFd k = if Model.sliceContainsNonnegSpec fds.val k = true then none else s.getFd k)
    (fun p => postfork.fd_ops.close_unused_slice_loop.body fds fds.len p.1 p.2)
    (s, 0#usize) ?_ ⟨SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, by scalar_tac, fun k => by simp [Model.sliceContainsNonnegSpec]⟩
  intro ⟨s1, idx⟩ hinv
  rcases hinv with ⟨hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, hidxLe, hget1⟩
  unfold postfork.fd_ops.close_unused_slice_loop.body
  by_cases hlt : idx < fds.len
  · rcases slice_idx_succ fds hlt with ⟨hjlt, hidx, idx1, hinc, hval⟩
    simp only [hlt, ↓reduceIte]
    rw [hidx, bind_ok]
    have hstep : OkPost (if fds.val[idx.val] ≥ 0#i32 then do let (_, s2) ← sys.close s1 fds.val[idx.val]; Result.ok s2
        else Result.ok s1)
        fun s2 => SameChildConfig s2 s ∧ s2.pgid = s.pgid ∧ s2.cwd = s.cwd ∧ s2.sig = s.sig ∧
          s2.descs = s.descs ∧ s2.writeLog = s.writeLog ∧
          ∀ k, s2.getFd k =
            if Model.sliceContainsNonnegSpec (fds.val.take (idx.val + 1)) k = true then none else s.getFd k := by
      have htakeSucc : fds.val.take (idx.val + 1) = fds.val.take idx.val ++ [fds.val[idx.val]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hjlt]; rfl
      by_cases hnonneg : fds.val[idx.val] ≥ 0#i32
      · simp only [hnonneg, ↓reduceIte]
        refine okPost_bind (sys_close_spec s1 (hcfg1.status ▸ hRun) (hcfg1.oracle ▸ hOr) fds.val[idx.val])
          fun p2 hp2 => ?_
        rcases p2 with ⟨_, s2⟩
        rcases hp2 with ⟨hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hget2⟩
        dsimp only at hcfg2 hpg2 hcwd2 hsig2 hdescs2 hwl2 hget2
        refine okPost_ok _ _ ⟨hcfg2.trans hcfg1, hpg2.trans hpg1, hcwd2.trans hcwd1,
          hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1, fun k => ?_⟩
        rw [hget2 k, hget1 k, htakeSucc]
        by_cases hk : k = fds.val[idx.val].val
        · subst hk
          have hk0 : 0 ≤ fds.val[idx.val].val := by scalar_tac
          simp only [Model.sliceContainsNonnegSpec, hk0, decide_true, Bool.true_and,
            List.any_append, List.any_cons, List.any_nil, beq_self_eq_true, Bool.or_false,
            Bool.or_true, ↓reduceIte]
        · have hne : (fds.val[idx.val].val == k) = false := beq_false_of_ne (Ne.symm hk)
          simp only [Model.sliceContainsNonnegSpec, List.any_append, List.any_cons,
            List.any_nil, hne, Bool.or_false, hk, ↓reduceIte]
          rfl
      · simp only [hnonneg, ↓reduceIte]
        refine okPost_ok _ _ ⟨hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, fun k => ?_⟩
        rw [hget1 k, htakeSucc]
        by_cases hk0 : 0 ≤ k
        · have hne : (fds.val[idx.val].val == k) = false := beq_false_of_ne (by
            have : fds.val[idx.val].val < 0 := by scalar_tac
            omega)
          simp only [Model.sliceContainsNonnegSpec, hk0, decide_true, Bool.true_and,
            List.any_append, List.any_cons, List.any_nil, hne, Bool.or_false]
        · simp only [Model.sliceContainsNonnegSpec, hk0, decide_false, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte]
    refine okPost_bind hstep fun s2 ⟨hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hget2⟩ => ?_
    rw [hinc, bind_ok]
    refine okPost_ok _ _ ⟨⟨hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, ?_, fun k => ?_⟩, ?_⟩
    · change idx1.val ≤ fds.len.val; rw [hval]; exact hjlt
    · rw [hget2 k, hval]
    · dsimp; rw [hval]; exact Nat.sub_succ_lt_self fds.len.val idx.val hjlt
  · simp only [hlt, ↓reduceIte]
    have hjge : fds.val.length ≤ idx.val := by
      have : ¬ idx.val < fds.val.length := by simpa [Slice.len] using hlt
      omega
    refine okPost_ok _ _ ⟨hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, fun k => ?_⟩
    rw [hget1 k, List.take_of_length_le hjge]

end CloseUnusedSlice

section NextKeepGe

private theorem hcast_i32_to_u32_nonneg (x : I32) (hx : 0 ≤ x.val) :
    ((IScalar.hcast .U32 x : U32).val : ℤ) = x.val := by
  have hbv : (IScalar.hcast .U32 x : U32).bv = x.bv := by
    change BitVec.signExtend 32 x.bv = x.bv
    ext i hi
    simp
  change ((IScalar.hcast .U32 x : U32).bv.toNat : ℤ) = x.bv.toInt
  rw [hbv, BitVec.toInt_eq_toNat_cond]
  have hlt : 2 * x.bv.toNat < 2 ^ 32 := by
    by_contra hge
    have : (x.bv.toInt : ℤ) < 0 := by
      rw [BitVec.toInt_eq_toNat_cond]
      simp only [hge, ↓reduceIte]
      have : x.bv.toNat < 2 ^ 32 := x.bv.isLt
      omega
    exact absurd hx (not_le_of_gt this)
  simp only [hlt, ↓reduceIte]

private def IsBestKeepSoFar (extra_keep_fd : I32) (xs : List I32) (lo : U32) (best : Option U32) : Prop :=
  match best with
  | none => ∀ k : ℤ, (lo.val : ℤ) ≤ k → k ≤ 2147483647 → Model.isKeptAbove2 extra_keep_fd xs k = false
  | some b => (lo.val : ℤ) ≤ (b.val : ℤ) ∧ 2 < (b.val : ℤ) ∧ (b.val : ℤ) ≤ 2147483647 ∧
      Model.isKeptAbove2 extra_keep_fd xs (b.val : ℤ) = true ∧
      ∀ k' : ℤ, (lo.val : ℤ) ≤ k' → k' < (b.val : ℤ) → Model.isKeptAbove2 extra_keep_fd xs k' = false

private theorem isKeptAbove2_nil (extra_keep_fd : I32) (k : ℤ) :
    Model.isKeptAbove2 extra_keep_fd [] k =
      (decide (k > 2) && (decide (extra_keep_fd.val > 2) && (extra_keep_fd.val == k))) := by
  simp [Model.isKeptAbove2, Model.sliceContainsNonnegSpec]

private theorem isKeptAbove2_append_singleton (extra_keep_fd : I32) (xs : List I32) (fd : I32) (k : ℤ) :
    Model.isKeptAbove2 extra_keep_fd (xs ++ [fd]) k =
      (Model.isKeptAbove2 extra_keep_fd xs k ||
        (decide (k > 2) && decide (0 ≤ k) && (fd.val == k))) := by
  simp only [Model.isKeptAbove2, Model.sliceContainsNonnegSpec, List.any_append, List.any_cons,
    List.any_nil, Bool.or_false]
  cases decide (k > 2) <;> cases decide (0 ≤ k) <;> simp [Bool.and_or_distrib_left, Bool.or_assoc]

/-- Exact specification and unconditional totality for `postfork.fd_ops.next_keep_ge`. -/
theorem next_keep_ge_spec (extra_keep_fd : I32) (keep_fds : Slice I32) (lo : U32) :
    OkPost (postfork.fd_ops.next_keep_ge extra_keep_fd keep_fds lo) fun res =>
      IsBestKeepSoFar extra_keep_fd keep_fds.val lo res := by
  unfold postfork.fd_ops.next_keep_ge postfork.fd_ops.next_keep_ge_loop
  dsimp only [lift]
  have hBest0 : OkPost (if extra_keep_fd > 2#i32 then do
        let i ← Result.ok (IScalar.hcast .U32 extra_keep_fd)
        if i ≥ lo then do let i1 ← Result.ok (IScalar.hcast .U32 extra_keep_fd); Result.ok (some i1)
        else Result.ok none
      else Result.ok none)
      (IsBestKeepSoFar extra_keep_fd [] lo) := by
    by_cases hex : extra_keep_fd > 2#i32
    · have hex0 : 0 ≤ extra_keep_fd.val := by scalar_tac
      have hval := hcast_i32_to_u32_nonneg extra_keep_fd hex0
      set u : U32 := IScalar.hcast .U32 extra_keep_fd
      simp only [hex, ↓reduceIte, bind_ok]
      by_cases hge : u ≥ lo
      · simp only [hge, ↓reduceIte]
        refine okPost_ok _ _ ⟨by scalar_tac, by rw [hval]; scalar_tac, by rw [hval]; scalar_tac, ?_, ?_⟩
        · rw [isKeptAbove2_nil, hval]
          simp [show extra_keep_fd.val > 2 by scalar_tac]
        · intro k' _ hklt
          rw [isKeptAbove2_nil]
          have hne : (extra_keep_fd.val == k') = false := beq_false_of_ne (by omega)
          simp [hne]
      · simp only [hge, ↓reduceIte]
        refine okPost_ok _ _ fun k hklo _ => ?_
        rw [isKeptAbove2_nil]
        have hne : (extra_keep_fd.val == k) = false := beq_false_of_ne (by
          have : (u.val : ℤ) < (lo.val : ℤ) := by scalar_tac
          omega)
        simp [hne]
    · simp only [hex, ↓reduceIte]
      refine okPost_ok _ _ fun k _ _ => ?_
      rw [isKeptAbove2_nil]
      have hnot : ¬ (extra_keep_fd.val > 2) := by scalar_tac
      simp [hnot]
  refine okPost_bind hBest0 fun b0 hb0 => ?_
  refine okPost_loop_decr_nat
    (fun p => keep_fds.len.val - p.2.val)
    (fun p => p.2 ≤ keep_fds.len ∧ IsBestKeepSoFar extra_keep_fd (keep_fds.val.take p.2.val) lo p.1)
    (IsBestKeepSoFar extra_keep_fd keep_fds.val lo)
    (fun p => postfork.fd_ops.next_keep_ge_loop.body keep_fds lo keep_fds.len p.1 p.2)
    (b0, 0#usize) ?_ ⟨by scalar_tac, by simpa using hb0⟩
  intro ⟨best, idx⟩ hinv
  dsimp only at hinv
  rcases hinv with ⟨hidxLe, hBest⟩
  unfold postfork.fd_ops.next_keep_ge_loop.body
  by_cases hlt : idx < keep_fds.len
  · rcases slice_idx_succ keep_fds hlt with ⟨hjlt, hidx, idx1, hinc, hval⟩
    simp only [hlt, ↓reduceIte]
    rw [hidx, bind_ok]
    dsimp only [lift]
    set fd := keep_fds.val[idx.val]
    have htakeSucc : keep_fds.val.take (idx.val + 1) = keep_fds.val.take idx.val ++ [fd] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjlt]; rfl
    have hstep : OkPost (if fd > 2#i32 then do
          let u ← Result.ok (IScalar.hcast .U32 fd)
          if u ≥ lo then do
            let i1 ← match best with
              | none => Result.ok u
              | some cur => if u < cur then Result.ok u else Result.ok cur
            Result.ok (some i1)
          else Result.ok best
        else Result.ok best)
        (IsBestKeepSoFar extra_keep_fd (keep_fds.val.take (idx.val + 1)) lo) := by
      by_cases hfd2 : fd > 2#i32
      · have hfd0 : 0 ≤ fd.val := by scalar_tac
        have huval := hcast_i32_to_u32_nonneg fd hfd0
        set u : U32 := IScalar.hcast .U32 fd
        simp only [hfd2, ↓reduceIte, bind_ok]
        by_cases huge : u ≥ lo
        · simp only [huge, ↓reduceIte]
          cases best with
          | none =>
            dsimp only [IsBestKeepSoFar] at hBest
            simp only [bind_ok]
            have huMax : (u.val : ℤ) ≤ 2147483647 := by rw [huval]; scalar_tac
            refine okPost_ok _ _ ⟨by scalar_tac, by rw [huval]; scalar_tac, huMax, ?_, ?_⟩
            · rw [htakeSucc, isKeptAbove2_append_singleton, huval]
              simp [show fd.val > 2 by scalar_tac, show 0 ≤ fd.val by omega]
            · intro k' hklo hklt
              rw [htakeSucc, isKeptAbove2_append_singleton, hBest k' hklo (by omega)]
              have hne : (fd.val == k') = false := beq_false_of_ne (by omega)
              simp [hne]
          | some cur =>
            rcases hBest with ⟨hcurlo, hcur2, hcurmax, hcurkept, hcurmin⟩
            by_cases huc : u < cur
            · simp only [huc, ↓reduceIte, bind_ok]
              refine okPost_ok _ _ ⟨by scalar_tac, by rw [huval]; scalar_tac, by rw [huval]; scalar_tac, ?_, ?_⟩
              · rw [htakeSucc, isKeptAbove2_append_singleton, huval]
                simp [show fd.val > 2 by scalar_tac, show 0 ≤ fd.val by omega]
              · intro k' hklo hklt
                have hkltcur : k' < (cur.val : ℤ) := by
                  have : (u.val : ℤ) < (cur.val : ℤ) := by scalar_tac
                  omega
                rw [htakeSucc, isKeptAbove2_append_singleton, hcurmin k' hklo hkltcur]
                have hne : (fd.val == k') = false := beq_false_of_ne (by omega)
                simp [hne]
            · simp only [huc, ↓reduceIte, bind_ok]
              refine okPost_ok _ _ ⟨hcurlo, hcur2, hcurmax, ?_, ?_⟩
              · rw [htakeSucc, isKeptAbove2_append_singleton, hcurkept]; simp
              · intro k' hklo hklt
                rw [htakeSucc, isKeptAbove2_append_singleton, hcurmin k' hklo hklt]
                have hne : (fd.val == k') = false := beq_false_of_ne (by
                  have : (cur.val : ℤ) ≤ (u.val : ℤ) := by scalar_tac
                  omega)
                simp [hne]
        · simp only [huge, ↓reduceIte]
          have hunchanged : ∀ k : ℤ, (lo.val : ℤ) ≤ k →
              Model.isKeptAbove2 extra_keep_fd (keep_fds.val.take (idx.val + 1)) k =
                Model.isKeptAbove2 extra_keep_fd (keep_fds.val.take idx.val) k := by
            intro k hklo
            rw [htakeSucc, isKeptAbove2_append_singleton]
            have hne : (fd.val == k) = false := beq_false_of_ne (by
              have : (u.val : ℤ) < (lo.val : ℤ) := by scalar_tac
              omega)
            simp [hne]
          refine okPost_ok _ _ ?_
          cases best with
          | none =>
            intro k hklo hkmax
            rw [hunchanged k hklo]
            exact hBest k hklo hkmax
          | some b =>
            rcases hBest with ⟨hblo, hb2, hbmax, hbkept, hbmin⟩
            refine ⟨hblo, hb2, hbmax, ?_, fun k' hklo hklt => ?_⟩
            · rw [hunchanged b.val hblo]; exact hbkept
            · rw [hunchanged k' hklo]; exact hbmin k' hklo hklt
      · simp only [hfd2, ↓reduceIte]
        have hunchanged : ∀ k : ℤ, 2 < k →
            Model.isKeptAbove2 extra_keep_fd (keep_fds.val.take (idx.val + 1)) k =
              Model.isKeptAbove2 extra_keep_fd (keep_fds.val.take idx.val) k := by
          intro k hk2
          rw [htakeSucc, isKeptAbove2_append_singleton]
          have hne : (fd.val == k) = false := beq_false_of_ne (by
            have : fd.val ≤ 2 := by scalar_tac
            omega)
          simp [hne]
        refine okPost_ok _ _ ?_
        cases best with
        | none =>
          intro k hklo hkmax
          by_cases hk2 : 2 < k
          · rw [hunchanged k hk2]; exact hBest k hklo hkmax
          · simp [Model.isKeptAbove2, show ¬(k > 2) by omega]
        | some b =>
          rcases hBest with ⟨hblo, hb2, hbmax, hbkept, hbmin⟩
          refine ⟨hblo, hb2, hbmax, ?_, fun k' hklo hklt => ?_⟩
          · rw [hunchanged b.val hb2]; exact hbkept
          · by_cases hk2 : 2 < k'
            · rw [hunchanged k' hk2]; exact hbmin k' hklo hklt
            · simp [Model.isKeptAbove2, show ¬(k' > 2) by omega]
    refine okPost_bind hstep fun b1 hb1 => ?_
    rw [hinc, bind_ok]
    refine okPost_ok _ _ ⟨⟨?_, ?_⟩, ?_⟩
    · change idx1.val ≤ keep_fds.len.val; rw [hval]; exact hjlt
    · rw [hval]; exact hb1
    · rw [hval]; exact Nat.sub_succ_lt_self keep_fds.len.val idx.val hjlt
  · simp only [hlt, ↓reduceIte]
    have hjge : keep_fds.val.length ≤ idx.val := by
      have : ¬ idx.val < keep_fds.val.length := by simpa [Slice.len] using hlt
      omega
    rw [List.take_of_length_le hjge] at hBest
    exact okPost_ok _ _ hBest

end NextKeepGe

section TryCloseRangeExcept

private theorem find?_filter_range (fds : List (ℤ × FdEntry)) (lo hi : ℤ) (k : ℤ) :
    (List.filter (fun p => !decide (lo ≤ p.1 ∧ p.1 ≤ hi)) fds).find? (fun p => p.1 == k) =
      if lo ≤ k ∧ k ≤ hi then none else fds.find? (fun p => p.1 == k) := by
  induction fds with
  | nil =>
    by_cases h : lo ≤ k ∧ k ≤ hi <;> simp [h]
  | cons p rest ih =>
    rcases p with ⟨fd, e⟩
    rw [List.filter_cons]
    by_cases hp : lo ≤ fd ∧ fd ≤ hi
    · have hcond : (!decide (lo ≤ fd ∧ fd ≤ hi)) = false := by simp [hp]
      change List.find? (fun p => p.1 == k)
          (if (!decide (lo ≤ fd ∧ fd ≤ hi)) = true then (fd, e) :: List.filter (fun p => !decide (lo ≤ p.1 ∧ p.1 ≤ hi)) rest
          else List.filter (fun p => !decide (lo ≤ p.1 ∧ p.1 ≤ hi)) rest) = _
      rw [hcond]
      simp only [Bool.false_eq_true, ↓reduceIte, ih, List.find?_cons]
      by_cases hfk : (fd == k) = true
      · have heq : fd = k := beq_iff_eq.mp hfk
        subst heq; simp only [hp, and_self, ↓reduceIte]
      · simp only [hfk]
    · have hcond : (!decide (lo ≤ fd ∧ fd ≤ hi)) = true := by simp [hp]
      change List.find? (fun p => p.1 == k)
          (if (!decide (lo ≤ fd ∧ fd ≤ hi)) = true then (fd, e) :: List.filter (fun p => !decide (lo ≤ p.1 ∧ p.1 ≤ hi)) rest
          else List.filter (fun p => !decide (lo ≤ p.1 ∧ p.1 ≤ hi)) rest) = _
      rw [hcond]
      simp only [↓reduceIte, List.find?_cons]
      by_cases hfk : (fd == k) = true
      · have heq : fd = k := beq_iff_eq.mp hfk
        subst heq; simp only [hp, ↓reduceIte, beq_self_eq_true]
      · simp only [hfk, ih]

private theorem u32_add_one (k : U32) (hk : (k.val : ℤ) ≤ 2147483647) :
    ∃ z : U32, k + 1#u32 = Result.ok z ∧ z.val = k.val + 1 := by
  have hs : OkPost (k + 1#u32) fun z => z.val = k.val + 1 :=
    (okPost_iff_wp_spec _ _).mpr (UScalar.add_spec (by scalar_tac))
  exact hs

private theorem u32_sub_one (k : U32) (hk : 1 ≤ k.val) :
    ∃ z : U32, k - 1#u32 = Result.ok z ∧ z.val = k.val - 1 := by
  have hs : OkPost (k - 1#u32) fun z => z.val = k.val - 1 ∧ (1#u32 : U32).val ≤ k.val :=
    (okPost_iff_wp_spec _ _).mpr (UScalar.sub_spec (by scalar_tac))
  rcases hs with ⟨z, hz, hv, _⟩
  exact ⟨z, hz, hv⟩

private theorem sys_close_range_total (s : sys.Sys) (first last : U32) :
    OkPost (sys.close_range s first last 0#u32) fun p =>
      SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧ p.2.writeLog = s.writeLog ∧
        p.2.descs = s.descs ∧
        (p.2.status = .running → p.2.trace.length = s.trace.length + 1) ∧
        (s.status = .running → s.closeRangeSupported = false →
          ∃ e, p.1 = .Err e ∧ p.2.fds = s.fds ∧
            (oracleHasSeccomp s.oracle = false → e = sanitizeErrno s.closeRangeErrno)) := by
  unfold sys.close_range LeanSwe.PostFork.Aeneas.Internal.Sys.close_range runUnitSyscall
  cases hst : s.status with
  | running =>
    dsimp only
    by_cases hsup : s.closeRangeSupported = true
    · have hns : (!s.closeRangeSupported) = false := by simp [hsup]
      simp only [hns, Bool.false_eq_true, ↓reduceIte]
      cases hf : currentFault s with
      | seccomp rawE =>
        dsimp only
        exact okPost_ok _ _ ⟨⟨rfl, by simp [hst], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          rfl, rfl, rfl, rfl, rfl, fun _ => by simp,
          fun _ hc => by simp [hsup] at hc⟩
      | normal | partialWrite _ | dentsBatch _ | fail _ =>
        by_cases hbad : (decide (first.val > last.val) || (0#u32 : U32) &&& 4294967289#u32 != 0#u32) = true
        · simp only [hbad, ↓reduceIte]
          exact okPost_ok _ _ ⟨⟨rfl, by simp [hst], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
            rfl, rfl, rfl, rfl, rfl, fun _ => by simp,
            fun _ hc => by simp [hsup] at hc⟩
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
          exact okPost_ok _ _ ⟨⟨rfl, by simp [hst], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
            rfl, rfl, rfl, rfl, rfl, fun _ => by simp,
            fun _ hc => by simp [hsup] at hc⟩
    · have hns : (!s.closeRangeSupported) = true := by simp [hsup]
      simp only [hns, ↓reduceIte]
      cases hf : currentFault s with
      | seccomp rawE =>
        dsimp only
        exact okPost_ok _ _ ⟨⟨rfl, by simp [hst], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          rfl, rfl, rfl, rfl, rfl, fun _ => by simp,
          fun _ _ => ⟨_, rfl, rfl, fun hor => False.elim (not_seccomp_of_oracleHasSeccomp_false hor hf)⟩⟩
      | normal | partialWrite _ | dentsBatch _ | fail _ =>
        exact okPost_ok _ _ ⟨⟨rfl, by simp [hst], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          rfl, rfl, rfl, rfl, rfl, fun _ => by simp,
          fun _ _ => ⟨sanitizeErrno s.closeRangeErrno, rfl, rfl, fun _ => rfl⟩⟩
  | exited _ =>
    refine okPost_ok _ _ ⟨SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro h; dsimp only at h; rw [hst] at h; cases h
    · intro h; cases h
  | signaled _ =>
    refine okPost_ok _ _ ⟨SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro h; dsimp only at h; rw [hst] at h; cases h
    · intro h; cases h
  | execd _ =>
    refine okPost_ok _ _ ⟨SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro h; dsimp only at h; rw [hst] at h; cases h
    · intro h; cases h

private theorem sys_close_range_run_ok_spec (s : sys.Sys) (hRun : s.status = .running)
    (hOr : s.oracle = []) (hSup : s.closeRangeSupported = true)
    (first last : U32) (hle : first.val ≤ last.val) :
    OkPost (sys.close_range s first last 0#u32) fun p =>
      p.1 = .Ok () ∧ SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        ∀ k : ℤ, p.2.getFd k = if (first.val : ℤ) ≤ k ∧ k ≤ last.val then none else s.getFd k := by
  unfold sys.close_range LeanSwe.PostFork.Aeneas.Internal.Sys.close_range runUnitSyscall
  have hns : (!s.closeRangeSupported) = false := by simp [hSup]
  have hbad : (decide (first.val > last.val) || (0#u32 : U32) &&& 4294967289#u32 != 0#u32) = false := by
    have h0 : (0#u32 : U32) &&& 4294967289#u32 = 0#u32 := by decide
    simp [h0, show ¬ (first.val > last.val) by omega]
  have hF : currentFault s = .normal := currentFault_oracle_nil s hOr
  have hflag4 : ((0#u32 : U32) &&& 4#u32 != 0#u32) = false := by decide
  rw [hRun]
  simp only [hns, Bool.false_eq_true, ↓reduceIte, hbad, hF, hflag4]
  refine okPost_ok _ _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, fun k => ?_⟩
  simp only [ChildState.getFd]
  rw [find?_filter_range]
  by_cases h : (first.val : ℤ) ≤ k ∧ k ≤ last.val <;> simp [h]

/-- Unconditional totality for `postfork.fd_ops.try_close_range_except`. -/
theorem try_close_range_except_total (s : sys.Sys) (extra_keep_fd : I32) (keep_fds : Slice I32) :
    OkPost (postfork.fd_ops.try_close_range_except s extra_keep_fd keep_fds) (fun _ => True) := by
  unfold postfork.fd_ops.try_close_range_except postfork.fd_ops.try_close_range_except_loop
  have hLoop : OkPost (loop (fun x => postfork.fd_ops.try_close_range_except_loop.body extra_keep_fd keep_fds x.1 x.2) (3#u32, s))
      (fun _ => True) := by
    refine okPost_loop_decr_nat
      (fun p => 2147483649 - p.1.val)
      (fun p => 3 ≤ p.1.val ∧ p.1.val ≤ 2147483648)
      (fun _ => True)
      (fun p => postfork.fd_ops.try_close_range_except_loop.body extra_keep_fd keep_fds p.1 p.2)
      (3#u32, s) ?_ ⟨by dsimp; decide, by dsimp; decide⟩
    intro ⟨lo, s1⟩ hinv
    dsimp only at hinv
    rcases hinv with ⟨hlo3, hloMax⟩
    unfold postfork.fd_ops.try_close_range_except_loop.body
    refine okPost_bind (next_keep_ge_spec extra_keep_fd keep_fds lo) fun o ho => ?_
    cases o with
    | none =>
      refine okPost_bind (sys_close_range_total s1 lo core.num.U32.MAX) fun p2 _ => ?_
      rcases p2 with ⟨r, s2⟩
      cases r <;> exact okPost_ok _ _ trivial
    | some k =>
      rcases ho with ⟨hlok, _, hkmax, _, _⟩
      obtain ⟨lo1, hok1, hval1⟩ := u32_add_one k (by omega)
      by_cases hkgt : k > lo
      · simp only [hkgt, ↓reduceIte]
        obtain ⟨hi, hokSub, _⟩ := u32_sub_one k (by scalar_tac)
        rw [hokSub, bind_ok]
        refine okPost_bind (sys_close_range_total s1 lo hi) fun p2 _ => ?_
        rcases p2 with ⟨r, s2⟩
        cases r with
        | Ok _ =>
          change OkPost (do let lo1 ← k + 1#u32; Result.ok (ControlFlow.cont (lo1, s2))) _
          rw [hok1, bind_ok]
          refine okPost_ok _ _ ⟨⟨?_, ?_⟩, ?_⟩
          · dsimp; omega
          · dsimp; omega
          · dsimp; omega
        | Err _ =>
          exact okPost_ok _ _ trivial
      · simp only [hkgt, ↓reduceIte]
        rw [hok1, bind_ok]
        refine okPost_ok _ _ ⟨⟨?_, ?_⟩, ?_⟩
        · dsimp; omega
        · dsimp; omega
        · dsimp; omega
  refine okPost_bind hLoop fun p _ => ?_
  rcases p with ⟨s1, err, failed⟩
  by_cases hf : failed = true <;> simp [hf, okPost_ok]

/-- Error specification for `postfork.fd_ops.try_close_range_except` when `close_range` is unsupported. -/
theorem try_close_range_except_err_spec (s : sys.Sys) (hRun : s.status = .running)
    (hUnsup : s.closeRangeSupported = false) (extra_keep_fd : I32) (keep_fds : Slice I32) :
    OkPost (postfork.fd_ops.try_close_range_except s extra_keep_fd keep_fds) fun p =>
      (∃ e, p.1 = .Err e ∧ (oracleHasSeccomp s.oracle = false → e = sanitizeErrno s.closeRangeErrno)) ∧
        SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧ p.2.writeLog = s.writeLog ∧
        p.2.descs = s.descs ∧ p.2.fds = s.fds ∧
        p.2.trace.length = s.trace.length + 1 := by
  unfold postfork.fd_ops.try_close_range_except postfork.fd_ops.try_close_range_except_loop
  refine okPost_bind (okPost_loop_decr_nat
    (fun p => 2147483649 - p.1.val)
    (fun p => 3 ≤ p.1.val ∧ p.1.val ≤ 2147483648 ∧ SameChildConfig p.2 s ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧ p.2.writeLog = s.writeLog ∧
      p.2.descs = s.descs ∧ p.2.fds = s.fds ∧ p.2.trace.length = s.trace.length)
    (fun r => r.2.2 = true ∧ (oracleHasSeccomp s.oracle = false → r.2.1 = sanitizeErrno s.closeRangeErrno) ∧
      SameChildConfig r.1 s ∧
      r.1.pgid = s.pgid ∧ r.1.cwd = s.cwd ∧ r.1.sig = s.sig ∧ r.1.writeLog = s.writeLog ∧
      r.1.descs = s.descs ∧ r.1.fds = s.fds ∧ r.1.trace.length = s.trace.length + 1)
    (fun p => postfork.fd_ops.try_close_range_except_loop.body extra_keep_fd keep_fds p.1 p.2)
    (3#u32, s) ?_ ⟨by dsimp; decide, by dsimp; decide, SameChildConfig.refl s,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) fun p hp => ?_
  · intro ⟨lo, s1⟩ hinv
    dsimp only at hinv
    rcases hinv with ⟨hlo3, hloMax, hcfg1, hpg1, hcwd1, hsig1, hwl1, hdescs1, hfds1, htr1⟩
    unfold postfork.fd_ops.try_close_range_except_loop.body
    refine okPost_bind (next_keep_ge_spec extra_keep_fd keep_fds lo) fun o ho => ?_
    cases o with
    | none =>
      refine okPost_bind (sys_close_range_total s1 lo core.num.U32.MAX) fun p2 hp2 => ?_
      rcases p2 with ⟨r, s2⟩
      rcases hp2 with ⟨hcfg2, hpg2, hcwd2, hsig2, hwl2, hdescs2, htr2, herr2⟩
      dsimp only at hcfg2 hpg2 hcwd2 hsig2 hwl2 hdescs2 htr2 herr2
      have hs1Run : s1.status = .running := hcfg1.status.trans hRun
      have hs1Unsup : s1.closeRangeSupported = false := hcfg1.closeRangeSupported.trans hUnsup
      rcases herr2 hs1Run hs1Unsup with ⟨err2, hr, hfds2, herrEq⟩
      rw [hr]
      have hs2Run : s2.status = .running := hcfg2.status.trans hs1Run
      exact okPost_ok _ _ ⟨rfl,
        fun hor => (herrEq (by rw [hcfg1.oracle]; exact hor)).trans (by rw [hcfg1.closeRangeErrno]),
        hcfg2.trans hcfg1, hpg2.trans hpg1, hcwd2.trans hcwd1, hsig2.trans hsig1, hwl2.trans hwl1,
        hdescs2.trans hdescs1, hfds2.trans hfds1, by rw [htr2 hs2Run, htr1]⟩
    | some k =>
      rcases ho with ⟨hlok, _, hkmax, _, _⟩
      by_cases hkgt : k > lo
      · simp only [hkgt, ↓reduceIte]
        obtain ⟨hi, hokSub, _⟩ := u32_sub_one k (by scalar_tac)
        rw [hokSub, bind_ok]
        refine okPost_bind (sys_close_range_total s1 lo hi) fun p2 hp2 => ?_
        rcases p2 with ⟨r, s2⟩
        rcases hp2 with ⟨hcfg2, hpg2, hcwd2, hsig2, hwl2, hdescs2, htr2, herr2⟩
        dsimp only at hcfg2 hpg2 hcwd2 hsig2 hwl2 hdescs2 htr2 herr2
        have hs1Run : s1.status = .running := hcfg1.status.trans hRun
        have hs1Unsup : s1.closeRangeSupported = false := hcfg1.closeRangeSupported.trans hUnsup
        rcases herr2 hs1Run hs1Unsup with ⟨err2, hr, hfds2, herrEq⟩
        rw [hr]
        have hs2Run : s2.status = .running := hcfg2.status.trans hs1Run
        exact okPost_ok _ _ ⟨rfl,
          fun hor => (herrEq (by rw [hcfg1.oracle]; exact hor)).trans (by rw [hcfg1.closeRangeErrno]),
          hcfg2.trans hcfg1, hpg2.trans hpg1, hcwd2.trans hcwd1, hsig2.trans hsig1, hwl2.trans hwl1,
          hdescs2.trans hdescs1, hfds2.trans hfds1, by rw [htr2 hs2Run, htr1]⟩
      · simp only [hkgt, ↓reduceIte]
        obtain ⟨lo1, hok1, hval1⟩ := u32_add_one k (by omega)
        rw [hok1, bind_ok]
        refine okPost_ok _ _ ⟨⟨by dsimp; omega, by dsimp; omega, hcfg1,
          hpg1, hcwd1, hsig1, hwl1, hdescs1, hfds1, htr1⟩, by dsimp; omega⟩
  · rcases p with ⟨s1, err, failed⟩
    dsimp only at hp
    rcases hp with ⟨hfl, herr, hcfg, hpg, hcwd, hsig, hwl, hdescs, hfds, htr⟩
    simp only [hfl]
    exact okPost_ok _ _ ⟨⟨err, rfl, herr⟩, hcfg, hpg, hcwd, hsig, hwl, hdescs, hfds, htr⟩

/-- Functional specification for `postfork.fd_ops.try_close_range_except` when `close_range` is supported. -/
theorem try_close_range_except_spec (s : sys.Sys) (hRun : s.status = .running)
    (hOr : s.oracle = []) (hSup : s.closeRangeSupported = true)
    (extra_keep_fd : I32) (keep_fds : Slice I32) :
    OkPost (postfork.fd_ops.try_close_range_except s extra_keep_fd keep_fds) fun p =>
      p.1 = .Ok () ∧ SameChildConfig p.2 s ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        CloseAbove2Post s extra_keep_fd keep_fds.val p.2 := by
  unfold postfork.fd_ops.try_close_range_except postfork.fd_ops.try_close_range_except_loop
  let inv : U32 × sys.Sys → Prop := fun p =>
    3 ≤ p.1.val ∧ p.1.val ≤ 2147483648 ∧ SameChildConfig p.2 s ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      (∀ fd : ℤ, 0 ≤ fd → fd ≤ 2 → p.2.getFd fd = s.getFd fd) ∧
      (∀ fd : ℤ, 3 ≤ fd → fd < p.1.val →
        if Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then p.2.getFd fd = s.getFd fd else p.2.getFd fd = none) ∧
      (∀ fd : ℤ, (p.1.val : ℤ) ≤ fd → fd ≤ 2147483647 → p.2.getFd fd = s.getFd fd)
  refine okPost_bind (okPost_loop_decr_nat (fun p => 2147483649 - p.1.val) inv
    (fun r => r.2.2 = false ∧ SameChildConfig r.1 s ∧
      r.1.pgid = s.pgid ∧ r.1.cwd = s.cwd ∧ r.1.sig = s.sig ∧
      r.1.descs = s.descs ∧ r.1.writeLog = s.writeLog ∧
      CloseAbove2Post s extra_keep_fd keep_fds.val r.1)
    (fun p => postfork.fd_ops.try_close_range_except_loop.body extra_keep_fd keep_fds p.1 p.2)
    (3#u32, s) ?_ ⟨by dsimp; decide, by dsimp; decide, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl,
      fun _ _ _ => rfl, fun fd h3 hlt => absurd hlt (by dsimp only at hlt; change ¬ fd < 3; omega), fun _ _ _ => rfl⟩)
    fun p hp => ?_
  · intro ⟨lo, s1⟩ hinv
    dsimp only [inv] at hinv
    rcases hinv with ⟨hlo3, hloMax, hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1, h02, hltlo, hgelo⟩
    unfold postfork.fd_ops.try_close_range_except_loop.body
    have hRun1 : s1.status = .running := hcfg1.status.trans hRun
    have hOr1 : s1.oracle = [] := hcfg1.oracle.trans hOr
    have hSup1 : s1.closeRangeSupported = true := hcfg1.closeRangeSupported.trans hSup
    refine okPost_bind (next_keep_ge_spec extra_keep_fd keep_fds lo) fun o ho => ?_
    cases o with
    | none =>
      have hloU32 : lo.val ≤ core.num.U32.MAX.val := by
        have : core.num.U32.MAX.val = 4294967295 := by decide
        omega
      refine okPost_bind (sys_close_range_run_ok_spec s1 hRun1 hOr1 hSup1 lo core.num.U32.MAX hloU32)
        fun p2 hp2 => ?_
      rcases p2 with ⟨r, s2⟩
      rcases hp2 with ⟨hr, hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hget2⟩
      dsimp only at hr hcfg2 hpg2 hcwd2 hsig2 hdescs2 hwl2 hget2
      rw [hr]
      refine okPost_ok _ _ ⟨rfl, hcfg2.trans hcfg1, hpg2.trans hpg1, hcwd2.trans hcwd1,
        hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1, fun fd hfd0 hfd2 => ?_, fun fd hfd3 hfdmax => ?_⟩
      · rw [hget2 fd, ite_eq_right (by omega)]; exact h02 fd hfd0 hfd2
      · by_cases hfdlt : fd < lo.val
        · have hnot : ¬ ((lo.val : ℤ) ≤ fd ∧ fd ≤ core.num.U32.MAX.val) := by omega
          simp only [hget2 fd, hnot, ↓reduceIte]
          exact hltlo fd hfd3 hfdlt
        · have hge : (lo.val : ℤ) ≤ fd := by omega
          have hnotkept : Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false := ho fd hge hfdmax
          have hlemax : fd ≤ core.num.U32.MAX.val := by
            have : (core.num.U32.MAX.val : ℤ) = 4294967295 := by decide
            omega
          simp only [hnotkept, Bool.false_eq_true, ↓reduceIte]
          rw [hget2 fd]
          simp only [hge, hlemax, and_self, ↓reduceIte]
    | some k =>
      rcases ho with ⟨hlok, _, hkmax, hkkept, hmink⟩
      obtain ⟨lo1, hok1, hval1⟩ := u32_add_one k (by omega)
      by_cases hkgt : k > lo
      · simp only [hkgt, ↓reduceIte]
        obtain ⟨hi, hokSub, hvalSub⟩ := u32_sub_one k (by scalar_tac)
        rw [hokSub, bind_ok]
        have hlohi : lo.val ≤ hi.val := by change lo.val < k.val at hkgt; omega
        refine okPost_bind (sys_close_range_run_ok_spec s1 hRun1 hOr1 hSup1 lo hi hlohi)
          fun p2 hp2 => ?_
        rcases p2 with ⟨r, s2⟩
        rcases hp2 with ⟨hr, hcfg2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hget2⟩
        dsimp only at hr hcfg2 hpg2 hcwd2 hsig2 hdescs2 hwl2 hget2
        rw [hr]
        change OkPost (do let lo1 ← k + 1#u32; Result.ok (ControlFlow.cont (lo1, s2))) _
        rw [hok1, bind_ok]
        refine okPost_ok _ _ ⟨⟨by dsimp; omega, by dsimp; omega, hcfg2.trans hcfg1, hpg2.trans hpg1,
          hcwd2.trans hcwd1, hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1,
          fun fd hfd0 hfd2 => ?_, fun fd hfd3 hfdlt => ?_, fun fd hfdge hfdmax => ?_⟩, ?_⟩
        · rw [hget2 fd, ite_eq_right (by omega)]; exact h02 fd hfd0 hfd2
        · rw [hval1] at hfdlt
          by_cases hltlo' : fd < lo.val
          · have hnot : ¬ ((lo.val : ℤ) ≤ fd ∧ fd ≤ hi.val) := by omega
            simp only [hget2 fd, hnot, ↓reduceIte]
            exact hltlo fd hfd3 hltlo'
          · by_cases hfk : fd = k.val
            · subst hfk
              simp only [hkkept, ↓reduceIte]
              have hnot : ¬ ((lo.val : ℤ) ≤ k.val ∧ (k.val : ℤ) ≤ hi.val) := by omega
              simp only [hget2 k.val, hnot, ↓reduceIte]
              exact hgelo k.val hlok hkmax
            · have hge : (lo.val : ℤ) ≤ fd := by omega
              have hlt : fd < k.val := by omega
              have hnotkept : Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false := hmink fd hge hlt
              have hlehi : fd ≤ hi.val := by omega
              simp only [hnotkept, Bool.false_eq_true, ↓reduceIte]
              rw [hget2 fd]
              simp only [hge, hlehi, and_self, ↓reduceIte]
        · dsimp only at hfdge
          rw [hval1] at hfdge
          have hnot : ¬ ((lo.val : ℤ) ≤ fd ∧ fd ≤ hi.val) := by omega
          simp only [hget2 fd, hnot, ↓reduceIte]
          exact hgelo fd (by omega) hfdmax
        · dsimp; omega
      · simp only [hkgt, ↓reduceIte]
        rw [hok1, bind_ok]
        have hkeq : k.val = lo.val := by change ¬ (lo.val < k.val) at hkgt; omega
        refine okPost_ok _ _ ⟨⟨by dsimp; omega, by dsimp; omega, hcfg1, hpg1, hcwd1, hsig1, hdescs1, hwl1,
          h02, fun fd hfd3 hfdlt => ?_, fun fd hfdge hfdmax => ?_⟩, ?_⟩
        · dsimp only at hfdlt
          rw [hval1, hkeq] at hfdlt
          by_cases hltlo' : fd < lo.val
          · exact hltlo fd hfd3 hltlo'
          · have hfeq : fd = k.val := by omega
            subst hfeq
            simp only [hkkept, ↓reduceIte]
            exact hgelo k.val hlok hkmax
        · dsimp only at hfdge
          rw [hval1] at hfdge
          exact hgelo fd (by omega) hfdmax
        · dsimp; omega
  · rcases p with ⟨s2, err, failed⟩
    dsimp only at hp
    rcases hp with ⟨hfl, hcfg, hpg, hcwd, hsig, hdescs, hwl, hpost⟩
    change OkPost (if failed = true then Result.ok (core.result.Result.Err err, s2)
      else Result.ok (core.result.Result.Ok (), s2)) _
    simp only [hfl, Bool.false_eq_true, ↓reduceIte]
    exact okPost_ok _ _ ⟨rfl, hcfg, hpg, hcwd, hsig, hdescs, hwl, hpost⟩

private theorem sys_close_range_run_safety (s : sys.Sys) (hRun : s.status = .running)
    (first last : U32) (hle : first.val ≤ last.val) :
    OkPost (sys.close_range s first last 0#u32) fun p =>
      SameChildConfig p.2 s ∧
        p.2.status = .running ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        (p.1 = .Ok () →
          ∀ k : ℤ, p.2.getFd k = if (first.val : ℤ) ≤ k ∧ k ≤ last.val then none else s.getFd k) ∧
        (∀ e, p.1 = .Err e → p.2.fds = s.fds) := by
  unfold sys.close_range LeanSwe.PostFork.Aeneas.Internal.Sys.close_range runUnitSyscall
  rw [hRun]
  by_cases hsup : s.closeRangeSupported = true
  · have hns : (!s.closeRangeSupported) = false := by simp [hsup]
    have hbad : (decide (first.val > last.val) || (0#u32 : U32) &&& 4294967289#u32 != 0#u32) = false := by
      have h0 : (0#u32 : U32) &&& 4294967289#u32 = 0#u32 := by decide
      simp [h0, show ¬ (first.val > last.val) by omega]
    have hflag4 : ((0#u32 : U32) &&& 4#u32 != 0#u32) = false := by decide
    simp only [hns, Bool.false_eq_true, ↓reduceIte, hbad]
    cases hf : currentFault s with
    | seccomp rawE =>
      dsimp only
      exact okPost_ok _ _ ⟨⟨rfl, by simp [hRun], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        rfl, rfl, rfl, rfl, rfl, rfl, (fun h => by cases h), fun _ _ => rfl⟩
    | fail rawE =>
      dsimp only
      exact okPost_ok _ _ ⟨⟨rfl, by simp [hRun], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        by simp [hRun], rfl, rfl, rfl, rfl, rfl, (fun h => by cases h), fun _ _ => rfl⟩
    | normal | partialWrite _ | dentsBatch _ =>
      simp only [hflag4, Bool.false_eq_true, ↓reduceIte]
      refine okPost_ok _ _ ⟨⟨rfl, by simp [hRun], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        by simp [hRun], rfl, rfl, rfl, rfl, rfl, (fun _ k => ?_), fun _ h => by cases h⟩
      simp only [ChildState.getFd]
      rw [find?_filter_range]
      by_cases h : (first.val : ℤ) ≤ k ∧ k ≤ last.val <;> simp [h]
  · have hns : (!s.closeRangeSupported) = true := by simp [hsup]
    simp only [hns, ↓reduceIte]
    cases currentFault s <;> (
      dsimp only
      exact okPost_ok _ _ ⟨⟨rfl, by simp [hRun], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        by simp [hRun], rfl, rfl, rfl, rfl, rfl, (fun h => by cases h), fun _ _ => rfl⟩)

/-- Arbitrary-oracle safety specification for `postfork.fd_ops.try_close_range_except`. -/
theorem try_close_range_except_safety (s : sys.Sys) (hRun : s.status = .running)
    (extra_keep_fd : I32) (keep_fds : Slice I32) :
    OkPost (postfork.fd_ops.try_close_range_except s extra_keep_fd keep_fds) fun p =>
      SameChildConfig p.2 s ∧
        p.2.status = .running ∧
        p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
        p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        (∀ fd : ℤ, 0 ≤ fd → fd ≤ 2 → p.2.getFd fd = s.getFd fd) ∧
        (∀ fd : ℤ, 3 ≤ fd → fd ≤ 2147483647 →
          Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true → p.2.getFd fd = s.getFd fd) ∧
        (p.1 = .Ok () → CloseAbove2Post s extra_keep_fd keep_fds.val p.2) := by
  unfold postfork.fd_ops.try_close_range_except postfork.fd_ops.try_close_range_except_loop
  let inv : U32 × sys.Sys → Prop := fun p =>
    3 ≤ p.1.val ∧ p.1.val ≤ 2147483648 ∧ SameChildConfig p.2 s ∧
      p.2.status = .running ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      (∀ fd : ℤ, 0 ≤ fd → fd ≤ 2 → p.2.getFd fd = s.getFd fd) ∧
      (∀ fd : ℤ, 3 ≤ fd → fd < p.1.val →
        if Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true then p.2.getFd fd = s.getFd fd else p.2.getFd fd = none) ∧
      (∀ fd : ℤ, (p.1.val : ℤ) ≤ fd → fd ≤ 2147483647 → p.2.getFd fd = s.getFd fd)
  let donePost : (sys.Sys × I32 × Bool) → Prop := fun r =>
    SameChildConfig r.1 s ∧
      r.1.status = .running ∧
      r.1.pgid = s.pgid ∧ r.1.cwd = s.cwd ∧ r.1.sig = s.sig ∧
      r.1.descs = s.descs ∧ r.1.writeLog = s.writeLog ∧
      (∀ fd : ℤ, 0 ≤ fd → fd ≤ 2 → r.1.getFd fd = s.getFd fd) ∧
      (∀ fd : ℤ, 3 ≤ fd → fd ≤ 2147483647 →
        Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = true → r.1.getFd fd = s.getFd fd) ∧
      (r.2.2 = false → CloseAbove2Post s extra_keep_fd keep_fds.val r.1)
  refine okPost_bind (okPost_loop_decr_nat (fun p => 2147483649 - p.1.val) inv donePost
    (fun p => postfork.fd_ops.try_close_range_except_loop.body extra_keep_fd keep_fds p.1 p.2)
    (3#u32, s) ?_ ⟨by dsimp; decide, by dsimp; decide, SameChildConfig.refl s, hRun, rfl, rfl, rfl, rfl, rfl,
      fun _ _ _ => rfl, fun fd h3 hlt => absurd hlt (by dsimp only at hlt; change ¬ fd < 3; omega), fun _ _ _ => rfl⟩)
    fun p hp => ?_
  · intro ⟨lo, s1⟩ hinv
    dsimp only [inv] at hinv
    rcases hinv with ⟨hlo3, hloMax, hcfg1, hRun1, hpg1, hcwd1, hsig1, hdescs1, hwl1, h02, hltlo, hgelo⟩
    unfold postfork.fd_ops.try_close_range_except_loop.body
    refine okPost_bind (next_keep_ge_spec extra_keep_fd keep_fds lo) fun o ho => ?_
    cases o with
    | none =>
      have hloU32 : lo.val ≤ core.num.U32.MAX.val := by
        have : core.num.U32.MAX.val = 4294967295 := by decide
        omega
      refine okPost_bind (sys_close_range_run_safety s1 hRun1 lo core.num.U32.MAX hloU32)
        fun p2 hp2 => ?_
      rcases p2 with ⟨r, s2⟩
      rcases hp2 with ⟨hcfg2, hRun2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hok2, herr2⟩
      dsimp only at hcfg2 hRun2 hpg2 hcwd2 hsig2 hdescs2 hwl2 hok2 herr2
      cases r with
      | Err e =>
        have hFds2 := herr2 e rfl
        have hGet2 : ∀ k, s2.getFd k = s1.getFd k := fun k => by simp [ChildState.getFd, hFds2]
        refine okPost_ok _ _ ⟨hcfg2.trans hcfg1, hRun2, hpg2.trans hpg1, hcwd2.trans hcwd1,
          hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1,
          fun fd hfd0 hfd2 => by rw [hGet2, h02 fd hfd0 hfd2],
          fun fd hfd3 hfdmax hkept => ?_,
          fun h => by simp at h⟩
        rw [hGet2]
        by_cases hfdlt : fd < lo.val
        · have h := hltlo fd hfd3 hfdlt
          simpa [hkept] using h
        · exact hgelo fd (by omega) hfdmax
      | Ok _ =>
        have hget2 := hok2 rfl
        refine okPost_ok _ _ ⟨hcfg2.trans hcfg1, hRun2, hpg2.trans hpg1, hcwd2.trans hcwd1,
          hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1,
          fun fd hfd0 hfd2 => by rw [hget2 fd, ite_eq_right (by omega)]; exact h02 fd hfd0 hfd2,
          fun fd hfd3 hfdmax hkept => ?_,
          fun _ => ⟨fun fd hfd0 hfd2 => by rw [hget2 fd, ite_eq_right (by omega)]; exact h02 fd hfd0 hfd2,
            fun fd hfd3 hfdmax => ?_⟩⟩
        · by_cases hfdlt : fd < lo.val
          · have hnot : ¬ ((lo.val : ℤ) ≤ fd ∧ fd ≤ core.num.U32.MAX.val) := by omega
            simp only [hget2 fd, hnot, ↓reduceIte]
            have h := hltlo fd hfd3 hfdlt
            simpa [hkept] using h
          · have hge : (lo.val : ℤ) ≤ fd := by omega
            have hnotkept := ho fd hge hfdmax
            simp [hkept] at hnotkept
        · by_cases hfdlt : fd < lo.val
          · have hnot : ¬ ((lo.val : ℤ) ≤ fd ∧ fd ≤ core.num.U32.MAX.val) := by omega
            simp only [hget2 fd, hnot, ↓reduceIte]
            exact hltlo fd hfd3 hfdlt
          · have hge : (lo.val : ℤ) ≤ fd := by omega
            have hnotkept : Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false := ho fd hge hfdmax
            have hlemax : fd ≤ core.num.U32.MAX.val := by
              have : (core.num.U32.MAX.val : ℤ) = 4294967295 := by decide
              omega
            simp only [hnotkept, Bool.false_eq_true, ↓reduceIte]
            rw [hget2 fd]
            simp only [hge, hlemax, and_self, ↓reduceIte]
    | some k =>
      rcases ho with ⟨hlok, _, hkmax, hkkept, hmink⟩
      obtain ⟨lo1, hok1, hval1⟩ := u32_add_one k (by omega)
      by_cases hkgt : k > lo
      · simp only [hkgt, ↓reduceIte]
        obtain ⟨hi, hokSub, hvalSub⟩ := u32_sub_one k (by scalar_tac)
        rw [hokSub, bind_ok]
        have hlohi : lo.val ≤ hi.val := by change lo.val < k.val at hkgt; omega
        refine okPost_bind (sys_close_range_run_safety s1 hRun1 lo hi hlohi) fun p2 hp2 => ?_
        rcases p2 with ⟨r, s2⟩
        rcases hp2 with ⟨hcfg2, hRun2, hpg2, hcwd2, hsig2, hdescs2, hwl2, hok2, herr2⟩
        dsimp only at hcfg2 hRun2 hpg2 hcwd2 hsig2 hdescs2 hwl2 hok2 herr2
        cases r with
        | Err e =>
          have hFds2 := herr2 e rfl
          have hGet2 : ∀ k, s2.getFd k = s1.getFd k := fun k => by simp [ChildState.getFd, hFds2]
          refine okPost_ok _ _ ⟨hcfg2.trans hcfg1, hRun2, hpg2.trans hpg1, hcwd2.trans hcwd1,
            hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1,
            fun fd hfd0 hfd2 => by rw [hGet2, h02 fd hfd0 hfd2],
            fun fd hfd3 hfdmax hkept => ?_,
            fun h => by simp at h⟩
          rw [hGet2]
          by_cases hfdlt : fd < lo.val
          · have h := hltlo fd hfd3 hfdlt
            simpa [hkept] using h
          · exact hgelo fd (by omega) hfdmax
        | Ok _ =>
          have hget2 := hok2 rfl
          change OkPost (do let lo1 ← k + 1#u32; Result.ok (ControlFlow.cont (lo1, s2))) _
          rw [hok1, bind_ok]
          refine okPost_ok _ _ ⟨⟨by dsimp; omega, by dsimp; omega, hcfg2.trans hcfg1, hRun2, hpg2.trans hpg1,
            hcwd2.trans hcwd1, hsig2.trans hsig1, hdescs2.trans hdescs1, hwl2.trans hwl1,
            fun fd hfd0 hfd2 => ?_, fun fd hfd3 hfdlt => ?_, fun fd hfdge hfdmax => ?_⟩, ?_⟩
          · rw [hget2 fd, ite_eq_right (by omega)]; exact h02 fd hfd0 hfd2
          · rw [hval1] at hfdlt
            by_cases hltlo' : fd < lo.val
            · have hnot : ¬ ((lo.val : ℤ) ≤ fd ∧ fd ≤ hi.val) := by omega
              simp only [hget2 fd, hnot, ↓reduceIte]
              exact hltlo fd hfd3 hltlo'
            · by_cases hfk : fd = k.val
              · subst hfk
                simp only [hkkept, ↓reduceIte]
                have hnot : ¬ ((lo.val : ℤ) ≤ k.val ∧ (k.val : ℤ) ≤ hi.val) := by omega
                simp only [hget2 k.val, hnot, ↓reduceIte]
                exact hgelo k.val hlok hkmax
              · have hge : (lo.val : ℤ) ≤ fd := by omega
                have hlt : fd < k.val := by omega
                have hnotkept : Model.isKeptAbove2 extra_keep_fd keep_fds.val fd = false := hmink fd hge hlt
                have hlehi : fd ≤ hi.val := by omega
                simp only [hnotkept, Bool.false_eq_true, ↓reduceIte]
                rw [hget2 fd]
                simp only [hge, hlehi, and_self, ↓reduceIte]
          · dsimp only at hfdge
            rw [hval1] at hfdge
            have hnot : ¬ ((lo.val : ℤ) ≤ fd ∧ fd ≤ hi.val) := by omega
            simp only [hget2 fd, hnot, ↓reduceIte]
            exact hgelo fd (by omega) hfdmax
          · dsimp; omega
      · simp only [hkgt, ↓reduceIte]
        rw [hok1, bind_ok]
        have hkeq : k.val = lo.val := by change ¬ (lo.val < k.val) at hkgt; omega
        refine okPost_ok _ _ ⟨⟨by dsimp; omega, by dsimp; omega, hcfg1, hRun1, hpg1, hcwd1, hsig1, hdescs1, hwl1,
          h02, fun fd hfd3 hfdlt => ?_, fun fd hfdge hfdmax => ?_⟩, ?_⟩
        · dsimp only at hfdlt
          rw [hval1, hkeq] at hfdlt
          by_cases hltlo' : fd < lo.val
          · exact hltlo fd hfd3 hltlo'
          · have hfeq : fd = k.val := by omega
            subst hfeq
            simp only [hkkept, ↓reduceIte]
            exact hgelo k.val hlok hkmax
        · dsimp only at hfdge
          rw [hval1] at hfdge
          exact hgelo fd (by omega) hfdmax
        · dsimp; omega
  · rcases p with ⟨s2, err, failed⟩
    dsimp only [donePost] at hp
    rcases hp with ⟨hcfg, hRun2, hpg, hcwd, hsig, hdescs, hwl, h02, hkept, hpost⟩
    change OkPost (if failed = true then Result.ok (core.result.Result.Err err, s2)
      else Result.ok (core.result.Result.Ok (), s2)) _
    split
    · next hf =>
      exact okPost_ok _ _ ⟨hcfg, hRun2, hpg, hcwd, hsig, hdescs, hwl, h02, hkept, fun h => by cases h⟩
    · next hnf =>
      have hff : failed = false := Bool.eq_false_iff.mpr hnf
      exact okPost_ok _ _ ⟨hcfg, hRun2, hpg, hcwd, hsig, hdescs, hwl, h02, hkept, fun _ => hpost hff⟩

end TryCloseRangeExcept

/-- Arbitrary-oracle safety specification for `postfork.fd_ops.clear_cloexec`. -/
theorem clear_cloexec_safety (s : ChildState) (hRun : s.status = .running) (fd : I32) :
    OkPost (postfork.fd_ops.clear_cloexec s fd) fun p =>
      p.2.status = .running ∧ SameChildConfig p.2 s ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      (p.1 = .Ok () → CloexecTogglePost false s fd (.Ok ()) p.2) := by
  unfold postfork.fd_ops.clear_cloexec
  obtain ⟨r1, s1, h1, hs1eq, _, _, hget1⟩ := sys_fcntl_getfd_running s hRun fd
  rw [h1, bind_ok]
  have hs1Cfg : SameChildConfig s1 s := by
    rw [hs1eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hs1Run : s1.status = .running := by rw [hs1eq]; exact hRun
  have hs1Pg : s1.pgid = s.pgid := by rw [hs1eq]
  have hs1Cw : s1.cwd = s.cwd := by rw [hs1eq]
  have hs1Si : s1.sig = s.sig := by rw [hs1eq]
  have hs1De : s1.descs = s.descs := by rw [hs1eq]
  have hs1Wl : s1.writeLog = s.writeLog := by rw [hs1eq]
  have hs1Fds : s1.fds = s.fds := by rw [hs1eq]
  have hs1Mask : s1.kernelMasksSetfd = s.kernelMasksSetfd := by rw [hs1eq]
  cases hf : currentFault s with
  | seccomp rawE =>
    rw [hf] at hget1
    rw [hget1]
    exact okPost_ok _ _ ⟨hs1Run, hs1Cfg, hs1Pg, hs1Cw, hs1Si, hs1De, hs1Wl, fun h => by cases h⟩
  | fail rawE =>
    cases hFd : s.getFd fd.val <;> (
      rw [hFd, hf] at hget1
      rw [hget1]
      exact okPost_ok _ _ ⟨hs1Run, hs1Cfg, hs1Pg, hs1Cw, hs1Si, hs1De, hs1Wl, fun h => by cases h⟩)
  | normal | partialWrite _ | dentsBatch _ =>
    cases hFd : s.getFd fd.val with
    | none =>
      rw [hFd, hf] at hget1
      rw [hget1]
      exact okPost_ok _ _ ⟨hs1Run, hs1Cfg, hs1Pg, hs1Cw, hs1Si, hs1De, hs1Wl, fun h => by cases h⟩
    | some e =>
      rw [hFd, hf] at hget1
      rw [hget1]
      change OkPost (do
        let i ← lift (~~~postfork.fd_ops.FD_CLOEXEC)
        let i1 ← lift ((fdFlagsWord e) &&& i)
        sys.fcntl_setfd s1 fd i1) _
      have hclo : postfork.fd_ops.FD_CLOEXEC = 1#i32 := by
        unfold postfork.fd_ops.FD_CLOEXEC; rfl
      rw [show lift (~~~postfork.fd_ops.FD_CLOEXEC) = Result.ok (~~~1#i32) from by rw [hclo]; rfl,
        bind_ok,
        show lift ((fdFlagsWord e) &&& (~~~1#i32)) =
          Result.ok ((fdFlagsWord e) &&& (~~~1#i32)) from rfl,
        bind_ok]
      obtain ⟨r2, s2, h2, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, _, hErr2, hOk2, _⟩ :=
        sys_fcntl_setfd_running s1 hs1Run fd ((fdFlagsWord e) &&& (~~~1#i32))
      rw [h2]
      refine okPost_ok _ _ ⟨(hcfg2.trans hs1Cfg).status.trans hRun, hcfg2.trans hs1Cfg,
        hpg2.trans hs1Pg, hcw2.trans hs1Cw, hsi2.trans hs1Si, hde2.trans hs1De, hwl2.trans hs1Wl,
        fun hr2 => ?_⟩
      subst hr2
      have hfd2 := hOk2 rfl
      have hs1Get : s1.getFd fd.val = some e := by rw [getFd_eq_of_fds_eq hs1Fds, hFd]
      have hs2GetEq := fun k => getFd_eq_of_fds_eq hfd2 k
      simp only [hs1Get] at hs2GetEq
      have hupd := updateFdFlags_clear_cloexec s e
      change CloexecTogglePost false s fd (.Ok ()) s2
      simp only [CloexecTogglePost, hFd]
      refine ⟨trivial, ?_, fun k hne => ?_⟩
      · rw [hs2GetEq fd.val, getFd_putSlot_self, hs1Mask]; exact congrArg some hupd
      · rw [hs2GetEq k, getFd_putSlot_ne _ hne, getFd_eq_of_fds_eq hs1Fds]

/-- Arbitrary-oracle safety specification for `postfork.fd_ops.probe_stdio_open`. -/
theorem probe_stdio_open_safety (s : ChildState) (hRun : s.status = .running)
    (stdin_fd stdout_fd stderr_fd : I32) :
    OkPost (postfork.fd_ops.probe_stdio_open s stdin_fd stdout_fd stderr_fd) fun p =>
      p.2.status = .running ∧ SameChildConfig p.2 s ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.fds = s.fds ∧ p.2.writeLog = s.writeLog ∧
      (p.1 = .Ok () →
        0#i32 ≤ stdin_fd ∧ 0#i32 ≤ stdout_fd ∧ 0#i32 ≤ stderr_fd ∧
        s.isOpen stdin_fd.val = true ∧ s.isOpen stdout_fd.val = true ∧ s.isOpen stderr_fd.val = true) := by
  unfold postfork.fd_ops.probe_stdio_open
  by_cases h0 : stdin_fd < 0#i32
  · simp only [h0, ↓reduceIte]
    exact okPost_ok _ _ ⟨hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, rfl, fun h => by cases h⟩
  · by_cases h1 : stdout_fd < 0#i32
    · simp only [h0, ↓reduceIte, h1]
      exact okPost_ok _ _ ⟨hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, rfl, fun h => by cases h⟩
    · by_cases h2 : stderr_fd < 0#i32
      · simp only [h0, ↓reduceIte, h1, h2]
        exact okPost_ok _ _ ⟨hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, rfl, fun h => by cases h⟩
      · simp only [h0, ↓reduceIte, h1, h2]
        have hn0 : 0#i32 ≤ stdin_fd := by scalar_tac
        have hn1 : 0#i32 ≤ stdout_fd := by scalar_tac
        have hn2 : 0#i32 ≤ stderr_fd := by scalar_tac
        obtain ⟨r1, s1, h1eq, hs1eq, _, _, hg1⟩ := sys_fcntl_getfd_running s hRun stdin_fd
        rw [h1eq, bind_ok]
        have hs1Cfg : SameChildConfig s1 s := by
          rw [hs1eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hs1Run : s1.status = .running := by rw [hs1eq]; exact hRun
        have hs1Fds : s1.fds = s.fds := by rw [hs1eq]
        cases r1 with
        | Err e =>
          exact okPost_ok _ _ ⟨hs1Run, hs1Cfg, by rw [hs1eq], by rw [hs1eq], by rw [hs1eq],
            by rw [hs1eq], hs1Fds, by rw [hs1eq], fun h => by cases h⟩
        | Ok v1 =>
          have hOpen0 : s.isOpen stdin_fd.val = true := by
            cases hcf : currentFault s with
            | seccomp rawE => rw [hcf] at hg1; cases hg1
            | fail _ | normal | partialWrite _ | dentsBatch _ =>
              cases hG : s.getFd stdin_fd.val with
              | none => rw [hcf, hG] at hg1; cases hg1
              | some _ => simp [ChildState.isOpen, hG]
          obtain ⟨r2, s2, h2eq, hs2eq, _, _, hg2⟩ := sys_fcntl_getfd_running s1 hs1Run stdout_fd
          change OkPost (do
            let (r1, s2') ← sys.fcntl_getfd s1 stdout_fd
            match r1 with
            | core.result.Result.Ok _ => do
              let (r2, s3) ← sys.fcntl_getfd s2' stderr_fd
              match r2 with
              | core.result.Result.Ok _ => Result.ok (core.result.Result.Ok (), s3)
              | core.result.Result.Err e => Result.ok (core.result.Result.Err e, s3)
            | core.result.Result.Err e => Result.ok (core.result.Result.Err e, s2')) _
          rw [h2eq, bind_ok]
          have hs2Cfg : SameChildConfig s2 s := by
            rw [hs2eq, hs1eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          have hs2Run : s2.status = .running := by rw [hs2eq]; exact hs1Run
          have hs2Fds : s2.fds = s.fds := by rw [hs2eq, hs1Fds]
          cases r2 with
          | Err e =>
            exact okPost_ok _ _ ⟨hs2Run, hs2Cfg, by rw [hs2eq, hs1eq], by rw [hs2eq, hs1eq],
              by rw [hs2eq, hs1eq], by rw [hs2eq, hs1eq], hs2Fds, by rw [hs2eq, hs1eq], fun h => by cases h⟩
          | Ok v2 =>
            have hOpen1 : s.isOpen stdout_fd.val = true := by
              unfold ChildState.isOpen
              rw [← getFd_eq_of_fds_eq hs1Fds]
              cases hcf : currentFault s1 with
              | seccomp rawE => rw [hcf] at hg2; cases hg2
              | fail _ | normal | partialWrite _ | dentsBatch _ =>
                cases hG : s1.getFd stdout_fd.val with
                | none => rw [hcf, hG] at hg2; cases hg2
                | some _ => rfl
            obtain ⟨r3, s3, h3eq, hs3eq, _, _, hg3⟩ := sys_fcntl_getfd_running s2 hs2Run stderr_fd
            change OkPost (do
              let (r2, s3') ← sys.fcntl_getfd s2 stderr_fd
              match r2 with
              | core.result.Result.Ok _ => Result.ok (core.result.Result.Ok (), s3')
              | core.result.Result.Err e => Result.ok (core.result.Result.Err e, s3')) _
            rw [h3eq, bind_ok]
            have hs3Cfg : SameChildConfig s3 s := by
              rw [hs3eq, hs2eq, hs1eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            have hs3Run : s3.status = .running := by rw [hs3eq]; exact hs2Run
            have hs3Fds : s3.fds = s.fds := by rw [hs3eq, hs2Fds]
            cases r3 with
            | Err e =>
              exact okPost_ok _ _ ⟨hs3Run, hs3Cfg, by rw [hs3eq, hs2eq, hs1eq], by rw [hs3eq, hs2eq, hs1eq],
                by rw [hs3eq, hs2eq, hs1eq], by rw [hs3eq, hs2eq, hs1eq], hs3Fds,
                by rw [hs3eq, hs2eq, hs1eq], fun h => by cases h⟩
            | Ok v3 =>
              have hOpen2 : s.isOpen stderr_fd.val = true := by
                unfold ChildState.isOpen
                rw [← getFd_eq_of_fds_eq hs2Fds]
                cases hcf : currentFault s2 with
                | seccomp rawE => rw [hcf] at hg3; cases hg3
                | fail _ | normal | partialWrite _ | dentsBatch _ =>
                  cases hG : s2.getFd stderr_fd.val with
                  | none => rw [hcf, hG] at hg3; cases hg3
                  | some _ => rfl
              exact okPost_ok _ _ ⟨hs3Run, hs3Cfg, by rw [hs3eq, hs2eq, hs1eq], by rw [hs3eq, hs2eq, hs1eq],
                by rw [hs3eq, hs2eq, hs1eq], by rw [hs3eq, hs2eq, hs1eq], hs3Fds,
                by rw [hs3eq, hs2eq, hs1eq], fun _ => ⟨hn0, hn1, hn2, hOpen0, hOpen1, hOpen2⟩⟩

private theorem setupStdioClear012_safety (s : sys.Sys) (hRun : s.status = .running)
    {e0 e1 e2 : FdEntry} (h0 : s.getFd 0 = some e0) (h1 : s.getFd 1 = some e1)
    (h2 : s.getFd 2 = some e2) :
    OkPost (setupStdioClear012 s) fun p =>
      p.2.status = .running ∧ SameChildConfig p.2 s ∧
      p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧ p.2.sig = s.sig ∧
      p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
      (p.1 = .Ok () →
        (∃ f0, p.2.getFd 0 = some f0 ∧ f0.desc = e0.desc ∧ f0.cloexec = false) ∧
        (∃ f1, p.2.getFd 1 = some f1 ∧ f1.desc = e1.desc ∧ f1.cloexec = false) ∧
        (∃ f2, p.2.getFd 2 = some f2 ∧ f2.desc = e2.desc ∧ f2.cloexec = false) ∧
        (∀ k > 2, p.2.getFd k = s.getFd k)) := by
  unfold setupStdioClear012
  refine okPost_bind (clear_cloexec_safety s hRun 0#i32) fun ⟨r6, s10⟩ hs10 => ?_
  dsimp only at hs10
  rcases hs10 with ⟨hs10Run, hcfg0, hpg0, hcw0, hsi0, hde0, hwl0, hOk0⟩
  cases r6 with
  | Err e =>
    exact okPost_ok _ _ ⟨hs10Run, hcfg0, hpg0, hcw0, hsi0, hde0, hwl0, fun h => by cases h⟩
  | Ok _ =>
    have hct0 := hOk0 rfl
    change CloexecTogglePost false s 0#i32 (.Ok ()) s10 at hct0
    simp only [CloexecTogglePost, show (0#i32 : I32).val = 0 by decide, h0] at hct0
    rcases hct0 with ⟨_, hs10_0, hs10_ne⟩
    refine okPost_bind (clear_cloexec_safety s10 hs10Run 1#i32) fun ⟨r7, s12⟩ hs12 => ?_
    dsimp only at hs12
    rcases hs12 with ⟨hs12Run, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hOk1⟩
    have hs10_1 : s10.getFd 1 = some e1 := by rw [hs10_ne 1 (by omega), h1]
    cases r7 with
    | Err e =>
      exact okPost_ok _ _ ⟨hs12Run, hcfg1.trans hcfg0, hpg1.trans hpg0, hcw1.trans hcw0,
        hsi1.trans hsi0, hde1.trans hde0, hwl1.trans hwl0, fun h => by cases h⟩
    | Ok _ =>
      have hct1 := hOk1 rfl
      change CloexecTogglePost false s10 1#i32 (.Ok ()) s12 at hct1
      simp only [CloexecTogglePost, show (1#i32 : I32).val = 1 by decide, hs10_1] at hct1
      rcases hct1 with ⟨_, hs12_1, hs12_ne⟩
      refine okPost_mono (clear_cloexec_safety s12 hs12Run 2#i32) fun ⟨r8, s13⟩ hs13 => ?_
      dsimp only at hs13
      rcases hs13 with ⟨hs13Run, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, hOk2⟩
      refine ⟨hs13Run, hcfg2.trans (hcfg1.trans hcfg0), hpg2.trans (hpg1.trans hpg0),
        hcw2.trans (hcw1.trans hcw0), hsi2.trans (hsi1.trans hsi0), hde2.trans (hde1.trans hde0),
        hwl2.trans (hwl1.trans hwl0), fun hr8 => ?_⟩
      have hct2 := hOk2 hr8
      have hs12_2 : s12.getFd 2 = some e2 := by rw [hs12_ne 2 (by omega), hs10_ne 2 (by omega), h2]
      change CloexecTogglePost false s12 2#i32 (.Ok ()) s13 at hct2
      simp only [CloexecTogglePost, show (2#i32 : I32).val = 2 by decide, hs12_2] at hct2
      rcases hct2 with ⟨_, hs13_2, hs13_ne⟩
      have hs13_0 : s13.getFd 0 =
          some { desc := e0.desc, cloexec := false, extraFdFlags := expectedExtraFlagsAfterSetfd s e0 } := by
        rw [hs13_ne 0 (by omega), hs12_ne 0 (by omega), hs10_0]
      have hs13_1 : s13.getFd 1 =
          some { desc := e1.desc, cloexec := false, extraFdFlags := expectedExtraFlagsAfterSetfd s10 e1 } := by
        rw [hs13_ne 1 (by omega), hs12_1]
      refine ⟨⟨_, hs13_0, rfl, rfl⟩, ⟨_, hs13_1, rfl, rfl⟩, ⟨_, hs13_2, rfl, rfl⟩, fun k hk => ?_⟩
      rw [hs13_ne k (by omega), hs12_ne k (by omega), hs10_ne k (by omega)]

/-- Seccomp-tolerant safety postcondition for `setupStdio`. -/
def SetupStdioSafetyPost
    (s : ChildState)
    (inFd outFd errFd : Std.I32)
    (closeAbove2 : Bool)
    (s' : ChildState) : Prop :=
  (∃ e0 f0, s.getFd inFd.val = some e0 ∧ s'.getFd 0 = some f0 ∧ f0.desc = e0.desc ∧ f0.cloexec = false) ∧
  (∃ e1 f1, s.getFd outFd.val = some e1 ∧ s'.getFd 1 = some f1 ∧ f1.desc = e1.desc ∧ f1.cloexec = false) ∧
  (∃ e2 f2, s.getFd errFd.val = some e2 ∧ s'.getFd 2 = some f2 ∧ f2.desc = e2.desc ∧ f2.cloexec = false) ∧
  (∀ k > 2, (closeAbove2 = false ∨ (k ≠ inFd.val ∧ k ≠ outFd.val ∧ k ≠ errFd.val)) →
    s.getFd k ≠ none → s'.getFd k = s.getFd k) ∧
  (oracleHasSeccomp s.oracle = false → SetupStdioPost s inFd outFd errFd closeAbove2 s')

private theorem close_getFd_safe {s s' : sys.Sys} {fd : I32}
    (hfds : s'.fds = match currentFault s with | .seccomp _ => s.fds | _ => (s.closeSlot fd.val).fds) :
    (∀ k, k ≠ fd.val → s'.getFd k = s.getFd k) ∧
    (oracleHasSeccomp s.oracle = false → ∀ k, s'.getFd k = if k = fd.val then none else s.getFd k) := by
  refine ⟨fun k hk => ?_, fun hor k => ?_⟩
  · cases hf : currentFault s <;> rw [hf] at hfds
    all_goals
      try (rw [getFd_eq_of_fds_eq hfds]; exact getFd_closeSlot_ne s hk)
    rw [getFd_eq_of_fds_eq hfds]
  · cases hf : currentFault s <;> rw [hf] at hfds
    all_goals
      try (
        rw [getFd_eq_of_fds_eq hfds]
        by_cases hk : k = fd.val
        · subst hk; simp [getFd_closeSlot_self]
        · simp [hk, getFd_closeSlot_ne s hk])
    exact False.elim (not_seccomp_of_oracleHasSeccomp_false hor hf)

private theorem setupStdioCloseAbove2_safety (s : sys.Sys) (hRun : s.status = .running)
    (stdin_fd stdout_fd stderr_fd : I32) :
    OkPost (setupStdioCloseAbove2 s stdin_fd stdout_fd stderr_fd) fun s' =>
      s'.status = .running ∧ SameChildConfig s' s ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      (∀ k, (k ≤ 2 ∨ (k ≠ stdin_fd.val ∧ k ≠ stdout_fd.val ∧ k ≠ stderr_fd.val)) → s'.getFd k = s.getFd k) ∧
      (oracleHasSeccomp s.oracle = false → ∀ k > 2, s'.getFd k =
        if (k == stdin_fd.val || k == stdout_fd.val || k == stderr_fd.val) = true then none else s.getFd k) := by
  unfold setupStdioCloseAbove2
  have h1 : OkPost (if stdin_fd > 2#i32 then do let (_, s12) ← sys.close s stdin_fd; Result.ok s12 else Result.ok s)
      fun s10 => s10.status = .running ∧ SameChildConfig s10 s ∧
        s10.pgid = s.pgid ∧ s10.cwd = s.cwd ∧ s10.sig = s.sig ∧
        s10.descs = s.descs ∧ s10.writeLog = s.writeLog ∧
        (∀ k, (k ≤ 2 ∨ k ≠ stdin_fd.val) → s10.getFd k = s.getFd k) ∧
        (oracleHasSeccomp s.oracle = false → ∀ k > 2, s10.getFd k = if (k == stdin_fd.val) = true then none else s.getFd k) := by
    by_cases hgt : stdin_fd > 2#i32
    · simp only [hgt, ↓reduceIte]
      obtain ⟨r1, s12, hEq, hcfg, hpg, hcw, hsi, hde, hwl, _, hfds, _⟩ := sys_close_running s hRun stdin_fd
      rw [hEq, bind_ok]
      obtain ⟨hne, hor⟩ := close_getFd_safe hfds
      refine okPost_ok _ _ ⟨hcfg.status.trans hRun, hcfg, hpg, hcw, hsi, hde, hwl,
        fun k hk => hne k (by rcases hk with h | h; scalar_tac; exact h), fun hor0 k _ => ?_⟩
      rw [hor hor0 k]; by_cases hke : k = stdin_fd.val <;> simp [hke]
    · simp only [hgt, ↓reduceIte]
      refine okPost_ok _ _ ⟨hRun, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl,
        fun _ _ => rfl, fun _ k hk => ?_⟩
      have hne : (k == stdin_fd.val) = false := beq_false_of_ne (by scalar_tac)
      simp [hne]
  refine okPost_bind h1 fun s10 ⟨hs10Run, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1, hle1, hgt1⟩ => ?_
  have h2 : OkPost (if stdout_fd > 2#i32 then if (stdout_fd != stdin_fd) = true then do let (_, s13) ← sys.close s10 stdout_fd; Result.ok s13 else Result.ok s10 else Result.ok s10)
      fun s12 => s12.status = .running ∧ SameChildConfig s12 s ∧
        s12.pgid = s.pgid ∧ s12.cwd = s.cwd ∧ s12.sig = s.sig ∧
        s12.descs = s.descs ∧ s12.writeLog = s.writeLog ∧
        (∀ k, (k ≤ 2 ∨ (k ≠ stdin_fd.val ∧ k ≠ stdout_fd.val)) → s12.getFd k = s.getFd k) ∧
        (oracleHasSeccomp s.oracle = false → ∀ k > 2, s12.getFd k = if (k == stdin_fd.val || k == stdout_fd.val) = true then none else s.getFd k) := by
    by_cases hgt : stdout_fd > 2#i32
    · by_cases hne : (stdout_fd != stdin_fd) = true
      · simp only [hgt, ↓reduceIte, hne]
        obtain ⟨r2, s13, hEq, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, _, hfds2, _⟩ :=
          sys_close_running s10 hs10Run stdout_fd
        rw [hEq, bind_ok]
        obtain ⟨hne2, hor2⟩ := close_getFd_safe hfds2
        refine okPost_ok _ _ ⟨hcfg2.status.trans hs10Run, hcfg2.trans hcfg1, hpg2.trans hpg1,
          hcw2.trans hcw1, hsi2.trans hsi1, hde2.trans hde1, hwl2.trans hwl1,
          fun k hk => (hne2 k (by rcases hk with h | h; scalar_tac; exact h.2)).trans
            (hle1 k (by rcases hk with h | h; exact Or.inl h; exact Or.inr h.1)), fun hor0 k hk => ?_⟩
        rw [hor2 (by rw [hcfg1.oracle]; exact hor0) k, hgt1 hor0 k hk]
        by_cases hk2 : k = stdout_fd.val <;> simp [hk2]
      · have heq : stdout_fd.val = stdin_fd.val := by
          have : ¬(stdout_fd ≠ stdin_fd) := by simpa using hne
          rw [not_not] at this; rw [this]
        simp only [hgt, ↓reduceIte, hne]
        refine okPost_ok _ _ ⟨hs10Run, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1,
          fun k hk => hle1 k (by rcases hk with h | h; exact Or.inl h; exact Or.inr h.1), fun hor0 k hk => ?_⟩
        rw [hgt1 hor0 k hk, heq]; by_cases hk2 : k = stdin_fd.val <;> simp [hk2]
    · simp only [hgt, ↓reduceIte]
      refine okPost_ok _ _ ⟨hs10Run, hcfg1, hpg1, hcw1, hsi1, hde1, hwl1,
        fun k hk => hle1 k (by rcases hk with h | h; exact Or.inl h; exact Or.inr h.1), fun hor0 k hk => ?_⟩
      have hne : (k == stdout_fd.val) = false := beq_false_of_ne (by scalar_tac)
      simp [hgt1 hor0 k hk, hne]
  refine okPost_bind h2 fun s12 ⟨hs12Run, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, hle2, hgt2⟩ => ?_
  by_cases hgt : stderr_fd > 2#i32
  · by_cases hne1 : (stderr_fd != stdin_fd) = true
    · by_cases hne2 : (stderr_fd != stdout_fd) = true
      · simp only [hgt, ↓reduceIte, hne1, hne2]
        obtain ⟨r3, s13, hEq, hcfg3, hpg3, hcw3, hsi3, hde3, hwl3, _, hfds3, _⟩ :=
          sys_close_running s12 hs12Run stderr_fd
        rw [hEq, bind_ok]
        obtain ⟨hne3, hor3⟩ := close_getFd_safe hfds3
        refine okPost_ok _ _ ⟨hcfg3.status.trans hs12Run, hcfg3.trans hcfg2, hpg3.trans hpg2,
          hcw3.trans hcw2, hsi3.trans hsi2, hde3.trans hde2, hwl3.trans hwl2,
          fun k hk => (hne3 k (by rcases hk with h | h; scalar_tac; exact h.2.2)).trans
            (hle2 k (by rcases hk with h | h; exact Or.inl h; exact Or.inr ⟨h.1, h.2.1⟩)), fun hor0 k hk => ?_⟩
        rw [hor3 (by rw [hcfg2.oracle]; exact hor0) k, hgt2 hor0 k hk]
        by_cases hk3 : k = stderr_fd.val <;> simp [hk3]
      · have heq : stderr_fd.val = stdout_fd.val := by
          have : ¬(stderr_fd ≠ stdout_fd) := by simpa using hne2
          rw [not_not] at this; rw [this]
        simp only [hgt, ↓reduceIte, hne1, hne2]
        refine okPost_ok _ _ ⟨hs12Run, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2,
          fun k hk => hle2 k (by rcases hk with h | h; exact Or.inl h; exact Or.inr ⟨h.1, h.2.1⟩), fun hor0 k hk => ?_⟩
        rw [hgt2 hor0 k hk, heq]; by_cases hk3 : k = stdout_fd.val <;> simp [hk3]
    · have heq : stderr_fd.val = stdin_fd.val := by
        have : ¬(stderr_fd ≠ stdin_fd) := by simpa using hne1
        rw [not_not] at this; rw [this]
      simp only [hgt, ↓reduceIte, hne1]
      refine okPost_ok _ _ ⟨hs12Run, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2,
        fun k hk => hle2 k (by rcases hk with h | h; exact Or.inl h; exact Or.inr ⟨h.1, h.2.1⟩), fun hor0 k hk => ?_⟩
      rw [hgt2 hor0 k hk, heq]; by_cases hk3 : k = stdin_fd.val <;> simp [hk3]
  · simp only [hgt, ↓reduceIte]
    refine okPost_ok _ _ ⟨hs12Run, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2,
      fun k hk => hle2 k (by rcases hk with h | h; exact Or.inl h; exact Or.inr ⟨h.1, h.2.1⟩), fun hor0 k hk => ?_⟩
    have hne : (k == stderr_fd.val) = false := beq_false_of_ne (by scalar_tac)
    simp [hgt2 hor0 k hk, hne]

private theorem setupStdioCloseTmpsErr_safety (s : sys.Sys) (hRun : s.status = .running)
    (tmp0 tmp1 : I32) (r : core.result.Result Unit I32) :
    OkPost (setupStdioCloseTmpsErr s tmp0 tmp1 r) fun p => p.2.status = .running ∧ p.1 = r := by
  unfold setupStdioCloseTmpsErr
  have h1 : OkPost (if tmp1 ≥ 0#i32 then do let (_, s8) ← sys.close s tmp1; Result.ok s8 else Result.ok s)
      fun s7 => s7.status = .running := by
    by_cases h : tmp1 ≥ 0#i32
    · simp only [h, ↓reduceIte]
      obtain ⟨_, s8, hEq, hcfg, _⟩ := sys_close_running s hRun tmp1
      rw [hEq, bind_ok]
      exact okPost_ok _ _ (hcfg.status.trans hRun)
    · simp only [h, ↓reduceIte]
      exact okPost_ok _ _ hRun
  refine okPost_bind h1 fun s7 hs7 => ?_
  by_cases h : tmp0 ≥ 0#i32
  · simp only [h, ↓reduceIte]
    obtain ⟨_, s8, hEq, hcfg, _⟩ := sys_close_running s7 hs7 tmp0
    rw [hEq, bind_ok]
    exact okPost_ok _ _ ⟨hcfg.status.trans hs7, rfl⟩
  · simp only [h, ↓reduceIte]
    exact okPost_ok _ _ ⟨hs7, rfl⟩

private theorem setupStdioFinish_safety (s sOrig : sys.Sys) (tmp0 tmp1 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool)
    (hRun : s.status = .running) (hCfg : SameChildConfig s sOrig)
    (hPg : s.pgid = sOrig.pgid) (hCw : s.cwd = sOrig.cwd)
    (hSi : s.sig = sOrig.sig) (hDe : s.descs = sOrig.descs) (hWl : s.writeLog = sOrig.writeLog)
    {e0 e1 e2 f0 f1 f2 : FdEntry}
    (hs0 : s.getFd 0 = some f0) (hd0 : f0.desc = e0.desc)
    (hs1 : s.getFd 1 = some f1) (hd1 : f1.desc = e1.desc)
    (hs2 : s.getFd 2 = some f2) (hd2 : f2.desc = e2.desc)
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2)
    (ht0 : tmp0 < 0#i32 ∨ (3 ≤ tmp0.val ∧ sOrig.getFd tmp0.val = none))
    (ht1 : tmp1 < 0#i32 ∨ (3 ≤ tmp1.val ∧ sOrig.getFd tmp1.val = none))
    (hAbove : ∀ k > 2, k ≠ tmp0.val → k ≠ tmp1.val → s.getFd k = sOrig.getFd k) :
    OkPost (setupStdioFinish s tmp0 tmp1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.status = .running ∧ SameChildConfig p.2 sOrig ∧
      p.2.pgid = sOrig.pgid ∧ p.2.cwd = sOrig.cwd ∧ p.2.sig = sOrig.sig ∧
      p.2.descs = sOrig.descs ∧ p.2.writeLog = sOrig.writeLog ∧
      (p.1 = .Ok () → SetupStdioSafetyPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2) := by
  unfold setupStdioFinish
  have hClose1 : OkPost (if tmp1 ≥ 0#i32 then do let (_, s8) ← sys.close s tmp1; Result.ok s8 else Result.ok s)
      fun s7 => s7.status = .running ∧ SameChildConfig s7 sOrig ∧
        s7.pgid = sOrig.pgid ∧ s7.cwd = sOrig.cwd ∧ s7.sig = sOrig.sig ∧
        s7.descs = sOrig.descs ∧ s7.writeLog = sOrig.writeLog ∧
        (∀ k ≤ 2, s7.getFd k = s.getFd k) ∧
        (∀ k > 2, k ≠ tmp0.val → sOrig.getFd k ≠ none → s7.getFd k = sOrig.getFd k) ∧
        (oracleHasSeccomp sOrig.oracle = false → ∀ k > 2, k ≠ tmp0.val → s7.getFd k = sOrig.getFd k) := by
    by_cases h1 : tmp1 ≥ 0#i32
    · rcases ht1 with ht1neg | ⟨ht1_3, ht1_none⟩
      · exfalso; scalar_tac
      · simp only [h1, ↓reduceIte]
        obtain ⟨_, s8, hEq, hcfg, hpg, hcw, hsi, hde, hwl, _, hfds, _⟩ := sys_close_running s hRun tmp1
        rw [hEq, bind_ok]
        obtain ⟨hne1, hor1⟩ := close_getFd_safe hfds
        refine okPost_ok _ _ ⟨hcfg.status.trans hRun, hcfg.trans hCfg, hpg.trans hPg, hcw.trans hCw,
          hsi.trans hSi, hde.trans hDe, hwl.trans hWl,
          fun k hk => hne1 k (by omega),
          fun k hk hne0 hsome => ?_,
          fun hor0 k hk hne0 => ?_⟩
        · have hneTmp1 : k ≠ tmp1.val := fun h => hsome (h ▸ ht1_none)
          exact (hne1 k hneTmp1).trans (hAbove k hk hne0 hneTmp1)
        · rw [hor1 (by rw [hCfg.oracle]; exact hor0) k]
          by_cases hke : k = tmp1.val
          · subst hke; simp [ht1_none]
          · simp only [hke, ↓reduceIte]; exact hAbove k hk hne0 hke
    · simp only [h1, ↓reduceIte]
      have hne1 : ∀ k > 2, k ≠ tmp1.val := fun k hk => by
        rcases ht1 with ht1neg | ⟨_, _⟩
        · scalar_tac
        · exfalso; apply h1; scalar_tac
      refine okPost_ok _ _ ⟨hRun, hCfg, hPg, hCw, hSi, hDe, hWl, fun _ _ => rfl,
        fun k hk hne0 _ => hAbove k hk hne0 (hne1 k hk),
        fun _ k hk hne0 => hAbove k hk hne0 (hne1 k hk)⟩
  refine okPost_bind hClose1 fun s7 ⟨hs7Run, hcfg7, hpg7, hcw7, hsi7, hde7, hwl7, hle7, hne7, hgt7⟩ => ?_
  have hClose0 : OkPost (if tmp0 ≥ 0#i32 then do let (_, s9) ← sys.close s7 tmp0; Result.ok s9 else Result.ok s7)
      fun s8 => s8.status = .running ∧ SameChildConfig s8 sOrig ∧
        s8.pgid = sOrig.pgid ∧ s8.cwd = sOrig.cwd ∧ s8.sig = sOrig.sig ∧
        s8.descs = sOrig.descs ∧ s8.writeLog = sOrig.writeLog ∧
        (∀ k ≤ 2, s8.getFd k = s.getFd k) ∧
        (∀ k > 2, sOrig.getFd k ≠ none → s8.getFd k = sOrig.getFd k) ∧
        (oracleHasSeccomp sOrig.oracle = false → ∀ k > 2, s8.getFd k = sOrig.getFd k) := by
    by_cases h0 : tmp0 ≥ 0#i32
    · rcases ht0 with ht0neg | ⟨ht0_3, ht0_none⟩
      · exfalso; scalar_tac
      · simp only [h0, ↓reduceIte]
        obtain ⟨_, s9, hEq, hcfg, hpg, hcw, hsi, hde, hwl, _, hfds, _⟩ := sys_close_running s7 hs7Run tmp0
        rw [hEq, bind_ok]
        obtain ⟨hne0, hor0⟩ := close_getFd_safe hfds
        refine okPost_ok _ _ ⟨hcfg.status.trans hs7Run, hcfg.trans hcfg7, hpg.trans hpg7, hcw.trans hcw7,
          hsi.trans hsi7, hde.trans hde7, hwl.trans hwl7,
          fun k hk => (hne0 k (by omega)).trans (hle7 k hk),
          fun k hk hsome => ?_,
          fun hor k hk => ?_⟩
        · have hneTmp0 : k ≠ tmp0.val := fun h => hsome (h ▸ ht0_none)
          exact (hne0 k hneTmp0).trans (hne7 k hk hneTmp0 hsome)
        · rw [hor0 (by rw [hcfg7.oracle]; exact hor) k]
          by_cases hke : k = tmp0.val
          · subst hke; simp [ht0_none]
          · simp only [hke, ↓reduceIte]; exact hgt7 hor k hk hke
    · simp only [h0, ↓reduceIte]
      have hne0 : ∀ k > 2, k ≠ tmp0.val := fun k hk => by
        rcases ht0 with ht0neg | ⟨_, _⟩
        · scalar_tac
        · exfalso; apply h0; scalar_tac
      refine okPost_ok _ _ ⟨hs7Run, hcfg7, hpg7, hcw7, hsi7, hde7, hwl7, hle7,
        fun k hk hsome => hne7 k hk (hne0 k hk) hsome,
        fun hor k hk => hgt7 hor k hk (hne0 k hk)⟩
  refine okPost_bind hClose0 fun s8 ⟨hs8Run, hcfg8, hpg8, hcw8, hsi8, hde8, hwl8, hle8, hne8, hgt8⟩ => ?_
  have hCA2 : OkPost (if close_sources_above2 = true then setupStdioCloseAbove2 s8 stdin_fd stdout_fd stderr_fd else Result.ok s8)
      fun s9 => s9.status = .running ∧ SameChildConfig s9 sOrig ∧
        s9.pgid = sOrig.pgid ∧ s9.cwd = sOrig.cwd ∧ s9.sig = sOrig.sig ∧
        s9.descs = sOrig.descs ∧ s9.writeLog = sOrig.writeLog ∧
        (∀ k ≤ 2, s9.getFd k = s.getFd k) ∧
        (∀ k > 2, (close_sources_above2 = false ∨ (k ≠ stdin_fd.val ∧ k ≠ stdout_fd.val ∧ k ≠ stderr_fd.val)) →
          sOrig.getFd k ≠ none → s9.getFd k = sOrig.getFd k) ∧
        (oracleHasSeccomp sOrig.oracle = false → ∀ k > 2, s9.getFd k =
          if (close_sources_above2 && (k == stdin_fd.val || k == stdout_fd.val || k == stderr_fd.val)) = true then none else sOrig.getFd k) := by
    by_cases hca : close_sources_above2 = true
    · simp only [hca, ↓reduceIte]
      refine okPost_mono (setupStdioCloseAbove2_safety s8 hs8Run stdin_fd stdout_fd stderr_fd) ?_
      rintro s9 ⟨hs9Run, hcfg9, hpg9, hcw9, hsi9, hde9, hwl9, hle9, hgt9⟩
      refine ⟨hs9Run, hcfg9.trans hcfg8, hpg9.trans hpg8, hcw9.trans hcw8, hsi9.trans hsi8,
        hde9.trans hde8, hwl9.trans hwl8, fun k hk => (hle9 k (Or.inl hk)).trans (hle8 k hk),
        fun k hk hcond hsome => (hle9 k (Or.inr (hcond.resolve_left (by intro h; cases h)))).trans (hne8 k hk hsome),
        fun hor k hk => ?_⟩
      rw [hgt9 (by rw [hcfg8.oracle]; exact hor) k hk, hgt8 hor k hk]; simp
    · have hcaf : close_sources_above2 = false := Bool.eq_false_iff.mpr hca
      simp only [hcaf, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      exact okPost_ok _ _ ⟨hs8Run, hcfg8, hpg8, hcw8, hsi8, hde8, hwl8, hle8,
        fun k hk _ hsome => hne8 k hk hsome,
        fun hor k hk => by simp [hgt8 hor k hk]⟩
  refine okPost_bind hCA2 fun s9 ⟨hs9Run, hcfg9, hpg9, hcw9, hsi9, hde9, hwl9, hle9, hne9, hgt9⟩ => ?_
  have hs9_0 : s9.getFd 0 = some f0 := by rw [hle9 0 (by omega), hs0]
  have hs9_1 : s9.getFd 1 = some f1 := by rw [hle9 1 (by omega), hs1]
  have hs9_2 : s9.getFd 2 = some f2 := by rw [hle9 2 (by omega), hs2]
  refine okPost_mono (setupStdioClear012_safety s9 hs9Run hs9_0 hs9_1 hs9_2) ?_
  rintro ⟨r, s10⟩ ⟨hs10Run, hcfg10, hpg10, hcw10, hsi10, hde10, hwl10, hOk10⟩
  refine ⟨hs10Run, hcfg10.trans hcfg9, hpg10.trans hpg9, hcw10.trans hcw9, hsi10.trans hsi9,
    hde10.trans hde9, hwl10.trans hwl9, fun hr => ?_⟩
  rcases hOk10 hr with ⟨⟨g0, hg0, hg0d, hg0c⟩, ⟨g1, hg1, hg1d, hg1c⟩, ⟨g2, hg2, hg2d, hg2c⟩, hs10_gt⟩
  refine ⟨⟨e0, g0, hOrig0, hg0, hg0d.trans hd0, hg0c⟩,
    ⟨e1, g1, hOrig1, hg1, hg1d.trans hd1, hg1c⟩,
    ⟨e2, g2, hOrig2, hg2, hg2d.trans hd2, hg2c⟩,
    fun k hk hcond hsome => (hs10_gt k hk).trans (hne9 k hk hcond hsome),
    fun hor => ⟨⟨e0, g0, hOrig0, hg0, hg0d.trans hd0, hg0c⟩,
      ⟨e1, g1, hOrig1, hg1, hg1d.trans hd1, hg1c⟩,
      ⟨e2, g2, hOrig2, hg2, hg2d.trans hd2, hg2c⟩,
      fun k hk => (hs10_gt k hk).trans (hgt9 hor k hk)⟩⟩

private theorem setupStdioDup12Direct_safety (s sOrig : sys.Sys)
    (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32) (close_sources_above2 : Bool)
    (hRun : s.status = .running) (hNotCycle : ¬((s11 != 1#i32) = true ∧ s21 = 1#i32))
    (hCfg : SameChildConfig s sOrig)
    (hPg : s.pgid = sOrig.pgid) (hCw : s.cwd = sOrig.cwd)
    (hSi : s.sig = sOrig.sig) (hDe : s.descs = sOrig.descs) (hWl : s.writeLog = sOrig.writeLog)
    {e0 e1 e2 f0 f1 f2 : FdEntry}
    (hs0 : s.getFd 0 = some f0) (hd0 : f0.desc = e0.desc)
    (hs11 : s.getFd s11.val = some f1) (hd1 : f1.desc = e1.desc)
    (hs21 : s.getFd s21.val = some f2) (hd2 : f2.desc = e2.desc)
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2)
    (ht0 : tmp0 < 0#i32 ∨ (3 ≤ tmp0.val ∧ sOrig.getFd tmp0.val = none))
    (hAbove : ∀ k > 2, k ≠ tmp0.val → s.getFd k = sOrig.getFd k) :
    OkPost (setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.status = .running ∧
      (p.1 = .Ok () →
        SameChildConfig p.2 sOrig ∧ p.2.pgid = sOrig.pgid ∧ p.2.cwd = sOrig.cwd ∧
        p.2.sig = sOrig.sig ∧ p.2.descs = sOrig.descs ∧ p.2.writeLog = sOrig.writeLog ∧
        SetupStdioSafetyPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2) := by
  unfold setupStdioDup12Direct
  obtain ⟨r3, s4, h3eq, hcfg3, hpg3, hcw3, hsi3, hde3, hwl3, _, _, hOk3, _⟩ :=
    sys_dup2_running s hRun s11 1#i32
  rw [h3eq, bind_ok]
  have hs4Run : s4.status = .running := hcfg3.status.trans hRun
  cases r3 with
  | Err e =>
    change OkPost (setupStdioCloseTmpsErr s4 tmp0 (-1)#i32 (core.result.Result.Err e)) _
    exact okPost_mono (setupStdioCloseTmpsErr_safety s4 hs4Run tmp0 (-1)#i32 (.Err e))
      fun p ⟨hp1, hp2⟩ => ⟨hp1, fun h => by rw [hp2] at h; cases h⟩
  | Ok _ =>
    have hfds4 := hOk3 rfl
    have h1v : (1#i32 : I32).val = 1 := by decide
    have hget4 : ∀ k, s4.getFd k =
        if k = 1 then some (if s11.val = 1 then f1 else { desc := f1.desc, cloexec := false })
        else s.getFd k := fun k => by
      rw [getFd_eq_of_fds_eq hfds4, h1v]
      by_cases h1 : s11.val = 1
      · simp only [h1, ↓reduceIte]
        by_cases hk : k = 1
        · subst hk; simp only [↓reduceIte]; rw [← h1, hs11]
        · simp [hk]
      · simp only [h1, ↓reduceIte, hs11]
        by_cases hk : k = 1
        · subst hk; simp [getFd_putSlot_self]
        · simp [hk, getFd_putSlot_ne _ hk]
    have hs4_0 : s4.getFd 0 = some f0 := by rw [hget4 0]; simp [hs0]
    have hs4_1 : ∃ g1, s4.getFd 1 = some g1 ∧ g1.desc = e1.desc := by
      rw [hget4 1]; simp only [↓reduceIte]; split <;> exact ⟨_, rfl, hd1⟩
    rcases hs4_1 with ⟨g1, hs4_1, hg1d⟩
    have hs4_21 : ∃ g2, s4.getFd s21.val = some g2 ∧ g2.desc = e2.desc := by
      by_cases h11 : s11 = 1#i32
      · have hs11_1 : s11.val = 1 := by simp [h11]
        by_cases h21 : s21.val = 1
        · rw [h21, hget4 1]; simp only [↓reduceIte, hs11_1]
          have hfeq : f1 = f2 := by
            have : some f1 = some f2 := by rw [← hs11, hs11_1, ← h21, hs21]
            cases this; rfl
          exact ⟨f1, rfl, by rw [hfeq]; exact hd2⟩
        · rw [hget4 s21.val, ite_eq_right h21]; exact ⟨f2, hs21, hd2⟩
      · have hne1 : s21.val ≠ 1 := by
          intro heq; apply hNotCycle; refine ⟨by simp [h11], ?_⟩
          apply Aeneas.Std.IScalar.eq_of_val_eq; exact heq
        rw [hget4 s21.val, ite_eq_right hne1]; exact ⟨f2, hs21, hd2⟩
    rcases hs4_21 with ⟨g2, hs4_21, hg2d⟩
    change OkPost (do
      let (r4, s5) ← sys.dup2 s4 s21 2#i32
      match r4 with
      | .Ok _ => setupStdioFinish s5 tmp0 (-1)#i32 stdin_fd stdout_fd stderr_fd close_sources_above2
      | .Err _ => setupStdioCloseTmpsErr s5 tmp0 (-1)#i32 r4) _
    obtain ⟨r4, s5, h4eq, hcfg4, hpg4, hcw4, hsi4, hde4, hwl4, _, _, hOk4, _⟩ :=
      sys_dup2_running s4 hs4Run s21 2#i32
    rw [h4eq, bind_ok]
    have hs5Run : s5.status = .running := hcfg4.status.trans hs4Run
    cases r4 with
    | Err e =>
      change OkPost (setupStdioCloseTmpsErr s5 tmp0 (-1)#i32 (core.result.Result.Err e)) _
      exact okPost_mono (setupStdioCloseTmpsErr_safety s5 hs5Run tmp0 (-1)#i32 (.Err e))
        fun p ⟨hp1, hp2⟩ => ⟨hp1, fun h => by rw [hp2] at h; cases h⟩
    | Ok _ =>
      have hfds5 := hOk4 rfl
      have h2v : (2#i32 : I32).val = 2 := by decide
      have hget5 : ∀ k, s5.getFd k =
          if k = 2 then some (if s21.val = 2 then g2 else { desc := g2.desc, cloexec := false })
          else s4.getFd k := fun k => by
        rw [getFd_eq_of_fds_eq hfds5, h2v]
        by_cases h2 : s21.val = 2
        · simp only [h2, ↓reduceIte]
          by_cases hk : k = 2
          · subst hk; simp only [↓reduceIte]; rw [← h2, hs4_21]
          · simp [hk]
        · simp only [h2, ↓reduceIte, hs4_21]
          by_cases hk : k = 2
          · subst hk; simp [getFd_putSlot_self]
          · simp [hk, getFd_putSlot_ne _ hk]
      have hs5_0 : s5.getFd 0 = some f0 := by rw [hget5 0]; simp [hs4_0]
      have hs5_1 : s5.getFd 1 = some g1 := by rw [hget5 1]; simp [hs4_1]
      have hs5_2 : ∃ h2, s5.getFd 2 = some h2 ∧ h2.desc = e2.desc := by
        rw [hget5 2]; simp only [↓reduceIte]; split <;> exact ⟨_, rfl, hg2d⟩
      rcases hs5_2 with ⟨h2, hs5_2, hh2d⟩
      refine okPost_mono
        (setupStdioFinish_safety s5 sOrig tmp0 (-1)#i32 stdin_fd stdout_fd stderr_fd close_sources_above2
          hs5Run (hcfg4.trans (hcfg3.trans hCfg)) (hpg4.trans (hpg3.trans hPg))
          (hcw4.trans (hcw3.trans hCw)) (hsi4.trans (hsi3.trans hSi))
          (hde4.trans (hde3.trans hDe)) (hwl4.trans (hwl3.trans hWl))
          hs5_0 hd0 hs5_1 hg1d hs5_2 hh2d hOrig0 hOrig1 hOrig2 ht0 (Or.inl (by decide)) fun k hk hne0 _ => ?_) ?_
      · rw [hget5 k, ite_eq_right (by omega), hget4 k, ite_eq_right (by omega)]
        exact hAbove k hk hne0
      · rintro ⟨r, sOut⟩ ⟨hsOutRun, hcfgOut, hpgOut, hcwOut, hsiOut, hdeOut, hwlOut, hOkOut⟩
        exact ⟨hsOutRun, fun hr => ⟨hcfgOut, hpgOut, hcwOut, hsiOut, hdeOut, hwlOut, hOkOut hr⟩⟩

private theorem setupStdioAfterDup0_safety (s sOrig : sys.Sys)
    (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32) (close_sources_above2 : Bool)
    (hRun : s.status = .running) (hCfg : SameChildConfig s sOrig)
    (hPg : s.pgid = sOrig.pgid) (hCw : s.cwd = sOrig.cwd)
    (hSi : s.sig = sOrig.sig) (hDe : s.descs = sOrig.descs) (hWl : s.writeLog = sOrig.writeLog)
    {e0 e1 e2 f0 f1 f2 : FdEntry}
    (hs0 : s.getFd 0 = some f0) (hd0 : f0.desc = e0.desc)
    (hs11 : s.getFd s11.val = some f1) (hd1 : f1.desc = e1.desc)
    (hs21 : s.getFd s21.val = some f2) (hd2 : f2.desc = e2.desc)
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2)
    (ht0 : tmp0 < 0#i32 ∨ (3 ≤ tmp0.val ∧ sOrig.getFd tmp0.val = none ∧ ∃ et, s.getFd tmp0.val = some et))
    (hAbove : ∀ k > 2, k ≠ tmp0.val → s.getFd k = sOrig.getFd k) :
    OkPost (setupStdioAfterDup0 s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.status = .running ∧
      (p.1 = .Ok () →
        SameChildConfig p.2 sOrig ∧ p.2.pgid = sOrig.pgid ∧ p.2.cwd = sOrig.cwd ∧
        p.2.sig = sOrig.sig ∧ p.2.descs = sOrig.descs ∧ p.2.writeLog = sOrig.writeLog ∧
        SetupStdioSafetyPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2) := by
  unfold setupStdioAfterDup0
  by_cases hcyc : (s11 != 1#i32) = true ∧ s21 = 1#i32
  · simp only [hcyc.1, ↓reduceIte, hcyc.2]
    have hs_1 : s.getFd (1#i32 : I32).val = some f2 := by
      change s.getFd 1 = some f2; rw [← show s21.val = 1 by simp [hcyc.2]]; exact hs21
    obtain ⟨r3, s4, h3eq, hcfg3, hpg3, hcw3, hsi3, hde3, hwl3, _, _, hOk3, _⟩ :=
      sys_fcntl_dupfd_cloexec_running s hRun 1#i32 3#i32
    rw [h3eq, bind_ok]
    have hs4Run : s4.status = .running := hcfg3.status.trans hRun
    cases r3 with
    | Err e =>
      change OkPost (if tmp0 ≥ 0#i32 then do let (_, s5) ← sys.close s4 tmp0; Result.ok (core.result.Result.Err e, s5)
        else Result.ok (core.result.Result.Err e, s4)) _
      by_cases ht : tmp0 ≥ 0#i32
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ht)]
        obtain ⟨_, s5, hEq, hcfg, _⟩ := sys_close_running s4 hs4Run tmp0
        rw [hEq, bind_ok]
        exact okPost_ok _ _ ⟨hcfg.status.trans hs4Run, fun h => by cases h⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false ht)]
        exact okPost_ok _ _ ⟨hs4Run, fun h => by cases h⟩
    | Ok fd1 =>
      rcases hOk3 fd1 rfl with ⟨eOne, dstInt, hs1_dup, _, hfd1_eq, h3le, _, hs_fd1_none, hfds4⟩
      rw [← hfd1_eq] at hs_fd1_none
      have h3val : (3#i32 : Int) = 3 := by decide
      have hfd1_3 : 3 ≤ fd1.val := by omega
      have heOne_eq : eOne = f2 := by
        have : some eOne = some f2 := by rw [← hs1_dup, hs_1]
        cases this; rfl
      have hs_1_int : s.getFd (1#i32 : I32).val = some f2 := hs_1
      have hget4 : ∀ k, s4.getFd k =
          if k = fd1.val then some { desc := f2.desc, cloexec := true } else s.getFd k := fun k => by
        rw [getFd_eq_of_fds_eq hfds4, heOne_eq, ← hfd1_eq]
        by_cases hk : k = fd1.val
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hk), hk, getFd_putSlot_self]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
          exact getFd_putSlot_ne _ hk _
      have hsOrig_fd1_none : sOrig.getFd fd1.val = none := by
        have hne0 : fd1.val ≠ tmp0.val := by
          intro heq
          have hnone : s.getFd tmp0.val = none := by rw [← heq]; exact hs_fd1_none
          rcases ht0 with hneg | ⟨_, _, et, het⟩
          · have : tmp0.val < 0 := hneg
            omega
          · rw [het] at hnone; cases hnone
        have := hAbove fd1.val (by omega) hne0
        rw [← this]; exact hs_fd1_none
      have hne_s11_fd1 : s11.val ≠ fd1.val := by
        intro heq
        have : s.getFd fd1.val = none := hs_fd1_none
        rw [← heq, hs11] at this; cases this
      have hs4_11 : s4.getFd s11.val = some f1 := by
        rw [hget4 s11.val, ite_eq_right hne_s11_fd1]; exact hs11
      have hs4_0 : s4.getFd 0 = some f0 := by
        rw [hget4 0, ite_eq_right (by omega)]; exact hs0
      have hs4_fd1 : s4.getFd fd1.val = some { desc := f2.desc, cloexec := true } := by
        rw [hget4 fd1.val]; simp
      change OkPost (do
        let (r4, s5) ← sys.dup2 s4 s11 1#i32
        match r4 with
        | .Ok _ => do
          let (r5, s6) ← sys.dup2 s5 fd1 2#i32
          match r5 with
          | .Ok _ => setupStdioFinish s6 tmp0 fd1 stdin_fd stdout_fd stderr_fd close_sources_above2
          | .Err _ => setupStdioCloseTmpsErr s6 tmp0 fd1 r5
        | .Err _ => setupStdioCloseTmpsErr s5 tmp0 fd1 r4) _
      obtain ⟨r4, s5, h4eq, hcfg4, hpg4, hcw4, hsi4, hde4, hwl4, _, _, hOk4, _⟩ :=
        sys_dup2_running s4 hs4Run s11 1#i32
      rw [h4eq, bind_ok]
      have hs5Run : s5.status = .running := hcfg4.status.trans hs4Run
      cases r4 with
      | Err e =>
        change OkPost (setupStdioCloseTmpsErr s5 tmp0 fd1 (core.result.Result.Err e)) _
        exact okPost_mono (setupStdioCloseTmpsErr_safety s5 hs5Run tmp0 fd1 (.Err e))
          fun p ⟨hp1, hp2⟩ => ⟨hp1, fun h => by rw [hp2] at h; cases h⟩
      | Ok _ =>
        have hfds5 := hOk4 rfl
        have h1v : (1#i32 : I32).val = 1 := by decide
        have h11ne1 : s11.val ≠ 1 := by simpa using hcyc.1
        have hget5 : ∀ k, s5.getFd k =
            if k = 1 then some { desc := f1.desc, cloexec := false } else s4.getFd k := fun k => by
          rw [getFd_eq_of_fds_eq hfds5, h1v]
          simp only [h11ne1, ↓reduceIte, hs4_11]
          by_cases hk : k = 1
          · subst hk; simp [getFd_putSlot_self]
          · simp [hk, getFd_putSlot_ne _ hk]
        have hs5_0 : s5.getFd 0 = some f0 := by rw [hget5 0]; simp [hs4_0]
        have hs5_1 : s5.getFd 1 = some { desc := f1.desc, cloexec := false } := by
          rw [hget5 1]; simp
        have hs5_fd1 : s5.getFd fd1.val = some { desc := f2.desc, cloexec := true } := by
          rw [hget5 fd1.val, ite_eq_right (by omega)]; exact hs4_fd1
        change OkPost (do
          let (r5, s6) ← sys.dup2 s5 fd1 2#i32
          match r5 with
          | .Ok _ => setupStdioFinish s6 tmp0 fd1 stdin_fd stdout_fd stderr_fd close_sources_above2
          | .Err _ => setupStdioCloseTmpsErr s6 tmp0 fd1 r5) _
        obtain ⟨r5, s6, h5eq, hcfg5, hpg5, hcw5, hsi5, hde5, hwl5, _, _, hOk5, _⟩ :=
          sys_dup2_running s5 hs5Run fd1 2#i32
        rw [h5eq, bind_ok]
        have hs6Run : s6.status = .running := hcfg5.status.trans hs5Run
        cases r5 with
        | Err e =>
          change OkPost (setupStdioCloseTmpsErr s6 tmp0 fd1 (core.result.Result.Err e)) _
          exact okPost_mono (setupStdioCloseTmpsErr_safety s6 hs6Run tmp0 fd1 (.Err e))
            fun p ⟨hp1, hp2⟩ => ⟨hp1, fun h => by rw [hp2] at h; cases h⟩
        | Ok _ =>
          have hfds6 := hOk5 rfl
          have h2v : (2#i32 : I32).val = 2 := by decide
          have hget6 : ∀ k, s6.getFd k =
              if k = 2 then some { desc := f2.desc, cloexec := false } else s5.getFd k := fun k => by
            rw [getFd_eq_of_fds_eq hfds6, h2v]
            have hfd1ne2 : fd1.val ≠ 2 := by omega
            simp only [hfd1ne2, ↓reduceIte, hs5_fd1]
            by_cases hk : k = 2
            · subst hk; simp [getFd_putSlot_self]
            · simp [hk, getFd_putSlot_ne _ hk]
          have hs6_0 : s6.getFd 0 = some f0 := by rw [hget6 0]; simp [hs5_0]
          have hs6_1 : s6.getFd 1 = some { desc := f1.desc, cloexec := false } := by
            rw [hget6 1]; simp [hs5_1]
          have hs6_2 : s6.getFd 2 = some { desc := f2.desc, cloexec := false } := by
            rw [hget6 2]; simp
          refine okPost_mono
            (setupStdioFinish_safety s6 sOrig tmp0 fd1 stdin_fd stdout_fd stderr_fd close_sources_above2
              hs6Run (hcfg5.trans (hcfg4.trans (hcfg3.trans hCfg)))
              (hpg5.trans (hpg4.trans (hpg3.trans hPg)))
              (hcw5.trans (hcw4.trans (hcw3.trans hCw)))
              (hsi5.trans (hsi4.trans (hsi3.trans hSi)))
              (hde5.trans (hde4.trans (hde3.trans hDe)))
              (hwl5.trans (hwl4.trans (hwl3.trans hWl)))
              hs6_0 hd0 hs6_1 hd1 hs6_2 hd2 hOrig0 hOrig1 hOrig2
              (ht0.imp id fun ⟨ha, hb, _⟩ => ⟨ha, hb⟩) (Or.inr ⟨hfd1_3, hsOrig_fd1_none⟩)
              fun k hk hne0 hne1 => ?_) ?_
          · rw [hget6 k, ite_eq_right (by omega), hget5 k, ite_eq_right (by omega), hget4 k, ite_eq_right hne1]
            exact hAbove k hk hne0
          · rintro ⟨r, sOut⟩ ⟨hsOutRun, hcfgOut, hpgOut, hcwOut, hsiOut, hdeOut, hwlOut, hOkOut⟩
            exact ⟨hsOutRun, fun hr => ⟨hcfgOut, hpgOut, hcwOut, hsiOut, hdeOut, hwlOut, hOkOut hr⟩⟩
  · have hbr : (if (s11 != 1#i32) = true then if s21 = 1#i32 then
        (do let (r3, s4) ← sys.fcntl_dupfd_cloexec s 1#i32 3#i32
            match r3 with
            | .Ok fd1 => do
              let (r4, s5) ← sys.dup2 s4 s11 1#i32
              match r4 with
              | .Ok _ => do
                let (r5, s6) ← sys.dup2 s5 fd1 2#i32
                match r5 with
                | .Ok _ => setupStdioFinish s6 tmp0 fd1 stdin_fd stdout_fd stderr_fd close_sources_above2
                | .Err _ => setupStdioCloseTmpsErr s6 tmp0 fd1 r5
              | .Err _ => setupStdioCloseTmpsErr s5 tmp0 fd1 r4
            | .Err e =>
              if tmp0 ≥ 0#i32 then do let (_, s5) ← sys.close s4 tmp0; Result.ok (core.result.Result.Err e, s5)
              else Result.ok (core.result.Result.Err e, s4))
        else setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
        else setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2) =
        setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2 := by
      by_cases h1 : (s11 != 1#i32) = true
      · have h2 : s21 ≠ 1#i32 := fun h => hcyc ⟨h1, h⟩
        simp [h1, h2]
      · simp [h1]
    rw [hbr]
    exact setupStdioDup12Direct_safety s sOrig tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
      hRun hcyc hCfg hPg hCw hSi hDe hWl hs0 hd0 hs11 hd1 hs21 hd2 hOrig0 hOrig1 hOrig2
      (ht0.imp id fun ⟨ha, hb, _⟩ => ⟨ha, hb⟩) hAbove

private theorem setupStdioSave0_safety (s1 sOrig : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool)
    (hRun : s1.status = .running) (hFds : s1.fds = sOrig.fds)
    (hCfg : SameChildConfig s1 sOrig)
    (hPg : s1.pgid = sOrig.pgid) (hCw : s1.cwd = sOrig.cwd)
    (hSi : s1.sig = sOrig.sig) (hDe : s1.descs = sOrig.descs) (hWl : s1.writeLog = sOrig.writeLog)
    (hZero : stdout_fd = 0#i32 ∨ stderr_fd = 0#i32)
    {e0 e1 e2 : FdEntry}
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2) :
    OkPost (setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.status = .running ∧
      (p.1 = .Ok () →
        SameChildConfig p.2 sOrig ∧ p.2.pgid = sOrig.pgid ∧ p.2.cwd = sOrig.cwd ∧
        p.2.sig = sOrig.sig ∧ p.2.descs = sOrig.descs ∧ p.2.writeLog = sOrig.writeLog ∧
        SetupStdioSafetyPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2) := by
  unfold setupStdioSave0
  have heZero : ∃ eZ, s1.getFd (0#i32 : I32).val = some eZ ∧
      (stdout_fd = 0#i32 → eZ = e1) ∧ (stderr_fd = 0#i32 → eZ = e2) := by
    rcases hZero with h0 | h0
    · refine ⟨e1, ?_, fun _ => rfl, fun h0' => ?_⟩
      · change s1.getFd 0 = some e1
        rw [getFd_eq_of_fds_eq hFds, ← show stdout_fd.val = 0 by simp [h0]]; exact hOrig1
      · have : some e1 = some e2 := by rw [← hOrig1, h0, ← h0', hOrig2]
        cases this; rfl
    · refine ⟨e2, ?_, fun h0' => ?_, fun _ => rfl⟩
      · change s1.getFd 0 = some e2
        rw [getFd_eq_of_fds_eq hFds, ← show stderr_fd.val = 0 by simp [h0]]; exact hOrig2
      · have : some e2 = some e1 := by rw [← hOrig2, h0, ← h0', hOrig1]
        cases this; rfl
  rcases heZero with ⟨eZ, hs1_0, hz1, hz2⟩
  obtain ⟨r1, s2, h1eq, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, _, _, hOk1, _⟩ :=
    sys_fcntl_dupfd_cloexec_running s1 hRun 0#i32 3#i32
  rw [h1eq, bind_ok]
  have hs2Run : s2.status = .running := hcfg2.status.trans hRun
  cases r1 with
  | Err e => exact okPost_ok _ _ ⟨hs2Run, fun h => by cases h⟩
  | Ok fd =>
    rcases hOk1 fd rfl with ⟨eZ', dstInt, hs1_dup, _, hfd_eq, hfd_3, _, hnone_fd_int, hfds2⟩
    rw [← hfd_eq] at hnone_fd_int
    have h0v : (0#i32 : I32).val = 0 := by decide
    have h3val : (3#i32 : Int) = 3 := by decide
    have hfd_val3 : 3 ≤ fd.val := by omega
    have hnone_fd : s1.getFd fd.val = none := hnone_fd_int
    have hs1OrigNone : sOrig.getFd fd.val = none := by rw [← getFd_eq_of_fds_eq hFds]; exact hnone_fd
    have heZeq : eZ' = eZ := by
      have : some eZ' = some eZ := by rw [← hs1_dup, hs1_0]
      cases this; rfl
    have hs1_0' : s1.getFd 0 = some eZ := by rw [← h0v]; exact hs1_0
    have hget2 : ∀ k, s2.getFd k =
        if k = fd.val then some { desc := eZ.desc, cloexec := true } else s1.getFd k := fun k => by
      rw [getFd_eq_of_fds_eq hfds2, heZeq, ← hfd_eq]
      by_cases hk : k = fd.val
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hk), hk, getFd_putSlot_self]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
        exact getFd_putSlot_ne _ hk _
    have hs2_in : s2.getFd stdin_fd.val = some e0 := by
      have hne : stdin_fd.val ≠ fd.val := by
        intro heq; rw [heq, hs1OrigNone] at hOrig0; cases hOrig0
      rw [hget2 stdin_fd.val, ite_eq_right hne, getFd_eq_of_fds_eq hFds, hOrig0]
    have hs11Post : OkPost (if stdout_fd = 0#i32 then Result.ok fd else Result.ok stdout_fd)
        (fun v => v = if stdout_fd = 0#i32 then fd else stdout_fd) := by
      by_cases h : stdout_fd = 0#i32 <;> simp [h, okPost_ok]
    refine okPost_bind hs11Post fun s11 hs11eq => ?_
    have hs21Post : OkPost (if stderr_fd = 0#i32 then Result.ok fd else Result.ok stderr_fd)
        (fun v => v = if stderr_fd = 0#i32 then fd else stderr_fd) := by
      by_cases h : stderr_fd = 0#i32 <;> simp [h, okPost_ok]
    refine okPost_bind hs21Post fun s21 hs21eq => ?_
    subst hs11eq; subst hs21eq
    change OkPost (do
      let (r2, s3) ← sys.dup2 s2 stdin_fd 0#i32
      (match r2 with
        | .Ok _ => setupStdioAfterDup0 s3 fd
            (if stdout_fd = 0#i32 then fd else stdout_fd)
            (if stderr_fd = 0#i32 then fd else stderr_fd) stdin_fd stdout_fd stderr_fd close_sources_above2
        | .Err _ =>
          if fd ≥ 0#i32 then do let (_, s4) ← sys.close s3 fd; Result.ok (r2, s4)
          else Result.ok (r2, s3))) _
    obtain ⟨r2, s3, h2eq, hcfg3, hpg3, hcw3, hsi3, hde3, hwl3, _, _, hOk2, _⟩ :=
      sys_dup2_running s2 hs2Run stdin_fd 0#i32
    rw [h2eq, bind_ok]
    have hs3Run : s3.status = .running := hcfg3.status.trans hs2Run
    cases r2 with
    | Err e =>
      change OkPost (if fd ≥ 0#i32 then do let (_, s4) ← sys.close s3 fd; Result.ok (core.result.Result.Err e, s4)
        else Result.ok (core.result.Result.Err e, s3)) _
      by_cases hfd0 : fd ≥ 0#i32
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hfd0)]
        obtain ⟨_, s4, hEq, hcfg, _⟩ := sys_close_running s3 hs3Run fd
        rw [hEq, bind_ok]
        exact okPost_ok _ _ ⟨hcfg.status.trans hs3Run, fun h => by cases h⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hfd0)]
        exact okPost_ok _ _ ⟨hs3Run, fun h => by cases h⟩
    | Ok _ =>
      have hfds3 := hOk2 rfl
      have hget3 : ∀ k, s3.getFd k =
          if k = 0 then some (if stdin_fd.val = 0 then e0 else { desc := e0.desc, cloexec := false })
          else s2.getFd k := fun k => by
        rw [getFd_eq_of_fds_eq hfds3, h0v]
        by_cases h0 : stdin_fd.val = 0
        · simp only [h0, ↓reduceIte]
          by_cases hk : k = 0
          · subst hk; simp only [↓reduceIte]; rw [← h0, hs2_in]
          · simp [hk]
        · simp only [h0, ↓reduceIte, hs2_in]
          by_cases hk : k = 0
          · subst hk; simp [getFd_putSlot_self]
          · simp [hk, getFd_putSlot_ne _ hk]
      have hs3_0 : ∃ f0, s3.getFd 0 = some f0 ∧ f0.desc = e0.desc := by
        rw [hget3 0]; simp only [↓reduceIte]; split <;> exact ⟨_, rfl, rfl⟩
      rcases hs3_0 with ⟨f0, hs3_0, hf0d⟩
      have hs3_fd : s3.getFd fd.val = some { desc := eZ.desc, cloexec := true } := by
        rw [hget3 fd.val, ite_eq_right (by omega), hget2 fd.val]; simp
      have hs3_11 : ∃ f1, s3.getFd (if stdout_fd = 0#i32 then fd else stdout_fd).val = some f1 ∧ f1.desc = e1.desc := by
        by_cases h : stdout_fd = 0#i32
        · simp only [h, ↓reduceIte]
          exact ⟨{ desc := eZ.desc, cloexec := true }, hs3_fd, by simp [hz1 h]⟩
        · simp only [h, ↓reduceIte]
          have hne0 : stdout_fd.val ≠ 0 := fun hv => h (Aeneas.Std.IScalar.eq_of_val_eq hv)
          have hnefd : stdout_fd.val ≠ fd.val := by
            intro heq; rw [heq, hs1OrigNone] at hOrig1; cases hOrig1
          rw [hget3 stdout_fd.val, ite_eq_right hne0, hget2 stdout_fd.val, ite_eq_right hnefd, getFd_eq_of_fds_eq hFds]
          exact ⟨e1, hOrig1, rfl⟩
      have hs3_21 : ∃ f2, s3.getFd (if stderr_fd = 0#i32 then fd else stderr_fd).val = some f2 ∧ f2.desc = e2.desc := by
        by_cases h : stderr_fd = 0#i32
        · simp only [h, ↓reduceIte]
          exact ⟨{ desc := eZ.desc, cloexec := true }, hs3_fd, by simp [hz2 h]⟩
        · simp only [h, ↓reduceIte]
          have hne0 : stderr_fd.val ≠ 0 := fun hv => h (Aeneas.Std.IScalar.eq_of_val_eq hv)
          have hnefd : stderr_fd.val ≠ fd.val := by
            intro heq; rw [heq, hs1OrigNone] at hOrig2; cases hOrig2
          rw [hget3 stderr_fd.val, ite_eq_right hne0, hget2 stderr_fd.val, ite_eq_right hnefd, getFd_eq_of_fds_eq hFds]
          exact ⟨e2, hOrig2, rfl⟩
      rcases hs3_11 with ⟨f1, hs3_f1, hf1d⟩
      rcases hs3_21 with ⟨f2, hs3_f2, hf2d⟩
      refine setupStdioAfterDup0_safety s3 sOrig fd _ _ stdin_fd stdout_fd stderr_fd close_sources_above2
        hs3Run (hcfg3.trans (hcfg2.trans hCfg)) (hpg3.trans (hpg2.trans hPg))
        (hcw3.trans (hcw2.trans hCw)) (hsi3.trans (hsi2.trans hSi))
        (hde3.trans (hde2.trans hDe)) (hwl3.trans (hwl2.trans hWl))
        hs3_0 hf0d hs3_f1 hf1d hs3_f2 hf2d hOrig0 hOrig1 hOrig2
        (Or.inr ⟨hfd_val3, hs1OrigNone, _, hs3_fd⟩) fun k hk hne => ?_
      rw [hget3 k, ite_eq_right (by omega), hget2 k, ite_eq_right hne, getFd_eq_of_fds_eq hFds]

private theorem setupStdioNoSave0_safety (s1 sOrig : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool)
    (hRun : s1.status = .running) (hFds : s1.fds = sOrig.fds)
    (hCfg : SameChildConfig s1 sOrig)
    (hPg : s1.pgid = sOrig.pgid) (hCw : s1.cwd = sOrig.cwd)
    (hSi : s1.sig = sOrig.sig) (hDe : s1.descs = sOrig.descs) (hWl : s1.writeLog = sOrig.writeLog)
    (hOutNe0 : stdout_fd ≠ 0#i32 ∨ stdin_fd = 0#i32)
    (hErrNe0 : stderr_fd ≠ 0#i32 ∨ stdin_fd = 0#i32)
    {e0 e1 e2 : FdEntry}
    (hOrig0 : sOrig.getFd stdin_fd.val = some e0)
    (hOrig1 : sOrig.getFd stdout_fd.val = some e1)
    (hOrig2 : sOrig.getFd stderr_fd.val = some e2) :
    OkPost (setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.status = .running ∧
      (p.1 = .Ok () →
        SameChildConfig p.2 sOrig ∧ p.2.pgid = sOrig.pgid ∧ p.2.cwd = sOrig.cwd ∧
        p.2.sig = sOrig.sig ∧ p.2.descs = sOrig.descs ∧ p.2.writeLog = sOrig.writeLog ∧
        SetupStdioSafetyPost sOrig stdin_fd stdout_fd stderr_fd close_sources_above2 p.2) := by
  unfold setupStdioNoSave0
  have hs1_in : s1.getFd stdin_fd.val = some e0 := by rw [getFd_eq_of_fds_eq hFds, hOrig0]
  obtain ⟨r1, s2, h1eq, hcfg2, hpg2, hcw2, hsi2, hde2, hwl2, _, _, hOk1, _⟩ :=
    sys_dup2_running s1 hRun stdin_fd 0#i32
  rw [h1eq, bind_ok]
  have hs2Run : s2.status = .running := hcfg2.status.trans hRun
  cases r1 with
  | Err e =>
    change OkPost (if (-1)#i32 ≥ 0#i32 then do let (_, s3) ← sys.close s2 (-1)#i32; Result.ok (core.result.Result.Err e, s3) else Result.ok (core.result.Result.Err e, s2)) _
    have hneg : ¬ ((-1)#i32 ≥ 0#i32) := by decide
    simp only [hneg, ↓reduceIte]
    exact okPost_ok _ _ ⟨hs2Run, fun h => by cases h⟩
  | Ok _ =>
    have hfds2 := hOk1 rfl
    have h0v : (0#i32 : I32).val = 0 := by decide
    have hget2 : ∀ k, s2.getFd k =
        if k = 0 then some (if stdin_fd.val = 0 then e0 else { desc := e0.desc, cloexec := false })
        else s1.getFd k := fun k => by
      rw [getFd_eq_of_fds_eq hfds2, h0v]
      by_cases h0 : stdin_fd.val = 0
      · simp only [h0, ↓reduceIte]
        by_cases hk : k = 0
        · subst hk; simp only [↓reduceIte]; rw [← h0, hs1_in]
        · simp [hk]
      · simp only [h0, ↓reduceIte, hs1_in]
        by_cases hk : k = 0
        · subst hk; simp [getFd_putSlot_self]
        · simp [hk, getFd_putSlot_ne _ hk]
    have hs2_0 : ∃ f0, s2.getFd 0 = some f0 ∧ f0.desc = e0.desc := by
      rw [hget2 0]; simp only [↓reduceIte]; split <;> exact ⟨_, rfl, rfl⟩
    rcases hs2_0 with ⟨f0, hs2_0, hf0d⟩
    have hs2_1 : ∃ f1, s2.getFd stdout_fd.val = some f1 ∧ f1.desc = e1.desc := by
      by_cases h0 : stdout_fd.val = 0
      · rcases hOutNe0 with hne | hst0
        · exfalso; apply hne; apply Aeneas.Std.IScalar.eq_of_val_eq; exact h0
        · have he1eq : e1 = e0 := by
            have : some e1 = some e0 := by rw [← hOrig1, h0, ← show stdin_fd.val = 0 by simp [hst0], hOrig0]
            cases this; rfl
          rw [h0]; exact ⟨f0, hs2_0, by rw [hf0d, he1eq]⟩
      · rw [hget2 stdout_fd.val, ite_eq_right h0, getFd_eq_of_fds_eq hFds]
        exact ⟨e1, hOrig1, rfl⟩
    have hs2_2 : ∃ f2, s2.getFd stderr_fd.val = some f2 ∧ f2.desc = e2.desc := by
      by_cases h0 : stderr_fd.val = 0
      · rcases hErrNe0 with hne | hst0
        · exfalso; apply hne; apply Aeneas.Std.IScalar.eq_of_val_eq; exact h0
        · have he2eq : e2 = e0 := by
            have : some e2 = some e0 := by rw [← hOrig2, h0, ← show stdin_fd.val = 0 by simp [hst0], hOrig0]
            cases this; rfl
          rw [h0]; exact ⟨f0, hs2_0, by rw [hf0d, he2eq]⟩
      · rw [hget2 stderr_fd.val, ite_eq_right h0, getFd_eq_of_fds_eq hFds]
        exact ⟨e2, hOrig2, rfl⟩
    rcases hs2_1 with ⟨f1, hs2_f1, hf1d⟩
    rcases hs2_2 with ⟨f2, hs2_f2, hf2d⟩
    refine setupStdioAfterDup0_safety s2 sOrig (-1)#i32 stdout_fd stderr_fd stdin_fd stdout_fd stderr_fd close_sources_above2
      hs2Run (hcfg2.trans hCfg) (hpg2.trans hPg) (hcw2.trans hCw) (hsi2.trans hSi)
      (hde2.trans hDe) (hwl2.trans hWl) hs2_0 hf0d hs2_f1 hf1d hs2_f2 hf2d hOrig0 hOrig1 hOrig2
      (Or.inl (by decide)) fun k hk _ => ?_
    rw [hget2 k, ite_eq_right (by omega), getFd_eq_of_fds_eq hFds]

/-- Arbitrary-oracle safety specification for `postfork.fd_ops.setup_stdio`. -/
theorem setup_stdio_safety (s : sys.Sys) (hRun : s.status = .running)
    (stdin_fd stdout_fd stderr_fd : I32) (close_sources_above2 : Bool) :
    OkPost (postfork.fd_ops.setup_stdio s stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.status = .running ∧
      (p.1 = .Ok () →
        SameChildConfig p.2 s ∧ p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧
        p.2.sig = s.sig ∧ p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
        0#i32 ≤ stdin_fd ∧ 0#i32 ≤ stdout_fd ∧ 0#i32 ≤ stderr_fd ∧
        SetupStdioSafetyPost s stdin_fd stdout_fd stderr_fd close_sources_above2 p.2) := by
  rw [setup_stdio_eq_factored]
  refine okPost_bind (probe_stdio_open_safety s hRun stdin_fd stdout_fd stderr_fd) fun ⟨r, s1⟩ hs1 => ?_
  dsimp only at hs1
  rcases hs1 with ⟨hs1Run, hcfg1, hpg1, hcw1, hsi1, hde1, hfds1, hwl1, hOk1⟩
  cases r with
  | Err e => exact okPost_ok _ _ ⟨hs1Run, fun h => by cases h⟩
  | Ok _ =>
    rcases hOk1 rfl with ⟨hn0, hn1, hn2, hOp0, hOp1, hOp2⟩
    have ⟨e0, he0⟩ : ∃ e0, s.getFd stdin_fd.val = some e0 := by
      cases h : s.getFd stdin_fd.val <;> simp [ChildState.isOpen, h] at hOp0
      exact ⟨_, rfl⟩
    have ⟨e1, he1⟩ : ∃ e1, s.getFd stdout_fd.val = some e1 := by
      cases h : s.getFd stdout_fd.val <;> simp [ChildState.isOpen, h] at hOp1
      exact ⟨_, rfl⟩
    have ⟨e2, he2⟩ : ∃ e2, s.getFd stderr_fd.val = some e2 := by
      cases h : s.getFd stderr_fd.val <;> simp [ChildState.isOpen, h] at hOp2
      exact ⟨_, rfl⟩
    have wrap : ∀ (m : Result (core.result.Result Unit I32 × sys.Sys)),
        OkPost m (fun p => p.2.status = .running ∧
          (p.1 = .Ok () → SameChildConfig p.2 s ∧ p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧
            p.2.sig = s.sig ∧ p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
            SetupStdioSafetyPost s stdin_fd stdout_fd stderr_fd close_sources_above2 p.2)) →
        OkPost m (fun p => p.2.status = .running ∧
          (p.1 = .Ok () → SameChildConfig p.2 s ∧ p.2.pgid = s.pgid ∧ p.2.cwd = s.cwd ∧
            p.2.sig = s.sig ∧ p.2.descs = s.descs ∧ p.2.writeLog = s.writeLog ∧
            0#i32 ≤ stdin_fd ∧ 0#i32 ≤ stdout_fd ∧ 0#i32 ≤ stderr_fd ∧
            SetupStdioSafetyPost s stdin_fd stdout_fd stderr_fd close_sources_above2 p.2)) := by
      intro m hm
      refine okPost_mono hm fun p ⟨hpRun, hpOk⟩ => ⟨hpRun, fun hr => ?_⟩
      rcases hpOk hr with ⟨a, b, c, d, e, f, g⟩
      exact ⟨a, b, c, d, e, f, hn0, hn1, hn2, g⟩
    change OkPost (if (stdin_fd != 0#i32) = true then
        if stdout_fd = 0#i32 then setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
        else if stderr_fd = 0#i32 then setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
        else setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
      else setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) _
    by_cases hne0 : (stdin_fd != 0#i32) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hne0)]
      by_cases h1 : stdout_fd = 0#i32
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
        exact wrap _ (setupStdioSave0_safety s1 s stdin_fd stdout_fd stderr_fd close_sources_above2
          hs1Run hfds1 hcfg1 hpg1 hcw1 hsi1 hde1 hwl1 (Or.inl h1) he0 he1 he2)
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        by_cases h2 : stderr_fd = 0#i32
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
          exact wrap _ (setupStdioSave0_safety s1 s stdin_fd stdout_fd stderr_fd close_sources_above2
            hs1Run hfds1 hcfg1 hpg1 hcw1 hsi1 hde1 hwl1 (Or.inr h2) he0 he1 he2)
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
          exact wrap _ (setupStdioNoSave0_safety s1 s stdin_fd stdout_fd stderr_fd close_sources_above2
            hs1Run hfds1 hcfg1 hpg1 hcw1 hsi1 hde1 hwl1 (Or.inl h1) (Or.inl h2) he0 he1 he2)
    · have hst0 : stdin_fd = 0#i32 := Aeneas.Std.IScalar.eq_of_val_eq (by simpa using hne0)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne0)]
      exact wrap _ (setupStdioNoSave0_safety s1 s stdin_fd stdout_fd stderr_fd close_sources_above2
        hs1Run hfds1 hcfg1 hpg1 hcw1 hsi1 hde1 hwl1 (Or.inr hst0) (Or.inr hst0) he0 he1 he2)

private theorem probe_stdio_open_dspec_blockedSigs (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32) :
    WP.dspec (postfork.fd_ops.probe_stdio_open s stdin_fd stdout_fd stderr_fd) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.probe_stdio_open
  split
  · exact (WP.dspec_ok _).mpr rfl
  · split
    · exact (WP.dspec_ok _).mpr rfl
    · split
      · exact (WP.dspec_ok _).mpr rfl
      · refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s stdin_fd) fun ⟨r, s1⟩ hs1 => ?_
        cases r with
        | Err _ => exact (WP.dspec_ok _).mpr hs1
        | Ok _ =>
          refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s1 stdout_fd) fun ⟨r1, s2⟩ hs2 => ?_
          cases r1 with
          | Err _ => exact (WP.dspec_ok _).mpr (hs2.trans hs1)
          | Ok _ =>
            refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s2 stderr_fd) fun ⟨r2, s3⟩ hs3 => ?_
            cases r2 <;> exact (WP.dspec_ok _).mpr (hs3.trans (hs2.trans hs1))

private theorem clear_cloexec_dspec_blockedSigs (s : sys.Sys) (fd : I32) :
    WP.dspec (postfork.fd_ops.clear_cloexec s fd) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold postfork.fd_ops.clear_cloexec
  refine WP.dspec_bind (sys_fcntl_getfd_dspec_blockedSigs s fd) fun ⟨r, s1⟩ hs1 => ?_
  cases r with
  | Err _ => exact (WP.dspec_ok _).mpr hs1
  | Ok flags =>
    simp only [lift, bind_ok]
    exact WP.dspec_mono (sys_fcntl_setfd_dspec_blockedSigs s1 fd _) fun p hp => hp.trans hs1

private theorem setupStdioClear012_dspec_blockedSigs (s : sys.Sys) :
    WP.dspec (setupStdioClear012 s) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold setupStdioClear012
  refine WP.dspec_bind (clear_cloexec_dspec_blockedSigs s 0#i32) fun ⟨r6, s10⟩ hs10 => ?_
  cases r6 with
  | Err _ => exact (WP.dspec_ok _).mpr hs10
  | Ok _ =>
    refine WP.dspec_bind (clear_cloexec_dspec_blockedSigs s10 1#i32) fun ⟨r7, s12⟩ hs12 => ?_
    cases r7 with
    | Err _ => exact (WP.dspec_ok _).mpr (hs12.trans hs10)
    | Ok _ =>
      exact WP.dspec_mono (clear_cloexec_dspec_blockedSigs s12 2#i32) fun p hp =>
        hp.trans (hs12.trans hs10)

private theorem setupStdioCloseAbove2_dspec_blockedSigs (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32) :
    WP.dspec (setupStdioCloseAbove2 s stdin_fd stdout_fd stderr_fd) fun s' => s'.blockedSigs = s.blockedSigs := by
  unfold setupStdioCloseAbove2
  refine WP.dspec_bind (Pₘ := fun s10 => s10.blockedSigs = s.blockedSigs) ?_ fun s10 hs10 => ?_
  · split
    · exact WP.dspec_bind (sys_close_dspec_blockedSigs s stdin_fd) fun ⟨_, s12⟩ h =>
        (WP.dspec_ok _).mpr h
    · exact (WP.dspec_ok _).mpr rfl
  refine WP.dspec_bind (Pₘ := fun s12 => s12.blockedSigs = s.blockedSigs) ?_ fun s12 hs12 => ?_
  · split
    · split
      · exact WP.dspec_bind (sys_close_dspec_blockedSigs s10 stdout_fd) fun ⟨_, s13⟩ h =>
          (WP.dspec_ok _).mpr (h.trans hs10)
      · exact (WP.dspec_ok _).mpr hs10
    · exact (WP.dspec_ok _).mpr hs10
  split
  · split
    · split
      · exact WP.dspec_bind (sys_close_dspec_blockedSigs s12 stderr_fd) fun ⟨_, s13⟩ h =>
          (WP.dspec_ok _).mpr (h.trans hs12)
      · exact (WP.dspec_ok _).mpr hs12
    · exact (WP.dspec_ok _).mpr hs12
  · exact (WP.dspec_ok _).mpr hs12

private theorem setupStdioFinish_dspec_blockedSigs (s : sys.Sys) (tmp0 tmp1 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    WP.dspec (setupStdioFinish s tmp0 tmp1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold setupStdioFinish
  refine WP.dspec_bind (Pₘ := fun s7 => s7.blockedSigs = s.blockedSigs) ?_ fun s7 hs7 => ?_
  · split
    · exact WP.dspec_bind (sys_close_dspec_blockedSigs s tmp1) fun ⟨_, s8⟩ h =>
        (WP.dspec_ok _).mpr h
    · exact (WP.dspec_ok _).mpr rfl
  refine WP.dspec_bind (Pₘ := fun s8 => s8.blockedSigs = s.blockedSigs) ?_ fun s8 hs8 => ?_
  · split
    · exact WP.dspec_bind (sys_close_dspec_blockedSigs s7 tmp0) fun ⟨_, s9⟩ h =>
        (WP.dspec_ok _).mpr (h.trans hs7)
    · exact (WP.dspec_ok _).mpr hs7
  refine WP.dspec_bind (Pₘ := fun s9 => s9.blockedSigs = s.blockedSigs) ?_ fun s9 hs9 => ?_
  · split
    · exact WP.dspec_mono (setupStdioCloseAbove2_dspec_blockedSigs s8 stdin_fd stdout_fd stderr_fd)
        fun s9 h => h.trans hs8
    · exact (WP.dspec_ok _).mpr hs8
  exact WP.dspec_mono (setupStdioClear012_dspec_blockedSigs s9) fun p hp => hp.trans hs9

private theorem setupStdioCloseTmpsErr_dspec_blockedSigs (s : sys.Sys) (tmp0 tmp1 : I32)
    (r : core.result.Result Unit I32) :
    WP.dspec (setupStdioCloseTmpsErr s tmp0 tmp1 r) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold setupStdioCloseTmpsErr
  refine WP.dspec_bind (Pₘ := fun s7 => s7.blockedSigs = s.blockedSigs) ?_ fun s7 hs7 => ?_
  · split
    · exact WP.dspec_bind (sys_close_dspec_blockedSigs s tmp1) fun ⟨_, s8⟩ h =>
        (WP.dspec_ok _).mpr h
    · exact (WP.dspec_ok _).mpr rfl
  split
  · exact WP.dspec_bind (sys_close_dspec_blockedSigs s7 tmp0) fun ⟨_, s8⟩ h =>
      (WP.dspec_ok _).mpr (h.trans hs7)
  · exact (WP.dspec_ok _).mpr hs7

private theorem setupStdioDup12Direct_dspec_blockedSigs (s : sys.Sys) (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    WP.dspec (setupStdioDup12Direct s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold setupStdioDup12Direct
  refine WP.dspec_bind (sys_dup2_dspec_blockedSigs s s11 1#i32) fun ⟨r3, s4⟩ hs4 => ?_
  cases r3 with
  | Err _ =>
    exact WP.dspec_mono (setupStdioCloseTmpsErr_dspec_blockedSigs s4 tmp0 (-1)#i32 _)
      fun p hp => hp.trans hs4
  | Ok _ =>
    refine WP.dspec_bind (sys_dup2_dspec_blockedSigs s4 s21 2#i32) fun ⟨r4, s5⟩ hs5 => ?_
    cases r4 with
    | Err _ =>
      exact WP.dspec_mono (setupStdioCloseTmpsErr_dspec_blockedSigs s5 tmp0 (-1)#i32 _)
        fun p hp => hp.trans (hs5.trans hs4)
    | Ok _ =>
      exact WP.dspec_mono
        (setupStdioFinish_dspec_blockedSigs s5 tmp0 (-1)#i32 stdin_fd stdout_fd stderr_fd close_sources_above2)
        fun p hp => hp.trans (hs5.trans hs4)

private theorem setupStdioAfterDup0_dspec_blockedSigs (s : sys.Sys) (tmp0 s11 s21 stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    WP.dspec (setupStdioAfterDup0 s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  unfold setupStdioAfterDup0
  split
  · split
    · refine WP.dspec_bind (sys_fcntl_dupfd_cloexec_dspec_blockedSigs s 1#i32 3#i32) fun ⟨r3, s4⟩ hs4 => ?_
      cases r3 with
      | Err _ =>
        split
        · exact WP.dspec_bind (sys_close_dspec_blockedSigs s4 tmp0) fun ⟨_, s5⟩ hs5 =>
            (WP.dspec_ok _).mpr (hs5.trans hs4)
        · exact (WP.dspec_ok _).mpr hs4
      | Ok fd1 =>
        refine WP.dspec_bind (sys_dup2_dspec_blockedSigs s4 s11 1#i32) fun ⟨r4, s5⟩ hs5 => ?_
        cases r4 with
        | Err _ =>
          exact WP.dspec_mono (setupStdioCloseTmpsErr_dspec_blockedSigs s5 tmp0 fd1 _)
            fun p hp => hp.trans (hs5.trans hs4)
        | Ok _ =>
          refine WP.dspec_bind (sys_dup2_dspec_blockedSigs s5 fd1 2#i32) fun ⟨r5, s6⟩ hs6 => ?_
          cases r5 with
          | Err _ =>
            exact WP.dspec_mono (setupStdioCloseTmpsErr_dspec_blockedSigs s6 tmp0 fd1 _)
              fun p hp => hp.trans (hs6.trans (hs5.trans hs4))
          | Ok _ =>
            exact WP.dspec_mono
              (setupStdioFinish_dspec_blockedSigs s6 tmp0 fd1 stdin_fd stdout_fd stderr_fd close_sources_above2)
              fun p hp => hp.trans (hs6.trans (hs5.trans hs4))
    · exact setupStdioDup12Direct_dspec_blockedSigs s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2
  · exact setupStdioDup12Direct_dspec_blockedSigs s tmp0 s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2

private theorem setupStdioSave0_dspec_blockedSigs (s1 : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    WP.dspec (setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.blockedSigs = s1.blockedSigs := by
  unfold setupStdioSave0
  refine WP.dspec_bind (sys_fcntl_dupfd_cloexec_dspec_blockedSigs s1 0#i32 3#i32) fun ⟨r1, s2⟩ hs2 => ?_
  cases r1 with
  | Err _ => exact (WP.dspec_ok _).mpr hs2
  | Ok fd =>
    refine WP.dspec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.dspec_ok _).mpr trivial) fun s11 _ => ?_
    refine WP.dspec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.dspec_ok _).mpr trivial) fun s21 _ => ?_
    refine WP.dspec_bind (sys_dup2_dspec_blockedSigs s2 stdin_fd 0#i32) fun ⟨r2, s3⟩ hs3 => ?_
    cases r2 with
    | Ok _ =>
      exact WP.dspec_mono
        (setupStdioAfterDup0_dspec_blockedSigs s3 fd s11 s21 stdin_fd stdout_fd stderr_fd close_sources_above2)
        fun p hp => hp.trans (hs3.trans hs2)
    | Err _ =>
      split
      · exact WP.dspec_bind (sys_close_dspec_blockedSigs s3 fd) fun ⟨_, s4⟩ hs4 =>
          (WP.dspec_ok _).mpr (hs4.trans (hs3.trans hs2))
      · exact (WP.dspec_ok _).mpr (hs3.trans hs2)

private theorem setupStdioNoSave0_dspec_blockedSigs (s1 : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    WP.dspec (setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.blockedSigs = s1.blockedSigs := by
  unfold setupStdioNoSave0
  refine WP.dspec_bind (sys_dup2_dspec_blockedSigs s1 stdin_fd 0#i32) fun ⟨r1, s2⟩ hs2 => ?_
  cases r1 with
  | Ok _ =>
    exact WP.dspec_mono
      (setupStdioAfterDup0_dspec_blockedSigs s2 (-1)#i32 stdout_fd stderr_fd stdin_fd stdout_fd stderr_fd close_sources_above2)
      fun p hp => hp.trans hs2
  | Err _ =>
    split
    · exact WP.dspec_bind (sys_close_dspec_blockedSigs s2 (-1)#i32) fun ⟨_, s3⟩ hs3 =>
        (WP.dspec_ok _).mpr (hs3.trans hs2)
    · exact (WP.dspec_ok _).mpr hs2

/-- `postfork.fd_ops.setup_stdio` preserves `blockedSigs`. -/
theorem setup_stdio_dspec_blockedSigs (s : sys.Sys) (stdin_fd stdout_fd stderr_fd : I32)
    (close_sources_above2 : Bool) :
    WP.dspec (postfork.fd_ops.setup_stdio s stdin_fd stdout_fd stderr_fd close_sources_above2) fun p =>
      p.2.blockedSigs = s.blockedSigs := by
  rw [setup_stdio_eq_factored]
  refine WP.dspec_bind (probe_stdio_open_dspec_blockedSigs s stdin_fd stdout_fd stderr_fd) fun ⟨r, s1⟩ hs1 => ?_
  cases r with
  | Err _ => exact (WP.dspec_ok _).mpr hs1
  | Ok _ =>
    change WP.dspec (if (stdin_fd != 0#i32) = true then
        if stdout_fd = 0#i32 then setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
        else if stderr_fd = 0#i32 then setupStdioSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
        else setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2
      else setupStdioNoSave0 s1 stdin_fd stdout_fd stderr_fd close_sources_above2) _
    split
    · split
      · exact WP.dspec_mono (setupStdioSave0_dspec_blockedSigs s1 stdin_fd stdout_fd stderr_fd close_sources_above2)
          fun p hp => hp.trans hs1
      · split
        · exact WP.dspec_mono (setupStdioSave0_dspec_blockedSigs s1 stdin_fd stdout_fd stderr_fd close_sources_above2)
            fun p hp => hp.trans hs1
        · exact WP.dspec_mono (setupStdioNoSave0_dspec_blockedSigs s1 stdin_fd stdout_fd stderr_fd close_sources_above2)
            fun p hp => hp.trans hs1
    · exact WP.dspec_mono (setupStdioNoSave0_dspec_blockedSigs s1 stdin_fd stdout_fd stderr_fd close_sources_above2)
        fun p hp => hp.trans hs1

end LeanSwe.PostFork.Proofs
