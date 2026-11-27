import LeanSweProofs.PostFork.Aeneas.Model
import LeanSweProofs.PostFork.Aeneas.Api
import LeanSweProofs.PostFork.Aeneas.Funs

/-!
Foundation lemmas for `LeanSwe.PostFork` kernel proofs:
- `OkPost` and `Aeneas.Std.WP.spec` monadic/loop combinators (`okPost_loop_decr_nat`),
- `World.ChildState` slot, descriptor, signal, and exec-image map algebra,
- bit-level `I32` `FD_CLOEXEC` flag preservation lemmas,
- `findLowestFreeFd` bounds and availability invariants,
- trace/oracle progress and `sys.*` step characterizations.
-/

namespace LeanSwe.PostFork.Proofs

open _root_.Aeneas.Std
open LeanSwe.PostFork.Aeneas.Internal
open LeanSwe.PostFork.Aeneas.Internal.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model

section OkPostBridge

/-- Equivalence between `Model.OkPost` and `Aeneas.Std.WP.spec`. -/
theorem okPost_iff_wp_spec {α : Type} (r : Result α) (P : α → Prop) :
    OkPost r P ↔ WP.spec r P := by
  cases r <;> simp [OkPost, WP.spec_ok, WP.spec_div, WP.spec_vis]

/-- Constructor rule for `OkPost` on `Result.ok`. -/
theorem okPost_ok {α : Type} (v : α) (P : α → Prop) (h : P v) :
    OkPost (Result.ok v) P :=
  ⟨v, rfl, h⟩

/-- Monotonicity rule for `OkPost`. -/
theorem okPost_mono {α : Type} {r : Result α} {P Q : α → Prop}
    (hr : OkPost r P) (himp : ∀ x, P x → Q x) :
    OkPost r Q := by
  rcases hr with ⟨v, hv, hp⟩
  exact ⟨v, hv, himp v hp⟩

/-- Sequential composition rule for `OkPost` over `Result.bind` (`Aeneas.Std.bind`). -/
theorem okPost_bind {α β : Type} {m : Result α} {k : α → Result β}
    {P : α → Prop} {Q : β → Prop}
    (hm : OkPost m P) (hk : ∀ x, P x → OkPost (k x) Q) :
    OkPost (m >>= k) Q := by
  rcases hm with ⟨v, hv, hp⟩
  subst hv
  simpa using hk v hp

/-- Lift rule for `Aeneas.Std.lift` inside `OkPost`. -/
theorem okPost_lift {α : Type} (x : α) (P : α → Prop) (hx : P x) :
    OkPost (lift x) P :=
  ⟨x, rfl, hx⟩

/-- Natural-number decreasing variant rule for `Aeneas.Std.loop` under `OkPost`. -/
theorem okPost_loop_decr_nat {α β : Type} (measure : α → Nat) (inv : α → Prop)
    (post : β → Prop) (body : α → Result (ControlFlow α β)) (x : α)
    (hBody : ∀ a, inv a → OkPost (body a) fun r =>
      match r with
      | ControlFlow.done y => post y
      | ControlFlow.cont a' => inv a' ∧ measure a' < measure a)
    (hInv : inv x) :
    OkPost (loop body x) post := by
  rw [okPost_iff_wp_spec]
  refine loop.spec_decr_nat measure inv post body x ?_ hInv
  intro a ha
  rw [← okPost_iff_wp_spec]
  exact hBody a ha

end OkPostBridge

section StateMapLemmas

/-- Unfolding lemma for `ChildState.getFd` after `eraseFdEntries` when keys match. -/
theorem find?_eraseFdEntries_self (fds : List (Int × FdEntry)) (fd : Int) :
    (eraseFdEntries fds fd).find? (fun p => p.1 == fd) = none := by
  unfold eraseFdEntries
  induction fds with
  | nil => rfl
  | cons p rest ih =>
    rw [List.filter_cons]
    split
    · next h =>
      have hne : (p.1 == fd) = false := by simpa using h
      rw [List.find?_cons, hne]
      exact ih
    · exact ih

/-- Unfolding lemma for `ChildState.getFd` after `eraseFdEntries` at a distinct key. -/
theorem find?_eraseFdEntries_ne (fds : List (Int × FdEntry)) {k fd : Int} (hne : k ≠ fd) :
    (eraseFdEntries fds fd).find? (fun p => p.1 == k) = fds.find? (fun p => p.1 == k) := by
  unfold eraseFdEntries
  induction fds with
  | nil => rfl
  | cons p rest ih =>
    rw [List.filter_cons, List.find?_cons]
    split
    · rw [List.find?_cons]
      cases (p.1 == k) <;> simp [ih]
    · next hp =>
      have hpEq : p.1 = fd := by simpa using hp
      have hpk : (p.1 == k) = false := beq_false_of_ne (hpEq ▸ hne.symm)
      rw [hpk]
      exact ih

/-- Reading the slot just written by `ChildState.putSlot` returns the written `FdEntry`. -/
theorem getFd_putSlot_self (s : ChildState) (fd : Int) (e : FdEntry) :
    (s.putSlot fd e).getFd fd = some e := by
  simp [ChildState.getFd, ChildState.putSlot]

/-- Reading a distinct slot after `ChildState.putSlot` is unchanged. -/
theorem getFd_putSlot_ne (s : ChildState) {k fd : Int} (hne : k ≠ fd) (e : FdEntry) :
    (s.putSlot fd e).getFd k = s.getFd k := by
  have hk : (fd == k) = false := beq_false_of_ne hne.symm
  simp [ChildState.getFd, ChildState.putSlot, hk, find?_eraseFdEntries_ne s.fds hne]

/-- Reading the slot closed by `ChildState.closeSlot` returns `none`. -/
theorem getFd_closeSlot_self (s : ChildState) (fd : Int) :
    (s.closeSlot fd).getFd fd = none := by
  simp [ChildState.getFd, ChildState.closeSlot, find?_eraseFdEntries_self]

/-- Reading a distinct slot after `ChildState.closeSlot` is unchanged. -/
theorem getFd_closeSlot_ne (s : ChildState) {k fd : Int} (hne : k ≠ fd) :
    (s.closeSlot fd).getFd k = s.getFd k := by
  simp [ChildState.getFd, ChildState.closeSlot, find?_eraseFdEntries_ne s.fds hne]

/-- `ChildState.isOpen` holds iff `ChildState.getFd` is `some`. -/
theorem isOpen_iff_isSome (s : ChildState) (fd : Int) :
    s.isOpen fd = (s.getFd fd).isSome := rfl

/-- `isOpen` after `putSlot` at the same slot is `true`. -/
theorem isOpen_putSlot_self (s : ChildState) (fd : Int) (e : FdEntry) :
    (s.putSlot fd e).isOpen fd = true := by
  simp [ChildState.isOpen, getFd_putSlot_self]

/-- `isOpen` after `putSlot` at a distinct slot is unchanged. -/
theorem isOpen_putSlot_ne (s : ChildState) {k fd : Int} (hne : k ≠ fd) (e : FdEntry) :
    (s.putSlot fd e).isOpen k = s.isOpen k := by
  simp [ChildState.isOpen, getFd_putSlot_ne s hne e]

/-- `isOpen` after `closeSlot` at the same slot is `false`. -/
theorem isOpen_closeSlot_self (s : ChildState) (fd : Int) :
    (s.closeSlot fd).isOpen fd = false := by
  simp [ChildState.isOpen, getFd_closeSlot_self]

/-- `isOpen` after `closeSlot` at a distinct slot is unchanged. -/
theorem isOpen_closeSlot_ne (s : ChildState) {k fd : Int} (hne : k ≠ fd) :
    (s.closeSlot fd).isOpen k = s.isOpen k := by
  simp [ChildState.isOpen, getFd_closeSlot_ne s hne]

/-- Lookup of the descriptor just stored via `ChildState.putDesc`. -/
theorem getDesc_putDesc_self (s : ChildState) (d : Desc) (st : DescState) :
    (s.putDesc d st).getDesc d = st := by
  simp [ChildState.getDesc, ChildState.putDesc]

/-- Lookup of a distinct descriptor is unchanged by `ChildState.putDesc`. -/
theorem getDesc_putDesc_ne (s : ChildState) {k d : Desc} (hne : k ≠ d) (st : DescState) :
    (s.putDesc d st).getDesc k = s.getDesc k := by
  have hk : (d == k) = false := beq_false_of_ne hne.symm
  simp only [ChildState.getDesc, ChildState.putDesc, List.find?_cons, hk]
  suffices h : (List.filter (fun p => p.1 != d) s.descs).find? (fun p => p.1 == k) =
      s.descs.find? (fun p => p.1 == k) by
    rw [h]
  induction s.descs with
  | nil => rfl
  | cons p rest ih =>
    rw [List.filter_cons, List.find?_cons]
    split
    · rw [List.find?_cons]
      cases (p.1 == k) <;> simp [ih]
    · next hp =>
      have hpEq : p.1 = d := by simpa using hp
      have hpk : (p.1 == k) = false := beq_false_of_ne (hpEq ▸ hne.symm)
      rw [hpk]
      exact ih

/-- Lookup of a signal disposition just updated by `ChildState.putSig`. -/
theorem getSig_putSig_self (s : ChildState) (g : Int) (disp : Disp) :
    (s.putSig g disp).getSig g = disp := by
  simp [ChildState.getSig, ChildState.putSig]

/-- Lookup of a distinct signal is unchanged by `ChildState.putSig`. -/
theorem getSig_putSig_ne (s : ChildState) {k g : Int} (hne : k ≠ g) (disp : Disp) :
    (s.putSig g disp).getSig k = s.getSig k := by
  have hk : (g == k) = false := beq_false_of_ne hne.symm
  simp only [ChildState.getSig, ChildState.putSig, List.find?_cons, hk]
  suffices h : (List.filter (fun p => p.1 != g) s.sig).find? (fun p => p.1 == k) =
      s.sig.find? (fun p => p.1 == k) by
    rw [h]
  induction s.sig with
  | nil => rfl
  | cons p rest ih =>
    rw [List.filter_cons, List.find?_cons]
    split
    · rw [List.find?_cons]
      cases (p.1 == k) <;> simp [ih]
    · next hp =>
      have hpEq : p.1 = g := by simpa using hp
      have hpk : (p.1 == k) = false := beq_false_of_ne (hpEq ▸ hne.symm)
      rw [hpk]
      exact ih

/-- `dedupFdEntriesAux` keeps the first entry per key outside `seen`. -/
theorem find?_dedupFdEntriesAux (seen : List Int) (fds : List (Int × FdEntry)) (k : Int) :
    (dedupFdEntriesAux seen fds).find? (fun p => p.1 == k) =
      if k ∈ seen then none else fds.find? (fun p => p.1 == k) := by
  induction fds generalizing seen with
  | nil =>
    simp [dedupFdEntriesAux]
  | cons p rest ih =>
    rcases p with ⟨fd, e⟩
    have hstep : dedupFdEntriesAux seen ((fd, e) :: rest) =
        if seen.contains fd then dedupFdEntriesAux seen rest
        else (fd, e) :: dedupFdEntriesAux (fd :: seen) rest := rfl
    rw [hstep]
    split
    · next hmem =>
      rw [ih]
      have hfdSeen : fd ∈ seen := List.contains_iff_mem.mp hmem
      rw [List.find?_cons]
      by_cases hkf : (fd == k) = true
      · have hEq : fd = k := beq_iff_eq.mp hkf
        subst hEq
        simp [hfdSeen]
      · simp [hkf]
    · next hmem =>
      rw [List.find?_cons, List.find?_cons]
      by_cases hfk : (fd == k) = true
      · have hEq : fd = k := beq_iff_eq.mp hfk
        subst hEq
        have hnot : fd ∉ seen := fun hm => hmem (List.contains_iff_mem.mpr hm)
        simp [hnot]
      · have hne : fd ≠ k := fun h => hfk (beq_iff_eq.mpr h)
        have hfk' : (fd == k) = false := Bool.eq_false_iff.mpr hfk
        rw [hfk']
        dsimp only
        rw [ih (fd :: seen)]
        simp [hne.symm]

/-- `dedupFdEntriesAux` emits entries with keys disjoint from `seen` and pairwise distinct keys. -/
theorem nodup_dedupFdEntriesAux (seen : List Int) (fds : List (Int × FdEntry)) :
    (∀ p ∈ dedupFdEntriesAux seen fds, p.1 ∉ seen) ∧
      (dedupFdEntriesAux seen fds).Pairwise (fun a b => a.1 ≠ b.1) := by
  induction fds generalizing seen with
  | nil =>
    simp [dedupFdEntriesAux]
  | cons a rest ih =>
    rcases a with ⟨fd, e⟩
    have hstep : dedupFdEntriesAux seen ((fd, e) :: rest) =
        if seen.contains fd then dedupFdEntriesAux seen rest
        else (fd, e) :: dedupFdEntriesAux (fd :: seen) rest := rfl
    rw [hstep]
    split
    · exact ih seen
    · next hmem =>
      rcases ih (fd :: seen) with ⟨hseen, hpw⟩
      refine ⟨?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hprest
        · exact fun hm => hmem (List.contains_iff_mem.mpr hm)
        · exact fun hm => hseen p hprest (List.mem_cons_of_mem fd hm)
      · refine List.pairwise_cons.mpr ⟨?_, hpw⟩
        intro b hb heq
        exact hseen b hb (heq ▸ List.mem_cons_self)

/-- Helper showing `find?` on a key-unique list after `filter` checks the first match. -/
theorem find?_filter_of_pairwise {α : Type} {key : α → Int} {xs : List α}
    (hpw : xs.Pairwise (fun a b => key a ≠ key b)) (pred : α → Bool) (k : Int) :
    (xs.filter pred).find? (fun p => key p == k) =
      match xs.find? (fun p => key p == k) with
      | some p => if pred p then some p else none
      | none => none := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    rcases List.pairwise_cons.mp hpw with ⟨hhead, htail⟩
    rw [List.filter_cons, List.find?_cons]
    by_cases hak : (key a == k) = true
    · have hEq : key a = k := beq_iff_eq.mp hak
      have hnoneFilt : (rest.filter pred).find? (fun p => key p == k) = none := by
        rw [List.find?_eq_none]
        intro b hb hbk
        exact hhead b (List.mem_of_mem_filter hb) (hEq ▸ (beq_iff_eq.mp hbk).symm)
      have hnoneRest : rest.find? (fun p => key p == k) = none := by
        rw [List.find?_eq_none]
        intro b hb hbk
        exact hhead b hb (hEq ▸ (beq_iff_eq.mp hbk).symm)
      rw [hak]
      dsimp only
      split
      · simp [*]
      · simp [*]
    · have hakf : (key a == k) = false := Bool.eq_false_iff.mpr hak
      have ih' := ih htail
      rw [hakf]
      dsimp only
      split
      · rw [List.find?_cons, hakf]
        exact ih'
      · exact ih'

/-- Helper showing `find?` on a filtered deduplicated FD list matches finding first then checking `pred`. -/
theorem find?_filter_dedupFdEntries (fds : List (Int × FdEntry)) (pred : Int × FdEntry → Bool) (k : Int) :
    ((dedupFdEntries fds).filter pred).find? (fun p => p.1 == k) =
      match fds.find? (fun p => p.1 == k) with
      | some p => if pred p then some p else none
      | none => none := by
  have hfind : (dedupFdEntriesAux [] fds).find? (fun p => p.1 == k) = fds.find? (fun p => p.1 == k) := by
    simpa using find?_dedupFdEntriesAux [] fds k
  have hpw := (nodup_dedupFdEntriesAux [] fds).2
  change ((dedupFdEntriesAux [] fds).filter pred).find? (fun p => p.1 == k) = _
  rw [find?_filter_of_pairwise (key := Prod.fst) hpw pred k, hfind]
  cases fds.find? (fun p => p.1 == k) <;> rfl

/-- Lookup in `afterExecFds` matches `find?` iff the entry exists with `cloexec = false`. -/
theorem find?_afterExecFds (fds : List (Int × FdEntry)) (k : Int) :
    (afterExecFds fds).find? (fun p => p.1 == k) =
      match fds.find? (fun p => p.1 == k) with
      | some (fd, e) => if e.cloexec then none else some (fd, e)
      | none => none := by
  unfold afterExecFds
  rw [find?_filter_dedupFdEntries]
  cases fds.find? (fun p => p.1 == k) with
  | none => rfl
  | some p =>
    rcases p with ⟨fd, e⟩
    cases he : e.cloexec <;> simp [he]

/-- `execImageGetFd` characterization in terms of `ChildState.getFd`. -/
theorem execImageGetFd_imageOf (s : ChildState) (path : Bytes) (argv envp : List Bytes) (k : Int) :
    execImageGetFd (imageOf s path argv envp) k =
      match s.getFd k with
      | some e => if e.cloexec then none else some e
      | none => none := by
  simp only [execImageGetFd, imageOf, ChildState.getFd, find?_afterExecFds]
  cases hf : s.fds.find? (fun p => p.1 == k) with
  | none => rfl
  | some p =>
    rcases p with ⟨fd, e⟩
    cases he : e.cloexec <;> simp [he]

/-- `dedupSigEntriesAux` keeps the first entry per signal outside `seen`. -/
theorem find?_dedupSigEntriesAux (seen : List Int) (sigs : List (Int × Disp)) (k : Int) :
    (dedupSigEntriesAux seen sigs).find? (fun p => p.1 == k) =
      if k ∈ seen then none else sigs.find? (fun p => p.1 == k) := by
  induction sigs generalizing seen with
  | nil =>
    simp [dedupSigEntriesAux]
  | cons p rest ih =>
    rcases p with ⟨g, d⟩
    have hstep : dedupSigEntriesAux seen ((g, d) :: rest) =
        if seen.contains g then dedupSigEntriesAux seen rest
        else (g, d) :: dedupSigEntriesAux (g :: seen) rest := rfl
    rw [hstep]
    split
    · next hmem =>
      rw [ih]
      have hgSeen : g ∈ seen := List.contains_iff_mem.mp hmem
      rw [List.find?_cons]
      by_cases hkg : (g == k) = true
      · have hEq : g = k := beq_iff_eq.mp hkg
        subst hEq
        simp [hgSeen]
      · simp [hkg]
    · next hmem =>
      rw [List.find?_cons, List.find?_cons]
      by_cases hgk : (g == k) = true
      · have hEq : g = k := beq_iff_eq.mp hgk
        subst hEq
        have hnot : g ∉ seen := fun hm => hmem (List.contains_iff_mem.mpr hm)
        simp [hnot]
      · have hne : g ≠ k := fun h => hgk (beq_iff_eq.mpr h)
        have hgk' : (g == k) = false := Bool.eq_false_iff.mpr hgk
        rw [hgk']
        dsimp only
        rw [ih (g :: seen)]
        simp [hne.symm]

/-- `dedupSigEntriesAux` emits entries with signals disjoint from `seen` and pairwise distinct keys. -/
theorem nodup_dedupSigEntriesAux (seen : List Int) (sigs : List (Int × Disp)) :
    (∀ p ∈ dedupSigEntriesAux seen sigs, p.1 ∉ seen) ∧
      (dedupSigEntriesAux seen sigs).Pairwise (fun a b => a.1 ≠ b.1) := by
  induction sigs generalizing seen with
  | nil =>
    simp [dedupSigEntriesAux]
  | cons a rest ih =>
    rcases a with ⟨g, d⟩
    have hstep : dedupSigEntriesAux seen ((g, d) :: rest) =
        if seen.contains g then dedupSigEntriesAux seen rest
        else (g, d) :: dedupSigEntriesAux (g :: seen) rest := rfl
    rw [hstep]
    split
    · exact ih seen
    · next hmem =>
      rcases ih (g :: seen) with ⟨hseen, hpw⟩
      refine ⟨?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hprest
        · exact fun hm => hmem (List.contains_iff_mem.mpr hm)
        · exact fun hm => hseen p hprest (List.mem_cons_of_mem g hm)
      · refine List.pairwise_cons.mpr ⟨?_, hpw⟩
        intro b hb heq
        exact hseen b hb (heq ▸ List.mem_cons_self)

/-- `execImageGetSig` preserves `ignore` and resets `handler` to `default`. -/
theorem execImageGetSig_imageOf (s : ChildState) (path : Bytes) (argv envp : List Bytes) (k : Int) :
    execImageGetSig (imageOf s path argv envp) k =
      match s.getSig k with
      | Disp.ignore => Disp.ignore
      | Disp.default => Disp.default
      | Disp.handler => Disp.default := by
  have hfind : (dedupSigEntries s.sig).find? (fun p => p.1 == k) = s.sig.find? (fun p => p.1 == k) := by
    simpa [dedupSigEntries] using find?_dedupSigEntriesAux [] s.sig k
  have hpw := (nodup_dedupSigEntriesAux [] s.sig).2
  let keepIgn : (Int × Disp) → Option (Int × Disp) := fun p =>
    match p.2 with
    | Disp.ignore => some (p.1, Disp.ignore)
    | Disp.default => none
    | Disp.handler => none
  have hfm : ∀ (xs : List (Int × Disp)),
      xs.Pairwise (fun a b => a.1 ≠ b.1) →
      (xs.filterMap keepIgn).find? (fun p => p.1 == k) =
        match xs.find? (fun p => p.1 == k) with
        | some (g, Disp.ignore) => some (g, Disp.ignore)
        | _ => none := by
    intro xs huniq
    induction xs with
    | nil => simp
    | cons a rest ih =>
      rcases a with ⟨g, d⟩
      rcases List.pairwise_cons.mp huniq with ⟨hhead, htail⟩
      by_cases hgk : (g == k) = true
      · have hEq : g = k := beq_iff_eq.mp hgk
        have hnoneF : ((rest.filterMap keepIgn).find? (fun p => p.1 == k)) = none := by
          rw [List.find?_eq_none]
          intro b hb hbk
          rcases List.mem_filterMap.mp hb with ⟨⟨g', d'⟩, hmem', hmap⟩
          have hne : g ≠ g' := hhead (g', d') hmem'
          cases d' <;> simp only [keepIgn] at hmap
          · cases hmap
          · injection hmap with heqb
            subst heqb
            exact hne (hEq.trans (beq_iff_eq.mp hbk).symm)
          · cases hmap
        cases d with
        | default =>
          rw [List.filterMap_cons_none (h := by rfl), List.find?_cons, hgk, hnoneF]
        | ignore =>
          rw [List.filterMap_cons_some (b := (g, Disp.ignore)) (h := by rfl),
            List.find?_cons, List.find?_cons, hgk]
        | handler =>
          rw [List.filterMap_cons_none (h := by rfl), List.find?_cons, hgk, hnoneF]
      · have hgkf : (g == k) = false := Bool.eq_false_iff.mpr hgk
        cases d with
        | default =>
          rw [List.filterMap_cons_none (h := by rfl), List.find?_cons, hgkf]
          exact ih htail
        | ignore =>
          rw [List.filterMap_cons_some (b := (g, Disp.ignore)) (h := by rfl),
            List.find?_cons, List.find?_cons, hgkf]
          exact ih htail
        | handler =>
          rw [List.filterMap_cons_none (h := by rfl), List.find?_cons, hgkf]
          exact ih htail
  have hres := hfm (dedupSigEntries s.sig) hpw
  change (match (afterExecSigs s.sig).find? (fun p => p.1 == k) with
    | some (_, d) => d
    | none => Disp.default) = _
  have hafter : afterExecSigs s.sig = (dedupSigEntries s.sig).filterMap keepIgn := rfl
  rw [hafter, hres, hfind]
  simp only [ChildState.getSig]
  cases s.sig.find? (fun p => p.1 == k) with
  | none => rfl
  | some p =>
    rcases p with ⟨g, d⟩
    cases d <;> rfl

end StateMapLemmas

section BitVecAndFlags

/-- Converting an in-range `Int` via `World.mkI32` preserves its integer value. -/
theorem mkI32_val {z : Int} (hlo : -2147483648 ≤ z) (hhi : z ≤ 2147483647) :
    (mkI32 z : Int) = z := by
  unfold mkI32
  change (BitVec.ofInt 32 z).toInt = z
  rw [BitVec.toInt_ofInt]
  unfold Int.bmod
  dsimp only
  split <;> omega

/-- Non-negative bounded integers round-trip through `World.mkI32`. -/
theorem mkI32_val_nonneg {z : Int} (hlo : 0 ≤ z) (hhi : z ≤ 2147483647) :
    (mkI32 z : Int) = z :=
  mkI32_val (by omega) hhi

/-- Converting a `Nat` bounded by `2 ^ UScalarTy.Usize.numBits` via `World.mkUsize` preserves its natural value. -/
theorem mkUsize_val_of_lt {n : Nat} (hlt : n < 2 ^ UScalarTy.Usize.numBits) :
    (mkUsize n : Nat) = n := by
  unfold mkUsize
  change (BitVec.ofNat UScalarTy.Usize.numBits n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- Converting a `Nat` bounded by a `Usize` scalar via `World.mkUsize` preserves its natural value. -/
theorem mkUsize_val_le_scalar {n : Nat} (u : Usize) (hle : n ≤ (u : Nat)) :
    (mkUsize n : Nat) = n :=
  mkUsize_val_of_lt (Nat.lt_of_le_of_lt hle u.bv.isLt)

/-- Converting a `Nat` bounded by `255` via `World.mkU8` preserves its natural value. -/
theorem mkU8_val {n : Nat} (hhi : n ≤ 255) :
    (mkU8 n : Nat) = n := by
  unfold mkU8
  change (BitVec.ofNat 8 n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- Two `I32` values are equal if their underlying 32-bit `BitVec`s are equal. -/
theorem i32_eq_of_bv_eq {a b : I32} (h : a.bv = b.bv) : a = b := by
  rcases a with ⟨va⟩
  rcases b with ⟨vb⟩
  congr

/-- Clearing `FD_CLOEXEC` (`1#i32`) yields bit 0 unset. -/
theorem i32_and_not_one_and_one (x : I32) :
    ((x &&& ~~~1#i32) &&& 1#i32) = 0#i32 := by
  apply i32_eq_of_bv_eq
  change (x.bv &&& BitVec.ofNat 32 4294967294) &&& BitVec.ofNat 32 1 = BitVec.ofNat 32 0
  rw [BitVec.and_assoc, show (BitVec.ofNat 32 4294967294 &&& BitVec.ofNat 32 1) = BitVec.ofNat 32 0 from by decide,
    BitVec.and_zero]

/-- Setting `FD_CLOEXEC` (`1#i32`) yields bit 0 set. -/
theorem i32_or_one_and_one (x : I32) :
    ((x ||| 1#i32) &&& 1#i32) = 1#i32 := by
  apply i32_eq_of_bv_eq
  change (x.bv ||| BitVec.ofNat 32 1) &&& BitVec.ofNat 32 1 = BitVec.ofNat 32 1
  rw [BitVec.and_or_distrib_right,
    show (BitVec.ofNat 32 1 &&& BitVec.ofNat 32 1) = BitVec.ofNat 32 1 from by decide]
  ext i hi
  rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with rfl | hpos
  · simp
  · have hb : (BitVec.ofNat 32 1)[i] = false := by
      have hi32 : i < 32 := hi
      have hne : i ≠ 0 := Nat.ne_of_gt hpos
      revert i hi32 hne
      decide
    simp [hb]

/-- Clearing `FD_CLOEXEC` leaves `2147483646#i32` (`0x7ffffffe`) masked bits intact. -/
theorem i32_and_not_one_and_hi (x : I32) :
    ((x &&& ~~~1#i32) &&& 2147483646#i32) = (x &&& 2147483646#i32) := by
  apply i32_eq_of_bv_eq
  change (x.bv &&& BitVec.ofNat 32 4294967294) &&& BitVec.ofNat 32 2147483646 =
    x.bv &&& BitVec.ofNat 32 2147483646
  rw [BitVec.and_assoc,
    show (BitVec.ofNat 32 4294967294 &&& BitVec.ofNat 32 2147483646) = BitVec.ofNat 32 2147483646 from by decide]

/-- Setting `FD_CLOEXEC` leaves `2147483646#i32` (`0x7ffffffe`) masked bits intact. -/
theorem i32_or_one_and_hi (x : I32) :
    ((x ||| 1#i32) &&& 2147483646#i32) = (x &&& 2147483646#i32) := by
  apply i32_eq_of_bv_eq
  change (x.bv ||| BitVec.ofNat 32 1) &&& BitVec.ofNat 32 2147483646 =
    x.bv &&& BitVec.ofNat 32 2147483646
  rw [BitVec.and_or_distrib_right,
    show (BitVec.ofNat 32 1 &&& BitVec.ofNat 32 2147483646) = BitVec.ofNat 32 0 from by decide,
    BitVec.or_zero]

/-- Exact characterization of `updateFdFlags` after `clear_cloexec` (`flags &&& ~~~1#i32`). -/
theorem updateFdFlags_clear_cloexec (s : ChildState) (e : FdEntry) :
    updateFdFlags s.kernelMasksSetfd (fdFlagsWord e &&& ~~~1#i32) e =
      { desc := e.desc
        cloexec := false
        extraFdFlags := expectedExtraFlagsAfterSetfd s e } := by
  unfold updateFdFlags expectedExtraFlagsAfterSetfd
  have hclo : ((fdFlagsWord e &&& ~~~1#i32) &&& 1#i32 != 0#i32) = false := by
    rw [i32_and_not_one_and_one]
    decide
  rw [hclo]
  cases hk : s.kernelMasksSetfd
  · simpa [hk] using i32_and_not_one_and_hi (fdFlagsWord e)
  · simp

/-- Exact characterization of `updateFdFlags` after `set_cloexec` (`flags ||| 1#i32`). -/
theorem updateFdFlags_set_cloexec (s : ChildState) (e : FdEntry) :
    updateFdFlags s.kernelMasksSetfd (fdFlagsWord e ||| 1#i32) e =
      { desc := e.desc
        cloexec := true
        extraFdFlags := expectedExtraFlagsAfterSetfd s e } := by
  unfold updateFdFlags expectedExtraFlagsAfterSetfd
  have hclo : ((fdFlagsWord e ||| 1#i32) &&& 1#i32 != 0#i32) = true := by
    rw [i32_or_one_and_one]
    decide
  rw [hclo]
  cases hk : s.kernelMasksSetfd
  · simpa [hk] using i32_or_one_and_hi (fdFlagsWord e)
  · simp

end BitVecAndFlags

section FreeFdAndOracle

/-- Invariant satisfied by any slot returned from `findLowestFreeFdAux`. -/
theorem findLowestFreeFdAux_spec (s : ChildState) (cur : Int) (fuel : Nat) (dst : Int)
    (h : findLowestFreeFdAux s cur fuel = some dst) :
    cur ≤ dst ∧ dst < cur + Int.ofNat fuel ∧ s.isOpen dst = false := by
  induction fuel generalizing cur with
  | zero =>
    simp [findLowestFreeFdAux] at h
  | succ k ih =>
    have hstep : findLowestFreeFdAux s cur (k + 1) =
        if s.isOpen cur then findLowestFreeFdAux s (cur + 1) k else some cur := rfl
    rw [hstep] at h
    split at h
    · next hopen =>
      have hrec := ih (cur + 1) h
      simp only [Int.ofNat_eq_natCast] at hrec ⊢
      refine ⟨by omega, by omega, hrec.2.2⟩
    · next hopen =>
      injection h with heq
      subst heq
      have hfalse : s.isOpen cur = false := Bool.eq_false_iff.mpr hopen
      simp only [Int.ofNat_eq_natCast]
      exact ⟨by omega, by omega, hfalse⟩

/-- Any slot returned by `findLowestFreeFd` is `≥ minFd`, below `min s.fdLimit 2^31`, and currently closed. -/
theorem findLowestFreeFd_spec (s : ChildState) (minFd dst : Int)
    (h : findLowestFreeFd s minFd = some dst) :
    minFd ≤ dst ∧ 0 ≤ dst ∧ dst < min s.fdLimit 2147483648 ∧ dst ≤ 2147483647 ∧
      s.isOpen dst = false ∧ s.getFd dst = none := by
  unfold findLowestFreeFd at h
  dsimp only at h
  split at h
  · cases h
  · next hbad =>
    have hbadf : (decide (minFd < 0) || decide (minFd ≥ min s.fdLimit 2147483648)) = false :=
      Bool.eq_false_iff.mpr hbad
    have hparts := Bool.or_eq_false_iff.mp hbadf
    have hlo : 0 ≤ minFd := by
      by_contra hlt
      have : decide (minFd < 0) = true := decide_eq_true (Int.lt_of_not_ge hlt)
      rw [this] at hparts
      cases hparts.1
    have hhi : minFd < min s.fdLimit 2147483648 := by
      by_contra hge
      have : decide (minFd ≥ min s.fdLimit 2147483648) = true := decide_eq_true (Int.not_lt.mp hge)
      rw [this] at hparts
      cases hparts.2
    have haux := findLowestFreeFdAux_spec s minFd (min s.fdLimit 2147483648 - minFd).toNat dst h
    have hsub : Int.ofNat (min s.fdLimit 2147483648 - minFd).toNat = min s.fdLimit 2147483648 - minFd := by
      change ((Int.toNat (min s.fdLimit 2147483648 - minFd) : Nat) : Int) = min s.fdLimit 2147483648 - minFd
      omega
    have hclosed : s.getFd dst = none := by
      cases hg : s.getFd dst with
      | none => rfl
      | some e =>
        have hop := haux.2.2
        simp [ChildState.isOpen, hg] at hop
    refine ⟨haux.1, by omega, by omega, by omega, haux.2.2, hclosed⟩

/-- Empty oracle guarantees `currentFault s = StepFault.normal`. -/
theorem currentFault_oracle_nil (s : ChildState) (h : s.oracle = []) :
    currentFault s = StepFault.normal := by
  simp [currentFault, h]

/-- Once trace reaches or exceeds oracle length, `currentFault s = StepFault.normal`. -/
theorem currentFault_ge_oracle (s : ChildState) (h : s.oracle.length ≤ s.trace.length) :
    currentFault s = StepFault.normal := by
  simp [currentFault, List.getElem?_eq_none h]

/-- If `currentFault s` is `.fail rawE`, then `s.trace.length < s.oracle.length`. -/
theorem lt_oracle_of_currentFault_fail {s : ChildState} {rawE : I32}
    (h : currentFault s = StepFault.fail rawE) :
    s.trace.length < s.oracle.length := by
  by_contra hge
  have hnorm := currentFault_ge_oracle s (Nat.le_of_not_lt hge)
  rw [hnorm] at h
  cases h

/-- If `oracleHasSeccomp s.oracle = false`, `currentFault s` cannot be `StepFault.seccomp _`. -/
theorem not_seccomp_of_oracleHasSeccomp_false {s : ChildState}
    (h : oracleHasSeccomp s.oracle = false) {rawE : I32}
    (hsec : currentFault s = StepFault.seccomp rawE) : False := by
  unfold oracleHasSeccomp at h
  simp only [List.any_eq_false] at h
  unfold currentFault at hsec
  cases hget : s.oracle[s.trace.length]? with
  | none => rw [hget] at hsec; cases hsec
  | some f =>
    rw [hget] at hsec
    have hmem : f ∈ s.oracle := List.mem_of_getElem? hget
    have hf := h f hmem
    cases hsec
    simp [isSeccompFault] at hf

/-- `sanitizeErrno` always yields an errno in `[1, 4095]`, hence `≠ 0`. -/
theorem sanitizeErrno_bounds (e : I32) :
    1 ≤ (sanitizeErrno e : Int) ∧ (sanitizeErrno e : Int) ≤ 4095 := by
  unfold sanitizeErrno
  split
  · next h =>
    have h1 : (1#i32 : Int) ≤ (e : Int) := by simpa using (Bool.and_eq_true _ _).mp h |>.1
    have h2 : (e : Int) ≤ (4095#i32 : Int) := by simpa using (Bool.and_eq_true _ _).mp h |>.2
    exact ⟨h1, h2⟩
  · exact ⟨by decide, by decide⟩

end FreeFdAndOracle

section SysLemmas

/-- Environmental `ChildState` fields preserved by all non-`execve`/`exit` syscalls. -/
structure SameChildConfig (s' s : ChildState) : Prop where
  /-- Fault oracle preserved. -/
  oracle : s'.oracle = s.oracle
  /-- Running status preserved. -/
  status : s'.status = s.status
  /-- `RLIMIT_NOFILE` limit preserved. -/
  fdLimit : s'.fdLimit = s.fdLimit
  /-- `kernelMasksSetfd` setting preserved. -/
  kernelMasksSetfd : s'.kernelMasksSetfd = s.kernelMasksSetfd
  /-- `closeRangeSupported` setting preserved. -/
  closeRangeSupported : s'.closeRangeSupported = s.closeRangeSupported
  /-- `closeRangeErrno` setting preserved. -/
  closeRangeErrno : s'.closeRangeErrno = s.closeRangeErrno
  /-- `procSelfFdAvailable` setting preserved. -/
  procSelfFdAvailable : s'.procSelfFdAvailable = s.procSelfFdAvailable
  /-- `procOpenErrno` setting preserved. -/
  procOpenErrno : s'.procOpenErrno = s.procOpenErrno
  /-- Child PID preserved. -/
  pid : s'.pid = s.pid
  /-- Child SID preserved. -/
  sid : s'.sid = s.sid
  /-- Resolved `chdir` overrides preserved. -/
  chdirResolved : s'.chdirResolved = s.chdirResolved

/-- Reflexivity for `SameChildConfig`. -/
theorem SameChildConfig.refl (s : ChildState) : SameChildConfig s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Transitivity for `SameChildConfig`. -/
theorem SameChildConfig.trans {a b c : ChildState} (hab : SameChildConfig a b)
    (hbc : SameChildConfig b c) : SameChildConfig a c :=
  ⟨hab.oracle.trans hbc.oracle, hab.status.trans hbc.status,
   hab.fdLimit.trans hbc.fdLimit, hab.kernelMasksSetfd.trans hbc.kernelMasksSetfd,
   hab.closeRangeSupported.trans hbc.closeRangeSupported,
   hab.closeRangeErrno.trans hbc.closeRangeErrno,
   hab.procSelfFdAvailable.trans hbc.procSelfFdAvailable,
   hab.procOpenErrno.trans hbc.procOpenErrno,
   hab.pid.trans hbc.pid, hab.sid.trans hbc.sid,
   hab.chdirResolved.trans hbc.chdirResolved⟩

/-- Preserves `SameChildConfig` across a `trace` update. -/
theorem SameChildConfig.with_trace {a b : ChildState} (h : SameChildConfig a b) (t : List Event) :
    SameChildConfig { a with trace := t } b :=
  ⟨h.oracle, h.status, h.fdLimit, h.kernelMasksSetfd, h.closeRangeSupported,
   h.closeRangeErrno, h.procSelfFdAvailable, h.procOpenErrno, h.pid, h.sid, h.chdirResolved⟩

/-- `ChildState.closeSlot` preserves `SameChildConfig`. -/
theorem SameChildConfig.closeSlot (s : ChildState) (fd : Int) :
    SameChildConfig (s.closeSlot fd) s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `ChildState.putSlot` preserves `SameChildConfig`. -/
theorem SameChildConfig.putSlot (s : ChildState) (fd : Int) (e : FdEntry) :
    SameChildConfig (s.putSlot fd e) s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `ChildState.putSig` preserves `SameChildConfig`. -/
theorem SameChildConfig.putSig (s : ChildState) (g : Int) (d : Disp) :
    SameChildConfig (s.putSig g d) s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Updating `cwd` preserves `SameChildConfig`. -/
theorem SameChildConfig.with_cwd (s : ChildState) (c : Bytes) :
    SameChildConfig { s with cwd := c } s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Updating `pgid` preserves `SameChildConfig`. -/
theorem SameChildConfig.with_pgid (s : ChildState) (p : Int) :
    SameChildConfig { s with pgid := p } s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Non-running states short-circuit `runUnitSyscall` without modifying state. -/
theorem runUnitSyscall_not_running (s : ChildState) (h : s.status ≠ Status.running)
    (req : Req) (forcedErr? : Option I32) (onOk onErr : ChildState → ChildState) :
    runUnitSyscall s req forcedErr? onOk onErr = Result.ok (.Ok (), s) := by
  unfold runUnitSyscall
  cases hs : s.status
  · exact absurd hs h
  · rfl
  · rfl
  · rfl

/-- Non-running states short-circuit `runI32Syscall` without modifying state. -/
theorem runI32Syscall_not_running (s : ChildState) (h : s.status ≠ Status.running)
    (req : Req) (forcedErr? : Option I32) (onOk : ChildState → I32 × ChildState) :
    runI32Syscall s req forcedErr? onOk = Result.ok (.Ok 0#i32, s) := by
  unfold runI32Syscall
  cases hs : s.status
  · exact absurd hs h
  · rfl
  · rfl
  · rfl

/-- Exact outcome lemma for `runUnitSyscall` on a running state. -/
theorem runUnitSyscall_running (s : ChildState) (hs : s.status = Status.running)
    (req : Req) (forcedErr? : Option I32) (onOk onErr : ChildState → ChildState) :
    ∃ r s', runUnitSyscall s req forcedErr? onOk onErr = Result.ok (r, s') ∧
      match currentFault s with
      | StepFault.seccomp rawE =>
        let e := sanitizeErrno rawE
        r = .Err e ∧ s' = { s with trace := s.trace ++ [{ req := req, out := .err e }] }
      | fault =>
        match forcedErr? with
        | some e =>
          let sb := onErr s
          r = .Err e ∧ s' = { sb with trace := sb.trace ++ [{ req := req, out := .err e }] }
        | none =>
          match fault with
          | StepFault.fail rawE =>
            let e := sanitizeErrno rawE
            let sb := onErr s
            r = .Err e ∧ s' = { sb with trace := sb.trace ++ [{ req := req, out := .err e }] }
          | _ =>
            let sb := onOk s
            r = .Ok () ∧ s' = { sb with trace := sb.trace ++ [{ req := req, out := .okVal 0 }] } := by
  unfold runUnitSyscall
  rw [hs]
  cases hf : currentFault s with
  | seccomp rawE => exact ⟨.Err (sanitizeErrno rawE), _, rfl, rfl, rfl⟩
  | normal =>
    cases forcedErr? with
    | some e => exact ⟨.Err e, _, rfl, rfl, rfl⟩
    | none => exact ⟨.Ok (), _, rfl, rfl, rfl⟩
  | partialWrite k =>
    cases forcedErr? with
    | some e => exact ⟨.Err e, _, rfl, rfl, rfl⟩
    | none => exact ⟨.Ok (), _, rfl, rfl, rfl⟩
  | dentsBatch k =>
    cases forcedErr? with
    | some e => exact ⟨.Err e, _, rfl, rfl, rfl⟩
    | none => exact ⟨.Ok (), _, rfl, rfl, rfl⟩
  | fail rawE =>
    cases forcedErr? with
    | some e => exact ⟨.Err e, _, rfl, rfl, rfl⟩
    | none => exact ⟨.Err (sanitizeErrno rawE), _, rfl, rfl, rfl⟩

/-- Exact outcome lemma for `runI32Syscall` on a running state. -/
theorem runI32Syscall_running (s : ChildState) (hs : s.status = Status.running)
    (req : Req) (forcedErr? : Option I32) (onOk : ChildState → I32 × ChildState) :
    ∃ r s', runI32Syscall s req forcedErr? onOk = Result.ok (r, s') ∧
      match currentFault s with
      | StepFault.seccomp rawE =>
        let e := sanitizeErrno rawE
        r = .Err e ∧ s' = { s with trace := s.trace ++ [{ req := req, out := .err e }] }
      | fault =>
        match forcedErr? with
        | some e =>
          r = .Err e ∧ s' = { s with trace := s.trace ++ [{ req := req, out := .err e }] }
        | none =>
          match fault with
          | StepFault.fail rawE =>
            let e := sanitizeErrno rawE
            r = .Err e ∧ s' = { s with trace := s.trace ++ [{ req := req, out := .err e }] }
          | _ =>
            let p := onOk s
            r = .Ok p.1 ∧ s' = { p.2 with trace := p.2.trace ++ [{ req := req, out := .okVal (↑p.1 : Int) }] } := by
  unfold runI32Syscall
  rw [hs]
  cases hf : currentFault s with
  | seccomp rawE => exact ⟨.Err (sanitizeErrno rawE), _, rfl, rfl, rfl⟩
  | normal =>
    cases forcedErr? with
    | some e => exact ⟨.Err e, _, rfl, rfl, rfl⟩
    | none => exact ⟨.Ok (onOk s).1, _, rfl, rfl, rfl⟩
  | partialWrite k =>
    cases forcedErr? with
    | some e => exact ⟨.Err e, _, rfl, rfl, rfl⟩
    | none => exact ⟨.Ok (onOk s).1, _, rfl, rfl, rfl⟩
  | dentsBatch k =>
    cases forcedErr? with
    | some e => exact ⟨.Err e, _, rfl, rfl, rfl⟩
    | none => exact ⟨.Ok (onOk s).1, _, rfl, rfl, rfl⟩
  | fail rawE =>
    cases forcedErr? with
    | some e => exact ⟨.Err e, _, rfl, rfl, rfl⟩
    | none => exact ⟨.Err (sanitizeErrno rawE), _, rfl, rfl, rfl⟩

/-- Exact outcome lemma for `sys.exit`. -/
theorem sys_exit_eq (s : ChildState) (code : I32) :
    sys.exit s code = Result.ok (if s.status = Status.running then
      { s with
        trace := s.trace ++ [{ req := Req.exit code, out := .okVal 0 }]
        status := Status.exited code }
      else s) := by
  unfold sys.exit LeanSwe.PostFork.Aeneas.Internal.Sys.exit
  cases hs : s.status <;> simp

/-- `sys.close` step characterization on a running state. -/
theorem sys_close_running (s : ChildState) (hs : s.status = Status.running) (fd : I32) :
    ∃ r s', sys.close s fd = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.trace.length = s.trace.length + 1 ∧
      s'.fds = (match currentFault s with
        | StepFault.seccomp _ => s.fds
        | _ => (s.closeSlot (↑fd : Int)).fds) ∧
      (((∀ rawE, currentFault s ≠ StepFault.seccomp rawE) → s.isOpen (↑fd : Int) = false → r = .Err EBADF) ∧
       (s.isOpen (↑fd : Int) = true ∧ s.oracle = [] → r = .Ok ()) ∧
       (∀ rawE, currentFault s = StepFault.seccomp rawE → r = .Err (sanitizeErrno rawE))) := by
  unfold sys.close LeanSwe.PostFork.Aeneas.Internal.Sys.close
  have hrun := runUnitSyscall_running s hs (Req.close fd)
    (if s.isOpen ↑fd then none else some EBADF)
    (fun s => s.closeSlot ↑fd) (fun s => s.closeSlot ↑fd)
  rcases hrun with ⟨r, s', hEq, hSpec⟩
  refine ⟨r, s', hEq, ?_⟩
  cases hf : currentFault s with
  | seccomp rawE =>
    simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
    refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
      by simp, rfl, ⟨fun hne _ => absurd rfl (hne rawE), fun ⟨_, hor⟩ => ?_, fun _ heq => by cases heq; rfl⟩⟩
    exact absurd (hf.symm.trans (currentFault_oracle_nil s hor)) (by intro h; cases h)
  | normal | partialWrite _ | dentsBatch _ =>
    by_cases hopen : s.isOpen (↑fd : Int) = true
    · simp only [hf, hopen, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.closeSlot s ↑fd).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp [ChildState.closeSlot], rfl,
        ⟨fun _ h => by simp [hopen] at h, fun _ => rfl, fun _ h => by cases h⟩⟩
    · have hfalse : s.isOpen (↑fd : Int) = false := Bool.eq_false_iff.mpr hopen
      simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.closeSlot s ↑fd).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp [ChildState.closeSlot], rfl,
        ⟨fun _ _ => rfl, fun ⟨ht, _⟩ => by simp [hfalse] at ht, fun _ h => by cases h⟩⟩
  | fail rawE =>
    by_cases hopen : s.isOpen (↑fd : Int) = true
    · simp only [hf, hopen, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.closeSlot s ↑fd).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp [ChildState.closeSlot], rfl,
        ⟨fun _ h => by simp [hopen] at h, fun ⟨_, hor⟩ => ?_, fun _ h => by cases h⟩⟩
      exact absurd (hf.symm.trans (currentFault_oracle_nil s hor)) (by intro h; cases h)
    · have hfalse : s.isOpen (↑fd : Int) = false := Bool.eq_false_iff.mpr hopen
      simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.closeSlot s ↑fd).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp [ChildState.closeSlot], rfl,
        ⟨fun _ _ => rfl, fun ⟨ht, _⟩ => by simp [hfalse] at ht, fun _ h => by cases h⟩⟩

/-- `sys.close` on a non-running state leaves state unchanged. -/
theorem sys_close_not_running (s : ChildState) (hs : s.status ≠ Status.running) (fd : I32) :
    sys.close s fd = Result.ok (.Ok (), s) :=
  runUnitSyscall_not_running s hs _ _ _ _

/-- `sys.dup2` step characterization on a running state. -/
theorem sys_dup2_running (s : ChildState) (hs : s.status = Status.running) (oldfd newfd : I32) :
    ∃ r s', sys.dup2 s oldfd newfd = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.trace.length = s.trace.length + 1 ∧
      (∀ err, r = .Err err → s'.fds = s.fds) ∧
      (r = .Ok () → s'.fds =
        (if (↑oldfd : Int) = ↑newfd then s
         else match s.getFd ↑oldfd with
              | some e => s.putSlot ↑newfd { desc := e.desc, cloexec := false }
              | none => s).fds) ∧
      (s.oracle = [] →
        (s.isOpen ↑oldfd = false → r = .Err EBADF) ∧
        (s.isOpen ↑oldfd = true ∧ (↑oldfd : Int) ≠ ↑newfd ∧ ((↑newfd : Int) < 0 ∨ (↑newfd : Int) ≥ s.fdLimit) →
          r = .Err EBADF) ∧
        (s.isOpen ↑oldfd = true ∧ ((↑oldfd : Int) = ↑newfd ∨ (0 ≤ (↑newfd : Int) ∧ (↑newfd : Int) < s.fdLimit)) →
          r = .Ok ())) := by
  unfold sys.dup2 LeanSwe.PostFork.Aeneas.Internal.Sys.dup2
  let forcedErr? : Option I32 :=
    if (!s.isOpen ↑oldfd) = true then some EBADF
    else if ((↑oldfd : Int) == ↑newfd) = true then none
    else if (decide ((↑newfd : Int) < 0) || decide ((↑newfd : Int) ≥ s.fdLimit)) = true then some EBADF
    else none
  let onOk : ChildState → ChildState := fun s =>
    if ((↑oldfd : Int) == (↑newfd : Int)) = true then s
    else match s.getFd ↑oldfd with
      | some e => s.putSlot ↑newfd { desc := e.desc, cloexec := false }
      | none => s
  have hrun := runUnitSyscall_running s hs (Req.dup2 oldfd newfd) forcedErr? onOk id
  rcases hrun with ⟨r, s', hEq, hSpec⟩
  refine ⟨r, s', hEq, ?_⟩
  have h_onOk_cfg : SameChildConfig (onOk s) s := by
    dsimp [onOk]; split
    · exact SameChildConfig.refl s
    · cases s.getFd ↑oldfd with
      | none => exact SameChildConfig.refl s
      | some e => exact SameChildConfig.putSlot s ↑newfd _
  have h_onOk_rest :
      (onOk s).pgid = s.pgid ∧ (onOk s).cwd = s.cwd ∧ (onOk s).sig = s.sig ∧
      (onOk s).descs = s.descs ∧ (onOk s).writeLog = s.writeLog ∧ (onOk s).trace = s.trace := by
    dsimp [onOk]; split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases s.getFd ↑oldfd <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have h_onOk_fds : (onOk s).fds =
      (if (↑oldfd : Int) = ↑newfd then s
       else match s.getFd ↑oldfd with
            | some e => s.putSlot ↑newfd { desc := e.desc, cloexec := false }
            | none => s).fds := by
    dsimp [onOk]
    by_cases h : (↑oldfd : Int) = ↑newfd
    · simp [h]
    · simp [h]
  cases hf0 : currentFault s with
  | seccomp rawE =>
    simp only [hf0] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
    refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
      by simp, fun _ _ => rfl, fun h => (nomatch h), ?_⟩
    intro hor; have hnorm := currentFault_oracle_nil s hor; rw [hf0] at hnorm; cases hnorm
  | normal | partialWrite _ | dentsBatch _ =>
    cases hfe : forcedErr? with
    | some err =>
      simp only [hf0, hfe] at hSpec
      rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), ?_⟩
      intro _
      refine ⟨?_, ?_, ?_⟩
      · intro hnot; dsimp only [forcedErr?] at hfe; simp [hnot] at hfe; exact congrArg core.result.Result.Err hfe.symm
      · intro ⟨hopen, hne, hbad⟩
        dsimp only [forcedErr?] at hfe
        have hbeq : ((↑oldfd : Int) == ↑newfd) = false := beq_false_of_ne hne
        have hbd : (decide ((↑newfd : Int) < 0) || decide ((↑newfd : Int) ≥ s.fdLimit)) = true := by
          simp; omega
        simp [hopen, hbeq, hbd] at hfe
        exact congrArg core.result.Result.Err hfe.symm
      · intro ⟨hopen, hok⟩
        dsimp only [forcedErr?] at hfe
        simp only [hopen, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfe
        rcases hok with heq | hbounds
        · simp [heq] at hfe
        · by_cases heq : ((↑oldfd : Int) == ↑newfd) = true
          · simp [heq] at hfe
          · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hfe
            have hnobad : (decide ((↑newfd : Int) < 0) || decide ((↑newfd : Int) ≥ s.fdLimit)) = false := by
              simp; omega
            simp [hnobad] at hfe
    | none =>
      simp only [hf0, hfe] at hSpec
      rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨h_onOk_cfg.with_trace _, h_onOk_rest.1, h_onOk_rest.2.1, h_onOk_rest.2.2.1,
        h_onOk_rest.2.2.2.1, h_onOk_rest.2.2.2.2.1, by simp [h_onOk_rest.2.2.2.2.2],
        fun _ h => (nomatch h), fun _ => h_onOk_fds, ?_⟩
      intro _
      refine ⟨fun hnot => by dsimp only [forcedErr?] at hfe; simp [hnot] at hfe, ?_, fun _ => rfl⟩
      intro ⟨hopen, hne, hbad⟩
      dsimp only [forcedErr?] at hfe
      have hbeq : ((↑oldfd : Int) == ↑newfd) = false := beq_false_of_ne hne
      have hbd : (decide ((↑newfd : Int) < 0) || decide ((↑newfd : Int) ≥ s.fdLimit)) = true := by
        simp; omega
      simp [hopen, hbeq, hbd] at hfe
  | fail rawE =>
    cases hfe : forcedErr? with
    | some err =>
      simp only [hf0, hfe] at hSpec
      rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), ?_⟩
      intro hor; have hnorm := currentFault_oracle_nil s hor; rw [hf0] at hnorm; cases hnorm
    | none =>
      simp only [hf0, hfe] at hSpec
      rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), ?_⟩
      intro hor; have hnorm := currentFault_oracle_nil s hor; rw [hf0] at hnorm; cases hnorm

/-- `sys.fcntl_getfd` step characterization on a running state. -/
theorem sys_fcntl_getfd_running (s : ChildState) (hs : s.status = Status.running) (fd : I32) :
    ∃ r s', sys.fcntl_getfd s fd = Result.ok (r, s') ∧
      s' = { s with trace := s'.trace } ∧
      s'.oracle = s.oracle ∧
      s'.trace.length = s.trace.length + 1 ∧
      (match currentFault s with
       | StepFault.seccomp rawE => r = .Err (sanitizeErrno rawE)
       | fault =>
         match s.getFd ↑fd with
         | none => r = .Err EBADF
         | some e =>
           match fault with
           | StepFault.fail rawE => r = .Err (sanitizeErrno rawE)
           | _ => r = .Ok (fdFlagsWord e)) := by
  unfold sys.fcntl_getfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_getfd
  cases hf : currentFault s with
  | seccomp rawE =>
    cases hget : s.getFd (↑fd : Int) with
    | none =>
      have hrun := runI32Syscall_running s hs (Req.fcntlGetfd fd) (some EBADF) (fun s => (0#i32, s))
      rcases hrun with ⟨r, s', hEq, hSpec⟩
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨.Err (sanitizeErrno rawE), _, hEq, rfl, rfl, by simp, rfl⟩
    | some e =>
      have hrun := runI32Syscall_running s hs (Req.fcntlGetfd fd) none (fun s => (fdFlagsWord e, s))
      rcases hrun with ⟨r, s', hEq, hSpec⟩
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨.Err (sanitizeErrno rawE), _, hEq, rfl, rfl, by simp, rfl⟩
  | normal | partialWrite _ | dentsBatch _ =>
    cases hget : s.getFd (↑fd : Int) with
    | none =>
      have hrun := runI32Syscall_running s hs (Req.fcntlGetfd fd) (some EBADF) (fun s => (0#i32, s))
      rcases hrun with ⟨r, s', hEq, hSpec⟩
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨.Err EBADF, _, hEq, rfl, rfl, by simp, rfl⟩
    | some e =>
      have hrun := runI32Syscall_running s hs (Req.fcntlGetfd fd) none (fun s => (fdFlagsWord e, s))
      rcases hrun with ⟨r, s', hEq, hSpec⟩
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨.Ok (fdFlagsWord e), _, hEq, rfl, rfl, by simp, rfl⟩
  | fail rawE =>
    cases hget : s.getFd (↑fd : Int) with
    | none =>
      have hrun := runI32Syscall_running s hs (Req.fcntlGetfd fd) (some EBADF) (fun s => (0#i32, s))
      rcases hrun with ⟨r, s', hEq, hSpec⟩
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨.Err EBADF, _, hEq, rfl, rfl, by simp, rfl⟩
    | some e =>
      have hrun := runI32Syscall_running s hs (Req.fcntlGetfd fd) none (fun s => (fdFlagsWord e, s))
      rcases hrun with ⟨r, s', hEq, hSpec⟩
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨.Err (sanitizeErrno rawE), _, hEq, rfl, rfl, by simp, rfl⟩

/-- `sys.fcntl_setfd` step characterization on a running state. -/
theorem sys_fcntl_setfd_running (s : ChildState) (hs : s.status = Status.running) (fd flags : I32) :
    ∃ r s', sys.fcntl_setfd s fd flags = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.trace.length = s.trace.length + 1 ∧
      (∀ err, r = .Err err → s'.fds = s.fds) ∧
      (r = .Ok () → s'.fds =
        (match s.getFd ↑fd with
         | some e => s.putSlot ↑fd (updateFdFlags s.kernelMasksSetfd flags e)
         | none => s).fds) ∧
      (match currentFault s with
       | StepFault.seccomp rawE => r = .Err (sanitizeErrno rawE)
       | fault =>
         match s.getFd ↑fd with
         | none => r = .Err EBADF
         | some _ =>
           match fault with
           | StepFault.fail rawE => r = .Err (sanitizeErrno rawE)
           | _ => r = .Ok ()) := by
  unfold sys.fcntl_setfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_setfd
  have hopen_eq : s.isOpen (↑fd : Int) = (s.getFd ↑fd).isSome := rfl
  have hrun := runUnitSyscall_running s hs (Req.fcntlSetfd fd flags)
    (if s.isOpen ↑fd then none else some EBADF)
    (fun s => match s.getFd ↑fd with
      | some e => s.putSlot ↑fd (updateFdFlags s.kernelMasksSetfd flags e)
      | none => s)
    id
  rcases hrun with ⟨r, s', hEq, hSpec⟩
  cases hf : currentFault s with
  | seccomp rawE =>
    simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
    exact ⟨.Err (sanitizeErrno rawE), _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
      by simp, fun _ _ => rfl, fun h => (nomatch h), rfl⟩
  | normal | partialWrite _ | dentsBatch _ =>
    cases hget : s.getFd (↑fd : Int) with
    | none =>
      simp only [hf, hopen_eq, hget] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨.Err EBADF, _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), rfl⟩
    | some e =>
      simp only [hf, hopen_eq, hget] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨.Ok (), _, hEq,
        (SameChildConfig.putSlot s ↑fd (updateFdFlags s.kernelMasksSetfd flags e)).with_trace _,
        rfl, rfl, rfl, rfl, rfl,
        by simp [ChildState.putSlot], fun _ h => (nomatch h), fun _ => by simp, rfl⟩
  | fail rawE =>
    cases hget : s.getFd (↑fd : Int) with
    | none =>
      simp only [hf, hopen_eq, hget] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨.Err EBADF, _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), rfl⟩
    | some e =>
      simp only [hf, hopen_eq, hget] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨.Err (sanitizeErrno rawE), _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), rfl⟩

/-- `sys.fcntl_dupfd_cloexec` step characterization on a running state. -/
theorem sys_fcntl_dupfd_cloexec_running (s : ChildState) (hs : s.status = Status.running) (fd minFd : I32) :
    ∃ r s', sys.fcntl_dupfd_cloexec s fd minFd = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.pgid = s.pgid ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.trace.length = s.trace.length + 1 ∧
      (∀ err, r = .Err err → s'.fds = s.fds) ∧
      (∀ dst, r = .Ok dst →
        ∃ e dstInt, s.getFd ↑fd = some e ∧
          findLowestFreeFd s ↑minFd = some dstInt ∧
          (↑dst : Int) = dstInt ∧
          (↑minFd : Int) ≤ dstInt ∧ dstInt < min s.fdLimit 2147483648 ∧ s.getFd dstInt = none ∧
          s'.fds = (s.putSlot dstInt { desc := e.desc, cloexec := true }).fds) ∧
      (s.oracle = [] →
        match s.getFd ↑fd, findLowestFreeFd s ↑minFd with
        | some _, some dstInt =>
          if ((decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = true) then r = .Err EINVAL
          else ∃ dst, r = .Ok dst ∧ (↑dst : Int) = dstInt
        | none, _ => r = .Err EBADF
        | some _, none =>
          if ((decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = true) then r = .Err EINVAL
          else r = .Err EMFILE) := by
  unfold sys.fcntl_dupfd_cloexec LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_dupfd_cloexec
  cases hf : currentFault s with
  | seccomp rawE =>
    cases hget : s.getFd (↑fd : Int) with
    | none =>
      have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) (some EBADF) (fun s => (0#i32, s))
      rcases hrun with ⟨r, s', hEq, hSpec⟩
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨.Err (sanitizeErrno rawE), _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
      intro hor; have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
    | some e =>
      by_cases hbad : (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = true
      · simp only [hbad, ↓reduceIte]
        have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) (some EINVAL) (fun s => (0#i32, s))
        rcases hrun with ⟨r, s', hEq, hSpec⟩
        simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        refine ⟨.Err (sanitizeErrno rawE), _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
        intro hor; have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
      · have hbadf : (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = false :=
          Bool.eq_false_iff.mpr hbad
        simp only [hbadf, Bool.false_eq_true, ↓reduceIte]
        cases hfind : findLowestFreeFd s (↑minFd : Int) with
        | none =>
          have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) (some EMFILE) (fun s => (0#i32, s))
          rcases hrun with ⟨r, s', hEq, hSpec⟩
          simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
          refine ⟨.Err (sanitizeErrno rawE), _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
            by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
          intro hor; have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
        | some dstInt =>
          have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) none
            (fun s => (mkI32 dstInt, s.putSlot dstInt { desc := e.desc, cloexec := true }))
          rcases hrun with ⟨r, s', hEq, hSpec⟩
          simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
          refine ⟨.Err (sanitizeErrno rawE), _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
            by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
          intro hor; have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
  | normal | partialWrite _ | dentsBatch _ =>
    cases hget : s.getFd (↑fd : Int) with
    | none =>
      have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) (some EBADF) (fun s => (0#i32, s))
      rcases hrun with ⟨r, s', hEq, hSpec⟩
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨.Err EBADF, _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
      intro _; cases findLowestFreeFd s ↑minFd <;> rfl
    | some e =>
      by_cases hbad : (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = true
      · simp only [hbad, ↓reduceIte]
        have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) (some EINVAL) (fun s => (0#i32, s))
        rcases hrun with ⟨r, s', hEq, hSpec⟩
        simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        refine ⟨.Err EINVAL, _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
        intro _; cases findLowestFreeFd s ↑minFd <;> simp
      · have hbadf : (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = false :=
          Bool.eq_false_iff.mpr hbad
        simp only [hbadf, Bool.false_eq_true, ↓reduceIte]
        cases hfind : findLowestFreeFd s (↑minFd : Int) with
        | none =>
          have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) (some EMFILE) (fun s => (0#i32, s))
          rcases hrun with ⟨r, s', hEq, hSpec⟩
          simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
          refine ⟨.Err EMFILE, _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
            by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
          intro _; simp
        | some dstInt =>
          have hspec := findLowestFreeFd_spec s ↑minFd dstInt hfind
          have hmk : (mkI32 dstInt : Int) = dstInt := mkI32_val_nonneg hspec.2.1 hspec.2.2.2.1
          have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) none
            (fun s => (mkI32 dstInt, s.putSlot dstInt { desc := e.desc, cloexec := true }))
          rcases hrun with ⟨r, s', hEq, hSpec⟩
          simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
          refine ⟨.Ok (mkI32 dstInt), _, hEq,
            (SameChildConfig.putSlot s dstInt { desc := e.desc, cloexec := true }).with_trace _,
            rfl, rfl, rfl, rfl, rfl,
            by simp [ChildState.putSlot], fun _ h => (nomatch h), ?_, ?_⟩
          · intro dst hd; injection hd with hd'; subst hd'
            exact ⟨e, dstInt, rfl, rfl, hmk, hspec.1, hspec.2.2.1, hspec.2.2.2.2.2, rfl⟩
          · intro _; exact ⟨mkI32 dstInt, rfl, hmk⟩
  | fail rawE =>
    cases hget : s.getFd (↑fd : Int) with
    | none =>
      have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) (some EBADF) (fun s => (0#i32, s))
      rcases hrun with ⟨r, s', hEq, hSpec⟩
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨.Err EBADF, _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
      intro hor; exact absurd (hf.symm.trans (currentFault_oracle_nil s hor)) (by intro h; cases h)
    | some e =>
      by_cases hbad : (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = true
      · simp only [hbad, ↓reduceIte]
        have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) (some EINVAL) (fun s => (0#i32, s))
        rcases hrun with ⟨r, s', hEq, hSpec⟩
        simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        refine ⟨.Err EINVAL, _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
        intro hor; exact absurd (hf.symm.trans (currentFault_oracle_nil s hor)) (by intro h; cases h)
      · have hbadf : (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = false :=
          Bool.eq_false_iff.mpr hbad
        simp only [hbadf, Bool.false_eq_true, ↓reduceIte]
        cases hfind : findLowestFreeFd s (↑minFd : Int) with
        | none =>
          have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) (some EMFILE) (fun s => (0#i32, s))
          rcases hrun with ⟨r, s', hEq, hSpec⟩
          simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
          refine ⟨.Err EMFILE, _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
            by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
          intro hor; exact absurd (hf.symm.trans (currentFault_oracle_nil s hor)) (by intro h; cases h)
        | some dstInt =>
          have hrun := runI32Syscall_running s hs (Req.fcntlDupfdCloexec fd minFd) none
            (fun s => (mkI32 dstInt, s.putSlot dstInt { desc := e.desc, cloexec := true }))
          rcases hrun with ⟨r, s', hEq, hSpec⟩
          simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
          refine ⟨.Err (sanitizeErrno rawE), _, hEq, (SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
            by simp, fun _ _ => rfl, fun _ h => (nomatch h), ?_⟩
          intro hor; exact absurd (hf.symm.trans (currentFault_oracle_nil s hor)) (by intro h; cases h)

/-- `sys.chdir` step characterization on a running state. -/
theorem sys_chdir_running (s : ChildState) (hs : s.status = Status.running) (path : sys.CStr) :
    ∃ r s', sys.chdir s path = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.sig = s.sig ∧
      s'.writeLog = s.writeLog ∧ s'.pgid = s.pgid ∧
      s'.trace.length = s.trace.length + 1 ∧
      (∀ err, r = .Err err → s'.cwd = s.cwd) ∧
      (r = .Ok () → s'.cwd = resolveChdirTarget s path) ∧
      (s.oracle = [] → (path.isEmpty = true → r = .Err ENOENT) ∧ (path.isEmpty = false → r = .Ok ())) := by
  unfold sys.chdir LeanSwe.PostFork.Aeneas.Internal.Sys.chdir
  have hrun := runUnitSyscall_running s hs (Req.chdir path)
    (if path.isEmpty then some ENOENT else none)
    (fun s => { s with cwd := resolveChdirTarget s path }) id
  rcases hrun with ⟨r, s', hEq, hSpec⟩
  refine ⟨r, s', hEq, ?_⟩
  cases hf : currentFault s with
  | seccomp rawE =>
    simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
    refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
      by simp, fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
    have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
  | normal | partialWrite _ | dentsBatch _ =>
    by_cases hemp : path.isEmpty = true
    · simp only [hf, hemp, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), fun _ => ⟨fun _ => rfl, fun h => by simp [hemp] at h⟩⟩
    · have hfalse : path.isEmpty = false := Bool.eq_false_iff.mpr hemp
      simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨(SameChildConfig.with_cwd s (resolveChdirTarget s path)).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ h => (nomatch h), fun _ => rfl, fun _ => ⟨fun h => by simp [hfalse] at h, fun _ => rfl⟩⟩
  | fail rawE =>
    by_cases hemp : path.isEmpty = true
    · simp only [hf, hemp, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
      have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
    · have hfalse : path.isEmpty = false := Bool.eq_false_iff.mpr hemp
      simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
      have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm

/-- `sys.setpgid_self` step characterization on a running state. -/
theorem sys_setpgid_self_running (s : ChildState) (hs : s.status = Status.running) :
    ∃ r s', sys.setpgid_self s = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.sig = s.sig ∧
      s'.writeLog = s.writeLog ∧ s'.cwd = s.cwd ∧
      s'.trace.length = s.trace.length + 1 ∧
      (∀ err, r = .Err err → s'.pgid = s.pgid) ∧
      (r = .Ok () → s'.pgid = s.pid) ∧
      (s.oracle = [] →
        ((s.pid == s.sid && decide (s.pid > 0)) = true → r = .Err EPERM) ∧
        ((s.pid == s.sid && decide (s.pid > 0)) = false → r = .Ok ())) := by
  unfold sys.setpgid_self LeanSwe.PostFork.Aeneas.Internal.Sys.setpgid_self
  have hrun := runUnitSyscall_running s hs Req.setpgidSelf
    (if (s.pid == s.sid && decide (s.pid > 0)) then some EPERM else none)
    (fun s => { s with pgid := s.pid }) id
  rcases hrun with ⟨r, s', hEq, hSpec⟩
  refine ⟨r, s', hEq, ?_⟩
  cases hf : currentFault s with
  | seccomp rawE =>
    simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
    refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
      by simp, fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
    have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
  | normal | partialWrite _ | dentsBatch _ =>
    by_cases hlead : (s.pid == s.sid && decide (s.pid > 0)) = true
    · simp only [hf, hlead, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), fun _ => ⟨fun _ => rfl, fun h => by simp [hlead] at h⟩⟩
    · have hfalse : (s.pid == s.sid && decide (s.pid > 0)) = false := Bool.eq_false_iff.mpr hlead
      simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨(SameChildConfig.with_pgid s s.pid).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ h => (nomatch h), fun _ => rfl, fun _ => ⟨fun h => by simp [hfalse] at h, fun _ => rfl⟩⟩
  | fail rawE =>
    by_cases hlead : (s.pid == s.sid && decide (s.pid > 0)) = true
    · simp only [hf, hlead, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
      have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
    · have hfalse : (s.pid == s.sid && decide (s.pid > 0)) = false := Bool.eq_false_iff.mpr hlead
      simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
      have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm

/-- `sys.sig_dfl` step characterization on a running state. -/
theorem sys_sig_dfl_running (s : ChildState) (hs : s.status = Status.running) (sig : I32) :
    ∃ r s', sys.sig_dfl s sig = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.cwd = s.cwd ∧ s'.pgid = s.pgid ∧
      s'.trace.length = s.trace.length + (if isUserspaceInvalidSigactionSig sig then 0 else 1) ∧
      (∀ err, r = .Err err → s'.sig = s.sig) ∧
      (r = .Ok () → s'.sig = (s.putSig ↑sig Disp.default).sig) ∧
      (s.oracle = [] →
        (isInvalidSigactionSig sig = true → r = .Err EINVAL) ∧
        (isInvalidSigactionSig sig = false → r = .Ok ())) := by
  unfold sys.sig_dfl LeanSwe.PostFork.Aeneas.Internal.Sys.sig_dfl
  by_cases hus : isUserspaceInvalidSigactionSig sig = true
  · refine ⟨.Err EINVAL, s, ?_, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, by simp [hus],
      fun _ _ => rfl, fun h => (nomatch h), fun _ => ⟨fun _ => rfl, fun h => ?_⟩⟩
    · simp [hs, hus]
    · simp [isInvalidSigactionSig, hus] at h
  · have husFalse : isUserspaceInvalidSigactionSig sig = false := Bool.eq_false_iff.mpr hus
    have hrun := runUnitSyscall_running s hs (Req.sigDfl sig)
      (if isKernelInvalidSigactionSig sig then some EINVAL else none)
      (fun s => s.putSig ↑sig Disp.default) id
    rcases hrun with ⟨r, s', hEq, hSpec⟩
    refine ⟨r, s', ?_, ?_⟩
    · simp [hs, husFalse, hEq]
    cases hf : currentFault s with
    | seccomp rawE =>
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp [husFalse], fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
      have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
    | normal | partialWrite _ | dentsBatch _ =>
      by_cases hinv : isKernelInvalidSigactionSig sig = true
      · simp only [hf, hinv, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        exact ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp [husFalse], fun _ _ => rfl, fun h => (nomatch h),
          fun _ => ⟨fun _ => rfl, fun h => by simp [isInvalidSigactionSig, hinv] at h⟩⟩
      · have hfalse : isKernelInvalidSigactionSig sig = false := Bool.eq_false_iff.mpr hinv
        simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        exact ⟨(SameChildConfig.putSig s ↑sig Disp.default).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp [ChildState.putSig, husFalse], fun _ h => (nomatch h), fun _ => rfl,
          fun _ => ⟨fun h => by simp [isInvalidSigactionSig, husFalse, hfalse] at h, fun _ => rfl⟩⟩
    | fail rawE =>
      by_cases hinv : isKernelInvalidSigactionSig sig = true
      · simp only [hf, hinv, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp [husFalse], fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
        have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
      · have hfalse : isKernelInvalidSigactionSig sig = false := Bool.eq_false_iff.mpr hinv
        simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp [husFalse], fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
        have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm

/-- `sys.sig_ign` step characterization on a running state. -/
theorem sys_sig_ign_running (s : ChildState) (hs : s.status = Status.running) (sig : I32) :
    ∃ r s', sys.sig_ign s sig = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.cwd = s.cwd ∧ s'.pgid = s.pgid ∧
      s'.trace.length = s.trace.length + (if isUserspaceInvalidSigactionSig sig then 0 else 1) ∧
      (∀ err, r = .Err err → s'.sig = s.sig) ∧
      (r = .Ok () → s'.sig = (s.putSig ↑sig Disp.ignore).sig) ∧
      (s.oracle = [] →
        (isInvalidSigactionSig sig = true → r = .Err EINVAL) ∧
        (isInvalidSigactionSig sig = false → r = .Ok ())) := by
  unfold sys.sig_ign LeanSwe.PostFork.Aeneas.Internal.Sys.sig_ign
  by_cases hus : isUserspaceInvalidSigactionSig sig = true
  · refine ⟨.Err EINVAL, s, ?_, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, by simp [hus],
      fun _ _ => rfl, fun h => (nomatch h), fun _ => ⟨fun _ => rfl, fun h => ?_⟩⟩
    · simp [hs, hus]
    · simp [isInvalidSigactionSig, hus] at h
  · have husFalse : isUserspaceInvalidSigactionSig sig = false := Bool.eq_false_iff.mpr hus
    have hrun := runUnitSyscall_running s hs (Req.sigIgn sig)
      (if isKernelInvalidSigactionSig sig then some EINVAL else none)
      (fun s => s.putSig ↑sig Disp.ignore) id
    rcases hrun with ⟨r, s', hEq, hSpec⟩
    refine ⟨r, s', ?_, ?_⟩
    · simp [hs, husFalse, hEq]
    cases hf : currentFault s with
    | seccomp rawE =>
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
        by simp [husFalse], fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
      have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
    | normal | partialWrite _ | dentsBatch _ =>
      by_cases hinv : isKernelInvalidSigactionSig sig = true
      · simp only [hf, hinv, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        exact ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp [husFalse], fun _ _ => rfl, fun h => (nomatch h),
          fun _ => ⟨fun _ => rfl, fun h => by simp [isInvalidSigactionSig, hinv] at h⟩⟩
      · have hfalse : isKernelInvalidSigactionSig sig = false := Bool.eq_false_iff.mpr hinv
        simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        exact ⟨(SameChildConfig.putSig s ↑sig Disp.ignore).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp [ChildState.putSig, husFalse], fun _ h => (nomatch h), fun _ => rfl,
          fun _ => ⟨fun h => by simp [isInvalidSigactionSig, husFalse, hfalse] at h, fun _ => rfl⟩⟩
    | fail rawE =>
      by_cases hinv : isKernelInvalidSigactionSig sig = true
      · simp only [hf, hinv, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp [husFalse], fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
        have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
      · have hfalse : isKernelInvalidSigactionSig sig = false := Bool.eq_false_iff.mpr hinv
        simp only [hf, hfalse, Bool.false_eq_true, ↓reduceIte] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
        refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl,
          by simp [husFalse], fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
        have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm

/-- `sys.sig_unblock` step characterization on a running state. -/
theorem sys_sig_unblock_running (s : ChildState) (hs : s.status = Status.running) (sig : I32) :
    ∃ r s', sys.sig_unblock s sig = Result.ok (r, s') ∧
      SameChildConfig s' s ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.writeLog = s.writeLog ∧
      s'.cwd = s.cwd ∧ s'.pgid = s.pgid ∧ s'.sig = s.sig ∧
      s'.trace.length = s.trace.length + (if sig.val < 1 || sig.val > 64 then 0 else 1) ∧
      (∀ err, r = .Err err → s'.blockedSigs = s.blockedSigs) ∧
      (r = .Ok () → s'.blockedSigs = s.blockedSigs.filter (· != sig.val)) ∧
      (s.oracle = [] →
        ((sig.val < 1 ∨ sig.val > 64) → r = .Err EINVAL) ∧
        (1 ≤ sig.val → sig.val ≤ 64 → r = .Ok ())) := by
  unfold sys.sig_unblock LeanSwe.PostFork.Aeneas.Internal.Sys.sig_unblock
  by_cases hInv : (sig.val < 1 || sig.val > 64) = true
  · have hDisj : sig.val < 1 ∨ sig.val > 64 := by simpa [Bool.or_eq_true] using hInv
    refine ⟨.Err EINVAL, s, ?_, SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, rfl,
      by simp [hInv], fun _ _ => rfl, fun h => (nomatch h), fun _ => ⟨fun _ => rfl, fun h1 h64 => by omega⟩⟩
    simp [hs, hInv]
  · have hInvFalse : (sig.val < 1 || sig.val > 64) = false := Bool.eq_false_iff.mpr hInv
    have hGe1 : 1 ≤ sig.val := by
      simp only [Bool.or_eq_false_eq_eq_false_and_eq_false, decide_eq_false_iff_not] at hInvFalse
      omega
    have hLe64 : sig.val ≤ 64 := by
      simp only [Bool.or_eq_false_eq_eq_false_and_eq_false, decide_eq_false_iff_not] at hInvFalse
      omega
    have hrun := runUnitSyscall_running s hs (Req.sigUnblock sig) none
      (fun s => { s with blockedSigs := s.blockedSigs.filter (· != sig.val) }) id
    rcases hrun with ⟨r, s', hEq, hSpec⟩
    refine ⟨r, s', ?_, ?_⟩
    · simp [hs, hInvFalse, hEq]
    cases hf : currentFault s with
    | seccomp rawE =>
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl, rfl,
        by simp [hInvFalse], fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
      have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm
    | normal | partialWrite _ | dentsBatch _ =>
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      exact ⟨{ SameChildConfig.refl s with
          oracle := rfl, status := rfl, fdLimit := rfl, kernelMasksSetfd := rfl,
          closeRangeSupported := rfl, closeRangeErrno := rfl, procSelfFdAvailable := rfl,
          procOpenErrno := rfl, pid := rfl, sid := rfl, chdirResolved := rfl },
        rfl, rfl, rfl, rfl, rfl, rfl, by simp [hInvFalse],
        fun _ h => (nomatch h), fun _ => rfl,
        fun _ => ⟨fun h => by omega, fun _ _ => rfl⟩⟩
    | fail rawE =>
      simp only [hf] at hSpec; rcases hSpec with ⟨rfl, rfl⟩
      refine ⟨(SameChildConfig.refl s).with_trace _, rfl, rfl, rfl, rfl, rfl, rfl,
        by simp [hInvFalse], fun _ _ => rfl, fun h => (nomatch h), fun hor => ?_⟩
      have hnorm := currentFault_oracle_nil s hor; rw [hf] at hnorm; cases hnorm

/-- `sys.execve` step characterization on a running state. -/
theorem sys_execve_running (s : ChildState) (hs : s.status = Status.running)
    (path : sys.CStr) (argv envp : sys.CStrArray) :
    ∃ err s', sys.execve s path argv envp = Result.ok (err, s') ∧
      s'.oracle = s.oracle ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.cwd = s.cwd ∧ s'.sig = s.sig ∧
      s'.pgid = s.pgid ∧ s'.writeLog = s.writeLog ∧
      s'.trace.length = s.trace.length + 1 ∧
      (match currentFault s with
       | StepFault.seccomp rawE => err = sanitizeErrno rawE ∧ s'.status = Status.running
       | fault =>
         if path.isEmpty then
           err = ENOENT ∧ s'.status = Status.running
         else
           match fault with
           | StepFault.fail rawE => err = sanitizeErrno rawE ∧ s'.status = Status.running
           | _ => err = 0#i32 ∧ s'.status = Status.execd (imageOf s path argv envp)) := by
  unfold sys.execve LeanSwe.PostFork.Aeneas.Internal.Sys.execve
  rw [hs]
  cases hf : currentFault s with
  | seccomp rawE =>
    exact ⟨sanitizeErrno rawE, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, rfl, by simp⟩
  | fail rawE =>
    by_cases hemp : path.isEmpty = true
    · simp only [hemp, ↓reduceIte]
      exact ⟨ENOENT, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, rfl, by simp⟩
    · have hfalse : path.isEmpty = false := Bool.eq_false_iff.mpr hemp
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      exact ⟨sanitizeErrno rawE, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, rfl, by simp⟩
  | normal | partialWrite _ | dentsBatch _ =>
    by_cases hemp : path.isEmpty = true
    · simp only [hemp, ↓reduceIte]
      exact ⟨ENOENT, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, rfl, by simp⟩
    · have hfalse : path.isEmpty = false := Bool.eq_false_iff.mpr hemp
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      exact ⟨0#i32, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, rfl, rfl⟩

/-- `sys.execve` on a non-running state leaves state unchanged and returns `0#i32`. -/
theorem sys_execve_not_running (s : ChildState) (hs : s.status ≠ Status.running)
    (path : sys.CStr) (argv envp : sys.CStrArray) :
    sys.execve s path argv envp = Result.ok (0#i32, s) := by
  unfold sys.execve LeanSwe.PostFork.Aeneas.Internal.Sys.execve
  cases h : s.status
  · exact absurd h hs
  · rfl
  · rfl
  · rfl

/-- Extract the postcondition from `WP.dspec` when the monadic action evaluates to `Result.ok`. -/
theorem dspec_of_ok {α : Type} {x : Result α} {p : α → Prop} (h : WP.dspec x p)
    {v : α} (hx : x = Result.ok v) : p v := by
  rw [hx, WP.dspec_ok] at h
  exact h

/-- Strengthen an `OkPost` specification with a partial correctness `WP.dspec` invariant. -/
theorem okPost_dspec {α : Type} {x : Result α} {P Q : α → Prop}
    (h1 : OkPost x P) (h2 : WP.dspec x Q) : OkPost x (fun v => P v ∧ Q v) := by
  rcases h1 with ⟨v, hx, hv⟩
  exact ⟨v, hx, hv, dspec_of_ok h2 hx⟩

/-- Partial-correctness induction for `Aeneas.Std.loop` via `loop.fixpoint_induct`. -/
theorem loop_dspec {α β : Type} (body : α → Result (ControlFlow α β))
    (inv : α → Prop) (post : β → Prop)
    (hStep : ∀ a, inv a → WP.dspec (body a) (fun r => match r with | .cont a' => inv a' | .done b => post b))
    (a : α) (ha : inv a) :
    WP.dspec (loop body a) post := by
  have hMot : ∀ a, inv a → WP.dspec (loop body a) post := by
    apply loop.fixpoint_induct body (fun f => ∀ a, inv a → WP.dspec (f a) post)
    · exact Lean.Order.admissible_pi _ fun a => Lean.Order.admissible_pi _ fun _ =>
        WP.dspec_func_admissible a post
    · intro f ih a ha
      dsimp only
      refine WP.dspec_bind (hStep a ha) fun r hr => ?_
      cases r with
      | cont a' => exact ih a' hr
      | done b => simpa [WP.dspec_ok] using hr
  exact hMot a ha

private theorem runUnitSyscall_dspec_blockedSigs (s : ChildState) (req : Req)
    (forcedErr? : Option I32) (onOk onErr : ChildState → ChildState)
    (hOk : (onOk s).blockedSigs = s.blockedSigs)
    (hErr : (onErr s).blockedSigs = s.blockedSigs) :
    WP.dspec (runUnitSyscall s req forcedErr? onOk onErr) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold runUnitSyscall
  cases s.status <;> simp only [WP.dspec_ok]
  cases currentFault s <;>
    cases forcedErr? <;>
    simp only [WP.dspec_ok] <;>
    first | exact hOk | exact hErr

private theorem runI32Syscall_dspec_blockedSigs (s : ChildState) (req : Req)
    (forcedErr? : Option I32) (onOk : ChildState → I32 × ChildState)
    (hOk : (onOk s).2.blockedSigs = s.blockedSigs) :
    WP.dspec (runI32Syscall s req forcedErr? onOk) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold runI32Syscall
  cases s.status <;> simp only [WP.dspec_ok]
  cases currentFault s <;>
    cases forcedErr? <;>
    simp only [WP.dspec_ok] <;>
    exact hOk

/-- `sys.setpgid_self` preserves `blockedSigs`. -/
theorem sys_setpgid_self_dspec_blockedSigs (s : ChildState) :
    WP.dspec (sys.setpgid_self s) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.setpgid_self LeanSwe.PostFork.Aeneas.Internal.Sys.setpgid_self
  exact runUnitSyscall_dspec_blockedSigs s _ _ _ _ rfl rfl

/-- `sys.sig_dfl` preserves `blockedSigs`. -/
theorem sys_sig_dfl_dspec_blockedSigs (s : ChildState) (sig : I32) :
    WP.dspec (sys.sig_dfl s sig) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.sig_dfl LeanSwe.PostFork.Aeneas.Internal.Sys.sig_dfl
  by_cases h : (s.status == Status.running && isUserspaceInvalidSigactionSig sig) = true
  · simp only [h, ↓reduceIte, WP.dspec_ok]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact runUnitSyscall_dspec_blockedSigs s _ _ _ _ rfl rfl

/-- `sys.chdir` preserves `blockedSigs`. -/
theorem sys_chdir_dspec_blockedSigs (s : ChildState) (path : sys.CStr) :
    WP.dspec (sys.chdir s path) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.chdir LeanSwe.PostFork.Aeneas.Internal.Sys.chdir
  exact runUnitSyscall_dspec_blockedSigs s _ _ _ _ rfl rfl

/-- `sys.close` preserves `blockedSigs`. -/
theorem sys_close_dspec_blockedSigs (s : ChildState) (fd : I32) :
    WP.dspec (sys.close s fd) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.close LeanSwe.PostFork.Aeneas.Internal.Sys.close
  exact runUnitSyscall_dspec_blockedSigs s _ _ _ _ rfl rfl

/-- `sys.dup2` preserves `blockedSigs`. -/
theorem sys_dup2_dspec_blockedSigs (s : ChildState) (oldfd newfd : I32) :
    WP.dspec (sys.dup2 s oldfd newfd) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.dup2 LeanSwe.PostFork.Aeneas.Internal.Sys.dup2
  refine runUnitSyscall_dspec_blockedSigs s _ _ _ _ ?_ rfl
  split
  · rfl
  · cases s.getFd oldfd.val <;> rfl

/-- `sys.fcntl_getfd` preserves `blockedSigs`. -/
theorem sys_fcntl_getfd_dspec_blockedSigs (s : ChildState) (fd : I32) :
    WP.dspec (sys.fcntl_getfd s fd) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.fcntl_getfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_getfd
  cases s.getFd fd.val with
  | none => exact runI32Syscall_dspec_blockedSigs s _ _ _ rfl
  | some _ => exact runI32Syscall_dspec_blockedSigs s _ _ _ rfl

/-- `sys.fcntl_setfd` preserves `blockedSigs`. -/
theorem sys_fcntl_setfd_dspec_blockedSigs (s : ChildState) (fd flags : I32) :
    WP.dspec (sys.fcntl_setfd s fd flags) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.fcntl_setfd LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_setfd
  refine runUnitSyscall_dspec_blockedSigs s _ _ _ _ ?_ rfl
  cases s.getFd fd.val <;> rfl

/-- `sys.fcntl_dupfd_cloexec` preserves `blockedSigs`. -/
theorem sys_fcntl_dupfd_cloexec_dspec_blockedSigs (s : ChildState) (fd minFd : I32) :
    WP.dspec (sys.fcntl_dupfd_cloexec s fd minFd) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.fcntl_dupfd_cloexec LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_dupfd_cloexec
  cases s.getFd fd.val with
  | none => exact runI32Syscall_dspec_blockedSigs s _ _ _ rfl
  | some _ =>
    by_cases h : (minFd.val < 0 || minFd.val ≥ s.fdLimit) = true
    · simp only [h, ↓reduceIte]
      exact runI32Syscall_dspec_blockedSigs s _ _ _ rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      cases findLowestFreeFd s minFd.val with
      | none => exact runI32Syscall_dspec_blockedSigs s _ _ _ rfl
      | some _ => exact runI32Syscall_dspec_blockedSigs s _ _ _ rfl

/-- `sys.close_range` preserves `blockedSigs`. -/
theorem sys_close_range_dspec_blockedSigs (s : ChildState) (first last flags : U32) :
    WP.dspec (sys.close_range s first last flags) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.close_range LeanSwe.PostFork.Aeneas.Internal.Sys.close_range
  refine runUnitSyscall_dspec_blockedSigs s _ _ _ _ ?_ rfl
  split <;> rfl

/-- `sys.open_proc_self_fd` preserves `blockedSigs`. -/
theorem sys_open_proc_self_fd_dspec_blockedSigs (s : ChildState) :
    WP.dspec (sys.open_proc_self_fd s) fun p => p.2.blockedSigs = s.blockedSigs := by
  unfold sys.open_proc_self_fd LeanSwe.PostFork.Aeneas.Internal.Sys.open_proc_self_fd
  cases findLowestFreeFd s 0 with
  | none => exact runI32Syscall_dspec_blockedSigs s _ _ _ rfl
  | some _ =>
    by_cases h : (!s.procSelfFdAvailable) = true
    · simp only [h, ↓reduceIte]
      exact runI32Syscall_dspec_blockedSigs s _ _ _ rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact runI32Syscall_dspec_blockedSigs s _ _ _ rfl

/-- `sys.getdents64` preserves `blockedSigs`. -/
theorem sys_getdents64_dspec_blockedSigs (s : ChildState) (dirfd : I32) (buf : Array U8 256#usize) :
    WP.dspec (sys.getdents64 s dirfd buf) fun p => p.2.1.blockedSigs = s.blockedSigs := by
  unfold sys.getdents64 LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64
  cases s.status <;> simp only [WP.dspec_ok]
  cases currentFault s <;> cases s.getFd dirfd.val <;> simp only [WP.dspec_ok]
  all_goals
    rename_i e
    cases s.getDesc e.desc <;> simp only [WP.dspec_ok]
  all_goals
    split <;> rfl

/-- `sys.read1` preserves `blockedSigs`. -/
theorem sys_read1_dspec_blockedSigs (s : ChildState) (fd : I32) (buf : Array U8 1#usize) :
    WP.dspec (sys.read1 s fd buf) fun p => p.2.1.blockedSigs = s.blockedSigs := by
  unfold sys.read1 LeanSwe.PostFork.Aeneas.Internal.Sys.read1
  cases s.status <;> simp only [WP.dspec_ok]
  cases currentFault s <;> cases s.getFd fd.val <;> simp only [WP.dspec_ok]
  all_goals
    rename_i e
    cases s.getDesc e.desc with
    | directory _ | procSelfFd _ => rw [WP.dspec_ok]
    | stream rd _ _ st =>
      cases rd
      · rw [WP.dspec_ok]
      · try (cases st)
        all_goals (rw [WP.dspec_ok]; try rfl)

end SysLemmas

end LeanSwe.PostFork.Proofs
