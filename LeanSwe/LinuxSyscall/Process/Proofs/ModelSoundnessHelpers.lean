import LeanSwe.LinuxSyscall.Process.Model

namespace LeanSwe.LinuxSyscall.Process

theorem nextFreeHid_ge_hint (fds : List (HandleId × ProcessFdDesc)) (hint : HandleId) :
    hint ≤ nextFreeHid fds hint := by
  induction fds generalizing hint with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    rcases hd with ⟨k, _⟩
    unfold nextFreeHid
    exact Nat.le_trans (Nat.le_max_left hint (k + 1)) (ih _)

theorem lt_nextFreeHid_of_mem (fds : List (HandleId × ProcessFdDesc)) (hint k : HandleId)
    (v : ProcessFdDesc) (hmem : (k, v) ∈ fds) :
    k < nextFreeHid fds hint := by
  induction fds generalizing hint with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨k', _⟩
    unfold nextFreeHid
    cases hmem with
    | head _ =>
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k)
        (Nat.le_trans (Nat.le_max_right hint (k + 1)) (nextFreeHid_ge_hint tl _))
    | tail _ hmem' =>
      exact ih _ hmem'

theorem assocGet_none_of_ge {β : Type} (xs : List (Nat × β)) (h : Nat)
    (hgt : ∀ k v, (k, v) ∈ xs → k < h) :
    assocGet xs h = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    have hlt : k < h := hgt k v (by simp)
    have hne : (k == h) = false := beq_false_of_ne (Nat.ne_of_lt hlt)
    simp only [assocGet, hne, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun k' v' hmem => hgt k' v' (List.mem_cons_of_mem _ hmem))

private theorem normalizeWaitSig_bounds (sig : UInt32) :
    (1 ≤ normalizeWaitSig sig && normalizeWaitSig sig ≤ 126) = true := by
  unfold normalizeWaitSig
  by_cases h : (1 ≤ sig && sig ≤ 126) = true
  · simp only [h, ↓reduceIte]
  · have hF : (1 ≤ sig && sig ≤ 126) = false := Bool.eq_false_iff.mpr h
    simp only [hF, Bool.false_eq_true, ↓reduceIte]; decide

private theorem assocGet_of_nodup_keys {β : Type} (xs : List (UInt32 × β))
    (hnodup : (xs.map Prod.fst).Nodup) {k : UInt32} {v : β} (hmem : (k, v) ∈ xs) :
    assocGet xs k = some v := by
  induction xs with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨hnot, htl⟩
    cases hmem with
    | head _ => simp [assocGet]
    | tail _ hmem' =>
      have hne : k' ≠ k := by
        intro heq
        subst heq
        exact hnot (List.mem_map.mpr ⟨(k', v), hmem', rfl⟩)
      have hbeq : (k' == k) = false := beq_false_of_ne hne
      simp only [assocGet, hbeq, Bool.false_eq_true, ↓reduceIte]
      exact ih htl hmem'

private theorem nodup_reverse_aux {α : Type} (l acc : List α)
    (hl : l.Nodup) (ha : acc.Nodup) (hdisj : ∀ x, x ∈ l → x ∉ acc) :
    (l.reverseAux acc).Nodup := by
  induction l generalizing acc with
  | nil => exact ha
  | cons hd tl ih =>
    simp only [List.nodup_cons] at hl
    refine ih (hd :: acc) hl.2 (List.nodup_cons.mpr ⟨hdisj hd (List.mem_cons_self ..), ha⟩) ?_
    intro x hx hx'
    cases hx' with
    | head _ => exact hl.1 hx
    | tail _ hmem => exact hdisj x (List.mem_cons_of_mem _ hx) hmem

private theorem matchingUnreapedChildrenGo_nodup
    (selfPid selfPgid : UInt32) (pid : Int32) (flags : WaitFlags)
    (procs : List (UInt32 × ProcEntry)) (seen : Std.TreeSet UInt32 compare)
    (acc : List (UInt32 × ProcEntry))
    (hseen : ∀ p e, (p, e) ∈ acc → seen.contains p = true)
    (hnodup : (acc.map Prod.fst).Nodup) :
    ((matchingUnreapedChildrenGo selfPid selfPgid pid flags procs seen acc).map Prod.fst).Nodup := by
  induction procs generalizing seen acc with
  | nil =>
    unfold matchingUnreapedChildrenGo
    rw [List.map_reverse]
    exact nodup_reverse_aux (acc.map Prod.fst) [] hnodup List.nodup_nil (fun _ _ h => by cases h)
  | cons hd tl ih =>
    rcases hd with ⟨cPid, entry⟩
    unfold matchingUnreapedChildrenGo
    by_cases hc : seen.contains cPid = true
    · simp only [hc, ↓reduceIte]
      exact ih seen acc hseen hnodup
    · have hcF : seen.contains cPid = false := Bool.eq_false_iff.mpr hc
      simp only [hcF, Bool.false_eq_true, ↓reduceIte]
      split
      · refine ih (seen.insert cPid) ((cPid, entry) :: acc) ?_ ?_
        · intro p e hmem
          cases hmem with
          | head _ => exact Std.TreeSet.contains_insert_self
          | tail _ hmem' =>
            rw [Std.TreeSet.contains_insert]
            simp [hseen p e hmem']
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, hnodup⟩
          intro hin
          rcases List.mem_map.mp hin with ⟨⟨p, e⟩, hmem', hp⟩
          dsimp only at hp
          subst hp
          exact hc (hseen p e hmem')
      · refine ih (seen.insert cPid) acc ?_ hnodup
        intro p e hmem'
        rw [Std.TreeSet.contains_insert]
        simp [hseen p e hmem']

theorem assocGet_matching_mem (s : ProcessSysState) (pid : Int32) (flags : WaitFlags)
    {cPid : UInt32} {e : ProcEntry}
    (hmem : (cPid, e) ∈ matchingUnreapedChildren s pid flags) :
    assocGet (matchingUnreapedChildren s pid flags) cPid = some e :=
  assocGet_of_nodup_keys _
    (matchingUnreapedChildrenGo_nodup (effectiveSelfPid s) (effectiveSelfPgid s) pid flags s.procs {} []
      (fun _ _ h => by cases h) List.nodup_nil)
    hmem

private theorem find?_eq_some {xs : List UInt32} {p : UInt32 → Bool} {x : UInt32}
    (h : xs.find? p = some x) : xs.contains x = true ∧ p x = true := by
  induction xs with
  | nil =>
    unfold List.find? at h
    cases h
  | cons hd tl ih =>
    unfold List.find? at h
    cases hp : p hd with
    | true =>
      simp only [hp] at h
      cases h
      change List.elem x (x :: tl) = true ∧ p x = true
      exact ⟨by unfold List.elem; rw [beq_self_eq_true], hp⟩
    | false =>
      simp only [hp] at h
      obtain ⟨hmem, hpx⟩ := ih h
      change List.elem x (hd :: tl) = true ∧ p x = true
      refine ⟨?_, hpx⟩
      unfold List.elem
      cases hx : (x == hd) with
      | true => rfl
      | false => exact hmem

private theorem u32_bne_self (x : UInt32) : (x != x) = false := by
  show (!(x == x)) = false
  rw [beq_self_eq_true]
  rfl

theorem isSome_eq_getD {α : Type} {o : Option α} {d : α} (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some _ => rfl

private theorem collectActiveSubthreadTgidsGo_mono (procs : List (UInt32 × ProcEntry))
    (seen acc : Std.TreeSet UInt32 compare) (x : UInt32) (hx : acc.contains x = true) :
    (collectActiveSubthreadTgidsGo procs seen acc).contains x = true := by
  induction procs generalizing seen acc with
  | nil => exact hx
  | cons hd tl ih =>
    rcases hd with ⟨pid, entry⟩
    dsimp only [collectActiveSubthreadTgidsGo]
    split
    · exact ih seen acc hx
    · apply ih
      cases entry.role with
      | thread tgid =>
        dsimp only
        split
        · by_cases heq : compare tgid x = .eq
          · simp [Std.TreeSet.contains_insert, heq]
          · simp [Std.TreeSet.contains_insert, hx]
        · exact hx
      | child _ _ | foreign _ => exact hx

private theorem collectActiveSubthreadTgidsGo_sound (procs : List (UInt32 × ProcEntry))
    (seen acc : Std.TreeSet UInt32 compare) (cPid : UInt32)
    (hacc : acc.contains cPid = false)
    (hgo : (collectActiveSubthreadTgidsGo procs seen acc).contains cPid = false) :
    anyActiveProcGo procs seen (fun _ e =>
      match e.role with
      | .thread tgid =>
        tgid == cPid &&
          match e.lifecycle with
          | .alive a => a.auto == .controlled && !a.canDeliverFatal
          | _ => false
      | _ => false) = false := by
  induction procs generalizing seen acc with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨pid, entry⟩
    rcases entry with ⟨pgid, canSignal, sameSession, orphanedPgid, unignoredSigs, role, reapedSubthreads, lifecycle⟩
    dsimp only [anyActiveProcGo, collectActiveSubthreadTgidsGo] at hgo ⊢
    cases hseen : seen.contains pid
    · simp only [hseen, Bool.false_eq_true, ↓reduceIte] at hgo ⊢
      cases role with
      | thread tgid =>
        dsimp only at hgo ⊢
        cases lifecycle with
        | alive a =>
          dsimp only at hgo ⊢
          have hne : (ProcLifecycle.alive a != .reaped && ProcLifecycle.alive a != .exitDead) = true := rfl
          simp only [hne, ↓reduceIte] at hgo
          by_cases heq : (tgid == cPid) = true
          · have hcmp : compare tgid cPid = .eq := by simpa using heq
            have hin : (acc.insert tgid).contains cPid = true := by simp [Std.TreeSet.contains_insert, hcmp]
            have hcontra := collectActiveSubthreadTgidsGo_mono tl (seen.insert pid) (acc.insert tgid) cPid hin
            rw [hgo] at hcontra; cases hcontra
          · have heqF : (tgid == cPid) = false := Bool.eq_false_iff.mpr heq
            have hcmp : compare tgid cPid ≠ .eq := by
              intro hc; exact heq (by simpa using hc)
            have hnotin : (acc.insert tgid).contains cPid = false := by
              simp [Std.TreeSet.contains_insert, hcmp, hacc]
            simp only [heqF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            exact ih (seen.insert pid) (acc.insert tgid) hnotin hgo
        | zombie z =>
          dsimp only at hgo ⊢
          have hne : (ProcLifecycle.zombie z != .reaped && ProcLifecycle.zombie z != .exitDead) = true := rfl
          simp only [hne, ↓reduceIte] at hgo
          by_cases hcmp : compare tgid cPid = .eq
          · have hin : (acc.insert tgid).contains cPid = true := by simp [Std.TreeSet.contains_insert, hcmp]
            have hcontra := collectActiveSubthreadTgidsGo_mono tl (seen.insert pid) (acc.insert tgid) cPid hin
            rw [hgo] at hcontra; cases hcontra
          · have hnotin : (acc.insert tgid).contains cPid = false := by
              simp [Std.TreeSet.contains_insert, hcmp, hacc]
            simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih (seen.insert pid) (acc.insert tgid) hnotin hgo
        | delayedZombie z k ts run cont ss exitReap race ds rs =>
          dsimp only at hgo ⊢
          have hne : (ProcLifecycle.delayedZombie z k ts run cont ss exitReap race ds rs != .reaped &&
              ProcLifecycle.delayedZombie z k ts run cont ss exitReap race ds rs != .exitDead) = true := rfl
          simp only [hne, ↓reduceIte] at hgo
          by_cases hcmp : compare tgid cPid = .eq
          · have hin : (acc.insert tgid).contains cPid = true := by simp [Std.TreeSet.contains_insert, hcmp]
            have hcontra := collectActiveSubthreadTgidsGo_mono tl (seen.insert pid) (acc.insert tgid) cPid hin
            rw [hgo] at hcontra; cases hcontra
          · have hnotin : (acc.insert tgid).contains cPid = false := by
              simp [Std.TreeSet.contains_insert, hcmp, hacc]
            simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih (seen.insert pid) (acc.insert tgid) hnotin hgo
        | exitDead =>
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact ih (seen.insert pid) acc hacc hgo
        | reaped =>
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact ih (seen.insert pid) acc hacc hgo
      | child _ _ =>
        exact ih (seen.insert pid) acc hacc hgo
      | foreign _ =>
        exact ih (seen.insert pid) acc hacc hgo
    · simp only [hseen, ↓reduceIte] at hgo ⊢
      exact ih seen acc hacc hgo

private theorem collectActiveSubthreadTgids_false_implies_no_controlled
    (procs : List (UInt32 × ProcEntry)) (cPid : UInt32)
    (h : (collectActiveSubthreadTgids procs).contains cPid = false) :
    hasControlledLiveSubthread procs cPid = false := by
  have hraw : hasRawControlledLiveSubthread procs cPid = false :=
    collectActiveSubthreadTgidsGo_sound procs {} {} cPid rfl h
  simp [hasControlledLiveSubthread, hraw]

private theorem collectActiveSubthreadTgidsGo_complete (procs : List (UInt32 × ProcEntry))
    (seen acc : Std.TreeSet UInt32 compare) (cPid : UInt32)
    (hacc : acc.contains cPid = false)
    (hgo : (collectActiveSubthreadTgidsGo procs seen acc).contains cPid = true) :
    anyActiveProcGo procs seen (fun _ e =>
      match e.role with
      | .thread tgid => tgid == cPid && e.lifecycle != .reaped && e.lifecycle != .exitDead
      | _ => false) = true := by
  induction procs generalizing seen acc with
  | nil =>
    dsimp only [collectActiveSubthreadTgidsGo] at hgo
    rw [hgo] at hacc
    cases hacc
  | cons hd tl ih =>
    rcases hd with ⟨pid, entry⟩
    rcases entry with ⟨pgid, canSignal, sameSession, orphanedPgid, unignoredSigs, role, reapedSubthreads, lifecycle⟩
    dsimp only [anyActiveProcGo, collectActiveSubthreadTgidsGo] at hgo ⊢
    cases hseen : seen.contains pid
    · simp only [hseen, Bool.false_eq_true, ↓reduceIte] at hgo ⊢
      cases role with
      | thread tgid =>
        dsimp only at hgo ⊢
        cases hact : (lifecycle != .reaped && lifecycle != .exitDead)
        · simp only [hact, Bool.false_eq_true, ↓reduceIte] at hgo
          have hact' : (tgid == cPid && lifecycle != .reaped && lifecycle != .exitDead) = false := by
            cases h1 : (lifecycle != .reaped) <;> cases h2 : (lifecycle != .exitDead) <;>
              simp_all [Bool.and_assoc]
          simp only [hact', Bool.false_eq_true, ↓reduceIte]
          exact ih (seen.insert pid) acc hacc hgo
        · simp only [hact, ↓reduceIte] at hgo
          obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hact
          by_cases heq : (tgid == cPid) = true
          · simp only [heq, h1, h2, Bool.and_true, ↓reduceIte]
          · have heqF : (tgid == cPid) = false := Bool.eq_false_iff.mpr heq
            have hcmp : compare tgid cPid ≠ .eq := by
              intro hc; exact heq (by simpa using hc)
            have hnotin : (acc.insert tgid).contains cPid = false := by
              simp [Std.TreeSet.contains_insert, hcmp, hacc]
            simp only [heqF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            exact ih (seen.insert pid) (acc.insert tgid) hnotin hgo
      | child _ _ =>
        exact ih (seen.insert pid) acc hacc hgo
      | foreign _ =>
        exact ih (seen.insert pid) acc hacc hgo
    · simp only [hseen, ↓reduceIte] at hgo ⊢
      exact ih seen acc hacc hgo

private theorem collectActiveSubthreadTgids_true_implies_hasActiveSubthread
    (procs : List (UInt32 × ProcEntry)) (cPid : UInt32)
    (h : (collectActiveSubthreadTgids procs).contains cPid = true) :
    hasActiveSubthread procs cPid = true :=
  collectActiveSubthreadTgidsGo_complete procs {} {} cPid rfl h

private theorem collectControlledSubthreadTgidsGo_mono (procs : List (UInt32 × ProcEntry))
    (seen acc : Std.TreeSet UInt32 compare) (cPid : UInt32)
    (hx : acc.contains cPid = true) :
    (collectControlledSubthreadTgidsGo procs seen acc).contains cPid = true := by
  induction procs generalizing seen acc with
  | nil => exact hx
  | cons hd tl ih =>
    rcases hd with ⟨pid, entry⟩
    dsimp only [collectControlledSubthreadTgidsGo]
    cases seen.contains pid
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply ih
      cases entry.role with
      | thread tgid =>
        cases entry.lifecycle with
        | alive a =>
          dsimp only
          by_cases hc : (a.auto == .controlled && !a.canDeliverFatal) = true
          · simp only [hc, ↓reduceIte]
            by_cases heq : compare tgid cPid = .eq
            · simp [Std.TreeSet.contains_insert, heq]
            · simp [Std.TreeSet.contains_insert, hx]
          · have hcF : (a.auto == .controlled && !a.canDeliverFatal) = false := Bool.eq_false_iff.mpr hc
            simp only [hcF, Bool.false_eq_true, ↓reduceIte]; exact hx
        | zombie _ | delayedZombie _ _ _ _ _ _ _ _ _ _ | exitDead | reaped => exact hx
      | child _ _ | foreign _ => exact hx
    · simp only [↓reduceIte]
      exact ih seen acc hx

private theorem collectControlledSubthreadTgidsGo_sound (procs : List (UInt32 × ProcEntry))
    (seen acc : Std.TreeSet UInt32 compare) (cPid : UInt32)
    (hacc : acc.contains cPid = false)
    (hgo : (collectControlledSubthreadTgidsGo procs seen acc).contains cPid = false) :
    anyActiveProcGo procs seen (fun _ e =>
      match e.role with
      | .thread tgid =>
        tgid == cPid &&
          match e.lifecycle with
          | .alive a => a.auto == .controlled && !a.canDeliverFatal
          | _ => false
      | _ => false) = false := by
  induction procs generalizing seen acc with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨pid, entry⟩
    rcases entry with ⟨pgid, canSignal, sameSession, orphanedPgid, unignoredSigs, role, reapedSubthreads, lifecycle⟩
    dsimp only [anyActiveProcGo, collectControlledSubthreadTgidsGo] at hgo ⊢
    cases hseen : seen.contains pid
    · simp only [hseen, Bool.false_eq_true, ↓reduceIte] at hgo ⊢
      cases role with
      | thread tgid =>
        dsimp only at hgo ⊢
        cases lifecycle with
        | alive a =>
          dsimp only at hgo ⊢
          by_cases hc : (a.auto == .controlled && !a.canDeliverFatal) = true
          · simp only [hc, ↓reduceIte] at hgo
            by_cases heq : (tgid == cPid) = true
            · have hcmp : compare tgid cPid = .eq := by simpa using heq
              have hin : (acc.insert tgid).contains cPid = true := by simp [Std.TreeSet.contains_insert, hcmp]
              have hcontra := collectControlledSubthreadTgidsGo_mono tl (seen.insert pid) (acc.insert tgid) cPid hin
              rw [hgo] at hcontra; cases hcontra
            · have heqF : (tgid == cPid) = false := Bool.eq_false_iff.mpr heq
              have hcmp : compare tgid cPid ≠ .eq := by
                intro hcp; exact heq (by simpa using hcp)
              have hnotin : (acc.insert tgid).contains cPid = false := by
                simp [Std.TreeSet.contains_insert, hcmp, hacc]
              simp only [heqF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              exact ih (seen.insert pid) (acc.insert tgid) hnotin hgo
          · have hcF : (a.auto == .controlled && !a.canDeliverFatal) = false := Bool.eq_false_iff.mpr hc
            simp only [hcF, Bool.false_eq_true, ↓reduceIte] at hgo
            simp only [hcF, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih (seen.insert pid) acc hacc hgo
        | zombie _ | delayedZombie _ _ _ _ _ _ _ _ _ _ | exitDead | reaped =>
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact ih (seen.insert pid) acc hacc hgo
      | child _ _ =>
        exact ih (seen.insert pid) acc hacc hgo
      | foreign _ =>
        exact ih (seen.insert pid) acc hacc hgo
    · simp only [hseen, ↓reduceIte] at hgo ⊢
      exact ih seen acc hacc hgo

private theorem collectGroupExitSubthreadTgidsGo_complete (procs : List (UInt32 × ProcEntry))
    (seen acc : Std.TreeSet UInt32 compare) (cPid : UInt32)
    (hacc : acc.contains cPid = false)
    (hgo : (collectGroupExitSubthreadTgidsGo procs seen acc).contains cPid = true) :
    anyActiveProcGo procs seen (fun pid e =>
      match e.role with
      | .thread tgid =>
        tgid == cPid &&
          match e.lifecycle with
          | .alive a => a.canTriggerGroupExit
          | _ => false
      | _ =>
        pid == cPid && e.reapedSubthreads.any AliveState.canTriggerGroupExit) = true := by
  induction procs generalizing seen acc with
  | nil =>
    dsimp only [collectGroupExitSubthreadTgidsGo] at hgo
    rw [hgo] at hacc
    cases hacc
  | cons hd tl ih =>
    rcases hd with ⟨pid, entry⟩
    rcases entry with ⟨pgid, canSignal, sameSession, orphanedPgid, unignoredSigs, role, reapedSubthreads, lifecycle⟩
    dsimp only [anyActiveProcGo, collectGroupExitSubthreadTgidsGo] at hgo ⊢
    cases hseen : seen.contains pid
    · simp only [hseen, Bool.false_eq_true, ↓reduceIte] at hgo ⊢
      cases role with
      | thread tgid =>
        dsimp only at hgo ⊢
        cases lifecycle with
        | alive a =>
          dsimp only at hgo ⊢
          by_cases hge : a.canTriggerGroupExit = true
          · simp only [hge, ↓reduceIte, Bool.and_true] at hgo ⊢
            by_cases heq : (tgid == cPid) = true
            · simp only [heq, ↓reduceIte]
            · have heqF : (tgid == cPid) = false := Bool.eq_false_iff.mpr heq
              have hcmp : compare tgid cPid ≠ .eq := by
                intro hc; exact heq (by simpa using hc)
              have hnotin : (acc.insert tgid).contains cPid = false := by
                simp [Std.TreeSet.contains_insert, hcmp, hacc]
              simp only [heqF, Bool.false_eq_true, ↓reduceIte]
              exact ih (seen.insert pid) (acc.insert tgid) hnotin hgo
          · have hgeF : a.canTriggerGroupExit = false := Bool.eq_false_iff.mpr hge
            simp only [hgeF, Bool.false_eq_true, ↓reduceIte, Bool.and_false] at hgo ⊢
            exact ih (seen.insert pid) acc hacc hgo
        | zombie _ | delayedZombie _ _ _ _ _ _ _ _ _ _ | exitDead | reaped =>
          dsimp only at hgo ⊢
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact ih (seen.insert pid) acc hacc hgo
      | child _ _ | foreign _ =>
        dsimp only at hgo ⊢
        by_cases hge : reapedSubthreads.any AliveState.canTriggerGroupExit = true
        · simp only [hge, ↓reduceIte, Bool.and_true] at hgo ⊢
          by_cases heq : (pid == cPid) = true
          · simp only [heq, ↓reduceIte]
          · have heqF : (pid == cPid) = false := Bool.eq_false_iff.mpr heq
            have hcmp : compare pid cPid ≠ .eq := by
              intro hc; exact heq (by simpa using hc)
            have hnotin : (acc.insert pid).contains cPid = false := by
              simp [Std.TreeSet.contains_insert, hcmp, hacc]
            simp only [heqF, Bool.false_eq_true, ↓reduceIte]
            exact ih (seen.insert pid) (acc.insert pid) hnotin hgo
        · have hgeF : reapedSubthreads.any AliveState.canTriggerGroupExit = false := Bool.eq_false_iff.mpr hge
          simp only [hgeF, Bool.false_eq_true, ↓reduceIte, Bool.and_false] at hgo ⊢
          exact ih (seen.insert pid) acc hacc hgo
    · simp only [hseen, ↓reduceIte] at hgo ⊢
      exact ih seen acc hacc hgo

private theorem isHeldByControlledSubthreadSet_false_implies_no_controlled
    (procs : List (UInt32 × ProcEntry)) (cPid : UInt32)
    (h : isHeldByControlledSubthreadSet (collectControlledSubthreadTgids procs)
           (collectGroupExitSubthreadTgids procs) cPid = false) :
    hasControlledLiveSubthread procs cPid = false := by
  unfold isHeldByControlledSubthreadSet at h
  unfold hasControlledLiveSubthread
  by_cases hc : (collectControlledSubthreadTgids procs).contains cPid = true
  · simp only [hc, Bool.true_and] at h
    have hg : (collectGroupExitSubthreadTgids procs).contains cPid = true := by
      cases hgt : (collectGroupExitSubthreadTgids procs).contains cPid <;> simp_all
    have hge : hasGroupExitSubthread procs cPid = true :=
      collectGroupExitSubthreadTgidsGo_complete procs {} {} cPid rfl hg
    simp [hge]
  · have hcF : (collectControlledSubthreadTgids procs).contains cPid = false := Bool.eq_false_iff.mpr hc
    have hraw : hasRawControlledLiveSubthread procs cPid = false :=
      collectControlledSubthreadTgidsGo_sound procs {} {} cPid rfl hcF
    simp [hraw]

private theorem pickImmediateWaitStep_sound
    (s : ProcessSysState) (activeSubTgids : Std.TreeSet UInt32 compare)
    (cPid : UInt32)
    (hsub : activeSubTgids.contains cPid = false → hasControlledLiveSubthread s.procs cPid = false)
    (hactHas : activeSubTgids.contains cPid = true → hasActiveSubthread s.procs cPid = true)
    (entry : ProcEntry) (flags : WaitFlags) {wres : WaitResult}
    (hfind : pickImmediateWaitStep activeSubTgids cPid entry flags = some wres) :
    (waitChildStep s cPid entry flags wres).isSome = true := by
  rcases entry with ⟨pgid, canSignal, sameSession, orphanedPgid, unignoredSigs, role, reapedSubthreads, lifecycle⟩
  cases lifecycle with
  | zombie z =>
    dsimp only [pickImmediateWaitStep] at hfind
    cases hfind
    cases z with
    | exited code =>
      simp only [ZombieStatus.toWaitResult, waitChildStep, u32_bne_self,
        Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Option.isSome_some]
    | signaled sig core =>
      have hbounds := normalizeWaitSig_bounds sig
      simp only [ZombieStatus.toWaitResult, waitChildStep, u32_bne_self, Bool.false_or,
        hbounds, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true, Option.isSome_some]
  | delayedZombie z k ts run cont ss exitReap race ds rs =>
    dsimp only [pickImmediateWaitStep] at hfind
    split at hfind
    · next hact =>
      have hsubAct := hactHas hact
      cases run with
      | stopped rawSig rep =>
        cases rep with
        | true => cases hfind
        | false =>
          by_cases huntr : flags.untraced = true
          · simp only [huntr, ↓reduceIte] at hfind
            cases hfind
            have hbounds := normalizeWaitSig_bounds rawSig
            simp only [waitChildStep, u32_bne_self, Bool.false_or, huntr, hbounds,
              Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              beq_self_eq_true, hsubAct, Bool.and_self, Option.isSome_some]
          · have huntrF : flags.untraced = false := Bool.eq_false_iff.mpr huntr
            simp only [huntrF, Bool.false_eq_true, ↓reduceIte] at hfind
            cases hfind
      | running =>
        by_cases hus : (flags.untraced && !k) = true
        · simp only [hus, ↓reduceIte] at hfind
          have huntr : flags.untraced = true := ((Bool.and_eq_true _ _).mp hus).1
          have hnkT : (!k) = true := ((Bool.and_eq_true _ _).mp hus).2
          cases hsf : ss.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
          | some sig =>
            simp only [hsf] at hfind
            cases hfind
            obtain ⟨hcontains, hbounds⟩ := find?_eq_some hsf
            simp only [waitChildStep, u32_bne_self, Bool.false_or, huntr, hbounds,
              Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              hnkT, hcontains, Bool.true_or, hsubAct, Bool.and_self, Option.isSome_some]
          | none =>
            simp only [hsf] at hfind
            by_cases hcont : (flags.continued && cont != .none) = true
            · simp only [hcont, ↓reduceIte] at hfind
              cases hfind
              have hcf : flags.continued = true := ((Bool.and_eq_true _ _).mp hcont).1
              have hne : (cont != .none) = true := ((Bool.and_eq_true _ _).mp hcont).2
              simp only [waitChildStep, u32_bne_self, Bool.false_or, hcf, hnkT, hne,
                beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
                hsubAct, Bool.and_true, ↓reduceIte, Option.isSome_some]
            · have hcontF : (flags.continued && cont != .none) = false := Bool.eq_false_iff.mpr hcont
              simp only [hcontF, Bool.false_eq_true, ↓reduceIte] at hfind
              cases hfind
        · have husF : (flags.untraced && !k) = false := Bool.eq_false_iff.mpr hus
          simp only [husF, Bool.false_eq_true, ↓reduceIte] at hfind
          by_cases hcont : (flags.continued && !k && cont != .none) = true
          · simp only [hcont, ↓reduceIte] at hfind
            cases hfind
            have hc12 := ((Bool.and_eq_true _ _).mp hcont).1
            have hcf : flags.continued = true := ((Bool.and_eq_true _ _).mp hc12).1
            have hnkT : (!k) = true := ((Bool.and_eq_true _ _).mp hc12).2
            have hne : (cont != .none) = true := ((Bool.and_eq_true _ _).mp hcont).2
            simp only [waitChildStep, u32_bne_self, Bool.false_or, hcf, hnkT, hne,
              beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
              hsubAct, Bool.and_true, ↓reduceIte, Option.isSome_some]
          · have hcontF : (flags.continued && !k && cont != .none) = false := Bool.eq_false_iff.mpr hcont
            simp only [hcontF, Bool.false_eq_true, ↓reduceIte] at hfind
            cases hfind
    · next hact =>
      have hactF : activeSubTgids.contains cPid = false := Bool.eq_false_iff.mpr hact
      have hnoctrl := hsub hactF
      by_cases hreap : (exitReap != .autoreapOnly && (k || run == .running)) = true
      · have hnotAuto : (exitReap != .autoreapOnly) = true := ((Bool.and_eq_true _ _).mp hreap).1
        have hkrun : (k || run == .running) = true := ((Bool.and_eq_true _ _).mp hreap).2
        simp only [hreap, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfind
        cases hk : k
        · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hfind
          simp only [hk, Bool.false_or] at hkrun
          have hrun : run = .running := by
            cases hr : run <;> simp only [hr] at hkrun <;> first | rfl | cases hkrun
          have hrr : (TaskRunState.running == TaskRunState.running) = true := rfl
          cases htf : firstValidTermSig? ts with
          | some sig =>
            simp only [htf] at hfind
            cases hfind
            obtain ⟨hcontains, hbounds⟩ := find?_eq_some htf
            simp only [waitChildStep, u32_bne_self, Bool.false_or, hbounds,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte, delayedZombieCanDeliverFatal,
              hrun, hrr, htf, Option.isSome_some, Bool.and_self, Bool.or_true, hnotAuto,
              Bool.not_false, hcontains, Bool.true_or]
          | none =>
            simp only [htf] at hfind
            cases hfind
            cases z with
            | exited code =>
              simp [ZombieStatus.toWaitResult, waitChildStep, delayedZombieCanDeliverFatal,
                hnotAuto, hrun, htf, hnoctrl]
            | signaled sig core =>
              have hbounds := normalizeWaitSig_bounds sig
              simp [ZombieStatus.toWaitResult, waitChildStep, delayedZombieCanDeliverFatal,
                hnotAuto, hrun, htf, hnoctrl, hbounds]
        · simp only [hk, ↓reduceIte] at hfind
          cases hfind
          simp [waitChildStep, delayedZombieCanDeliverFatal, hnotAuto]
      · have hreapF : (exitReap != .autoreapOnly && (k || run == .running)) = false :=
          Bool.eq_false_iff.mpr hreap
        simp only [hreapF, Bool.not_false, ↓reduceIte] at hfind
        cases hfind
  | alive a =>
    rcases a with ⟨run, cont, auto, pending, exitReap, subExitedRace⟩
    cases run with
    | stopped rawSig rep =>
      dsimp only [pickImmediateWaitStep] at hfind
      cases rep with
      | true => cases hfind
      | false =>
        by_cases huntr : flags.untraced = true
        · simp only [huntr, ↓reduceIte] at hfind
          cases hfind
          have hbounds := normalizeWaitSig_bounds rawSig
          simp only [waitChildStep, u32_bne_self, Bool.false_or, huntr, hbounds,
            Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            beq_self_eq_true, Option.isSome_some]
        · have huntrF : flags.untraced = false := Bool.eq_false_iff.mpr huntr
          simp only [huntrF, Bool.false_eq_true, ↓reduceIte] at hfind
          cases hfind
    | running =>
      dsimp only [pickImmediateWaitStep] at hfind
      by_cases hus : (flags.untraced && !pending.killed) = true
      · simp only [hus, ↓reduceIte] at hfind
        have huntr : flags.untraced = true := ((Bool.and_eq_true _ _).mp hus).1
        have hnkT : (!pending.killed) = true := ((Bool.and_eq_true _ _).mp hus).2
        cases hsf : pending.stopSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
        | some sig =>
          simp only [hsf] at hfind
          cases hfind
          obtain ⟨hcontains, hbounds⟩ := find?_eq_some hsf
          simp only [waitChildStep, u32_bne_self, Bool.false_or, huntr, hbounds,
            Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            hnkT, hcontains, Bool.true_or, Option.isSome_some]
        | none =>
          simp only [hsf] at hfind
          by_cases hcont : (flags.continued && cont != .none) = true
          · simp only [hcont, ↓reduceIte] at hfind
            cases hfind
            have hcf : flags.continued = true := ((Bool.and_eq_true _ _).mp hcont).1
            have hne : (cont != .none) = true := ((Bool.and_eq_true _ _).mp hcont).2
            simp only [waitChildStep, u32_bne_self, Bool.false_or, hcf, hnkT,
              hne, beq_self_eq_true, Bool.true_and, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, Option.isSome_some]
          · have hcontF : (flags.continued && cont != .none) = false := Bool.eq_false_iff.mpr hcont
            simp only [hcontF, Bool.false_eq_true, ↓reduceIte] at hfind
            by_cases hmz : AliveState.mayZombie { run := .running, cont := cont, auto := auto, pending := pending, exitReap := exitReap, subExitedRace := subExitedRace } = true
            · simp only [hmz, ↓reduceIte] at hfind
              cases htf : pending.termSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
              | some sig =>
                simp only [htf, Option.map_some] at hfind
                cases hfind
                obtain ⟨hcontains, hbounds⟩ := find?_eq_some htf
                simp only [waitChildStep, u32_bne_self, Bool.false_or, hbounds,
                  Bool.not_true, Bool.false_eq_true, ↓reduceIte, hmz,
                  AliveState.allowsSignaled, beq_self_eq_true, hcontains, Bool.not_false,
                  Bool.true_and, Bool.true_or, Bool.or_true, Option.isSome_some]
              | none =>
                simp only [htf, Option.map_none] at hfind
                cases hfind
            · have hmzF : AliveState.mayZombie { run := .running, cont := cont, auto := auto, pending := pending, exitReap := exitReap, subExitedRace := subExitedRace } = false := Bool.eq_false_iff.mpr hmz
              simp only [hmzF, Bool.false_eq_true, ↓reduceIte] at hfind
              cases hfind
      · have husF : (flags.untraced && !pending.killed) = false := Bool.eq_false_iff.mpr hus
        simp only [husF, Bool.false_eq_true, ↓reduceIte] at hfind
        by_cases hcont : (flags.continued && !pending.killed && cont != .none) = true
        · simp only [hcont, ↓reduceIte] at hfind
          cases hfind
          have hc12 := ((Bool.and_eq_true _ _).mp hcont).1
          have hcf : flags.continued = true := ((Bool.and_eq_true _ _).mp hc12).1
          have hnkT : (!pending.killed) = true := ((Bool.and_eq_true _ _).mp hc12).2
          have hne : (cont != .none) = true := ((Bool.and_eq_true _ _).mp hcont).2
          simp only [waitChildStep, u32_bne_self, Bool.false_or, hcf, hnkT,
            hne, beq_self_eq_true, Bool.true_and, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, Option.isSome_some]
        · have hcontF : (flags.continued && !pending.killed && cont != .none) = false := Bool.eq_false_iff.mpr hcont
          simp only [hcontF, Bool.false_eq_true, ↓reduceIte] at hfind
          by_cases hmz : AliveState.mayZombie { run := .running, cont := cont, auto := auto, pending := pending, exitReap := exitReap, subExitedRace := subExitedRace } = true
          · simp only [hmz, ↓reduceIte] at hfind
            by_cases hpk : pending.killed = true
            · simp only [hpk, ↓reduceIte] at hfind
              cases hfind
              have h9 : (1 ≤ (9 : UInt32) && (9 : UInt32) ≤ 126) = true := rfl
              simp only [waitChildStep, u32_bne_self, h9, Bool.not_true, Bool.false_or, hmz,
                AliveState.allowsSignaled, hpk, Bool.true_and, Bool.true_or,
                Bool.not_false, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
                Option.isSome_some]
            · have hpkF : pending.killed = false := Bool.eq_false_iff.mpr hpk
              simp only [hpkF, Bool.false_eq_true, ↓reduceIte] at hfind
              cases htf : pending.termSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
              | some sig =>
                simp only [htf, Option.map_some] at hfind
                cases hfind
                obtain ⟨hcontains, hbounds⟩ := find?_eq_some htf
                simp only [waitChildStep, u32_bne_self, Bool.false_or, hbounds,
                  Bool.not_true, Bool.false_eq_true, ↓reduceIte, hmz,
                  AliveState.allowsSignaled, beq_self_eq_true, hcontains, Bool.not_false,
                  Bool.true_and, Bool.true_or, Bool.or_true, Option.isSome_some]
              | none =>
                simp only [htf, Option.map_none] at hfind
                cases hfind
          · have hmzF : AliveState.mayZombie { run := .running, cont := cont, auto := auto, pending := pending, exitReap := exitReap, subExitedRace := subExitedRace } = false := Bool.eq_false_iff.mpr hmz
            simp only [hmzF, Bool.false_eq_true, ↓reduceIte] at hfind
            cases hfind
  | exitDead =>
    dsimp only [pickImmediateWaitStep] at hfind
    cases hfind
  | reaped =>
    dsimp only [pickImmediateWaitStep] at hfind
    cases hfind

private theorem pickImmediateWaitStep_allowedStepWaitResult
    (s : ProcessSysState) (activeSubTgids : Std.TreeSet UInt32 compare)
    (matching : List (UInt32 × ProcEntry)) (flags : WaitFlags)
    (cPid : UInt32) (entry : ProcEntry) {wres : WaitResult}
    (hget : assocGet matching cPid = some entry)
    (hfind : pickImmediateWaitStep activeSubTgids cPid entry flags = some wres) :
    allowedStepWaitResult s matching flags wres = waitChildStep s cPid entry flags wres := by
  have hp : match wres with
      | .stillRunning => False
      | .exited rPid _ | .signaled rPid _ _ | .stopped rPid _ | .continued rPid => rPid = cPid := by
    rcases entry with ⟨pgid, canSignal, sameSession, orphanedPgid, unignoredSigs, role, reapedSubthreads, lifecycle⟩
    cases lifecycle with
    | zombie z =>
      dsimp only [pickImmediateWaitStep] at hfind
      cases hfind; cases z <;> rfl
    | delayedZombie z k ts run cont ss exitReap race ds rs =>
      dsimp only [pickImmediateWaitStep] at hfind
      split at hfind
      · cases run with
        | stopped rawSig rep =>
          cases rep with
          | true => cases hfind
          | false =>
            by_cases huntr : flags.untraced = true
            · simp only [huntr, ↓reduceIte] at hfind; cases hfind; rfl
            · have huntrF : flags.untraced = false := Bool.eq_false_iff.mpr huntr
              simp only [huntrF, Bool.false_eq_true, ↓reduceIte] at hfind; cases hfind
        | running =>
          by_cases hus : (flags.untraced && !k) = true
          · simp only [hus, ↓reduceIte] at hfind
            cases hsf : ss.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
            | some sig => simp only [hsf] at hfind; cases hfind; rfl
            | none =>
              simp only [hsf] at hfind
              by_cases hcont : (flags.continued && cont != .none) = true
              · simp only [hcont, ↓reduceIte] at hfind; cases hfind; rfl
              · have hcontF : (flags.continued && cont != .none) = false := Bool.eq_false_iff.mpr hcont
                simp only [hcontF, Bool.false_eq_true, ↓reduceIte] at hfind; cases hfind
          · have husF : (flags.untraced && !k) = false := Bool.eq_false_iff.mpr hus
            simp only [husF, Bool.false_eq_true, ↓reduceIte] at hfind
            by_cases hcont : (flags.continued && !k && cont != .none) = true
            · simp only [hcont, ↓reduceIte] at hfind; cases hfind; rfl
            · have hcontF : (flags.continued && !k && cont != .none) = false := Bool.eq_false_iff.mpr hcont
              simp only [hcontF, Bool.false_eq_true, ↓reduceIte] at hfind; cases hfind
      · by_cases hreap : (exitReap != .autoreapOnly && (k || run == .running)) = true
        · simp only [hreap, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfind
          by_cases hk : k = true
          · simp only [hk, ↓reduceIte] at hfind; cases hfind; rfl
          · have hkF : k = false := Bool.eq_false_iff.mpr hk
            simp only [hkF, Bool.false_eq_true, ↓reduceIte] at hfind
            cases htf : firstValidTermSig? ts with
            | some sig => simp only [htf] at hfind; cases hfind; rfl
            | none => simp only [htf] at hfind; cases hfind; cases z <;> rfl
        · have hreapF : (exitReap != .autoreapOnly && (k || run == .running)) = false :=
            Bool.eq_false_iff.mpr hreap
          simp only [hreapF, Bool.not_false, ↓reduceIte] at hfind; cases hfind
    | alive a =>
      rcases a with ⟨run, cont, auto, pending, exitReap, subExitedRace⟩
      cases run with
      | stopped rawSig rep =>
        dsimp only [pickImmediateWaitStep] at hfind
        cases rep with
        | true => cases hfind
        | false =>
          by_cases huntr : flags.untraced = true
          · simp only [huntr, ↓reduceIte] at hfind; cases hfind; rfl
          · have huntrF : flags.untraced = false := Bool.eq_false_iff.mpr huntr
            simp only [huntrF, Bool.false_eq_true, ↓reduceIte] at hfind; cases hfind
      | running =>
        dsimp only [pickImmediateWaitStep] at hfind
        by_cases hus : (flags.untraced && !pending.killed) = true
        · simp only [hus, ↓reduceIte] at hfind
          cases hsf : pending.stopSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
          | some sig => simp only [hsf] at hfind; cases hfind; rfl
          | none =>
            simp only [hsf] at hfind
            by_cases hcont : (flags.continued && cont != .none) = true
            · simp only [hcont, ↓reduceIte] at hfind; cases hfind; rfl
            · have hcontF : (flags.continued && cont != .none) = false := Bool.eq_false_iff.mpr hcont
              simp only [hcontF, Bool.false_eq_true, ↓reduceIte] at hfind
              by_cases hmz : AliveState.mayZombie { run := .running, cont := cont, auto := auto, pending := pending, exitReap := exitReap, subExitedRace := subExitedRace } = true
              · simp only [hmz, ↓reduceIte] at hfind
                cases htf : pending.termSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
                | some sig => simp only [htf, Option.map_some] at hfind; cases hfind; rfl
                | none => simp only [htf, Option.map_none] at hfind; cases hfind
              · have hmzF : AliveState.mayZombie { run := .running, cont := cont, auto := auto, pending := pending, exitReap := exitReap, subExitedRace := subExitedRace } = false := Bool.eq_false_iff.mpr hmz
                simp only [hmzF, Bool.false_eq_true, ↓reduceIte] at hfind; cases hfind
        · have husF : (flags.untraced && !pending.killed) = false := Bool.eq_false_iff.mpr hus
          simp only [husF, Bool.false_eq_true, ↓reduceIte] at hfind
          by_cases hcont : (flags.continued && !pending.killed && cont != .none) = true
          · simp only [hcont, ↓reduceIte] at hfind; cases hfind; rfl
          · have hcontF : (flags.continued && !pending.killed && cont != .none) = false := Bool.eq_false_iff.mpr hcont
            simp only [hcontF, Bool.false_eq_true, ↓reduceIte] at hfind
            by_cases hmz : AliveState.mayZombie { run := .running, cont := cont, auto := auto, pending := pending, exitReap := exitReap, subExitedRace := subExitedRace } = true
            · simp only [hmz, ↓reduceIte] at hfind
              by_cases hpk : pending.killed = true
              · simp only [hpk, ↓reduceIte] at hfind; cases hfind; rfl
              · have hpkF : pending.killed = false := Bool.eq_false_iff.mpr hpk
                simp only [hpkF, Bool.false_eq_true, ↓reduceIte] at hfind
                cases htf : pending.termSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
                | some sig => simp only [htf, Option.map_some] at hfind; cases hfind; rfl
                | none => simp only [htf, Option.map_none] at hfind; cases hfind
            · have hmzF : AliveState.mayZombie { run := .running, cont := cont, auto := auto, pending := pending, exitReap := exitReap, subExitedRace := subExitedRace } = false := Bool.eq_false_iff.mpr hmz
              simp only [hmzF, Bool.false_eq_true, ↓reduceIte] at hfind; cases hfind
    | exitDead => dsimp only [pickImmediateWaitStep] at hfind; cases hfind
    | reaped => dsimp only [pickImmediateWaitStep] at hfind; cases hfind
  cases wres with
  | stillRunning => contradiction
  | exited rPid _ | signaled rPid _ _ | stopped rPid _ | continued rPid =>
    dsimp only at hp
    subst hp
    simp only [allowedStepWaitResult, hget]

private theorem waitChildStep_some_implies_allowedStepWaitResult
    (s : ProcessSysState) (activeSubTgids : Std.TreeSet UInt32 compare)
    (cPid : UInt32)
    (hsub : activeSubTgids.contains cPid = false → hasControlledLiveSubthread s.procs cPid = false)
    (hactHas : activeSubTgids.contains cPid = true → hasActiveSubthread s.procs cPid = true)
    (matching : List (UInt32 × ProcEntry)) (flags : WaitFlags)
    (entry : ProcEntry) (wres : WaitResult)
    (hwc : pickImmediateWaitStep activeSubTgids cPid entry flags = some wres)
    (hget : assocGet matching cPid = some entry) :
    (allowedStepWaitResult s matching flags wres).isSome = true := by
  rw [pickImmediateWaitStep_allowedStepWaitResult s activeSubTgids matching flags cPid entry hget hwc]
  exact pickImmediateWaitStep_sound s activeSubTgids cPid hsub hactHas entry flags hwc

theorem pickImmediateWaitResult_sound
    (s : ProcessSysState) (matching : List (UInt32 × ProcEntry)) (flags : WaitFlags)
    (huniq : ∀ {cPid e}, (cPid, e) ∈ matching → assocGet matching cPid = some e)
    {wres : WaitResult}
    (hfind : pickImmediateWaitResult s.procs matching flags = some wres) :
    (allowedStepWaitResult s matching flags wres).isSome = true := by
  let activeSubTgids := collectActiveSubthreadTgids s.procs
  suffices hgen : ∀ (xs : List (UInt32 × ProcEntry)),
      (∀ {cPid e}, (cPid, e) ∈ xs → assocGet matching cPid = some e) →
      pickImmediateWaitResultSet activeSubTgids xs flags = some wres →
      (allowedStepWaitResult s matching flags wres).isSome = true from
    hgen matching huniq hfind
  intro xs hmem hfind
  induction xs with
  | nil =>
    unfold pickImmediateWaitResultSet at hfind
    cases hfind
  | cons hd tl ih =>
    rcases hd with ⟨cPid, entry⟩
    have hget : assocGet matching cPid = some entry := hmem (List.Mem.head tl)
    have htl : ∀ {c e}, (c, e) ∈ tl → assocGet matching c = some e :=
      fun hm => hmem (List.Mem.tail _ hm)
    unfold pickImmediateWaitResultSet at hfind
    cases hstep : pickImmediateWaitStep activeSubTgids cPid entry flags with
    | some w =>
      rw [hstep] at hfind
      cases hfind
      exact waitChildStep_some_implies_allowedStepWaitResult s activeSubTgids cPid
        (collectActiveSubthreadTgids_false_implies_no_controlled s.procs cPid)
        (collectActiveSubthreadTgids_true_implies_hasActiveSubthread s.procs cPid)
        matching flags entry wres hstep hget
    | none =>
      rw [hstep] at hfind
      exact ih htl hfind

private theorem pickImmediateWaitStep_none_implies_not_confirmed
    (activeSubTgids ctrlSubTgids groupExitSubTgids : Std.TreeSet UInt32 compare)
    (cPid : UInt32) (entry : ProcEntry) (flags : WaitFlags)
    (hnone : pickImmediateWaitStep activeSubTgids cPid entry flags = none) :
    hasConfirmedWaitableEntrySet activeSubTgids ctrlSubTgids groupExitSubTgids cPid entry flags = false := by
  rcases entry with ⟨pgid, canSignal, sameSession, orphanedPgid, unignoredSigs, role, reapedSubthreads, lifecycle⟩
  cases lifecycle with
  | zombie z =>
    dsimp only [pickImmediateWaitStep] at hnone
    cases hnone
  | delayedZombie z k ts run cont ss exitReap race ds rs =>
    dsimp only [pickImmediateWaitStep] at hnone
    dsimp only [hasConfirmedWaitableEntrySet]
    split at hnone
    · next hact =>
      rw [ite_eq_left_of_eq_true _ _ (eq_true hact)]
      cases run with
      | stopped rawSig rep =>
        cases rep with
        | true => rfl
        | false =>
          by_cases huntr : flags.untraced = true
          · simp only [huntr, ↓reduceIte] at hnone; cases hnone
          · exact Bool.eq_false_iff.mpr huntr
      | running =>
        cases hk : k with
        | true =>
          simp [delayedZombieCanDeliverFatal]
        | false =>
          have hcontF : (flags.continued && cont != .none) = false := by
            by_cases hcont : (flags.continued && cont != .none) = true
            · by_cases hus : flags.untraced = true
              · simp only [hk, Bool.not_false, Bool.and_true, hus, ↓reduceIte] at hnone
                cases hsf : ss.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
                | some _ => simp only [hsf] at hnone; cases hnone
                | none => simp only [hsf, hcont, ↓reduceIte] at hnone; cases hnone
              · have husF : flags.untraced = false := Bool.eq_false_iff.mpr hus
                simp only [hk, Bool.not_false, Bool.and_true, husF, Bool.false_eq_true, ↓reduceIte, hcont] at hnone
                cases hnone
            · exact Bool.eq_false_iff.mpr hcont
          cases hc : flags.continued with
          | false => rfl
          | true =>
            cases hco : cont with
            | none | maybe => rfl
            | confirmed => rw [hc, hco] at hcontF; cases hcontF
    · next hact =>
      rw [ite_eq_right_of_eq_false _ _ (eq_false hact)]
      by_cases hreap : (exitReap != .autoreapOnly && (k || run == .running)) = true
      · simp only [hreap, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hnone
        cases hk : k
        · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hnone
          cases htf : firstValidTermSig? ts <;> simp only [htf] at hnone <;> cases hnone
        · simp only [hk, ↓reduceIte] at hnone; cases hnone
      · have hreapF : (exitReap != .autoreapOnly && (k || run == .running)) = false :=
          Bool.eq_false_iff.mpr hreap
        cases exitReap <;> cases k <;> cases run <;> simp_all
  | alive a =>
    rcases a with ⟨run, cont, auto, pending, exitReap, subExitedRace⟩
    cases run with
    | stopped rawSig rep =>
      dsimp only [pickImmediateWaitStep] at hnone
      dsimp only [hasConfirmedWaitableEntrySet]
      cases rep with
      | true => rfl
      | false =>
        by_cases huntr : flags.untraced = true
        · simp only [huntr, ↓reduceIte] at hnone; cases hnone
        · exact Bool.eq_false_iff.mpr huntr
    | running =>
      dsimp only [pickImmediateWaitStep] at hnone
      dsimp only [hasConfirmedWaitableEntrySet]
      cases hk : pending.killed with
      | true =>
        simp [AliveState.canDeliverFatal, hk]
      | false =>
        have hcontF : (flags.continued && cont != .none) = false := by
          by_cases hcont : (flags.continued && cont != .none) = true
          · by_cases hus : flags.untraced = true
            · simp only [hk, Bool.not_false, Bool.and_true, hus, ↓reduceIte] at hnone
              cases hsf : pending.stopSigs.find? (fun sig => 1 ≤ sig && sig ≤ 126) with
              | some _ => simp only [hsf] at hnone; cases hnone
              | none => simp only [hsf, hcont, ↓reduceIte] at hnone; cases hnone
            · have husF : flags.untraced = false := Bool.eq_false_iff.mpr hus
              simp only [hk, Bool.not_false, Bool.and_true, husF, Bool.false_eq_true, ↓reduceIte, hcont] at hnone
              cases hnone
          · exact Bool.eq_false_iff.mpr hcont
        cases hc : flags.continued with
        | false => rfl
        | true =>
          cases hco : cont with
          | none | maybe => rfl
          | confirmed => rw [hc, hco] at hcontF; cases hcontF
  | exitDead => rfl
  | reaped => rfl

theorem pickImmediateWaitResult_none_implies_not_hasConfirmedWaitable
    (procs : List (UInt32 × ProcEntry)) (matching : List (UInt32 × ProcEntry)) (flags : WaitFlags)
    (hnone : pickImmediateWaitResult procs matching flags = none) :
    hasConfirmedWaitable procs matching flags = false := by
  let activeSubTgids := collectActiveSubthreadTgids procs
  let ctrlSubTgids := collectControlledSubthreadTgids procs
  let groupExitSubTgids := collectGroupExitSubthreadTgids procs
  suffices hgen : ∀ (xs : List (UInt32 × ProcEntry)),
      pickImmediateWaitResultSet activeSubTgids xs flags = none →
      hasConfirmedWaitableWithSet activeSubTgids ctrlSubTgids groupExitSubTgids xs flags = false from
    hgen matching hnone
  intro xs hnone
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨cPid, entry⟩
    unfold pickImmediateWaitResultSet at hnone
    unfold hasConfirmedWaitableWithSet
    cases hstep : pickImmediateWaitStep activeSubTgids cPid entry flags with
    | some _ =>
      rw [hstep] at hnone
      cases hnone
    | none =>
      rw [hstep] at hnone
      have hcf := pickImmediateWaitStep_none_implies_not_confirmed
        activeSubTgids ctrlSubTgids groupExitSubTgids cPid entry flags hstep
      simp only [hcf, Bool.false_eq_true, ↓reduceIte]
      exact ih hnone

private theorem pickAliveAutoExit?_spec (cPid : UInt32) (sub : AliveState) {wres : WaitResult}
    (h : pickAliveAutoExit? cPid sub = some wres) :
    match wres with
    | .exited rPid code => rPid = cPid ∧ sub.allowsExited code = true
    | .signaled rPid sig core => rPid = cPid ∧ (1 ≤ sig && sig ≤ 126) = true ∧ sub.allowsSignaled sig core = true
    | .stillRunning | .stopped _ _ | .continued _ => False := by
  unfold pickAliveAutoExit? at h
  by_cases hk : sub.pending.killed = true
  · simp only [hk, ↓reduceIte] at h
    cases h
    exact ⟨rfl, rfl, by simp [AliveState.allowsSignaled, hk]⟩
  · have hkF : sub.pending.killed = false := Bool.eq_false_iff.mpr hk
    simp only [hkF, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hr : (sub.run == .running) = true
    · simp only [hr, ↓reduceIte] at h
      cases htf : firstValidTermSig? sub.pending.termSigs with
      | some sig =>
        simp only [htf] at h
        cases h
        obtain ⟨hcontains, hbounds⟩ := find?_eq_some htf
        exact ⟨rfl, hbounds, by
          simp only [AliveState.allowsSignaled, hr, hcontains, Bool.not_false,
            Bool.true_or, Bool.and_self, Bool.or_true]⟩
      | none =>
        simp only [htf] at h
        cases hau : sub.auto with
        | planned z =>
          simp only [hau] at h
          cases h
          cases z with
          | exited code =>
            exact ⟨rfl, by simp [AliveState.allowsExited, hr, hau]⟩
          | signaled zs zc =>
            exact ⟨rfl, normalizeWaitSig_bounds zs, by simp [AliveState.allowsSignaled, hr, hau]⟩
        | arbitrary =>
          simp only [hau] at h
          cases h
          exact ⟨rfl, by simp [AliveState.allowsExited, hr, hau]⟩
        | controlled =>
          simp only [hau] at h
          cases h
    · have hrF : (sub.run == .running) = false := Bool.eq_false_iff.mpr hr
      simp only [hrF, Bool.false_eq_true, ↓reduceIte] at h
      cases h

private theorem pickActiveSubthreadAutoExitGo_spec (procs : List (UInt32 × ProcEntry))
    (seen : Std.TreeSet UInt32 compare) (cPid : UInt32) {wres : WaitResult}
    (h : pickActiveSubthreadAutoExitGo procs seen cPid = some wres) :
    match wres with
    | .exited rPid code =>
      rPid = cPid ∧
      anyActiveProcGo procs seen (fun _ e =>
        match e.role, e.lifecycle with
        | .thread tgid, .alive a => tgid == cPid && a.allowsExited code
        | _, _ => false) = true
    | .signaled rPid sig core =>
      rPid = cPid ∧ (1 ≤ sig && sig ≤ 126) = true ∧
      anyActiveProcGo procs seen (fun _ e =>
        match e.role, e.lifecycle with
        | .thread tgid, .alive a => tgid == cPid && a.allowsSignaled sig core
        | _, _ => false) = true
    | .stillRunning | .stopped _ _ | .continued _ => False := by
  induction procs generalizing seen with
  | nil =>
    unfold pickActiveSubthreadAutoExitGo at h
    cases h
  | cons hd tl ih =>
    rcases hd with ⟨pid, e⟩
    rcases e with ⟨pgid, canSig, sameSess, orphPg, unign, role, reapedSubs, lifecycle⟩
    unfold pickActiveSubthreadAutoExitGo at h
    cases hseen : seen.contains pid with
    | true =>
      simp only [hseen, ↓reduceIte] at h
      have hrec := ih seen h
      cases wres <;> simp only [anyActiveProcGo, hseen, ↓reduceIte] <;> exact hrec
    | false =>
      simp only [hseen, Bool.false_eq_true, ↓reduceIte] at h
      cases role with
      | thread tgid =>
        cases lifecycle with
        | alive sub =>
          dsimp only at h
          by_cases heq : (tgid == cPid) = true
          · simp only [heq, ↓reduceIte] at h
            cases hp : pickAliveAutoExit? cPid sub with
            | some w =>
              simp only [hp] at h
              cases h
              have hsp := pickAliveAutoExit?_spec cPid sub hp
              cases wres with
              | exited rPid code =>
                obtain ⟨hrp, hal⟩ := hsp
                exact ⟨hrp, by simp [anyActiveProcGo, hseen, heq, hal]⟩
              | signaled rPid sig core =>
                obtain ⟨hrp, hbnd, hal⟩ := hsp
                exact ⟨hrp, hbnd, by simp [anyActiveProcGo, hseen, heq, hal]⟩
              | stillRunning | stopped _ _ | continued _ => exact hsp
            | none =>
              simp only [hp] at h
              have hrec := ih (seen.insert pid) h
              cases wres with
              | exited rPid code =>
                obtain ⟨hrp, htl⟩ := hrec
                refine ⟨hrp, ?_⟩
                dsimp only [anyActiveProcGo]
                simp only [hseen, Bool.false_eq_true, ↓reduceIte]
                by_cases hpr : (tgid == cPid && sub.allowsExited code) = true
                · simp only [hpr, ↓reduceIte]
                · simp only [Bool.eq_false_iff.mpr hpr, Bool.false_eq_true, ↓reduceIte, htl]
              | signaled rPid sig core =>
                obtain ⟨hrp, hbnd, htl⟩ := hrec
                refine ⟨hrp, hbnd, ?_⟩
                dsimp only [anyActiveProcGo]
                simp only [hseen, Bool.false_eq_true, ↓reduceIte]
                by_cases hpr : (tgid == cPid && sub.allowsSignaled sig core) = true
                · simp only [hpr, ↓reduceIte]
                · simp only [Bool.eq_false_iff.mpr hpr, Bool.false_eq_true, ↓reduceIte, htl]
              | stillRunning | stopped _ _ | continued _ => exact hrec
          · have heqF : (tgid == cPid) = false := Bool.eq_false_iff.mpr heq
            simp only [heqF, Bool.false_eq_true, ↓reduceIte] at h
            have hrec := ih (seen.insert pid) h
            cases wres <;> simp only [anyActiveProcGo, hseen, heqF, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;> exact hrec
        | zombie _ | delayedZombie _ _ _ _ _ _ _ _ _ _ | exitDead | reaped =>
          dsimp only at h
          have hrec := ih (seen.insert pid) h
          cases wres <;> simp only [anyActiveProcGo, hseen, Bool.false_eq_true, ↓reduceIte] <;> exact hrec
      | child _ _ | foreign _ =>
        dsimp only at h
        have hrec := ih (seen.insert pid) h
        cases wres <;> simp only [anyActiveProcGo, hseen, Bool.false_eq_true, ↓reduceIte] <;> exact hrec

private theorem findSome?_pickAliveAutoExit?_spec (reapedSubs : List AliveState) (cPid : UInt32) {wres : WaitResult}
    (h : reapedSubs.findSome? (pickAliveAutoExit? cPid) = some wres) :
    match wres with
    | .exited rPid code => rPid = cPid ∧ reapedSubs.any (fun sub => sub.allowsExited code) = true
    | .signaled rPid sig core =>
      rPid = cPid ∧ (1 ≤ sig && sig ≤ 126) = true ∧ reapedSubs.any (fun sub => sub.allowsSignaled sig core) = true
    | .stillRunning | .stopped _ _ | .continued _ => False := by
  induction reapedSubs with
  | nil =>
    unfold List.findSome? at h
    cases h
  | cons sub rest ih =>
    unfold List.findSome? at h
    cases hp : pickAliveAutoExit? cPid sub with
    | some w =>
      simp only [hp] at h
      cases h
      have hsp := pickAliveAutoExit?_spec cPid sub hp
      cases wres with
      | exited rPid code =>
        obtain ⟨hrp, hal⟩ := hsp
        exact ⟨hrp, by simp [List.any_cons, hal]⟩
      | signaled rPid sig core =>
        obtain ⟨hrp, hbnd, hal⟩ := hsp
        exact ⟨hrp, hbnd, by simp [List.any_cons, hal]⟩
      | stillRunning | stopped _ _ | continued _ => exact hsp
    | none =>
      simp only [hp] at h
      have hrec := ih h
      cases wres with
      | exited rPid code =>
        obtain ⟨hrp, htl⟩ := hrec
        exact ⟨hrp, by simp [List.any_cons, htl]⟩
      | signaled rPid sig core =>
        obtain ⟨hrp, hbnd, htl⟩ := hrec
        exact ⟨hrp, hbnd, by simp [List.any_cons, htl]⟩
      | stillRunning | stopped _ _ | continued _ => exact hrec

private theorem pickSubthreadAutoExit?_spec (procs : List (UInt32 × ProcEntry))
    (cPid : UInt32) (reapedSubs : List AliveState) {wres : WaitResult}
    (h : pickSubthreadAutoExit? procs cPid reapedSubs = some wres) :
    match wres with
    | .exited rPid code =>
      rPid = cPid ∧
      (hasSubthreadAllowingExited procs cPid code || reapedSubs.any (fun sub => sub.allowsExited code)) = true
    | .signaled rPid sig core =>
      rPid = cPid ∧ (1 ≤ sig && sig ≤ 126) = true ∧
      (hasSubthreadAllowingSignaled procs cPid sig core || reapedSubs.any (fun sub => sub.allowsSignaled sig core)) = true
    | .stillRunning | .stopped _ _ | .continued _ => False := by
  unfold pickSubthreadAutoExit? at h
  cases hact : pickActiveSubthreadAutoExitGo procs {} cPid with
  | some w =>
    simp only [hact] at h
    cases h
    have hsp := pickActiveSubthreadAutoExitGo_spec procs {} cPid hact
    cases wres with
    | exited rPid code =>
      obtain ⟨hrp, hal⟩ := hsp
      have hex : hasSubthreadAllowingExited procs cPid code = true := hal
      exact ⟨hrp, by simp only [hex, Bool.true_or]⟩
    | signaled rPid sig core =>
      obtain ⟨hrp, hbnd, hal⟩ := hsp
      have hsg : hasSubthreadAllowingSignaled procs cPid sig core = true := hal
      exact ⟨hrp, hbnd, by simp only [hsg, Bool.true_or]⟩
    | stillRunning | stopped _ _ | continued _ => exact hsp
  | none =>
    simp only [hact] at h
    have hsp := findSome?_pickAliveAutoExit?_spec reapedSubs cPid h
    cases wres with
    | exited rPid code =>
      obtain ⟨hrp, hal⟩ := hsp
      exact ⟨hrp, by simp [hal]⟩
    | signaled rPid sig core =>
      obtain ⟨hrp, hbnd, hal⟩ := hsp
      exact ⟨hrp, hbnd, by simp [hal]⟩
    | stillRunning | stopped _ _ | continued _ => exact hsp

theorem pickBlockingAutoExit_sound
    (s : ProcessSysState) (matching : List (UInt32 × ProcEntry)) (flags : WaitFlags)
    (huniq : ∀ {cPid e}, (cPid, e) ∈ matching → assocGet matching cPid = some e)
    {wres : WaitResult}
    (hfind : pickBlockingAutoExit s.procs matching = some wres) :
    (allowedStepWaitResult s matching flags wres).isSome = true := by
  let ctrlSubTgids := collectControlledSubthreadTgids s.procs
  let groupExitSubTgids := collectGroupExitSubthreadTgids s.procs
  suffices hgen : ∀ (xs : List (UInt32 × ProcEntry)),
      (∀ {cPid e}, (cPid, e) ∈ xs → assocGet matching cPid = some e) →
      pickBlockingAutoExitSet s.procs ctrlSubTgids groupExitSubTgids xs = some wres →
      (allowedStepWaitResult s matching flags wres).isSome = true from
    hgen matching huniq hfind
  intro xs hmem hfind
  induction xs with
  | nil =>
    unfold pickBlockingAutoExitSet at hfind
    cases hfind
  | cons hd tl ih =>
    rcases hd with ⟨cPid, entry⟩
    have hget : assocGet matching cPid = some entry := hmem (List.Mem.head tl)
    have htl : ∀ {c e}, (c, e) ∈ tl → assocGet matching c = some e :=
      fun hm => hmem (List.Mem.tail _ hm)
    unfold pickBlockingAutoExitSet at hfind
    cases hlc : entry.lifecycle with
    | alive a =>
      simp only [hlc] at hfind
      by_cases hok : (a.run == .running && a.exitReap != .autoreapOnly) = true
      · simp only [hok, ↓reduceIte] at hfind
        have hrun : a.run = .running := by
          have h1 := ((Bool.and_eq_true _ _).mp hok).1
          cases hr : a.run <;> simp only [hr] at h1 <;> first | rfl | cases h1
        have hnotAuto : (a.exitReap != .autoreapOnly) = true := ((Bool.and_eq_true _ _).mp hok).2
        cases hau : a.auto with
        | planned z =>
          simp only [hau] at hfind
          cases hfind
          have hmz : a.mayZombie = true := by
            simp [AliveState.mayZombie, AliveState.canDeliverFatal, hrun, hau, hnotAuto]
          cases z with
          | exited code =>
            simp only [ZombieStatus.toWaitResult, allowedStepWaitResult, hget, waitChildStep,
              u32_bne_self, Bool.false_eq_true, ↓reduceIte, hlc, hmz,
              AliveState.allowsExited, hrun, hau, beq_self_eq_true, Bool.true_and,
              Bool.true_or, Option.isSome_some]
          | signaled sig core =>
            have hbounds := normalizeWaitSig_bounds sig
            simp only [ZombieStatus.toWaitResult, allowedStepWaitResult, hget, waitChildStep,
              u32_bne_self, Bool.false_or, hbounds, Bool.true_and, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte, hlc, hmz, AliveState.allowsSignaled, hrun, hau,
              beq_self_eq_true, Bool.or_true, Bool.true_or, Option.isSome_some]
        | arbitrary =>
          simp only [hau] at hfind
          cases hfind
          have hmz : a.mayZombie = true := by
            simp [AliveState.mayZombie, AliveState.canDeliverFatal, hrun, hau, hnotAuto]
          simp only [allowedStepWaitResult, hget, waitChildStep, u32_bne_self,
            Bool.false_eq_true, ↓reduceIte, hlc, hmz, AliveState.allowsExited, hrun, hau,
            beq_self_eq_true, Bool.true_and, Bool.true_or, Option.isSome_some]
        | controlled =>
          simp only [hau] at hfind
          by_cases hgf : (!a.canDeliverGroupFatal) = true
          · simp only [hgf, ↓reduceIte] at hfind
            cases hsub : pickSubthreadAutoExit? s.procs cPid entry.reapedSubthreads with
            | some w =>
              simp only [hsub] at hfind
              cases hfind
              have hsp := pickSubthreadAutoExit?_spec s.procs cPid entry.reapedSubthreads hsub
              cases wres with
              | exited rPid code =>
                obtain ⟨hrp, hcm⟩ := hsp
                subst hrp
                have hrr : (a.pending.killed || a.run == .running) = true := by simp [hrun]
                simp only [allowedStepWaitResult, hget, waitChildStep, u32_bne_self,
                  Bool.false_eq_true, ↓reduceIte, hlc, hnotAuto, hrr, hgf, hcm,
                  Bool.true_and, Bool.or_true, Option.isSome_some]
              | signaled rPid sig core =>
                obtain ⟨hrp, hbnd, hsm⟩ := hsp
                subst hrp
                have hrr : (a.pending.killed || a.run == .running) = true := by simp [hrun]
                simp only [allowedStepWaitResult, hget, waitChildStep, u32_bne_self,
                  Bool.false_or, hbnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  hlc, hnotAuto, hrr, hgf, hsm, Bool.true_and, Bool.or_true, Option.isSome_some]
              | stillRunning | stopped _ _ | continued _ => exact absurd hsp False.elim
            | none =>
              simp only [hsub] at hfind
              exact ih htl hfind
          · have hgfF : (!a.canDeliverGroupFatal) = false := Bool.eq_false_iff.mpr hgf
            simp only [hgfF, Bool.false_eq_true, ↓reduceIte] at hfind
            exact ih htl hfind
      · have hokF : (a.run == .running && a.exitReap != .autoreapOnly) = false := Bool.eq_false_iff.mpr hok
        simp only [hokF, Bool.false_eq_true, ↓reduceIte] at hfind
        exact ih htl hfind
    | zombie _ =>
      simp only [hlc] at hfind
      exact ih htl hfind
    | delayedZombie z k ts run cont ss exitReap race ds rs =>
      simp only [hlc] at hfind
      by_cases hreap : (exitReap != .autoreapOnly && (k || run == .running)) = true
      · have hnotAuto : (exitReap != .autoreapOnly) = true := ((Bool.and_eq_true _ _).mp hreap).1
        have hkrun : (k || run == .running) = true := ((Bool.and_eq_true _ _).mp hreap).2
        simp only [hreap, ↓reduceIte] at hfind
        cases hk : k
        · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hfind
          simp only [hk, Bool.false_or] at hkrun
          have hrun : run = .running := by
            cases hr : run <;> simp only [hr] at hkrun <;> first | rfl | cases hkrun
          have hrr : (TaskRunState.running == TaskRunState.running) = true := rfl
          cases htf : firstValidTermSig? ts with
          | some sig =>
            simp only [htf] at hfind
            cases hfind
            obtain ⟨hcontains, hbounds⟩ := find?_eq_some htf
            simp only [allowedStepWaitResult, hget, waitChildStep, u32_bne_self, Bool.false_or,
              hbounds, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlc,
              delayedZombieCanDeliverFatal, hrun, hrr, htf, Option.isSome_some, Bool.and_self,
              Bool.or_true, hnotAuto, Bool.not_false, hcontains, Bool.true_or]
          | none =>
            simp only [htf] at hfind
            by_cases hctrl : isHeldByControlledSubthreadSet ctrlSubTgids groupExitSubTgids cPid = true
            · simp only [hctrl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfind
              exact ih htl hfind
            · have hctrlF : isHeldByControlledSubthreadSet ctrlSubTgids groupExitSubTgids cPid = false :=
                Bool.eq_false_iff.mpr hctrl
              have hnoctrl : hasControlledLiveSubthread s.procs cPid = false :=
                isHeldByControlledSubthreadSet_false_implies_no_controlled s.procs cPid hctrlF
              simp only [hctrlF, Bool.not_false, ↓reduceIte] at hfind
              cases hfind
              cases z with
              | exited code =>
                simp [ZombieStatus.toWaitResult, allowedStepWaitResult, hget, waitChildStep,
                  delayedZombieCanDeliverFatal, hlc, hk, hrun, htf, hnotAuto, hnoctrl]
              | signaled sig core =>
                have hbounds := normalizeWaitSig_bounds sig
                simp [ZombieStatus.toWaitResult, allowedStepWaitResult, hget, waitChildStep,
                  delayedZombieCanDeliverFatal, hbounds, hlc, hk, hrun, htf, hnotAuto, hnoctrl]
        · simp only [hk, ↓reduceIte] at hfind
          cases hfind
          simp [allowedStepWaitResult, hget, waitChildStep, delayedZombieCanDeliverFatal,
            hnotAuto, hlc, hk]
      · have hreapF : (exitReap != .autoreapOnly && (k || run == .running)) = false :=
          Bool.eq_false_iff.mpr hreap
        simp only [hreapF, Bool.false_eq_true, ↓reduceIte] at hfind
        exact ih htl hfind
    | exitDead =>
      simp only [hlc] at hfind
      exact ih htl hfind
    | reaped =>
      simp only [hlc] at hfind
      exact ih htl hfind

end LeanSwe.LinuxSyscall.Process
