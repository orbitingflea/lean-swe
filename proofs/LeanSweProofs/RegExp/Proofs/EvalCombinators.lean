import LeanSwe.RegExp.Interface
import LeanSweProofs.RegExp.Model
import LeanSweProofs.RegExp.Proofs.ParserClass

namespace LeanSwe.RegExp.Proofs

private theorem utf8ByteOffset_succ (cs : List Char) {i : Nat} (hi : i < cs.length) :
    Model.utf8ByteOffset cs (i + 1) = Model.utf8ByteOffset cs i + cs[i].utf8Size := by
  rw [Model.utf8ByteOffset, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  rfl

private theorem buildByteOffsets_loop_inv :
    ∀ (n : Nat) (chars : Array Char) (i acc : Nat) (out : Array Nat),
      chars.size - i ≤ n →
      i ≤ chars.size →
      out.size = i + 1 →
      acc = Model.utf8ByteOffset chars.toList i →
      (∀ k ≤ i, out[k]! = Model.utf8ByteOffset chars.toList k) →
      let res := Internal.buildByteOffsets.loop chars i acc out
      res.size = chars.size + 1 ∧ ∀ k ≤ chars.size, res[k]! = Model.utf8ByteOffset chars.toList k := by
  intro n
  induction n with
  | zero =>
    intro chars i acc out hle hi hs ha hinv
    have hge : ¬ i < chars.size := by omega
    have hieq : i = chars.size := by omega
    subst hieq
    rw [Internal.buildByteOffsets.loop]
    simp only [hge, ↓reduceDIte]
    exact ⟨hs, hinv⟩
  | succ n ih =>
    intro chars i acc out hle hi hs ha hinv
    by_cases h : i < chars.size
    · rw [Internal.buildByteOffsets.loop]
      simp only [h, ↓reduceDIte]
      have hacc' : acc + chars[i].utf8Size = Model.utf8ByteOffset chars.toList (i + 1) := by
        rw [ha, utf8ByteOffset_succ chars.toList (by simpa using h)]
        rfl
      apply ih chars (i + 1) (acc + chars[i].utf8Size) (out.push (acc + chars[i].utf8Size))
        (by omega) h (by simp [hs]) hacc'
      intro k hk
      by_cases hki : k ≤ i
      · have hlt : k < out.size := by omega
        have hlt2 : k < (out.push (acc + chars[i].utf8Size)).size := by simp; omega
        simp only [getElem!_pos, hlt2, Array.getElem_push_lt hlt]
        have hk' := hinv k hki
        simp only [getElem!_pos, hlt] at hk'
        exact hk'
      · have hkeq : k = i + 1 := by omega
        subst hkeq
        have hlt2 : i + 1 < (out.push (acc + chars[i].utf8Size)).size := by simp [hs]
        have hget := arr_getElem! (out.push (acc + chars[i].utf8Size)) (i + 1) hlt2
        have hpush : (out.push (acc + chars[i].utf8Size))[i + 1] = acc + chars[i].utf8Size := by
          simpa [hs] using Array.getElem_push_eq (xs := out) (x := acc + chars[i].utf8Size)
        rw [hget, hpush]
        exact hacc'
    · have hieq : i = chars.size := by omega
      subst hieq
      rw [Internal.buildByteOffsets.loop]
      simp only [h, ↓reduceDIte]
      exact ⟨hs, hinv⟩

/-- `Internal.buildByteOffsets` computes `Model.utf8ByteOffset` at every `k ≤ chars.size`. -/
theorem buildByteOffsets_spec (chars : Array Char) :
    (Internal.buildByteOffsets chars).size = chars.size + 1 ∧
    ∀ k ≤ chars.size, (Internal.buildByteOffsets chars)[k]! = Model.utf8ByteOffset chars.toList k := by
  unfold Internal.buildByteOffsets
  refine buildByteOffsets_loop_inv chars.size chars 0 0 ((Array.mkEmpty (chars.size + 1)).push 0)
    (Nat.le_refl _) (Nat.zero_le _) (by simp) (by simp [Model.utf8ByteOffset]) ?_
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  simp [Model.utf8ByteOffset]

private theorem dedupFirstAux_eq (seen xs : List Nat) :
    Internal.dedupFirstAux seen xs = Model.dedupFirstAux seen xs := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x rest ih =>
    simp only [Internal.dedupFirstAux, Model.dedupFirstAux]
    split <;> simp [ih]

private theorem dedupFirstBoolAux_eq (bound : Nat) :
    ∀ (seenList : List Nat) (seen : Array Bool) (xs : List Nat),
      seen.size = bound + 1 →
      (∀ i ≤ bound, seen[i]! = decide (i ∈ seenList)) →
      (∀ x ∈ xs, x ≤ bound) →
      Internal.dedupFirstBoolAux seen xs = Model.dedupFirstAux seenList xs := by
  intro seenList seen xs hs hinv hbd
  induction xs generalizing seenList seen with
  | nil => rfl
  | cons x rest ih =>
    have hx : x ≤ bound := hbd x (by simp)
    have hinvx := hinv x hx
    simp only [Internal.dedupFirstBoolAux, Model.dedupFirstAux, hinvx]
    by_cases hm : x ∈ seenList
    · have hcon : seenList.contains x = true := List.contains_iff_mem.mpr hm
      simp only [hm, decide_true, ↓reduceIte, hcon]
      exact ih seenList seen hs hinv (fun y hy => hbd y (by simp [hy]))
    · have hcon : seenList.contains x = false :=
        Bool.eq_false_iff.mpr fun h => hm (List.contains_iff_mem.mp h)
      simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, hcon]
      congr 1
      apply ih (x :: seenList) (seen.setIfInBounds x true) (by simp [hs])
      · intro i hi
        have his : i < seen.size := by omega
        simp only [getElem!_pos, Array.size_setIfInBounds, his, Array.getElem_setIfInBounds]
        by_cases hxi : x = i
        · subst hxi; simp
        · by_cases hmem : i ∈ seenList
          · have hi' := hinv i hi
            have hget := arr_getElem! seen i his
            rw [hget, decide_eq_true hmem] at hi'
            simp [hxi, hi', hmem, Ne.symm hxi]
          · have hi' := hinv i hi
            have hget := arr_getElem! seen i his
            rw [hget, decide_eq_false hmem] at hi'
            simp [hxi, hi', hmem, Ne.symm hxi]
      · exact fun y hy => hbd y (by simp [hy])

/-- `Internal.dedupFirstFast` equals `Model.dedupFirst` on bounded indices. -/
theorem dedupFirstFast_eq (bound : Nat) (xs : List Nat) (hbd : ∀ x ∈ xs, x ≤ bound) :
    Internal.dedupFirstFast bound xs = Model.dedupFirst xs := by
  unfold Internal.dedupFirstFast Model.dedupFirst
  cases xs with
  | nil => rfl
  | cons x rest =>
    cases rest with
    | nil => simp [Model.dedupFirstAux]
    | cons y rest2 =>
      dsimp only
      split
      · exact dedupFirstAux_eq [] (x :: y :: rest2)
      · apply dedupFirstBoolAux_eq bound [] (Array.replicate (bound + 1) false) (x :: y :: rest2)
          (by simp)
        · intro i hi
          have hlt : i < (Array.replicate (bound + 1) false).size := by simp; omega
          have hget := arr_getElem! (Array.replicate (bound + 1) false) i hlt
          simp [hget]
        · exact hbd

private theorem isWordAt_eq (chars : Array Char) (idx : Nat) :
    Internal.isWordAt chars idx = Model.isWordAt chars.toList idx := by
  unfold Internal.isWordAt Model.isWordAt
  have hg : chars[idx]? = chars.toList[idx]? := by simp
  rw [hg]
  cases chars.toList[idx]? <;> rfl

/-- `Internal.isWordBoundary` agrees with `Model.isWordBoundary`. -/
theorem isWordBoundary_eq (chars : Array Char) (idx : Nat) :
    Internal.isWordBoundary chars idx = Model.isWordBoundary chars.toList idx := by
  simp [Internal.isWordBoundary, Model.isWordBoundary, isWordAt_eq]

/-- Table invariant stating `tab[pos]! = spec pos` with monotonic bounded end positions. -/
def TabMatches (n : Nat) (tab : Array (List Nat)) (spec : Nat → List Nat) : Prop :=
  tab.size = n + 1 ∧ ∀ pos ≤ n, tab[pos]! = spec pos ∧ ∀ p ∈ tab[pos]!, pos ≤ p ∧ p ≤ n

/-- `Internal.idTab` satisfies `TabMatches` for `fun pos => [pos]`. -/
theorem idTab_matches (n : Nat) :
    TabMatches n (Internal.idTab n) (fun pos => [pos]) := by
  refine ⟨by simp [Internal.idTab], ?_⟩
  intro pos hpos
  have hlt : pos < (Internal.idTab n).size := by simp [Internal.idTab]; omega
  refine ⟨by simp [Internal.idTab, getElem!_pos, Nat.lt_succ_of_le hpos], ?_⟩
  intro p hp
  simp [Internal.idTab, getElem!_pos, Nat.lt_succ_of_le hpos] at hp
  subst hp
  exact ⟨Nat.le_refl _, hpos⟩

/-- `Model.dedupFirst` preserves exact list membership. -/
theorem dedupFirst_mem_iff (xs : List Nat) (a : Nat) :
    a ∈ Model.dedupFirst xs ↔ a ∈ xs := by
  have haux : ∀ seen ys, a ∈ Model.dedupFirstAux seen ys ↔ a ∈ ys ∧ a ∉ seen := by
    intro seen ys
    induction ys generalizing seen with
    | nil => simp [Model.dedupFirstAux]
    | cons x rest ih =>
      simp only [Model.dedupFirstAux]
      by_cases hc : seen.contains x = true
      · have hx := List.contains_iff_mem.mp hc
        simp only [hc, ↓reduceIte, ih, List.mem_cons]
        constructor
        · rintro ⟨ha, hns⟩; exact ⟨Or.inr ha, hns⟩
        · rintro ⟨rfl | ha, hns⟩
          · exact absurd hx hns
          · exact ⟨ha, hns⟩
      · have hx : x ∉ seen := fun h => hc (List.contains_iff_mem.mpr h)
        simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨ha, hns⟩)
          · exact ⟨Or.inl rfl, hx⟩
          · exact ⟨Or.inr ha, fun hm => hns (Or.inr hm)⟩
        · rintro ⟨rfl | ha, hns⟩
          · exact Or.inl rfl
          · by_cases hax : a = x
            · exact Or.inl hax
            · exact Or.inr ⟨ha, fun hm => by
                rcases hm with rfl | hm'
                · exact hax rfl
                · exact hns hm'⟩
  simp [Model.dedupFirst, haux]

/-- `Internal.composeTab` satisfies `TabMatches` for sequential composition. -/
theorem composeTab_matches {n : Nat} {t1 t2 : Array (List Nat)} {s1 s2 : Nat → List Nat}
    (h1 : TabMatches n t1 s1) (h2 : TabMatches n t2 s2) :
    TabMatches n (Internal.composeTab n t1 t2) (fun pos => Model.dedupFirst ((s1 pos).flatMap s2)) := by
  refine ⟨by simp [Internal.composeTab], ?_⟩
  intro pos hpos
  have hpos1 : pos < t1.size := by rw [h1.1]; omega
  have ht1 := h1.2 pos hpos
  have hflat : (t1[pos]!.flatMap fun mid => t2[mid]!) = (s1 pos).flatMap s2 := by
    rw [ht1.1]
    apply list_flatMap_congr
    intro mid hmid
    have hm' : mid ∈ t1[pos]! := by rw [ht1.1]; exact hmid
    exact (h2.2 mid (ht1.2 mid hm').2).1
  have hbd : ∀ p ∈ (t1[pos]!.flatMap fun mid => t2[mid]!), p ≤ n := by
    intro p hp
    simp only [List.mem_flatMap] at hp
    rcases hp with ⟨mid, hmid, hp'⟩
    have hm := ht1.2 mid hmid
    exact ((h2.2 mid hm.2).2 p hp').2
  have hrow : (Internal.composeTab n t1 t2)[pos]! = Model.dedupFirst ((s1 pos).flatMap s2) := by
    simp only [Internal.composeTab, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn]
    rw [dedupFirstFast_eq n _ hbd, hflat]
  refine ⟨hrow, ?_⟩
  intro p hp
  rw [hrow, dedupFirst_mem_iff, List.mem_flatMap] at hp
  rcases hp with ⟨mid, hmid, hp'⟩
  have hm' : mid ∈ t1[pos]! := by rw [ht1.1]; exact hmid
  have bm := ht1.2 mid hm'
  have hp'' : p ∈ t2[mid]! := by rw [(h2.2 mid bm.2).1]; exact hp'
  have bp := (h2.2 mid bm.2).2 p hp''
  omega

/-- `Internal.altTab` satisfies `TabMatches` for alternation. -/
theorem altTab_matches {n : Nat} {t1 t2 : Array (List Nat)} {s1 s2 : Nat → List Nat}
    (h1 : TabMatches n t1 s1) (h2 : TabMatches n t2 s2) :
    TabMatches n (Internal.altTab n t1 t2) (fun pos => Model.dedupFirst (s1 pos ++ s2 pos)) := by
  refine ⟨by simp [Internal.altTab], ?_⟩
  intro pos hpos
  have ht1 := h1.2 pos hpos
  have ht2 := h2.2 pos hpos
  have hbd : ∀ p ∈ t1[pos]! ++ t2[pos]!, p ≤ n := by
    intro p hp
    rcases List.mem_append.mp hp with hp1 | hp2
    · exact (ht1.2 p hp1).2
    · exact (ht2.2 p hp2).2
  have hrow : (Internal.altTab n t1 t2)[pos]! = Model.dedupFirst (s1 pos ++ s2 pos) := by
    simp only [Internal.altTab, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn]
    rw [dedupFirstFast_eq n _ hbd, ht1.1, ht2.1]
  refine ⟨hrow, ?_⟩
  intro p hp
  rw [hrow, dedupFirst_mem_iff, List.mem_append] at hp
  rcases hp with hp1 | hp2
  · have hp1' : p ∈ t1[pos]! := by rw [ht1.1]; exact hp1
    exact ht1.2 p hp1'
  · have hp2' : p ∈ t2[pos]! := by rw [ht2.1]; exact hp2
    exact ht2.2 p hp2'

/-- `Internal.optStep` satisfies `TabMatches` for one bounded optional step. -/
theorem optStep_matches {n : Nat} {stepTab acc : Array (List Nat)}
    {step g : Nat → List Nat} (hstep : TabMatches n stepTab step) (hacc : TabMatches n acc g)
    (greedy : Bool) :
    TabMatches n (Internal.optStep n stepTab greedy acc)
      (fun pos =>
        let more := Model.dedupFirst ((step pos).flatMap g)
        if greedy then Model.dedupFirst (more ++ [pos]) else Model.dedupFirst (pos :: more)) := by
  refine ⟨by simp [Internal.optStep], ?_⟩
  intro pos hpos
  have hst := hstep.2 pos hpos
  have hflat : (stepTab[pos]!.flatMap fun mid => acc[mid]!) = (step pos).flatMap g := by
    rw [hst.1]
    apply list_flatMap_congr
    intro mid hmid
    have hm' : mid ∈ stepTab[pos]! := by rw [hst.1]; exact hmid
    exact (hacc.2 mid (hst.2 mid hm').2).1
  have hbdMore : ∀ p ∈ (stepTab[pos]!.flatMap fun mid => acc[mid]!), p ≤ n := by
    intro p hp
    rw [List.mem_flatMap] at hp
    rcases hp with ⟨mid, hmid, hp'⟩
    have hm := hst.2 mid hmid
    exact ((hacc.2 mid hm.2).2 p hp').2
  have hmoreEq :
      Internal.dedupFirstFast n (stepTab[pos]!.flatMap fun mid => acc[mid]!) =
        Model.dedupFirst ((step pos).flatMap g) := by
    rw [dedupFirstFast_eq n _ hbdMore, hflat]
  have hmoreBds : ∀ p ∈ Model.dedupFirst ((step pos).flatMap g), pos ≤ p ∧ p ≤ n := by
    intro p hp
    rw [dedupFirst_mem_iff, List.mem_flatMap] at hp
    rcases hp with ⟨mid, hmid, hp'⟩
    have hm' : mid ∈ stepTab[pos]! := by rw [hst.1]; exact hmid
    have bm := hst.2 mid hm'
    have hp'' : p ∈ acc[mid]! := by rw [(hacc.2 mid bm.2).1]; exact hp'
    have bp := (hacc.2 mid bm.2).2 p hp''
    omega
  have hrow :
      (Internal.optStep n stepTab greedy acc)[pos]! =
        let more := Model.dedupFirst ((step pos).flatMap g)
        if greedy then Model.dedupFirst (more ++ [pos]) else Model.dedupFirst (pos :: more) := by
    simp only [Internal.optStep, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, hmoreEq]
    cases greedy
    · have hbd : ∀ p ∈ pos :: Model.dedupFirst ((step pos).flatMap g), p ≤ n := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hpos
        · exact (hmoreBds p hp').2
      simp [dedupFirstFast_eq n _ hbd]
    · have hbd : ∀ p ∈ Model.dedupFirst ((step pos).flatMap g) ++ [pos], p ≤ n := by
        intro p hp
        rcases List.mem_append.mp hp with hp' | hp'
        · exact (hmoreBds p hp').2
        · simp only [List.mem_singleton] at hp'; subst hp'; exact hpos
      simp [dedupFirstFast_eq n _ hbd]
  refine ⟨hrow, ?_⟩
  intro p hp
  rw [hrow] at hp
  dsimp only at hp
  cases greedy <;> simp only [Bool.false_eq_true, ↓reduceIte, dedupFirst_mem_iff] at hp
  · rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨Nat.le_refl _, hpos⟩
    · exact hmoreBds p hp'
  · rcases List.mem_append.mp hp with hp' | hp'
    · exact hmoreBds p hp'
    · simp only [List.mem_singleton] at hp'; subst hp'; exact ⟨Nat.le_refl _, hpos⟩

/-- `k`-fold functional iteration of `F` starting at `g0`. -/
def iterSpec (F : (Nat → List Nat) → (Nat → List Nat)) (g0 : Nat → List Nat) :
    Nat → Nat → List Nat
  | 0 => g0
  | k + 1 => F (iterSpec F g0 k)

private theorem iterSpec_fix {n : Nat} {F : (Nat → List Nat) → (Nat → List Nat)}
    (hExt : ∀ g1 g2, (∀ pos ≤ n, g1 pos = g2 pos) → ∀ pos ≤ n, F g1 pos = F g2 pos)
    {g : Nat → List Nat} (hfix : ∀ pos ≤ n, F g pos = g pos) :
    ∀ k pos, pos ≤ n → iterSpec F g k pos = g pos := by
  intro k
  induction k with
  | zero => intro pos _; rfl
  | succ k ih =>
    intro pos hpos
    calc iterSpec F g (k + 1) pos
        = F (iterSpec F g k) pos := rfl
      _ = F g pos := hExt _ _ ih pos hpos
      _ = g pos := hfix pos hpos

/-- `Internal.iterTab` satisfies `TabMatches` for `iterSpec F g k`. -/
theorem iterTab_matches {n : Nat} {f : Array (List Nat) → Array (List Nat)}
    {F : (Nat → List Nat) → (Nat → List Nat)}
    (hf : ∀ acc g, TabMatches n acc g → TabMatches n (f acc) (F g))
    (hExt : ∀ g1 g2, (∀ pos ≤ n, g1 pos = g2 pos) → ∀ pos ≤ n, F g1 pos = F g2 pos) :
    ∀ k acc g, TabMatches n acc g →
      TabMatches n (Internal.iterTab f k acc) (iterSpec F g k) := by
  intro k
  induction k with
  | zero =>
    intro acc g hacc
    exact hacc
  | succ k ih =>
    intro acc g hacc
    simp only [Internal.iterTab]
    have hnext := hf acc g hacc
    by_cases heq : f acc == acc
    · simp only [heq, ↓reduceIte]
      have heq' : f acc = acc := beq_iff_eq.mp heq
      have hfix : ∀ pos ≤ n, F g pos = g pos := by
        intro pos hpos
        rw [← (hnext.2 pos hpos).1, heq', (hacc.2 pos hpos).1]
      refine ⟨hacc.1, ?_⟩
      intro pos hpos
      rw [iterSpec_fix hExt hfix (k + 1) pos hpos]
      exact hacc.2 pos hpos
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      have hrec := ih (f acc) (F g) hnext
      refine ⟨hrec.1, ?_⟩
      intro pos hpos
      have hspec : ∀ pos ≤ n, iterSpec F (F g) k pos = iterSpec F g (k + 1) pos := by
        clear hrec hnext hacc heq ih
        induction k with
        | zero => intro pos _; rfl
        | succ m ihm =>
          intro pos hpos
          exact hExt _ _ ihm pos hpos
      rw [← hspec pos hpos]
      exact hrec.2 pos hpos

/-- `iterSpec` of sequential composition equals `Model.evalExact`. -/
theorem iterSpec_compose_eq_evalExact (step : Nat → List Nat) :
    ∀ k pos, iterSpec (fun g p => Model.dedupFirst ((step p).flatMap g)) (fun p => [p]) k pos =
      Model.evalExact step k pos := by
  intro k
  induction k with
  | zero => intro pos; rfl
  | succ k ih =>
    intro pos
    simp only [iterSpec, Model.evalExact]
    have hfn : iterSpec (fun g p => Model.dedupFirst ((step p).flatMap g)) (fun p => [p]) k =
        Model.evalExact step k := funext (ih)
    rw [hfn]

/-- `iterSpec` of optional step equals `Model.evalOpt`. -/
theorem iterSpec_opt_eq_evalOpt (step : Nat → List Nat) (greedy : Bool) :
    ∀ k pos, iterSpec
        (fun g p =>
          let more := Model.dedupFirst ((step p).flatMap g)
          if greedy then Model.dedupFirst (more ++ [p]) else Model.dedupFirst (p :: more))
        (fun p => [p]) k pos =
      Model.evalOpt step greedy k pos := by
  intro k
  induction k with
  | zero => intro pos; rfl
  | succ k ih =>
    intro pos
    simp only [iterSpec, Model.evalOpt]
    have hfn : iterSpec
        (fun g p =>
          let more := Model.dedupFirst ((step p).flatMap g)
          if greedy then Model.dedupFirst (more ++ [p]) else Model.dedupFirst (p :: more))
        (fun p => [p]) k = Model.evalOpt step greedy k := funext ih
    rw [hfn]

/-- `Model.evalStarAux` is fuel-independent once `n - q ≤ fuel`. -/
theorem evalStarAux_fuel_indep {n : Nat} {step : Nat → List Nat}
    (hstep : ∀ i j, i ≤ n → j ∈ step i → i ≤ j ∧ j ≤ n) (greedy : Bool) :
    ∀ (d q fuel : Nat), q ≤ n → n - q ≤ d → n - q ≤ fuel →
      Model.evalStarAux step greedy fuel q = Model.evalStarAux step greedy (n - q) q ∧
      ∀ p ∈ Model.evalStarAux step greedy (n - q) q, q ≤ p ∧ p ≤ n := by
  intro d
  induction d with
  | zero =>
    intro q fuel hq hqd hqf
    have hqn : q = n := by omega
    subst hqn
    have hf : Model.evalStarAux step greedy fuel q = [q] := by
      cases fuel with
      | zero => rfl
      | succ fuel' =>
        have hempty : (step q).filter (· > q) = [] := by
          rw [List.filter_eq_nil_iff]
          intro p hp
          have hb := hstep q p (Nat.le_refl _) hp
          simp; omega
        simp only [Model.evalStarAux, hempty, List.flatMap_nil]
        have hd : Model.dedupFirst [] = [] := rfl
        rw [hd]
        cases greedy <;> rfl
    rw [hf]
    simp only [Nat.sub_self, Model.evalStarAux, List.mem_singleton]
    exact ⟨trivial, fun p hp => by subst hp; exact ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
  | succ d ih =>
    intro q fuel hq hqd hqf
    by_cases hqn : q = n
    · have h0 := ih n fuel (Nat.le_refl _) (by omega) (by omega)
      subst hqn
      exact h0
    · have hlt : q < n := Nat.lt_of_le_of_ne hq hqn
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hrem : ∃ r, n - q = r + 1 := ⟨n - q - 1, by omega⟩
      obtain ⟨r, hr⟩ := hrem
      have hrec_eq :
          ((step q).filter (· > q)).flatMap (Model.evalStarAux step greedy f) =
            ((step q).filter (· > q)).flatMap (Model.evalStarAux step greedy r) := by
        apply list_flatMap_congr
        intro p hp
        simp only [List.mem_filter, decide_eq_true_eq] at hp
        have hp_le := (hstep q p hq hp.1).2
        have hp_d : n - p ≤ d := by omega
        have h1 := (ih p f hp_le hp_d (by omega)).1
        have h2 := (ih p r hp_le hp_d (by omega)).1
        rw [h1, h2]
      have hmore_bds :
          ∀ p ∈ Model.dedupFirst (((step q).filter (· > q)).flatMap (Model.evalStarAux step greedy r)),
            q ≤ p ∧ p ≤ n := by
        intro p hp
        rw [dedupFirst_mem_iff, List.mem_flatMap] at hp
        rcases hp with ⟨mid, hmid, hp'⟩
        simp only [List.mem_filter, decide_eq_true_eq] at hmid
        have hm_le := (hstep q mid hq hmid.1).2
        have hp_eq := (ih mid r hm_le (by omega) (by omega)).1
        rw [hp_eq] at hp'
        have bp := (ih mid r hm_le (by omega) (by omega)).2 p hp'
        omega
      constructor
      · rw [hr]
        simp only [Model.evalStarAux, hrec_eq]
      · rw [hr]
        intro p hp
        simp only [Model.evalStarAux] at hp
        cases greedy <;> simp only [Bool.false_eq_true, ↓reduceIte, dedupFirst_mem_iff] at hp
        · rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨Nat.le_refl _, hq⟩
          · exact hmore_bds p hp'
        · rcases List.mem_append.mp hp with hp' | hp'
          · exact hmore_bds p hp'
          · simp only [List.mem_singleton] at hp'; subst hp'; exact ⟨Nat.le_refl _, hq⟩


end LeanSwe.RegExp.Proofs
