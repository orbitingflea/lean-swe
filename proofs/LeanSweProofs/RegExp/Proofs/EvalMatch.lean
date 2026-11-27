import LeanSwe.RegExp.Interface
import LeanSweProofs.RegExp.Model
import LeanSweProofs.RegExp.Proofs.ParserClass
import LeanSweProofs.RegExp.Proofs.EvalCombinators

namespace LeanSwe.RegExp.Proofs

private theorem fillStarAux_matches {n : Nat} {stepTab : Array (List Nat)} {step : Nat → List Nat}
    (hstep : TabMatches n stepTab step) (greedy : Bool) :
    ∀ (rem : Nat) (acc : Array (List Nat)),
      rem ≤ n →
      acc.size = n + 1 →
      (∀ q, rem ≤ q → q ≤ n →
        acc[q]! = Model.evalStarAux step greedy (n - q) q ∧ ∀ p ∈ acc[q]!, q ≤ p ∧ p ≤ n) →
      TabMatches n (Internal.fillStarAux n stepTab greedy rem acc)
        (fun q => Model.evalStarAux step greedy (n - q) q) := by
  intro rem
  induction rem with
  | zero =>
    intro acc _ hs hinv
    refine ⟨hs, ?_⟩
    intro pos hpos
    exact hinv pos (Nat.zero_le _) hpos
  | succ rem ih =>
    intro acc hrem hs hinv
    simp only [Internal.fillStarAux]
    have hlt : rem < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hrem
    have hst := hstep.2 rem (Nat.le_of_lt hlt)
    have hstep_bds : ∀ i j, i ≤ n → j ∈ step i → i ≤ j ∧ j ≤ n := by
      intro i j hi hj
      have hj' : j ∈ stepTab[i]! := by rw [(hstep.2 i hi).1]; exact hj
      exact (hstep.2 i hi).2 j hj'
    have hnext_eq :
        ((stepTab[rem]!).filter (· > rem)).flatMap (fun q => acc[q]!) =
          ((step rem).filter (· > rem)).flatMap (Model.evalStarAux step greedy (n - rem - 1)) := by
      rw [hst.1]
      apply list_flatMap_congr
      intro q hq
      simp only [List.mem_filter, decide_eq_true_eq] at hq
      have hq_le := (hstep_bds rem q (Nat.le_of_lt hlt) hq.1).2
      have hq_acc := (hinv q hq.2 hq_le).1
      have hq_fuel := (evalStarAux_fuel_indep hstep_bds greedy (n - q) q (n - rem - 1)
        hq_le (Nat.le_refl _) (by omega)).1
      rw [hq_acc, hq_fuel]
    have hbdMore : ∀ p ∈ ((stepTab[rem]!).filter (· > rem)).flatMap (fun q => acc[q]!), p ≤ n := by
      intro p hp
      rw [List.mem_flatMap] at hp
      rcases hp with ⟨q, hq, hp'⟩
      simp only [List.mem_filter, decide_eq_true_eq] at hq
      have hq_le := (hst.2 q hq.1).2
      exact ((hinv q hq.2 hq_le).2 p hp').2
    have hmoreEq :
        Internal.dedupFirstFast n (((stepTab[rem]!).filter (· > rem)).flatMap fun q => acc[q]!) =
          Model.dedupFirst (((step rem).filter (· > rem)).flatMap (Model.evalStarAux step greedy (n - rem - 1))) := by
      rw [dedupFirstFast_eq n _ hbdMore, hnext_eq]
    have hrow_eq :
        (if greedy then
            Internal.dedupFirstFast n
              (Internal.dedupFirstFast n (((stepTab[rem]!).filter (· > rem)).flatMap fun q => acc[q]!) ++ [rem])
          else
            Internal.dedupFirstFast n
              (rem :: Internal.dedupFirstFast n (((stepTab[rem]!).filter (· > rem)).flatMap fun q => acc[q]!))) =
          Model.evalStarAux step greedy (n - rem) rem := by
      have hsub : n - rem = (n - rem - 1) + 1 := by omega
      rw [hsub, Model.evalStarAux, hmoreEq]
      have hmore_le :
          ∀ p ∈ Model.dedupFirst (((step rem).filter (· > rem)).flatMap (Model.evalStarAux step greedy (n - rem - 1))),
            p ≤ n := by
        intro p hp
        rw [dedupFirst_mem_iff, List.mem_flatMap] at hp
        rcases hp with ⟨q, hq, hp'⟩
        simp only [List.mem_filter, decide_eq_true_eq] at hq
        have hq_le := (hstep_bds rem q (Nat.le_of_lt hlt) hq.1).2
        have hq_fuel := (evalStarAux_fuel_indep hstep_bds greedy (n - q) q (n - rem - 1)
          hq_le (Nat.le_refl _) (by omega)).1
        rw [hq_fuel] at hp'
        exact ((evalStarAux_fuel_indep hstep_bds greedy (n - q) q (n - rem - 1)
          hq_le (Nat.le_refl _) (by omega)).2 p hp').2
      cases hgr : greedy
      · have hbd :
            ∀ p ∈ rem :: Model.dedupFirst
              (((step rem).filter (· > rem)).flatMap (Model.evalStarAux step false (n - rem - 1))), p ≤ n := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact Nat.le_of_lt hlt
          · rw [← hgr] at hp'; exact hmore_le p hp'
        simp [dedupFirstFast_eq n _ hbd]
      · have hbd :
            ∀ p ∈ Model.dedupFirst
              (((step rem).filter (· > rem)).flatMap (Model.evalStarAux step true (n - rem - 1))) ++ [rem], p ≤ n := by
          intro p hp
          rcases List.mem_append.mp hp with hp' | hp'
          · rw [← hgr] at hp'; exact hmore_le p hp'
          · simp only [List.mem_singleton] at hp'; subst hp'; exact Nat.le_of_lt hlt
        simp [dedupFirstFast_eq n _ hbd]
    have hrow_bds : ∀ p ∈ Model.evalStarAux step greedy (n - rem) rem, rem ≤ p ∧ p ≤ n :=
      (evalStarAux_fuel_indep hstep_bds greedy (n - rem) rem (n - rem) (Nat.le_of_lt hlt)
        (Nat.le_refl _) (Nat.le_refl _)).2
    apply ih _ (by omega) (by simp [hs])
    intro q hqr hqn
    have hqs : q < acc.size := by omega
    simp only [getElem!_pos, Array.size_setIfInBounds, hqs, Array.getElem_setIfInBounds]
    by_cases heq : q = rem
    · subst heq
      simp only [↓reduceIte, hrow_eq]
      exact ⟨trivial, hrow_bds⟩
    · have hne : rem ≠ q := Ne.symm heq
      have hgt : rem + 1 ≤ q := by omega
      simp only [hne, ↓reduceIte]
      have hget := arr_getElem! acc q hqs
      rw [← hget]
      exact hinv q hgt hqn

private theorem starTab_matches {n : Nat} {stepTab : Array (List Nat)} {step : Nat → List Nat}
    (hstep : TabMatches n stepTab step) (greedy : Bool) :
    TabMatches n (Internal.starTab n stepTab greedy)
      (fun p => Model.evalStarAux step greedy (n - p) p) := by
  unfold Internal.starTab
  apply fillStarAux_matches hstep greedy n (Array.replicate (n + 1) [n]) (Nat.le_refl _) (by simp)
  intro q hnq hqn
  have hq : q = n := by omega
  subst hq
  simp only [Nat.sub_self, Model.evalStarAux, getElem!_pos, Array.size_replicate,
    Nat.lt_succ_self, Array.getElem_replicate, List.mem_singleton]
  exact ⟨trivial, fun p hp => by subst hp; exact ⟨Nat.le_refl _, Nat.le_refl _⟩⟩

/-- `Internal.evalTable` satisfies `TabMatches` against `Model.evalAt`. -/
theorem evalTable_matches (chars : Array Char) (ast : Internal.RegexAst) :
    TabMatches chars.size (Internal.evalTable chars ast)
      (Model.evalAt chars.toList (toModel ast)) := by
  induction ast with
  | empty => exact idTab_matches chars.size
  | char atom =>
    refine ⟨by simp [Internal.evalTable], ?_⟩
    intro pos hpos
    have hget : chars[pos]? = chars.toList[pos]? := by simp
    simp only [Internal.evalTable, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, Model.evalAt, toModel, hget]
    cases hch : chars.toList[pos]? with
    | none => simp
    | some c =>
      simp only [charAtomMatches_eq atom c]
      split
      · simp only [List.mem_singleton]
        have hlt : pos < chars.toList.length := (List.getElem?_eq_some_iff.mp hch).1
        have hlt' : pos < chars.size := by simpa using hlt
        exact ⟨trivial, fun p hp => by subst hp; omega⟩
      · simp
  | anchorStart =>
    refine ⟨by simp [Internal.evalTable], ?_⟩
    intro pos hpos
    simp only [Internal.evalTable, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, Model.evalAt, toModel]
    by_cases h0 : pos = 0
    · subst h0; simp
    · simp [h0]
  | anchorEnd =>
    refine ⟨by simp [Internal.evalTable], ?_⟩
    intro pos hpos
    simp only [Internal.evalTable, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, Model.evalAt, toModel, Array.length_toList]
    by_cases he : pos = chars.size
    · subst he; simp
    · simp [he]
  | wordBoundary positive =>
    refine ⟨by simp [Internal.evalTable], ?_⟩
    intro pos hpos
    simp only [Internal.evalTable, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, Model.evalAt, toModel, isWordBoundary_eq]
    split
    · simp only [List.mem_singleton]
      exact ⟨trivial, fun p hp => by subst hp; exact ⟨Nat.le_refl _, hpos⟩⟩
    · simp
  | seq r1 r2 ih1 ih2 =>
    exact composeTab_matches ih1 ih2
  | alt r1 r2 ih1 ih2 =>
    exact altTab_matches ih1 ih2
  | rep inner minVal max? greedy ih =>
    simp only [Internal.evalTable, Model.evalAt, toModel]
    have hcomposeExt :
        ∀ g1 g2 : Nat → List Nat, (∀ pos ≤ chars.size, g1 pos = g2 pos) →
          ∀ pos ≤ chars.size,
            Model.dedupFirst ((Model.evalAt chars.toList (toModel inner) pos).flatMap g1) =
              Model.dedupFirst ((Model.evalAt chars.toList (toModel inner) pos).flatMap g2) := by
      intro g1 g2 hg pos hpos
      congr 1
      apply list_flatMap_congr
      intro mid hmid
      have hm' : mid ∈ (Internal.evalTable chars inner)[pos]! := by rw [(ih.2 pos hpos).1]; exact hmid
      exact hg mid ((ih.2 pos hpos).2 mid hm').2
    have hbase :=
      iterTab_matches (fun acc g ha => composeTab_matches ih ha) hcomposeExt minVal
        (Internal.idTab chars.size) (fun p => [p]) (idTab_matches chars.size)
    have hbase' :
        TabMatches chars.size
          (Internal.iterTab (Internal.composeTab chars.size (Internal.evalTable chars inner)) minVal
            (Internal.idTab chars.size))
          (Model.evalExact (Model.evalAt chars.toList (toModel inner)) minVal) := by
      refine ⟨hbase.1, ?_⟩
      intro pos hpos
      rw [← iterSpec_compose_eq_evalExact]
      exact hbase.2 pos hpos
    cases max? with
    | none =>
      exact composeTab_matches hbase' (starTab_matches ih greedy)
    | some maxVal =>
      by_cases hlt : maxVal < minVal
      · simp only [hlt, ↓reduceIte]
        refine ⟨by simp, ?_⟩
        intro pos hpos
        have hlt' : pos < (Array.replicate (chars.size + 1) ([] : List Nat)).size := by simp; omega
        have hget := arr_getElem! (Array.replicate (chars.size + 1) ([] : List Nat)) pos hlt'
        simp [hget]
      · simp only [hlt, ↓reduceIte]
        have hoptExt :
            ∀ g1 g2 : Nat → List Nat, (∀ pos ≤ chars.size, g1 pos = g2 pos) →
              ∀ pos ≤ chars.size,
                (let more := Model.dedupFirst ((Model.evalAt chars.toList (toModel inner) pos).flatMap g1)
                 if greedy then Model.dedupFirst (more ++ [pos]) else Model.dedupFirst (pos :: more)) =
                (let more := Model.dedupFirst ((Model.evalAt chars.toList (toModel inner) pos).flatMap g2)
                 if greedy then Model.dedupFirst (more ++ [pos]) else Model.dedupFirst (pos :: more)) := by
          intro g1 g2 hg pos hpos
          have heq := hcomposeExt g1 g2 hg pos hpos
          dsimp only
          rw [heq]
        have hopt :=
          iterTab_matches (fun acc g ha => optStep_matches ih ha greedy) hoptExt
            (maxVal - minVal) (Internal.idTab chars.size) (fun p => [p]) (idTab_matches chars.size)
        have hopt' :
            TabMatches chars.size
              (Internal.iterTab (Internal.optStep chars.size (Internal.evalTable chars inner) greedy)
                (maxVal - minVal) (Internal.idTab chars.size))
              (Model.evalOpt (Model.evalAt chars.toList (toModel inner)) greedy (maxVal - minVal)) := by
          refine ⟨hopt.1, ?_⟩
          intro pos hpos
          rw [← iterSpec_opt_eq_evalOpt]
          exact hopt.2 pos hpos
        exact composeTab_matches hbase' hopt'

private theorem findFirstIdxAux_eq {n : Nat} {tab : Array (List Nat)} {r : Model.Regex}
    {cs : List Char} (ht : TabMatches n tab (Model.evalAt cs r)) :
    ∀ rem pos, pos + rem = n →
      Internal.findFirstIdxAux tab rem pos = Model.findFirstIdxAux r cs rem pos ∧
      (∀ i j, Internal.findFirstIdxAux tab rem pos = some (i, j) → pos ≤ i ∧ i ≤ j ∧ j ≤ n) := by
  intro rem
  induction rem with
  | zero =>
    intro pos hsum
    have hpos : pos ≤ n := by omega
    rw [Internal.findFirstIdxAux, Model.findFirstIdxAux, (ht.2 pos hpos).1]
    refine ⟨rfl, ?_⟩
    intro i j hij
    cases hrow : Model.evalAt cs r pos with
    | nil => simp [hrow] at hij
    | cons p rest =>
      simp only [hrow, Option.some.injEq, Prod.mk.injEq] at hij
      rcases hij with ⟨rfl, rfl⟩
      have hp : p ∈ tab[pos]! := by rw [(ht.2 pos hpos).1, hrow]; simp
      have bp := (ht.2 pos hpos).2 p hp
      exact ⟨Nat.le_refl _, bp.1, bp.2⟩
  | succ rem ih =>
    intro pos hsum
    have hpos : pos ≤ n := by omega
    rw [Internal.findFirstIdxAux, Model.findFirstIdxAux, (ht.2 pos hpos).1]
    cases hrow : Model.evalAt cs r pos with
    | nil =>
      simp only
      have hrec := ih (pos + 1) (by omega)
      refine ⟨hrec.1, ?_⟩
      intro i j hij
      have b := hrec.2 i j hij
      omega
    | cons p rest =>
      simp only
      refine ⟨trivial, ?_⟩
      intro i j hij
      have hij' : pos = i ∧ p = j := by simpa [hrow] using hij
      rcases hij' with ⟨rfl, rfl⟩
      have hp' : p ∈ tab[pos]! := by rw [(ht.2 pos hpos).1, hrow]; simp
      have bp := (ht.2 pos hpos).2 p hp'
      exact ⟨Nat.le_refl _, bp.1, bp.2⟩

/-- `Internal.findFirstIdx` equals `Model.findFirstIdx` with in-bounds match indices. -/
theorem findFirstIdx_eq (chars : Array Char) (ast : Internal.RegexAst) (start : Nat) :
    Internal.findFirstIdx (Internal.evalTable chars ast) chars.size start =
      Model.findFirstIdx (toModel ast) chars.toList start ∧
    (∀ i j, Internal.findFirstIdx (Internal.evalTable chars ast) chars.size start = some (i, j) →
      start ≤ i ∧ i ≤ j ∧ j ≤ chars.size) := by
  unfold Internal.findFirstIdx Model.findFirstIdx
  simp only [Array.length_toList]
  by_cases hs : start ≤ chars.size
  · simp only [hs, ↓reduceIte]
    exact findFirstIdxAux_eq (evalTable_matches chars ast) (chars.size - start) start (by omega)
  · simp [hs]

private theorem findAllIdxAux_eq (chars : Array Char) (ast : Internal.RegexAst) :
    ∀ fuel cursor,
      Internal.findAllIdxAux (Internal.evalTable chars ast) chars.size fuel cursor =
        Model.findAllIdxAux (toModel ast) chars.toList fuel cursor ∧
      ∀ sp ∈ Internal.findAllIdxAux (Internal.evalTable chars ast) chars.size fuel cursor,
        sp.1 ≤ sp.2 ∧ sp.2 ≤ chars.size := by
  intro fuel
  induction fuel with
  | zero => intro cursor; simp [Internal.findAllIdxAux, Model.findAllIdxAux]
  | succ fuel ih =>
    intro cursor
    rw [Internal.findAllIdxAux, Model.findAllIdxAux]
    have hf := findFirstIdx_eq chars ast cursor
    rw [hf.1]
    cases hres : Model.findFirstIdx (toModel ast) chars.toList cursor with
    | none => simp
    | some v =>
      obtain ⟨i, j⟩ := v
      have hbd := hf.2 i j (by rw [hf.1, hres])
      simp only [Array.length_toList]
      split
      · simp only [List.mem_cons]
        have hrec := ih j
        refine ⟨congrArg ((i, j) :: ·) hrec.1, ?_⟩
        rintro sp (rfl | hsp)
        · exact ⟨hbd.2.1, hbd.2.2⟩
        · exact hrec.2 sp hsp
      · split
        · simp only [List.mem_cons]
          have hrec := ih (j + 1)
          refine ⟨congrArg ((i, j) :: ·) hrec.1, ?_⟩
          rintro sp (rfl | hsp)
          · exact ⟨hbd.2.1, hbd.2.2⟩
          · exact hrec.2 sp hsp
        · simp [hbd.2.1, hbd.2.2]

/-- `Internal.findAllIdx` equals `Model.findAllIdx` with in-bounds spans. -/
theorem findAllIdx_eq (chars : Array Char) (ast : Internal.RegexAst) :
    Internal.findAllIdx chars ast = Model.findAllIdx (toModel ast) chars.toList ∧
    ∀ sp ∈ Internal.findAllIdx chars ast, sp.1 ≤ sp.2 ∧ sp.2 ≤ chars.size := by
  unfold Internal.findAllIdx Model.findAllIdx
  simpa [Array.length_toList] using findAllIdxAux_eq chars ast (chars.size + 1) 0

/-- `Internal.mkMatchSpanFast` equals `Model.mkMatchSpan` on valid indices. -/
theorem mkMatchSpanFast_eq (chars : Array Char) {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ chars.size) :
    Internal.mkMatchSpanFast chars (Internal.buildByteOffsets chars) i j =
      Model.mkMatchSpan chars.toList i j := by
  have hb := buildByteOffsets_spec chars
  unfold Internal.mkMatchSpanFast Model.mkMatchSpan
  rw [Array.toList_extract, List.extract_eq_take_drop,
    hb.2 i (Nat.le_trans hij hj), hb.2 j hj]

private theorem list_extract_prefix {α : Type _} (xs : Array α) (cursor i : Nat) :
    (xs.extract cursor i).toList = (xs.toList.drop cursor).take (i - cursor) := by
  rw [Array.toList_extract, List.extract_eq_take_drop]

/-- `Internal.replaceSpansFast` equals `Model.replaceSpans`. -/
theorem replaceSpansFast_eq (chars : Array Char) (rep : String) :
    ∀ (cursor : Nat) (spans : List (Nat × Nat)),
      Internal.replaceSpansFast chars rep cursor spans =
        Model.replaceSpans chars.toList rep cursor spans := by
  intro cursor spans
  induction spans generalizing cursor with
  | nil =>
    simp only [Internal.replaceSpansFast, Model.replaceSpans, list_extract_prefix]
    rw [List.take_of_length_le (by simp)]
  | cons sp rest ih =>
    obtain ⟨i, j⟩ := sp
    simp only [Internal.replaceSpansFast, Model.replaceSpans, list_extract_prefix]
    rw [ih j]

/-- `Internal.splitSpansFast` equals `Model.splitSpans`. -/
theorem splitSpansFast_eq (chars : Array Char) :
    ∀ (cursor : Nat) (spans : List (Nat × Nat)),
      Internal.splitSpansFast chars cursor spans =
        Model.splitSpans chars.toList cursor spans := by
  intro cursor spans
  induction spans generalizing cursor with
  | nil =>
    simp only [Internal.splitSpansFast, Model.splitSpans, list_extract_prefix]
    rw [List.take_of_length_le (by simp)]
  | cons sp rest ih =>
    obtain ⟨i, j⟩ := sp
    simp only [Internal.splitSpansFast, Model.splitSpans, list_extract_prefix]
    rw [ih j]


end LeanSwe.RegExp.Proofs
