import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.SpecTests

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model

private def ValidSeg (s : String) : Prop :=
  s ≠ "" ∧ s ≠ "." ∧ s ≠ ".." ∧ '/' ∉ s.toList ∧ hasNulChar s.toList = false

private theorem hasNulChar_append (xs ys : List Char) :
    hasNulChar (xs ++ ys) = (hasNulChar xs || hasNulChar ys) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    simp [hasNulChar, ih, Bool.or_assoc]

private theorem hasNulChar_reverse (cs : List Char) :
    hasNulChar cs.reverse = hasNulChar cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [hasNulChar_append, hasNulChar, ih, Bool.or_comm]

private theorem splitSlashAux_no_slash (acc cs : List Char) (hacc : '/' ∉ acc) :
    ∀ seg ∈ splitSlashAux acc cs, '/' ∉ seg := by
  induction cs generalizing acc with
  | nil =>
    intro seg hmem
    simp only [splitSlashAux, List.mem_singleton] at hmem
    subst hmem
    simpa [List.mem_reverse] using hacc
  | cons c cs ih =>
    simp only [splitSlashAux]
    split
    · intro seg hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simpa [List.mem_reverse] using hacc
      · exact ih [] (by simp) seg hmem
    · next hne =>
      have hc : c ≠ '/' := fun h => hne (by subst h; rfl)
      have hacc' : '/' ∉ c :: acc := by simp [hacc, hc.symm]
      exact ih (c :: acc) hacc'

private theorem splitSlashAux_no_nul (acc cs : List Char)
    (hacc : hasNulChar acc = false) (hcs : hasNulChar cs = false) :
    ∀ seg ∈ splitSlashAux acc cs, hasNulChar seg = false := by
  induction cs generalizing acc with
  | nil =>
    intro seg hmem
    simp only [splitSlashAux, List.mem_singleton] at hmem
    subst hmem
    rw [hasNulChar_reverse]
    exact hacc
  | cons c cs ih =>
    simp only [hasNulChar, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hcs
    simp only [splitSlashAux]
    split
    · intro seg hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · rw [hasNulChar_reverse]
        exact hacc
      · exact ih [] rfl hcs.2 seg hmem
    · have hacc' : hasNulChar (c :: acc) = false := by
        simp [hasNulChar, beq_false_of_ne hcs.1, hacc]
      exact ih (c :: acc) hacc' hcs.2

private theorem splitSlashAux_append_slash (acc a b : List Char) (ha : '/' ∉ a) :
    splitSlashAux acc (a ++ '/' :: b) = (acc.reverse ++ a) :: splitSlashAux [] b := by
  induction a generalizing acc with
  | nil => simp [splitSlashAux]
  | cons c a ih =>
    have hc : c ≠ '/' := fun h => ha (by subst h; simp)
    have ha' : '/' ∉ a := fun h => ha (by simp [h])
    have hbeq : (c == '/') = false := beq_false_of_ne hc
    simp only [List.cons_append, splitSlashAux, hbeq, Bool.false_eq_true, ↓reduceIte]
    rw [ih (c :: acc) ha']
    simp [List.reverse_cons, List.append_assoc]

private theorem splitSlashAux_of_no_slash (acc a : List Char) (ha : '/' ∉ a) :
    splitSlashAux acc a = [acc.reverse ++ a] := by
  induction a generalizing acc with
  | nil => simp [splitSlashAux]
  | cons c a ih =>
    have hc : c ≠ '/' := fun h => ha (by subst h; simp)
    have ha' : '/' ∉ a := fun h => ha (by simp [h])
    have hbeq : (c == '/') = false := beq_false_of_ne hc
    simp only [splitSlashAux, hbeq, Bool.false_eq_true, ↓reduceIte]
    rw [ih (c :: acc) ha']
    simp [List.reverse_cons, List.append_assoc]

private theorem splitSlashChars_intercalate (segs : List String) (hne : segs ≠ [])
    (hno : ∀ s ∈ segs, '/' ∉ s.toList) :
    splitSlashChars (String.intercalate "/" segs).toList = segs.map String.toList := by
  match segs with
  | [] => exact absurd rfl hne
  | [s] =>
    simp only [String.intercalate_singleton, splitSlashChars, List.map_cons, List.map_nil]
    simpa using splitSlashAux_of_no_slash [] s.toList (hno s (by simp))
  | s :: r :: rest =>
    rw [String.intercalate_cons_cons]
    have hinter : (s ++ "/" ++ String.intercalate "/" (r :: rest)).toList =
        s.toList ++ '/' :: (String.intercalate "/" (r :: rest)).toList := by
      simp [String.toList_append, List.append_assoc]
    rw [splitSlashChars, hinter, splitSlashAux_append_slash [] s.toList _ (hno s (by simp))]
    simp only [List.reverse_nil, List.nil_append]
    have ih := splitSlashChars_intercalate (r :: rest) (by simp) (fun x hx => hno x (by simp [hx]))
    rw [splitSlashChars] at ih
    rw [ih]
    rfl

private theorem hasNulChar_intercalate (segs : List String)
    (hno : ∀ s ∈ segs, hasNulChar s.toList = false) :
    hasNulChar (String.intercalate "/" segs).toList = false := by
  match segs with
  | [] => simp [String.intercalate_nil, hasNulChar]
  | [s] =>
    simp only [String.intercalate_singleton]
    exact hno s (by simp)
  | s :: r :: rest =>
    rw [String.intercalate_cons_cons]
    have hinter : (s ++ "/" ++ String.intercalate "/" (r :: rest)).toList =
        s.toList ++ '/' :: (String.intercalate "/" (r :: rest)).toList := by
      simp [String.toList_append, List.append_assoc]
    rw [hinter, hasNulChar_append, hno s (by simp), Bool.false_or]
    simp only [hasNulChar, beq_false_of_ne (by decide : '/' ≠ Char.ofNat 0), Bool.false_or]
    exact hasNulChar_intercalate (r :: rest) (fun x hx => hno x (by simp [hx]))

private theorem filterMap_validSegs (xs : List String) (hvalid : ∀ x ∈ xs, ValidSeg x) :
    (xs.map String.toList).filterMap (fun x =>
      if x.isEmpty || x == ['.'] then none else some (String.ofList x)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : ValidSeg x := hvalid x (by simp)
    have hxEmpty : x.toList.isEmpty = false := by
      cases htl : x.toList with
      | nil =>
        exfalso
        exact hx.1 (String.toList_injective htl)
      | cons _ _ => rfl
    have hxDot : (x.toList == ['.']) = false := by
      rw [beq_eq_false_iff_ne]
      intro hdot
      exact hx.2.1 (String.toList_injective hdot)
    simp only [List.map_cons, List.filterMap_cons, hxEmpty, hxDot, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte, String.ofList_toList]
    exact congrArg (x :: ·) (ih (fun y hy => hvalid y (by simp [hy])))

private theorem parseCleanAbsSegs_formatAbsSegs (segs : List String)
    (hvalid : ∀ s ∈ segs, ValidSeg s) :
    parseCleanAbsSegs (formatAbsSegs segs) = some segs := by
  cases segs with
  | nil => rfl
  | cons s rest =>
    have hnoSlash : ∀ x ∈ s :: rest, '/' ∉ x.toList := fun x hx => (hvalid x hx).2.2.2.1
    have hnoNul : ∀ x ∈ s :: rest, hasNulChar x.toList = false := fun x hx => (hvalid x hx).2.2.2.2
    have hFmtList : (formatAbsSegs (s :: rest)).toList =
        '/' :: (String.intercalate "/" (s :: rest)).toList := by
      simp [formatAbsSegs, String.toList_append]
    have hInterNul : hasNulChar (String.intercalate "/" (s :: rest)).toList = false :=
      hasNulChar_intercalate (s :: rest) hnoNul
    have hNulAll : hasNulChar ('/' :: (String.intercalate "/" (s :: rest)).toList) = false := by
      simp only [hasNulChar, beq_false_of_ne (by decide : '/' ≠ Char.ofNat 0), Bool.false_or,
        hInterNul]
    have hSplit := splitSlashChars_intercalate (s :: rest) (by simp) hnoSlash
    have hNoDotDot : ((s :: rest).map String.toList).any (fun x => x == ['.', '.']) = false := by
      rw [Bool.eq_false_iff]
      intro hAny
      rw [List.any_eq_true] at hAny
      rcases hAny with ⟨cs, hcs, hEq⟩
      rw [List.mem_map] at hcs
      rcases hcs with ⟨x, hx, rfl⟩
      have hdot : x.toList = ['.', '.'] := beq_iff_eq.mp hEq
      have hStr : x = ".." := String.toList_injective hdot
      exact (hvalid x hx).2.2.1 hStr
    have hFilter := filterMap_validSegs (s :: rest) hvalid
    unfold parseCleanAbsSegs
    simp only [hFmtList, List.isEmpty_cons, hNulAll, List.head?_cons, bne_self_eq_false,
      Bool.or_self, Bool.false_eq_true, ↓reduceIte, List.tail_cons, hSplit, hNoDotDot, hFilter]

private theorem parseCleanAbsSegs_validSegs (p : String) (segs : List String)
    (hp : parseCleanAbsSegs p = some segs) :
    ∀ s ∈ segs, ValidSeg s := by
  unfold parseCleanAbsSegs at hp
  dsimp only at hp
  by_cases hBad : (p.toList.isEmpty || hasNulChar p.toList || p.toList.head? != some '/') = true
  · simp [hBad] at hp
  · have hFBad : (p.toList.isEmpty || hasNulChar p.toList || p.toList.head? != some '/') = false :=
      Bool.eq_false_iff.mpr hBad
    simp only [hFBad, Bool.false_eq_true, ↓reduceIte] at hp
    simp only [Bool.or_eq_false_iff] at hFBad
    have hcsNotEmpty : p.toList.isEmpty = false := hFBad.1.1
    have hnoNul : hasNulChar p.toList = false := hFBad.1.2
    have htailNul : hasNulChar p.toList.tail = false := by
      cases hpList : p.toList with
      | nil => simp [hpList] at hcsNotEmpty
      | cons c cs =>
        rw [hpList, hasNulChar, Bool.or_eq_false_iff] at hnoNul
        simpa [hpList] using hnoNul.2
    by_cases hDD : (splitSlashChars p.toList.tail).any (fun s => s == ['.', '.']) = true
    · simp [hDD] at hp
    · have hNoDD : (splitSlashChars p.toList.tail).any (fun s => s == ['.', '.']) = false :=
        Bool.eq_false_iff.mpr hDD
      simp only [hNoDD, Bool.false_eq_true, ↓reduceIte] at hp
      injection hp with hEq
      subst hEq
      intro s hs
      rw [List.mem_filterMap] at hs
      rcases hs with ⟨cs, hcsMem, hcsRes⟩
      by_cases hSkip : (cs.isEmpty || cs == ['.']) = true
      · simp [hSkip] at hcsRes
      · have hNoSkip : (cs.isEmpty || cs == ['.']) = false := Bool.eq_false_iff.mpr hSkip
        simp only [hNoSkip, Bool.false_eq_true, ↓reduceIte] at hcsRes
        injection hcsRes with hsEq
        subst hsEq
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hNoSkip
        have hNoSlash : '/' ∉ cs := splitSlashAux_no_slash [] p.toList.tail (by simp) cs hcsMem
        have hNoNulCs : hasNulChar cs = false :=
          splitSlashAux_no_nul [] p.toList.tail rfl htailNul cs hcsMem
        have hNotEmptyCs : cs ≠ [] := by cases cs <;> simp_all
        have hNotDotCs : cs ≠ ['.'] := hNoSkip.2
        have hNotDotDotCs : cs ≠ ['.', '.'] := by
          intro hdd
          apply Bool.eq_false_iff.mp hNoDD
          rw [List.any_eq_true]
          exact ⟨cs, hcsMem, beq_iff_eq.mpr hdd⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro hEmp
          apply hNotEmptyCs
          simpa using congrArg String.toList hEmp
        · intro hDot
          apply hNotDotCs
          simpa [String.toList_ofList] using congrArg String.toList hDot
        · intro hDotDot
          apply hNotDotDotCs
          simpa [String.toList_ofList] using congrArg String.toList hDotDot
        · simpa [String.toList_ofList] using hNoSlash
        · simpa [String.toList_ofList] using hNoNulCs

private theorem parseSafePresetTargetSegs_validSegs (target : String) (segs : List String)
    (ht : parseSafePresetTargetSegs target = some segs) :
    ∀ s ∈ segs, ValidSeg s := by
  unfold parseSafePresetTargetSegs at ht
  dsimp only at ht
  by_cases hBad : (target.toList.isEmpty || hasNulChar target.toList) = true
  · simp [hBad] at ht
  · have hFBad : (target.toList.isEmpty || hasNulChar target.toList) = false :=
      Bool.eq_false_iff.mpr hBad
    simp only [hFBad, Bool.false_eq_true, ↓reduceIte] at ht
    simp only [Bool.or_eq_false_iff] at hFBad
    have hnoNul : hasNulChar target.toList = false := hFBad.2
    let body := if target.toList.head? == some '/' then target.toList.tail else target.toList
    have hBodyNul : hasNulChar body = false := by
      dsimp only [body]
      split
      · cases htList : target.toList with
        | nil => rfl
        | cons c cs =>
          rw [htList, hasNulChar, Bool.or_eq_false_iff] at hnoNul
          simpa using hnoNul.2
      · exact hnoNul
    change (let rawSegs := splitSlashChars body
      if rawSegs.any (fun s => s == ['.', '.']) then none
      else
        let clean := rawSegs.filterMap fun s =>
          if s.isEmpty || s == ['.'] then none else some (String.ofList s)
        if clean.isEmpty then none else some clean) = some segs at ht
    by_cases hDD : (splitSlashChars body).any (fun s => s == ['.', '.']) = true
    · simp only [hDD, ↓reduceIte] at ht
      cases ht
    · have hNoDD : (splitSlashChars body).any (fun s => s == ['.', '.']) = false :=
        Bool.eq_false_iff.mpr hDD
      simp only [hNoDD, Bool.false_eq_true, ↓reduceIte] at ht
      let clean := (splitSlashChars body).filterMap fun s =>
        if s.isEmpty || s == ['.'] then none else some (String.ofList s)
      change (if clean.isEmpty then none else some clean) = some segs at ht
      by_cases hCleanEmpty : clean.isEmpty = true
      · rw [ite_eq_left hCleanEmpty] at ht
        cases ht
      · have hCleanNE : clean.isEmpty = false := Bool.eq_false_iff.mpr hCleanEmpty
        rw [ite_eq_right (by simp [hCleanNE])] at ht
        injection ht with hEq
        subst hEq
        intro s hs
        dsimp only [clean] at hs
        rw [List.mem_filterMap] at hs
        rcases hs with ⟨cs, hcsMem, hcsRes⟩
        by_cases hSkip : (cs.isEmpty || cs == ['.']) = true
        · simp [hSkip] at hcsRes
        · have hNoSkip : (cs.isEmpty || cs == ['.']) = false := Bool.eq_false_iff.mpr hSkip
          simp only [hNoSkip, Bool.false_eq_true, ↓reduceIte] at hcsRes
          injection hcsRes with hsEq
          subst hsEq
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hNoSkip
          have hNoSlash : '/' ∉ cs := splitSlashAux_no_slash [] body (by simp) cs hcsMem
          have hNoNulCs : hasNulChar cs = false :=
            splitSlashAux_no_nul [] body rfl hBodyNul cs hcsMem
          have hNotEmptyCs : cs ≠ [] := by cases cs <;> simp_all
          have hNotDotCs : cs ≠ ['.'] := hNoSkip.2
          have hNotDotDotCs : cs ≠ ['.', '.'] := by
            intro hdd
            apply Bool.eq_false_iff.mp hNoDD
            rw [List.any_eq_true]
            exact ⟨cs, hcsMem, beq_iff_eq.mpr hdd⟩
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro hEmp
            apply hNotEmptyCs
            simpa using congrArg String.toList hEmp
          · intro hDot
            apply hNotDotCs
            simpa [String.toList_ofList] using congrArg String.toList hDot
          · intro hDotDot
            apply hNotDotDotCs
            simpa [String.toList_ofList] using congrArg String.toList hDotDot
          · simpa [String.toList_ofList] using hNoSlash
          · simpa [String.toList_ofList] using hNoNulCs

private theorem expandPresetTopSymlink_validSegs (entries : List PresetSystemEntry)
    (segs : List String) (hvalid : ∀ s ∈ segs, ValidSeg s) :
    ∀ s ∈ expandPresetTopSymlink entries segs, ValidSeg s := by
  cases segs with
  | nil => intro s hs; cases hs
  | cons top rest =>
    unfold expandPresetTopSymlink
    dsimp only
    split
    · split
      · next hTarget =>
        intro s hs
        rcases List.mem_append.mp hs with hsT | hsR
        · exact parseSafePresetTargetSegs_validSegs _ _ hTarget s hsT
        · exact hvalid s (List.mem_cons_of_mem top hsR)
      · exact hvalid
    · exact hvalid

private theorem lookupFsBytes_putFsBytes_eq (fs : List (String × ByteArray))
    (p : String) (data : ByteArray) :
    lookupFsBytes (putFsBytes fs p data) p = some data := by
  unfold lookupFsBytes putFsBytes
  split
  · next hAny =>
    induction fs with
    | nil => simp at hAny
    | cons kv rest ih =>
      simp only [List.any_cons, Bool.or_eq_true] at hAny
      by_cases hHead : (kv.1 == p) = true
      · simp only [List.map_cons, hHead, ↓reduceIte, List.find?_cons, beq_self_eq_true, Option.map_some]
      · have hFalse : (kv.1 == p) = false := Bool.eq_false_iff.mpr hHead
        have hRest : rest.any (fun kv => kv.1 == p) = true := by
          rcases hAny with h1 | h2
          · exact absurd h1 hHead
          · exact h2
        simp only [List.map_cons, hFalse, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
        exact ih hRest
  · simp

private theorem find_map_put_ne (fs : List (String × ByteArray))
    (p hp : String) (data : ByteArray) (hne : hp ≠ p) :
    (fs.map (fun kv => if kv.1 == p then (p, data) else kv)).find? (fun kv => kv.1 == hp) =
      fs.find? (fun kv => kv.1 == hp) := by
  induction fs with
  | nil => rfl
  | cons kv rest ih =>
    rw [List.map_cons]
    by_cases hk : (kv.1 == p) = true
    · have hEq : kv.1 = p := beq_iff_eq.mp hk
      have hHp : (p == hp) = false := beq_false_of_ne hne.symm
      have hKvHp : (kv.1 == hp) = false := by rw [hEq]; exact hHp
      rw [ite_eq_left hk, List.find?_cons, List.find?_cons]
      simp only [hHp, hKvHp]
      exact ih
    · have hFk : (kv.1 == p) = false := Bool.eq_false_iff.mpr hk
      rw [ite_eq_right (by simp [hFk]), List.find?_cons, List.find?_cons]
      by_cases hKvHp : (kv.1 == hp) = true
      · simp only [hKvHp]
      · have hFKvHp : (kv.1 == hp) = false := Bool.eq_false_iff.mpr hKvHp
        simp only [hFKvHp]
        exact ih

private theorem lookupFsBytes_putFsBytes_ne (fs : List (String × ByteArray))
    (p hp : String) (data : ByteArray) (hne : hp ≠ p) :
    lookupFsBytes (putFsBytes fs p data) hp = lookupFsBytes fs hp := by
  unfold lookupFsBytes putFsBytes
  split
  · exact congrArg (Option.map (fun kv : String × ByteArray => kv.2))
      (find_map_put_ne fs p hp data hne)
  · have hHp : (p == hp) = false := beq_false_of_ne hne.symm
    simp [hHp]

private theorem findLongestUserMount_mem {mounts : List SandboxMount} {segs : List String}
    {m : SandboxMount} {bSegs : List String}
    (h : findLongestUserMount mounts segs = some (m, bSegs)) :
    m ∈ mounts ∧ parseCleanAbsSegs (mountBoxPath m) = some bSegs ∧ bSegs.isPrefixOf segs = true := by
  have hgen : ∀ (best : Option (SandboxMount × List String)),
      (∀ bm bb, best = some (bm, bb) →
        bm ∈ mounts ∧ parseCleanAbsSegs (mountBoxPath bm) = some bb ∧ bb.isPrefixOf segs = true) →
      ∀ (ms : List SandboxMount),
      (∀ x ∈ ms, x ∈ mounts) →
      ms.foldl (fun best m =>
        match parseCleanAbsSegs (mountBoxPath m) with
        | some bSegs =>
          if bSegs.isPrefixOf segs then
            match best with
            | none => some (m, bSegs)
            | some (_, prevSegs) =>
              if prevSegs.length ≤ bSegs.length then some (m, bSegs) else best
          else
            best
        | none => best) best = some (m, bSegs) →
      m ∈ mounts ∧ parseCleanAbsSegs (mountBoxPath m) = some bSegs ∧ bSegs.isPrefixOf segs = true := by
    intro best hbest ms hms hfold
    induction ms generalizing best with
    | nil => exact hbest m bSegs hfold
    | cons hd tl ih =>
      simp only [List.foldl_cons] at hfold
      apply ih _ _ (fun x hx => hms x (by simp [hx])) hfold
      intro bm bb hres
      cases hParse : parseCleanAbsSegs (mountBoxPath hd) with
      | none =>
        rw [hParse] at hres
        exact hbest bm bb hres
      | some hdSegs =>
        rw [hParse] at hres
        dsimp only at hres
        by_cases hPref : hdSegs.isPrefixOf segs = true
        · rw [hPref] at hres
          simp only [↓reduceIte] at hres
          cases best with
          | none =>
            injection hres with hPair
            injection hPair with h1 h2
            subst h1 h2
            exact ⟨hms hd (by simp), hParse, hPref⟩
          | some prev =>
            dsimp only at hres
            split at hres
            · injection hres with hPair
              injection hPair with h1 h2
              subst h1 h2
              exact ⟨hms hd (by simp), hParse, hPref⟩
            · exact hbest bm bb hres
        · have hFPref : hdSegs.isPrefixOf segs = false := Bool.eq_false_iff.mpr hPref
          rw [hFPref] at hres
          simp only [Bool.false_eq_true, ↓reduceIte] at hres
          exact hbest bm bb hres
  exact hgen none (fun _ _ hc => by cases hc) mounts (fun _ hx => hx) h

private theorem validCompiledPlan_userMounts_ok (plan : CompiledSandboxPlan)
    (hvalid : ValidCompiledPlan plan) :
    ∀ m ∈ plan.userMounts.toList,
      (match validateAndNormalizeMount m with
      | .ok norm => norm == m
      | .error _ => false) = true := by
  unfold ValidCompiledPlan isValidCompiledPlan at hvalid
  simp only [Bool.and_eq_true, and_assoc] at hvalid
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hMounts, _⟩ := hvalid
  exact List.all_eq_true.mp hMounts

private theorem resolveBoxPath_userReadWrite_covered (plan : CompiledSandboxPlan)
    (hvalid : ValidCompiledPlan plan) (boxPath : String)
    {hRootSegs : List String} {hp : String}
    (hres : resolveBoxPath plan boxPath = .userReadWrite hRootSegs hp) :
    isCoveredByReadWriteGrant plan.userMounts.toList hp = true := by
  unfold resolveBoxPath at hres
  cases hParse : parseCleanAbsSegs boxPath with
  | none => rw [hParse] at hres; cases hres
  | some rawSegs =>
    rw [hParse] at hres
    cases rawSegs with
    | nil => cases hres
    | cons top rest =>
      dsimp only at hres
      split at hres
      · split at hres <;> cases hres
      · split at hres
        · split at hres <;> cases hres
        · split at hres
          · split at hres <;> cases hres
          · split at hres
            · cases hres
            · split at hres
              · cases hres
              · split at hres
                · cases hres
                · cases hFind : findLongestUserMount plan.userMounts.toList
                      (expandPresetTopSymlink plan.presetSystemEntries.toList (top :: rest)) with
                  | none => rw [hFind] at hres; cases hres
                  | some pair =>
                    rw [hFind] at hres
                    rcases pair with ⟨m, bSegs⟩
                    dsimp only at hres
                    cases m with
                    | scratch _ => cases hres
                    | readOnly _ _ => cases hres
                    | readWrite hostRoot boxRoot =>
                      injection hres with _ hHpEq
                      obtain ⟨hmMem, _, _⟩ := findLongestUserMount_mem hFind
                      have hmNorm := validCompiledPlan_userMounts_ok plan hvalid (.readWrite hostRoot boxRoot) hmMem
                      cases hValM : validateAndNormalizeMount (.readWrite hostRoot boxRoot) with
                      | error _ => rw [hValM] at hmNorm; simp at hmNorm
                      | ok normM =>
                        rw [hValM] at hmNorm
                        unfold validateAndNormalizeMount at hValM
                        dsimp only at hValM
                        cases hHostP : parseCleanAbsSegs hostRoot with
                        | none => rw [hHostP] at hValM; cases hValM
                        | some hSegs =>
                          rw [hHostP] at hValM
                          cases hBoxP : parseCleanAbsSegs boxRoot with
                          | none => rw [hBoxP] at hValM; cases hValM
                          | some bSegs' =>
                            rw [hBoxP] at hValM
                            dsimp only at hValM
                            split at hValM
                            · cases hValM
                            · injection hValM with hNormEq
                              have hRelValid : ∀ s ∈ (expandPresetTopSymlink plan.presetSystemEntries.toList (top :: rest)).drop bSegs.length, ValidSeg s := by
                                intro s hs
                                apply expandPresetTopSymlink_validSegs _ _ (parseCleanAbsSegs_validSegs boxPath (top :: rest) hParse)
                                exact List.mem_of_mem_drop hs
                              have hRootValid : ∀ s ∈ hSegs, ValidSeg s :=
                                parseCleanAbsSegs_validSegs hostRoot hSegs hHostP
                              have hHpSegs : hp = formatAbsSegs (hSegs ++ (expandPresetTopSymlink plan.presetSystemEntries.toList (top :: rest)).drop bSegs.length) := by
                                rw [← hHpEq, hHostP]
                                rfl
                              have hHpValid : ∀ s ∈ (hSegs ++ (expandPresetTopSymlink plan.presetSystemEntries.toList (top :: rest)).drop bSegs.length), ValidSeg s := by
                                intro s hs
                                rcases List.mem_append.mp hs with hs1 | hs2
                                · exact hRootValid s hs1
                                · exact hRelValid s hs2
                              have hParseHp : parseCleanAbsSegs hp = some (hSegs ++ (expandPresetTopSymlink plan.presetSystemEntries.toList (top :: rest)).drop bSegs.length) := by
                                rw [hHpSegs]
                                exact parseCleanAbsSegs_formatAbsSegs _ hHpValid
                              unfold isCoveredByReadWriteGrant
                              rw [List.any_eq_true]
                              refine ⟨.readWrite hostRoot boxRoot, hmMem, ?_⟩
                              dsimp only
                              unfold isHostPathUnderOrEq
                              rw [hHostP, hParseHp]
                              exact List.isPrefixOf_iff_prefix.mpr ⟨_, rfl⟩

private theorem classify_and_step_single (plan : CompiledSandboxPlan)
    (st : SandboxWorldState) (sc : GuestSyscall) :
    (classifySyscall plan st sc = .blocked →
      (stepGuestSyscall plan st sc).isOk = false ∧ stepWorldWith stepGuestSyscall plan st sc = st) ∧
    (classifySyscall plan st sc = .boxLocal →
      ∃ st', stepGuestSyscall plan st sc = .ok st' ∧ st'.host = st.host) := by
  dsimp only [stepWorldWith]
  cases sc with
  | adminOp _ | signalHostPid _ | clone3Attempt =>
    simp [classifySyscall, stepGuestSyscall, Except.isOk, Except.toBool]
  | anonUnixSocketpair sockType =>
    cases sockType <;> cases hAllow : plan.allowAnonUnixSocketpair <;>
      simp [classifySyscall, stepGuestSyscall, hAllow, Except.isOk, Except.toBool]
  | fsRead boxPath =>
    unfold classifySyscall stepGuestSyscall
    cases hRes : resolveBoxPath plan boxPath <;> simp only [hRes]
    all_goals (try (simp [Except.isOk, Except.toBool]; done))
    all_goals (split <;> simp_all [Except.isOk, Except.toBool])
  | fsWrite boxPath data =>
    unfold classifySyscall stepGuestSyscall
    cases hRes : resolveBoxPath plan boxPath with
    | virtualSafeDev =>
      simp only [hRes]
      split <;> simp_all [Except.isOk, Except.toBool]
    | userReadWrite _ _ =>
      simp only [hRes]
      cases hF : plan.limits.fileSizeMaxBytes with
      | none => simp
      | some maxF => dsimp only; split <;> simp_all [Except.isOk, Except.toBool]
    | userScratch bp =>
      simp only [hRes]
      cases plan.limits.fileSizeMaxBytes with
      | none =>
        cases plan.limits.memoryMaxBytes with
        | none => simp
        | some maxM =>
          dsimp only
          by_cases hMem : (st.box.boxMemoryBytes - ((lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0) + data.size) > maxM <;>
            simp [hMem, Except.isOk, Except.toBool]
      | some maxF =>
        dsimp only
        by_cases hFile : data.size > maxF
        · simp [hFile, Except.isOk, Except.toBool]
        · simp only [hFile, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases plan.limits.memoryMaxBytes with
          | none => simp
          | some maxM =>
            dsimp only
            by_cases hMem : (st.box.boxMemoryBytes - ((lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0) + data.size) > maxM <;>
              simp [hMem, Except.isOk, Except.toBool]
    | virtualRoot | virtualProc | virtualEtcHosts | maskedPreset
    | presetReadOnly _ | userReadOnly _ | unmounted =>
      simp [hRes, Except.isOk, Except.toBool]
  | mmapAnon bytes =>
    unfold classifySyscall stepGuestSyscall
    cases plan.limits.memoryMaxBytes with
    | none => simp
    | some maxM => dsimp only; split <;> simp_all [Except.isOk, Except.toBool]
  | cloneProc newBoxPid hasCloneNewFlags =>
    unfold classifySyscall stepGuestSyscall
    cases hasCloneNewFlags
    · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      split
      · simp [Except.isOk, Except.toBool]
      · cases plan.limits.pidsMax with
        | none => simp_all [Except.isOk, Except.toBool]
        | some maxP => dsimp only; split <;> simp_all [Except.isOk, Except.toBool]
    · simp [Except.isOk, Except.toBool]
  | tcpSend destIsLoopback port payload =>
    unfold classifySyscall stepGuestSyscall
    by_cases hBad : (!destIsLoopback || port == 0) = true
    · simp [hBad, Except.isOk, Except.toBool]
    · have hFBad : (!destIsLoopback || port == 0) = false := Bool.eq_false_iff.mpr hBad
      simp only [hFBad, Bool.false_eq_true, ↓reduceIte]
      cases hF : plan.portForwards.toList.find? (fun pf => pf.boxPort == port) with
      | some _ => simp
      | none => cases plan.allowBoxLocalhost <;> simp [Except.isOk, Except.toBool]

private theorem host_invariants_of_host_eq (plan : CompiledSandboxPlan)
    (st st' : SandboxWorldState) (h : st'.host = st.host) :
    st'.host.hostAdminState = st.host.hostAdminState ∧
    st'.host.hostProcs = st.host.hostProcs ∧
    (∀ hp : String,
      isCoveredByReadWriteGrant plan.userMounts.toList hp = false →
      lookupHostFile st'.host hp = lookupHostFile st.host hp) ∧
    (∀ maxF : Nat,
      plan.limits.fileSizeMaxBytes = some maxF →
      ∀ (hp : String) (bs : ByteArray),
        lookupHostFile st.host hp ≠ some bs →
        lookupHostFile st'.host hp = some bs →
        bs.size ≤ maxF) ∧
    (∀ port : UInt16,
      (plan.portForwards.toList.map (·.hostPort)).contains port = false →
      st'.host.hostPorts.filter (fun e => e.1 == port) =
        st.host.hostPorts.filter (fun e => e.1 == port)) := by
  rw [h]
  exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ _ h1 h2 => absurd h2 h1, fun _ _ => rfl⟩

private theorem stepWorld_host_invariants (plan : CompiledSandboxPlan)
    (hvalid : ValidCompiledPlan plan) (st : SandboxWorldState) (sc : GuestSyscall) :
    let st' := stepWorldWith stepGuestSyscall plan st sc
    st'.host.hostAdminState = st.host.hostAdminState ∧
    st'.host.hostProcs = st.host.hostProcs ∧
    (∀ hp : String,
      isCoveredByReadWriteGrant plan.userMounts.toList hp = false →
      lookupHostFile st'.host hp = lookupHostFile st.host hp) ∧
    (∀ maxF : Nat,
      plan.limits.fileSizeMaxBytes = some maxF →
      ∀ (hp : String) (bs : ByteArray),
        lookupHostFile st.host hp ≠ some bs →
        lookupHostFile st'.host hp = some bs →
        bs.size ≤ maxF) ∧
    (∀ port : UInt16,
      (plan.portForwards.toList.map (·.hostPort)).contains port = false →
      st'.host.hostPorts.filter (fun e => e.1 == port) =
        st.host.hostPorts.filter (fun e => e.1 == port)) := by
  dsimp only
  cases sc with
  | adminOp _ | signalHostPid _ | clone3Attempt =>
    exact host_invariants_of_host_eq plan st _ rfl
  | anonUnixSocketpair sockType =>
    apply host_invariants_of_host_eq
    cases sockType <;> cases hAllow : plan.allowAnonUnixSocketpair <;>
      simp [stepWorldWith, stepGuestSyscall, hAllow]
  | fsRead boxPath =>
    apply host_invariants_of_host_eq
    unfold stepWorldWith stepGuestSyscall
    cases hRes : resolveBoxPath plan boxPath with
    | presetReadOnly hp | userReadOnly hp | userReadWrite _ hp =>
      simp only [hRes]
      cases (lookupHostFile st.host hp).isSome <;> simp
    | userScratch bp =>
      simp only [hRes]
      cases (lookupFsBytes st.box.scratchFs bp).isSome <;> simp
    | virtualRoot | virtualProc | virtualSafeDev | virtualEtcHosts
    | maskedPreset | unmounted =>
      simp [hRes]
  | fsWrite boxPath data =>
    unfold stepWorldWith stepGuestSyscall
    cases hRes : resolveBoxPath plan boxPath with
    | virtualSafeDev =>
      apply host_invariants_of_host_eq
      simp only [hRes]
      cases (formatAbsSegs ((parseCleanAbsSegs boxPath).getD []) == "/dev") <;> simp
    | userScratch bp =>
      apply host_invariants_of_host_eq
      simp only [hRes]
      cases plan.limits.fileSizeMaxBytes with
      | none =>
        cases plan.limits.memoryMaxBytes with
        | none => simp
        | some maxM =>
          dsimp only
          by_cases hMem : (st.box.boxMemoryBytes - ((lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0) + data.size) > maxM <;>
            simp [hMem]
      | some maxF =>
        dsimp only
        by_cases hFile : data.size > maxF
        · simp [hFile]
        · simp only [hFile, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases plan.limits.memoryMaxBytes with
          | none => simp
          | some maxM =>
            dsimp only
            by_cases hMem : (st.box.boxMemoryBytes - ((lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0) + data.size) > maxM <;>
              simp [hMem]
    | userReadWrite hRootSegs hp' =>
      simp only [hRes]
      cases hF : plan.limits.fileSizeMaxBytes with
      | none =>
        dsimp only
        have hCov : isCoveredByReadWriteGrant plan.userMounts.toList hp' = true :=
          resolveBoxPath_userReadWrite_covered plan hvalid boxPath hRes
        refine ⟨rfl, rfl, ?_, ?_, ?_⟩
        · intro hp hNotCov
          have hne : hp ≠ hp' := fun hEq => by subst hEq; simp [hCov] at hNotCov
          exact lookupFsBytes_putFsBytes_ne st.host.hostFs hp' hp data hne
        · intro maxF hLim
          cases hLim
        · intro _ _; rfl
      | some maxF =>
        dsimp only
        by_cases hFile : data.size > maxF
        · have hDec : decide (data.size > maxF) = true := decide_eq_true hFile
          rw [ite_eq_left hDec]
          exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ _ h1 h2 => absurd h2 h1, fun _ _ => rfl⟩
        · have hDec : decide (data.size > maxF) = false := decide_eq_false hFile
          simp only [hDec, Bool.false_eq_true, ↓reduceIte]
          have hCov : isCoveredByReadWriteGrant plan.userMounts.toList hp' = true :=
            resolveBoxPath_userReadWrite_covered plan hvalid boxPath hRes
          refine ⟨trivial, trivial, ?_, ?_, ?_⟩
          · intro hp hNotCov
            have hne : hp ≠ hp' := fun hEq => by subst hEq; simp [hCov] at hNotCov
            exact lookupFsBytes_putFsBytes_ne st.host.hostFs hp' hp data hne
          · intro maxF' hLim hp bs hOld hNew
            injection hLim with hEqMax
            subst hEqMax
            by_cases hEq : hp = hp'
            · subst hEq
              unfold lookupHostFile at hNew
              rw [lookupFsBytes_putFsBytes_eq] at hNew
              injection hNew with hDataEq
              rw [← hDataEq]
              omega
            · unfold lookupHostFile at hOld hNew
              rw [lookupFsBytes_putFsBytes_ne st.host.hostFs hp' hp data hEq] at hNew
              exact absurd hNew hOld
          · intro _ _; trivial
    | virtualRoot | virtualProc | virtualEtcHosts | presetReadOnly _ | userReadOnly _
    | maskedPreset | unmounted =>
      exact host_invariants_of_host_eq plan st _ (by simp [hRes])
  | mmapAnon bytes =>
    apply host_invariants_of_host_eq
    unfold stepWorldWith stepGuestSyscall
    cases plan.limits.memoryMaxBytes with
    | none => rfl
    | some maxM =>
      dsimp only
      by_cases hMem : st.box.boxMemoryBytes + bytes > maxM <;> simp [hMem]
  | cloneProc newBoxPid hasCloneNewFlags =>
    apply host_invariants_of_host_eq
    unfold stepWorldWith stepGuestSyscall
    cases hasCloneNewFlags
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases (newBoxPid == 0 || st.box.boxProcs.contains newBoxPid)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases plan.limits.pidsMax with
        | none => rfl
        | some maxP =>
          dsimp only
          by_cases hPids : st.box.boxProcs.length ≥ maxP <;> simp [hPids]
      · rfl
    · rfl
  | tcpSend destIsLoopback port payload =>
    unfold stepWorldWith stepGuestSyscall
    by_cases hBad : (!destIsLoopback || port == 0) = true
    · exact host_invariants_of_host_eq plan st _ (by simp [hBad])
    · have hFBad : (!destIsLoopback || port == 0) = false := Bool.eq_false_iff.mpr hBad
      simp only [hFBad, Bool.false_eq_true, ↓reduceIte]
      cases hFind : plan.portForwards.toList.find? (fun pf => pf.boxPort == port) with
      | some pf =>
        dsimp only
        refine ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ _ h1 h2 => absurd h2 h1, ?_⟩
        intro q hNotContains
        have hMem : pf ∈ plan.portForwards.toList := List.mem_of_find?_eq_some hFind
        have hMapMem : pf.hostPort ∈ plan.portForwards.toList.map (·.hostPort) :=
          List.mem_map_of_mem hMem
        have hNe : pf.hostPort ≠ q := by
          intro hEq
          subst hEq
          have hTrue := List.contains_iff_mem.mpr hMapMem
          rw [hNotContains] at hTrue
          cases hTrue
        have hBeqFalse : (pf.hostPort == q) = false := beq_false_of_ne hNe
        simp [List.filter_append, hBeqFalse]
      | none =>
        apply host_invariants_of_host_eq
        cases plan.allowBoxLocalhost <;> simp

private theorem trace_host_invariants (plan : CompiledSandboxPlan)
    (hvalid : ValidCompiledPlan plan) (st₀ : SandboxWorldState) (trace : List GuestSyscall) :
    let st₁ := runGuestTraceWith stepGuestSyscall plan st₀ trace
    st₁.host.hostAdminState = st₀.host.hostAdminState ∧
    st₁.host.hostProcs = st₀.host.hostProcs ∧
    (∀ hp : String,
      isCoveredByReadWriteGrant plan.userMounts.toList hp = false →
      lookupHostFile st₁.host hp = lookupHostFile st₀.host hp) ∧
    (∀ maxF : Nat,
      plan.limits.fileSizeMaxBytes = some maxF →
      ∀ (hp : String) (bs : ByteArray),
        lookupHostFile st₀.host hp ≠ some bs →
        lookupHostFile st₁.host hp = some bs →
        bs.size ≤ maxF) ∧
    (∀ port : UInt16,
      (plan.portForwards.toList.map (·.hostPort)).contains port = false →
      st₁.host.hostPorts.filter (fun e => e.1 == port) =
        st₀.host.hostPorts.filter (fun e => e.1 == port)) := by
  induction trace generalizing st₀ with
  | nil =>
    dsimp only [runGuestTraceWith]
    refine ⟨rfl, rfl, fun _ _ => rfl, ?_, fun _ _ => rfl⟩
    intro _ _ _ _ hNe hEq
    exact absurd hEq hNe
  | cons sc rest ih =>
    simp only [runGuestTraceWith]
    have hStep := stepWorld_host_invariants plan hvalid st₀ sc
    have hRest := ih (stepWorldWith stepGuestSyscall plan st₀ sc)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hRest.1.trans hStep.1
    · exact hRest.2.1.trans hStep.2.1
    · intro hp hNotCov
      exact (hRest.2.2.1 hp hNotCov).trans (hStep.2.2.1 hp hNotCov)
    · intro maxF hLim hp bs hOld hNew
      by_cases hMid : lookupHostFile (stepWorldWith stepGuestSyscall plan st₀ sc).host hp = some bs
      · exact hStep.2.2.2.1 maxF hLim hp bs hOld hMid
      · exact hRest.2.2.2.1 maxF hLim hp bs hMid hNew
    · intro port hNotCont
      exact (hRest.2.2.2.2 port hNotCont).trans (hStep.2.2.2.2 port hNotCont)

/-- Formal proof of `Model.SpecHostUnchangedOutsideGrants` for `stepGuestSyscall`. -/
theorem specHostUnchangedOutsideGrants : Model.SpecHostUnchangedOutsideGrants := by
  refine ⟨?_, ?_⟩
  · intro plan st sc _
    exact classify_and_step_single plan st sc
  · intro plan st₀ trace hvalid
    exact trace_host_invariants plan hvalid st₀ trace

private theorem cgroup_limits_of_box_eq (plan : CompiledSandboxPlan)
    (st st' : SandboxWorldState) (h : st'.box = st.box)
    (hpids : ∀ maxP, plan.limits.pidsMax = some maxP → st.box.boxProcs.length ≤ maxP)
    (hmem : ∀ maxM, plan.limits.memoryMaxBytes = some maxM → st.box.boxMemoryBytes ≤ maxM) :
    (∀ maxP, plan.limits.pidsMax = some maxP → st'.box.boxProcs.length ≤ maxP) ∧
    (∀ maxM, plan.limits.memoryMaxBytes = some maxM → st'.box.boxMemoryBytes ≤ maxM) := by
  rw [h]
  exact ⟨hpids, hmem⟩

private theorem stepWorld_cgroup_limits (plan : CompiledSandboxPlan)
    (st : SandboxWorldState) (sc : GuestSyscall)
    (hpids : ∀ maxP, plan.limits.pidsMax = some maxP → st.box.boxProcs.length ≤ maxP)
    (hmem : ∀ maxM, plan.limits.memoryMaxBytes = some maxM → st.box.boxMemoryBytes ≤ maxM) :
    let st' := stepWorldWith stepGuestSyscall plan st sc
    (∀ maxP, plan.limits.pidsMax = some maxP → st'.box.boxProcs.length ≤ maxP) ∧
    (∀ maxM, plan.limits.memoryMaxBytes = some maxM → st'.box.boxMemoryBytes ≤ maxM) := by
  dsimp only
  cases sc with
  | adminOp _ | signalHostPid _ | clone3Attempt =>
    exact cgroup_limits_of_box_eq plan st _ rfl hpids hmem
  | anonUnixSocketpair sockType =>
    apply cgroup_limits_of_box_eq plan st _ _ hpids hmem
    cases sockType <;> cases hAllow : plan.allowAnonUnixSocketpair <;>
      simp [stepWorldWith, stepGuestSyscall, hAllow]
  | fsRead boxPath =>
    apply cgroup_limits_of_box_eq plan st _ _ hpids hmem
    unfold stepWorldWith stepGuestSyscall
    cases hRes : resolveBoxPath plan boxPath with
    | presetReadOnly hp | userReadOnly hp | userReadWrite _ hp =>
      simp only [hRes]
      cases (lookupHostFile st.host hp).isSome <;> simp
    | userScratch bp =>
      simp only [hRes]
      cases (lookupFsBytes st.box.scratchFs bp).isSome <;> simp
    | virtualRoot | virtualProc | virtualSafeDev | virtualEtcHosts
    | maskedPreset | unmounted =>
      simp [hRes]
  | fsWrite boxPath data =>
    unfold stepWorldWith stepGuestSyscall
    cases hRes : resolveBoxPath plan boxPath with
    | virtualSafeDev =>
      apply cgroup_limits_of_box_eq plan st _ _ hpids hmem
      simp only [hRes]
      cases (formatAbsSegs ((parseCleanAbsSegs boxPath).getD []) == "/dev") <;> simp
    | userScratch bp =>
      simp only [hRes]
      cases plan.limits.fileSizeMaxBytes with
      | none =>
        dsimp only
        cases hM : plan.limits.memoryMaxBytes with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hpids, fun maxM h => by cases h⟩
        | some maxM =>
          dsimp only
          by_cases hMemLim : (st.box.boxMemoryBytes - ((lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0) + data.size) > maxM
          · have hDec : decide (st.box.boxMemoryBytes - ((lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0) + data.size > maxM) = true :=
              decide_eq_true hMemLim
            rw [ite_eq_left hDec]
            exact ⟨hpids, fun m hm => hmem m (by rw [hM]; exact hm)⟩
          · have hDec := decide_eq_false hMemLim
            simp only [hDec, Bool.false_eq_true, ↓reduceIte]
            refine ⟨hpids, ?_⟩
            intro m hm
            injection hm with hmEq
            subst hmEq
            omega
      | some maxF =>
        dsimp only
        by_cases hFile : data.size > maxF
        · have hDec := decide_eq_true hFile
          exact cgroup_limits_of_box_eq plan st _ (by simp [hDec]) hpids hmem
        · have hDecF := decide_eq_false hFile
          simp only [hDecF, Bool.false_eq_true, ↓reduceIte]
          cases hM : plan.limits.memoryMaxBytes with
          | none =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨hpids, fun maxM h => by cases h⟩
          | some maxM =>
            dsimp only
            by_cases hMemLim : (st.box.boxMemoryBytes - ((lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0) + data.size) > maxM
            · have hDec : decide (st.box.boxMemoryBytes - ((lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0) + data.size > maxM) = true :=
                decide_eq_true hMemLim
              rw [ite_eq_left hDec]
              exact ⟨hpids, fun m hm => hmem m (by rw [hM]; exact hm)⟩
            · have hDec := decide_eq_false hMemLim
              simp only [hDec, Bool.false_eq_true, ↓reduceIte]
              refine ⟨hpids, ?_⟩
              intro m hm
              injection hm with hmEq
              subst hmEq
              omega
    | userReadWrite _ _ =>
      apply cgroup_limits_of_box_eq plan st _ _ hpids hmem
      simp only [hRes]
      cases plan.limits.fileSizeMaxBytes with
      | none => rfl
      | some maxF =>
        dsimp only
        by_cases hFile : data.size > maxF <;> simp [hFile]
    | virtualRoot | virtualProc | virtualEtcHosts | presetReadOnly _ | userReadOnly _
    | maskedPreset | unmounted =>
      exact cgroup_limits_of_box_eq plan st _ (by simp [hRes]) hpids hmem
  | mmapAnon bytes =>
    unfold stepWorldWith stepGuestSyscall
    cases hM : plan.limits.memoryMaxBytes with
    | none =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨hpids, fun maxM h => by cases h⟩
    | some maxM =>
      dsimp only
      by_cases hMemLim : st.box.boxMemoryBytes + bytes > maxM
      · have hDec : decide (st.box.boxMemoryBytes + bytes > maxM) = true :=
          decide_eq_true hMemLim
        rw [ite_eq_left hDec]
        exact ⟨hpids, fun m hm => hmem m (by rw [hM]; exact hm)⟩
      · have hDec := decide_eq_false hMemLim
        simp only [hDec, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hpids, ?_⟩
        intro m hm
        injection hm with hmEq
        subst hmEq
        omega
  | cloneProc newBoxPid hasCloneNewFlags =>
    unfold stepWorldWith stepGuestSyscall
    cases hasCloneNewFlags
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases (newBoxPid == 0 || st.box.boxProcs.contains newBoxPid)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hP : plan.limits.pidsMax with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨fun maxP h => (by cases h), hmem⟩
        | some maxP =>
          dsimp only
          by_cases hPidsLim : st.box.boxProcs.length ≥ maxP
          · have hDec : decide (st.box.boxProcs.length ≥ maxP) = true :=
              decide_eq_true hPidsLim
            rw [ite_eq_left hDec]
            exact ⟨fun p hp => hpids p (by rw [hP]; exact hp), hmem⟩
          · have hDec := decide_eq_false hPidsLim
            simp only [hDec, Bool.false_eq_true, ↓reduceIte]
            refine ⟨?_, hmem⟩
            intro p hp
            injection hp with hpEq
            subst hpEq
            simp only [List.length_cons]
            omega
      · exact ⟨hpids, hmem⟩
    · exact ⟨hpids, hmem⟩
  | tcpSend destIsLoopback port payload =>
    unfold stepWorldWith stepGuestSyscall
    by_cases hBad : (!destIsLoopback || port == 0) = true
    · exact cgroup_limits_of_box_eq plan st _ (by simp [hBad]) hpids hmem
    · have hFBad : (!destIsLoopback || port == 0) = false := Bool.eq_false_iff.mpr hBad
      simp only [hFBad, Bool.false_eq_true, ↓reduceIte]
      cases plan.portForwards.toList.find? (fun pf => pf.boxPort == port) with
      | some _ => exact cgroup_limits_of_box_eq plan st _ rfl hpids hmem
      | none =>
        cases plan.allowBoxLocalhost
        · exact cgroup_limits_of_box_eq plan st _ rfl hpids hmem
        · exact ⟨hpids, hmem⟩

private theorem trace_cgroup_limits (plan : CompiledSandboxPlan)
    (st₀ : SandboxWorldState) (trace : List GuestSyscall)
    (hpids : ∀ maxP, plan.limits.pidsMax = some maxP → st₀.box.boxProcs.length ≤ maxP)
    (hmem : ∀ maxM, plan.limits.memoryMaxBytes = some maxM → st₀.box.boxMemoryBytes ≤ maxM) :
    let stRun := runGuestTraceWith stepGuestSyscall plan st₀ trace
    (∀ maxP, plan.limits.pidsMax = some maxP → stRun.box.boxProcs.length ≤ maxP) ∧
    (∀ maxM, plan.limits.memoryMaxBytes = some maxM → stRun.box.boxMemoryBytes ≤ maxM) := by
  induction trace generalizing st₀ with
  | nil => exact ⟨hpids, hmem⟩
  | cons sc rest ih =>
    simp only [runGuestTraceWith]
    have hStep := stepWorld_cgroup_limits plan st₀ sc hpids hmem
    exact ih (stepWorldWith stepGuestSyscall plan st₀ sc) hStep.1 hStep.2

/-- Formal proof of `Model.SpecZeroSurvivingBoxProcs` for `stepGuestSyscall` and `reapAndTeardownBox`. -/
theorem specZeroSurvivingBoxProcs : Model.SpecZeroSurvivingBoxProcs := by
  intro plan st₀ trace _ hpids hmem
  have hLim := trace_cgroup_limits plan st₀ trace hpids hmem
  exact ⟨hLim.1, hLim.2, rfl, rfl, rfl, rfl, rfl⟩

private theorem mem_dedupByFirst_go {α β : Type} [BEq β] (f : α → β)
    (seen : List β) (xs : List α) {x : α}
    (hx : x ∈ dedupByFirst.go f seen xs) : x ∈ xs := by
  induction xs generalizing seen with
  | nil => simp [dedupByFirst.go] at hx
  | cons y ys ih =>
    simp only [dedupByFirst.go] at hx
    split at hx
    · exact List.mem_cons_of_mem y (ih seen hx)
    · rcases List.mem_cons.mp hx with rfl | hrest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem y (ih (f y :: seen) hrest)

private theorem mem_dedupByFirst {α β : Type} [BEq β] (f : α → β) (xs : List α) {x : α}
    (hx : x ∈ dedupByFirst f xs) : x ∈ xs :=
  mem_dedupByFirst_go f [] xs hx

private theorem mem_dedupByFirst_id_of_mem {α : Type} [BEq α] [LawfulBEq α]
    (seen xs : List α) {x : α} (hx : x ∈ xs) (hnot : seen.contains x = false) :
    x ∈ dedupByFirst.go id seen xs := by
  induction xs generalizing seen with
  | nil => cases hx
  | cons y ys ih =>
    unfold dedupByFirst.go
    by_cases hSeenY : seen.contains y = true
    · simp only [id_eq, hSeenY, ↓reduceIte]
      rcases List.mem_cons.mp hx with rfl | hy
      · rw [hnot] at hSeenY; cases hSeenY
      · exact ih seen hy hnot
    · have hFSeenY : seen.contains y = false := Bool.eq_false_iff.mpr hSeenY
      simp only [id_eq, hFSeenY, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.mp hx with rfl | hy
      · exact List.mem_cons_self
      · by_cases hEq : x = y
        · subst hEq; exact List.mem_cons_self
        · apply List.mem_cons_of_mem y
          apply ih (y :: seen) hy
          have hNotX : x ∉ seen := mt List.contains_iff_mem.mpr (Bool.eq_false_iff.mp hnot)
          apply Bool.eq_false_iff.mpr
          intro hCont
          have hMem := List.contains_iff_mem.mp hCont
          rcases List.mem_cons.mp hMem with rfl | hOld
          · exact hEq rfl
          · exact hNotX hOld

private theorem dedupByFirst_go_not_seen {α β : Type} [BEq β] [LawfulBEq β] (f : α → β)
    (seen : List β) (xs : List α) {x : α} (hx : x ∈ dedupByFirst.go f seen xs) :
    seen.contains (f x) = false := by
  induction xs generalizing seen with
  | nil => simp [dedupByFirst.go] at hx
  | cons y ys ih =>
    simp only [dedupByFirst.go] at hx
    split at hx
    · exact ih seen hx
    · rcases List.mem_cons.mp hx with rfl | hrest
      · next hNot => exact Bool.eq_false_iff.mpr hNot
      · have hIn := ih (f y :: seen) hrest
        simp only [List.contains_cons, Bool.or_eq_false_iff] at hIn
        exact hIn.2

private theorem allDistinct_dedupByFirst_go {α β : Type} [BEq β] [LawfulBEq β] (f : α → β)
    (seen : List β) (xs : List α) :
    allDistinct ((dedupByFirst.go f seen xs).map f) = true := by
  induction xs generalizing seen with
  | nil => rfl
  | cons y ys ih =>
    simp only [dedupByFirst.go]
    split
    · exact ih seen
    · simp only [List.map_cons, allDistinct, Bool.and_eq_true]
      refine ⟨?_, ih (f y :: seen)⟩
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro hCont
      rw [List.contains_iff_mem, List.mem_map] at hCont
      rcases hCont with ⟨z, hzMem, hzEq⟩
      have hNotSeen := dedupByFirst_go_not_seen f (f y :: seen) ys hzMem
      rw [hzEq] at hNotSeen
      simp at hNotSeen

private theorem allDistinct_dedupByFirst {α β : Type} [BEq β] [LawfulBEq β]
    (f : α → β) (xs : List α) :
    allDistinct ((dedupByFirst f xs).map f) = true :=
  allDistinct_dedupByFirst_go f [] xs

private theorem mem_insertByDepth_iff {α : Type} (depth : α → Nat) (x z : α) (ys : List α) :
    z ∈ insertByDepth depth x ys ↔ z = x ∨ z ∈ ys := by
  induction ys with
  | nil => simp [insertByDepth]
  | cons y ys ih =>
    simp only [insertByDepth]
    split
    · simp [List.mem_cons]
    · simp [List.mem_cons, ih, or_left_comm]

private theorem mem_sortByDepth_iff {α : Type} (depth : α → Nat) (xs : List α) (z : α) :
    z ∈ sortByDepth depth xs ↔ z ∈ xs := by
  induction xs with
  | nil => simp [sortByDepth]
  | cons x xs ih =>
    simp only [sortByDepth, mem_insertByDepth_iff, ih, List.mem_cons]

private theorem allDistinct_insertByDepth {α β : Type} [BEq β] [LawfulBEq β]
    (depth : α → Nat) (f : α → β) (x : α) (ys : List α)
    (hnot : (ys.map f).contains (f x) = false)
    (hdist : allDistinct (ys.map f) = true) :
    allDistinct ((insertByDepth depth x ys).map f) = true := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, allDistinct, Bool.and_eq_true, Bool.not_eq_true'] at hdist
    have hnotMem : f x ∉ (y :: ys).map f := mt List.contains_iff_mem.mpr (Bool.eq_false_iff.mp hnot)
    have hnotY : f y ≠ f x := fun h => hnotMem (by simp [h])
    have hnotTail : (ys.map f).contains (f x) = false := by
      apply Bool.eq_false_iff.mpr
      intro hCont
      have hMem := List.contains_iff_mem.mp hCont
      exact hnotMem (List.mem_cons_of_mem (f y) hMem)
    simp only [insertByDepth]
    split
    · simp only [List.map_cons, allDistinct, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, hdist.1, hdist.2⟩
      apply Bool.eq_false_iff.mpr
      intro hCont
      have hMem := List.contains_iff_mem.mp hCont
      rcases List.mem_cons.mp hMem with hEq | hIn
      · exact hnotY hEq.symm
      · have hFalse := Bool.eq_false_iff.mp hnotTail
        exact hFalse (List.contains_iff_mem.mpr hIn)
    · simp only [List.map_cons, allDistinct, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, ih hnotTail hdist.2⟩
      apply Bool.eq_false_iff.mpr
      intro hCont
      rw [List.contains_iff_mem, List.mem_map] at hCont
      rcases hCont with ⟨z, hzMem, hzEq⟩
      rw [mem_insertByDepth_iff] at hzMem
      rcases hzMem with rfl | hzYs
      · exact hnotY hzEq.symm
      · apply Bool.eq_false_iff.mp hdist.1
        rw [List.contains_iff_mem, List.mem_map]
        exact ⟨z, hzYs, hzEq⟩

private theorem allDistinct_sortByDepth {α β : Type} [BEq β] [LawfulBEq β]
    (depth : α → Nat) (f : α → β) (xs : List α)
    (hdist : allDistinct (xs.map f) = true) :
    allDistinct ((sortByDepth depth xs).map f) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, allDistinct, Bool.and_eq_true, Bool.not_eq_true'] at hdist
    simp only [sortByDepth]
    apply allDistinct_insertByDepth depth f x (sortByDepth depth xs)
    · apply Bool.eq_false_iff.mpr
      intro hCont
      rw [List.contains_iff_mem, List.mem_map] at hCont
      rcases hCont with ⟨z, hzMem, hzEq⟩
      rw [mem_sortByDepth_iff] at hzMem
      apply Bool.eq_false_iff.mp hdist.1
      rw [List.contains_iff_mem, List.mem_map]
      exact ⟨z, hzMem, hzEq⟩
    · exact ih hdist.2

private theorem mem_dedupEnvPairs {xs : List (String × String)} {kv : String × String}
    (h : kv ∈ dedupEnvPairs xs) : kv ∈ xs := by
  induction xs with
  | nil => simp [dedupEnvPairs] at h
  | cons p rest ih =>
    simp only [dedupEnvPairs] at h
    split at h
    · exact List.mem_cons_of_mem p (ih h)
    · rcases List.mem_cons.mp h with rfl | hrest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem p (ih hrest)

private theorem any_key_dedupEnvPairs (xs : List (String × String)) (k : String) :
    (dedupEnvPairs xs).any (fun kv => kv.1 == k) = xs.any (fun kv => kv.1 == k) := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    simp only [dedupEnvPairs, List.any_cons]
    split
    · next hAny =>
      rw [ih]
      by_cases hPk : (p.1 == k) = true
      · have hEq : p.1 = k := beq_iff_eq.mp hPk
        have hRest : (dedupEnvPairs rest).any (fun kv => kv.1 == k) = true := by
          simpa [hEq] using hAny
        rw [ih] at hRest
        simp [hPk, hRest]
      · have hFPk : (p.1 == k) = false := Bool.eq_false_iff.mpr hPk
        simp [hFPk]
    · simp [List.any_cons, ih]

private theorem sanitizePresetSystemEntry_idempotent (e e' : PresetSystemEntry)
    (h : sanitizePresetSystemEntry e = some e') :
    sanitizePresetSystemEntry e' = some e' := by
  unfold sanitizePresetSystemEntry at h
  cases e with
  | readOnlyDir path =>
    dsimp only at h
    cases hNorm : normalizeCleanAbsPath path with
    | none => rw [hNorm] at h; cases h
    | some cleanP =>
      rw [hNorm] at h
      dsimp only at h
      split at h
      · next hAllow =>
        injection h with hEq
        subst hEq
        unfold normalizeCleanAbsPath at hNorm
        cases hParse : parseCleanAbsSegs path with
        | none => rw [hParse] at hNorm; cases hNorm
        | some segs =>
          rw [hParse] at hNorm
          injection hNorm with hCleanEq
          have hNormClean : normalizeCleanAbsPath cleanP = some cleanP := by
            unfold normalizeCleanAbsPath
            rw [← hCleanEq, parseCleanAbsSegs_formatAbsSegs segs (parseCleanAbsSegs_validSegs path segs hParse)]
            simp [hCleanEq]
          unfold sanitizePresetSystemEntry
          simp only [hNormClean, hAllow, ↓reduceIte]
      · cases h
  | topSymlink linkPath target =>
    dsimp only at h
    cases hLink : normalizeCleanAbsPath linkPath with
    | none => rw [hLink] at h; cases h
    | some cleanLink =>
      rw [hLink] at h
      cases hTarg : parseSafePresetTargetSegs target with
      | none => rw [hTarg] at h; cases h
      | some targetSegs =>
        rw [hTarg] at h
        dsimp only at h
        split at h
        · next hAllow =>
          injection h with hEq
          subst hEq
          unfold normalizeCleanAbsPath at hLink
          cases hParse : parseCleanAbsSegs linkPath with
          | none => rw [hParse] at hLink; cases hLink
          | some segs =>
            rw [hParse] at hLink
            injection hLink with hCleanEq
            have hNormClean : normalizeCleanAbsPath cleanLink = some cleanLink := by
              unfold normalizeCleanAbsPath
              rw [← hCleanEq, parseCleanAbsSegs_formatAbsSegs segs (parseCleanAbsSegs_validSegs linkPath segs hParse)]
              simp [hCleanEq]
            unfold sanitizePresetSystemEntry
            simp only [hNormClean, hTarg, hAllow, ↓reduceIte]
        · cases h

private theorem sanitizePresetSystemEntry_allowlisted (e e' : PresetSystemEntry)
    (h : sanitizePresetSystemEntry e = some e') :
    allowlistedSystemRootPaths.contains (presetEntryBoxPath e') = true := by
  unfold sanitizePresetSystemEntry at h
  cases e with
  | readOnlyDir path =>
    dsimp only at h
    cases hNorm : normalizeCleanAbsPath path with
    | none => rw [hNorm] at h; cases h
    | some cleanP =>
      rw [hNorm] at h
      dsimp only at h
      split at h
      · next hAllow =>
        injection h with hEq
        subst hEq
        exact hAllow
      · cases h
  | topSymlink linkPath target =>
    dsimp only at h
    cases hLink : normalizeCleanAbsPath linkPath with
    | none => rw [hLink] at h; cases h
    | some cleanLink =>
      rw [hLink] at h
      cases hTarg : parseSafePresetTargetSegs target with
      | none => rw [hTarg] at h; cases h
      | some targetSegs =>
        rw [hTarg] at h
        dsimp only at h
        split at h
        · next hAllow =>
          injection h with hEq
          subst hEq
          simp only [Bool.and_eq_true] at hAllow
          exact hAllow.1
        · cases h

private theorem beq_self_sandboxMount (m : SandboxMount) : (m == m) = true := by
  cases m <;> dsimp [BEq.beq, Raw.instBEqSandboxMount.beq] <;> simp

private theorem validateAndNormalizeMount_idempotent (m m' : SandboxMount)
    (h : validateAndNormalizeMount m = .ok m') :
    validateAndNormalizeMount m' = .ok m' := by
  cases m with
  | readOnly hp bp =>
    unfold validateAndNormalizeMount at h
    dsimp only at h
    cases hHp : parseCleanAbsSegs hp with
    | none => rw [hHp] at h; cases h
    | some hSegs =>
      rw [hHp] at h
      cases hBp : parseCleanAbsSegs bp with
      | none => rw [hBp] at h; cases h
      | some bSegs =>
        rw [hBp] at h
        dsimp only at h
        split at h
        · cases h
        · next hRes =>
          injection h with hEq
          subst hEq
          have hHp' := parseCleanAbsSegs_formatAbsSegs hSegs (parseCleanAbsSegs_validSegs hp hSegs hHp)
          have hBp' := parseCleanAbsSegs_formatAbsSegs bSegs (parseCleanAbsSegs_validSegs bp bSegs hBp)
          simp [validateAndNormalizeMount, hHp', hBp', hRes]
  | readWrite hp bp =>
    unfold validateAndNormalizeMount at h
    dsimp only at h
    cases hHp : parseCleanAbsSegs hp with
    | none => rw [hHp] at h; cases h
    | some hSegs =>
      rw [hHp] at h
      cases hBp : parseCleanAbsSegs bp with
      | none => rw [hBp] at h; cases h
      | some bSegs =>
        rw [hBp] at h
        dsimp only at h
        split at h
        · cases h
        · next hRes =>
          injection h with hEq
          subst hEq
          have hHp' := parseCleanAbsSegs_formatAbsSegs hSegs (parseCleanAbsSegs_validSegs hp hSegs hHp)
          have hBp' := parseCleanAbsSegs_formatAbsSegs bSegs (parseCleanAbsSegs_validSegs bp bSegs hBp)
          simp [validateAndNormalizeMount, hHp', hBp', hRes]
  | scratch bp =>
    unfold validateAndNormalizeMount at h
    dsimp only at h
    cases hBp : parseCleanAbsSegs bp with
    | none => rw [hBp] at h; cases h
    | some bSegs =>
      rw [hBp] at h
      dsimp only at h
      split at h
      · cases h
      · next hRes =>
        injection h with hEq
        subst hEq
        have hBp' := parseCleanAbsSegs_formatAbsSegs bSegs (parseCleanAbsSegs_validSegs bp bSegs hBp)
        simp [validateAndNormalizeMount, hBp', hRes]

private theorem validateMountsList_ok (ms normMs : List SandboxMount)
    (h : validateMountsList ms = .ok normMs) :
    ∀ m ∈ normMs, ∃ m0, validateAndNormalizeMount m0 = .ok m := by
  induction ms generalizing normMs with
  | nil =>
    simp [validateMountsList] at h
    subst h
    intro m hm
    cases hm
  | cons hd tl ih =>
    unfold validateMountsList at h
    cases hHead : validateAndNormalizeMount hd with
    | error e => rw [hHead] at h; cases h
    | ok normHd =>
      rw [hHead] at h
      dsimp only [bind, Except.bind] at h
      cases hTail : validateMountsList tl with
      | error e => rw [hTail] at h; cases h
      | ok normTl =>
        rw [hTail] at h
        dsimp only [pure, Except.pure] at h
        injection h with hEq
        subst hEq
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hmTl
        · exact ⟨hd, hHead⟩
        · exact ih normTl hTail m hmTl

private theorem slash_append_inj {a b : String} (h : "/" ++ a = "/" ++ b) : a = b := by
  have hl : ('/' :: a.toList) = ('/' :: b.toList) := by
    have := congrArg String.toList h
    simpa [String.toList_append] using this
  exact String.toList_injective (List.cons.inj hl).2

private theorem allowlisted_single_seg (s : String)
    (h : ("/" ++ s) ∈ ["/usr", "/bin", "/sbin", "/lib", "/lib64"]) :
    s = "usr" ∨ s = "bin" ∨ s = "sbin" ∨ s = "lib" ∨ s = "lib64" := by
  rcases List.mem_cons.mp h with h1 | h1
  · exact Or.inl (slash_append_inj h1)
  · rcases List.mem_cons.mp h1 with h2 | h2
    · exact Or.inr (Or.inl (slash_append_inj h2))
    · rcases List.mem_cons.mp h2 with h3 | h3
      · exact Or.inr (Or.inr (Or.inl (slash_append_inj h3)))
      · rcases List.mem_cons.mp h3 with h4 | h4
        · exact Or.inr (Or.inr (Or.inr (Or.inl (slash_append_inj h4))))
        · rw [List.mem_singleton] at h4
          exact Or.inr (Or.inr (Or.inr (Or.inr (slash_append_inj h4))))

private theorem formatAbsSegs_two_plus_not_allowlisted (d0 d1 : String) (dTl : List String) :
    formatAbsSegs (d0 :: d1 :: dTl) ∉ ["/usr", "/bin", "/sbin", "/lib", "/lib64"] := by
  intro hMem
  have hTwo : 2 ≤ ((formatAbsSegs (d0 :: d1 :: dTl)).toList.filter (· == '/')).length := by
    have hStr : (formatAbsSegs (d0 :: d1 :: dTl)).toList =
        '/' :: (d0.toList ++ '/' :: (String.intercalate "/" (d1 :: dTl)).toList) := by
      simp [formatAbsSegs, String.intercalate_cons_cons, String.toList_append, List.append_assoc]
    rw [hStr, List.filter_cons]
    simp only [beq_self_eq_true, ↓reduceIte, List.length_cons]
    rw [List.filter_append, List.filter_cons]
    simp only [beq_self_eq_true, ↓reduceIte, List.length_append, List.length_cons]
    omega
  rcases List.mem_cons.mp hMem with h1 | h1
  · rw [h1] at hTwo; exact absurd hTwo (by decide)
  · rcases List.mem_cons.mp h1 with h2 | h2
    · rw [h2] at hTwo; exact absurd hTwo (by decide)
    · rcases List.mem_cons.mp h2 with h3 | h3
      · rw [h3] at hTwo; exact absurd hTwo (by decide)
      · rcases List.mem_cons.mp h3 with h4 | h4
        · rw [h4] at hTwo; exact absurd hTwo (by decide)
        · rw [List.mem_singleton] at h4
          rw [h4] at hTwo; exact absurd hTwo (by decide)

private theorem formatAbsSegs_eq_allowlisted_parse (dSegs : List String)
    (hAllow : allowlistedSystemRootPaths.contains (formatAbsSegs dSegs) = true) :
    parseCleanAbsSegs (formatAbsSegs dSegs) = some dSegs := by
  cases dSegs with
  | nil =>
    simp [formatAbsSegs, allowlistedSystemRootPaths] at hAllow
  | cons s rest =>
    cases rest with
    | nil =>
      have hMem : ("/" ++ s) ∈ ["/usr", "/bin", "/sbin", "/lib", "/lib64"] := by
        simpa [formatAbsSegs, String.intercalate_singleton, allowlistedSystemRootPaths] using
          List.contains_iff_mem.mp hAllow
      rcases allowlisted_single_seg s hMem with rfl | rfl | rfl | rfl | rfl <;> rfl
    | cons r tl =>
      exact absurd (List.contains_iff_mem.mp hAllow) (formatAbsSegs_two_plus_not_allowlisted s r tl)

private theorem validateSpecPure_post_cwd (spec : BoxSpec) (valid : ValidBoxSpec)
    (normCwd : String) (normMounts : List SandboxMount)
    (hMounts : validateMountsList spec.mounts.toList = .ok normMounts)
    (h :
      (if (!allDistinct (List.map mountBoxPath normMounts)) = true then
          (Except.error { kind := .invalidInput, message := "duplicate mount boxPath in BoxSpec" } : Except SandboxError ValidBoxSpec)
        else if (spec.portForwards.toList.any fun pf => pf.boxPort == 0 || pf.hostPort == 0) = true then
          Except.error { kind := .invalidInput, message := "portForwards ports must be in 1..65535" }
        else if (!allDistinct (List.map (·.boxPort) spec.portForwards.toList)) = true then
          Except.error { kind := .invalidInput, message := "duplicate boxPort in portForwards" }
        else if (!spec.env.toList.all isValidEnvPair) = true then
          Except.error { kind := .invalidInput, message := "invalid environment variable entry" }
        else if (spec.limits.timeoutMs == 0) = true then
          Except.error { kind := .invalidInput, message := "limits.timeoutMs must be greater than zero" }
        else if (spec.limits.memoryMaxBytes == some 0) = true then
          Except.error { kind := .invalidInput, message := "limits.memoryMaxBytes must be greater than zero when set" }
        else if (spec.limits.pidsMax == some 0) = true then
          Except.error { kind := .invalidInput, message := "limits.pidsMax must be greater than zero when set" }
        else
          Except.ok
            { program := spec.program
              args := spec.args
              cwd := normCwd
              stdin := spec.stdin
              mounts :=
                (if (normMounts.any fun m => mountBoxPath m == "/tmp") = true then normMounts
                  else .scratch "/tmp" :: normMounts).toArray
              allowBoxLocalhost := spec.allowBoxLocalhost
              portForwards := spec.portForwards
              env :=
                (if ((dedupEnvPairs spec.env.toList).any fun kv => kv.1 == "PATH") = true then
                    dedupEnvPairs spec.env.toList
                  else ("PATH", defaultSandboxPath) :: dedupEnvPairs spec.env.toList).toArray
              limits := spec.limits }) = Except.ok valid) :
    valid.cwd = normCwd ∧
    (∀ m ∈ valid.mounts.toList, ∃ m0, validateAndNormalizeMount m0 = .ok m) ∧
    allDistinct (valid.mounts.toList.map mountBoxPath) = true ∧
    valid.mounts.toList.any (fun m => mountBoxPath m == "/tmp") = true ∧
    spec.portForwards.toList.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0) = false ∧
    allDistinct (spec.portForwards.toList.map (·.boxPort)) = true ∧
    spec.env.toList.all isValidEnvPair = true ∧
    (spec.env.toList.any (fun kv => kv.1 == "PATH") = false →
      valid.env.toList.contains ("PATH", defaultSandboxPath) = true) ∧
    (∀ kv ∈ valid.env.toList, kv = ("PATH", defaultSandboxPath) ∨ kv ∈ spec.env.toList) ∧
    valid.env.toList.all isValidEnvPair = true ∧
    valid.env.toList.any (fun kv => kv.1 == "PATH") = true ∧
    valid.limits.timeoutMs > 0 ∧
    (valid.limits.memoryMaxBytes != some 0) = true ∧
    (valid.limits.pidsMax != some 0) = true ∧
    valid.portForwards = spec.portForwards ∧
    valid.limits = spec.limits := by
  by_cases h4 : (!allDistinct (normMounts.map mountBoxPath)) = true
  · rw [ite_eq_left h4] at h; cases h
  ·
      have hMountDistTrue : allDistinct (normMounts.map mountBoxPath) = true := by
        simpa using Bool.eq_false_iff.mpr h4
      rw [ite_eq_right (by simp [hMountDistTrue])] at h
      by_cases h5 : (spec.portForwards.toList.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0)) = true
      · rw [ite_eq_left h5] at h; cases h
      · have hPortsZeroFalse : spec.portForwards.toList.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0) = false :=
          Bool.eq_false_iff.mpr h5
        rw [ite_eq_right (by simp [hPortsZeroFalse])] at h
        by_cases h6 : (!allDistinct (spec.portForwards.toList.map (·.boxPort))) = true
        · rw [ite_eq_left h6] at h; cases h
        · have hPortsDistTrue : allDistinct (spec.portForwards.toList.map (·.boxPort)) = true := by
            simpa using Bool.eq_false_iff.mpr h6
          rw [ite_eq_right (by simp [hPortsDistTrue])] at h
          by_cases h7 : (!spec.env.toList.all isValidEnvPair) = true
          · rw [ite_eq_left h7] at h; cases h
          · have hEnvValidTrue : spec.env.toList.all isValidEnvPair = true := by
              simpa using Bool.eq_false_iff.mpr h7
            rw [ite_eq_right (by simp [hEnvValidTrue])] at h
            by_cases h8 : (spec.limits.timeoutMs == 0) = true
            · rw [ite_eq_left h8] at h; cases h
            · have h8F : (spec.limits.timeoutMs == 0) = false := Bool.eq_false_iff.mpr h8
              have hToutPos : spec.limits.timeoutMs > 0 := by
                have : spec.limits.timeoutMs ≠ 0 := beq_eq_false_iff_ne.mp h8F
                omega
              rw [ite_eq_right (by simp [h8F])] at h
              by_cases h9 : (spec.limits.memoryMaxBytes == some 0) = true
              · rw [ite_eq_left h9] at h; cases h
              · have h9F : (spec.limits.memoryMaxBytes == some 0) = false := Bool.eq_false_iff.mpr h9
                have hMemNe : (spec.limits.memoryMaxBytes != some 0) = true := by
                  simpa [bne] using h9F
                rw [ite_eq_right (by simp [h9F])] at h
                by_cases h10 : (spec.limits.pidsMax == some 0) = true
                · rw [ite_eq_left h10] at h; cases h
                · have h10F : (spec.limits.pidsMax == some 0) = false := Bool.eq_false_iff.mpr h10
                  have hPidsNe : (spec.limits.pidsMax != some 0) = true := by
                    simpa [bne] using h10F
                  rw [ite_eq_right (by simp [h10F])] at h
                  injection h with hValidEq
                  subst hValidEq
                  have hNormMounts := validateMountsList_ok spec.mounts.toList normMounts hMounts
                  refine ⟨rfl, ?_, ?_, ?_, hPortsZeroFalse, hPortsDistTrue,
                    hEnvValidTrue, ?_, ?_, ?_, ?_, hToutPos, hMemNe, hPidsNe, rfl, rfl⟩
                  · intro m hm
                    dsimp only at hm
                    split at hm
                    · exact hNormMounts m hm
                    · rcases List.mem_cons.mp hm with rfl | hmRest
                      · exact ⟨.scratch "/tmp", rfl⟩
                      · exact hNormMounts m hmRest
                  · dsimp only
                    split
                    · exact hMountDistTrue
                    · next hNoTmp =>
                      have hNotMem : (normMounts.map mountBoxPath).contains (mountBoxPath (.scratch "/tmp")) = false := by
                        rw [Bool.eq_false_iff]
                        intro hCont
                        rw [List.contains_iff_mem, List.mem_map] at hCont
                        rcases hCont with ⟨m, hmMem, hmEq⟩
                        apply hNoTmp
                        rw [List.any_eq_true]
                        exact ⟨m, hmMem, beq_iff_eq.mpr hmEq⟩
                      simp only [List.map_cons, allDistinct, hNotMem, hMountDistTrue]
                      rfl
                  · dsimp only
                    split
                    · next hHasTmp => exact hHasTmp
                    · simp [mountBoxPath]
                  · intro hNoPath
                    dsimp only
                    have hDedupNoPath : (dedupEnvPairs spec.env.toList).any (fun kv => kv.1 == "PATH") = false := by
                      rw [any_key_dedupEnvPairs]
                      exact hNoPath
                    simp [hDedupNoPath]
                  · intro kv hkv
                    dsimp only at hkv
                    split at hkv
                    · exact Or.inr (mem_dedupEnvPairs hkv)
                    · rcases List.mem_cons.mp hkv with rfl | hkvRest
                      · exact Or.inl rfl
                      · exact Or.inr (mem_dedupEnvPairs hkvRest)
                  · dsimp only
                    rw [List.all_eq_true]
                    intro kv hkv
                    split at hkv
                    · rw [List.all_eq_true] at hEnvValidTrue
                      exact hEnvValidTrue kv (mem_dedupEnvPairs hkv)
                    · rcases List.mem_cons.mp hkv with rfl | hkvRest
                      · decide
                      · rw [List.all_eq_true] at hEnvValidTrue
                        exact hEnvValidTrue kv (mem_dedupEnvPairs hkvRest)
                  · dsimp only
                    split
                    · next hAny => exact hAny
                    · simp

private theorem validateSpecPure_ok_props (spec : BoxSpec) (valid : ValidBoxSpec)
    (h : validateSpecPure spec = .ok valid) :
    (spec.cwd = none → valid.cwd = defaultSandboxCwd) ∧
    (∀ m ∈ valid.mounts.toList, ∃ m0, validateAndNormalizeMount m0 = .ok m) ∧
    allDistinct (valid.mounts.toList.map mountBoxPath) = true ∧
    valid.mounts.toList.any (fun m => mountBoxPath m == "/tmp") = true ∧
    spec.portForwards.toList.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0) = false ∧
    allDistinct (spec.portForwards.toList.map (·.boxPort)) = true ∧
    spec.env.toList.all isValidEnvPair = true ∧
    (spec.env.toList.any (fun kv => kv.1 == "PATH") = false →
      valid.env.toList.contains ("PATH", defaultSandboxPath) = true) ∧
    (∀ kv ∈ valid.env.toList, kv = ("PATH", defaultSandboxPath) ∨ kv ∈ spec.env.toList) ∧
    valid.env.toList.all isValidEnvPair = true ∧
    valid.env.toList.any (fun kv => kv.1 == "PATH") = true ∧
    valid.limits.timeoutMs > 0 ∧
    (valid.limits.memoryMaxBytes != some 0) = true ∧
    (valid.limits.pidsMax != some 0) = true ∧
    valid.portForwards = spec.portForwards ∧
    valid.limits = spec.limits := by
  unfold validateSpecPure at h
  dsimp only at h
  by_cases h1 : spec.program.isEmpty = true
  · rw [ite_eq_left h1] at h; cases h
  · have h1F : spec.program.isEmpty = false := Bool.eq_false_iff.mpr h1
    rw [ite_eq_right (by simp [h1F])] at h
    by_cases h2 : hasNulChar spec.program.toList = true
    · rw [ite_eq_left h2] at h; cases h
    · have h2F : hasNulChar spec.program.toList = false := Bool.eq_false_iff.mpr h2
      rw [ite_eq_right (by simp [h2F])] at h
      by_cases h3 : (spec.args.toList.any (fun a => hasNulChar a.toList)) = true
      · rw [ite_eq_left h3] at h; cases h
      · have h3F : (spec.args.toList.any (fun a => hasNulChar a.toList)) = false :=
          Bool.eq_false_iff.mpr h3
        rw [ite_eq_right (by simp [h3F])] at h
        cases hCwd : spec.cwd with
        | none =>
          rw [hCwd] at h
          dsimp only at h
          cases hMounts : validateMountsList spec.mounts.toList with
          | error _ => rw [hMounts] at h; cases h
          | ok normMounts =>
            rw [hMounts] at h
            have hPost := validateSpecPure_post_cwd spec valid defaultSandboxCwd normMounts hMounts h
            exact ⟨fun _ => hPost.1, hPost.2⟩
        | some d =>
          rw [hCwd] at h
          dsimp only at h
          cases hNorm : normalizeCleanAbsPath d with
          | none =>
            rw [hNorm] at h
            dsimp only at h
            cases h
          | some cleanD =>
            rw [hNorm] at h
            dsimp only at h
            cases hMounts : validateMountsList spec.mounts.toList with
            | error _ => rw [hMounts] at h; cases h
            | ok normMounts =>
              rw [hMounts] at h
              have hPost := validateSpecPure_post_cwd spec valid cleanD normMounts hMounts h
              exact ⟨fun hc => (by cases hc), hPost.2⟩

private theorem resolveBoxPath_maskedPreset_of_prefix (plan : CompiledSandboxPlan)
    (hSegs : List String) (dSegs : List String)
    (hdNotEmpty : (!dSegs.isEmpty) = true)
    (hdAllow : allowlistedSystemRootPaths.contains (formatAbsSegs dSegs) = true)
    (hdPref : dSegs.isPrefixOf hSegs = true)
    (hdLen : dSegs.length < hSegs.length)
    (hMaskContains : formatAbsSegs hSegs ∈ plan.maskedPresetPaths.toList)
    (hSegsParse : parseCleanAbsSegs (formatAbsSegs hSegs) = some hSegs)
    (boxP : String) (rawPSegs : List String)
    (hBoxParse : parseCleanAbsSegs boxP = some rawPSegs)
    (hPrefix : hSegs.isPrefixOf (expandPresetTopSymlink plan.presetSystemEntries.toList rawPSegs) = true) :
    resolveBoxPath plan boxP = .maskedPreset := by
  let segs := expandPresetTopSymlink plan.presetSystemEntries.toList rawPSegs
  have hPrefSegs : hSegs.isPrefixOf segs = true := hPrefix
  have hdSegsPref : dSegs.isPrefixOf segs = true := by
    rw [List.isPrefixOf_iff_prefix] at hdPref hPrefSegs ⊢
    exact List.IsPrefix.trans hdPref hPrefSegs
  have hDNonEmpty : dSegs ≠ [] := by
    intro hNil; subst hNil; simp at hdNotEmpty
  obtain ⟨d0, dTl, rfl⟩ := List.exists_cons_of_ne_nil hDNonEmpty
  have hdTop : d0 = "usr" ∨ d0 = "bin" ∨ d0 = "sbin" ∨ d0 = "lib" ∨ d0 = "lib64" := by
    cases dTl with
    | nil =>
      have hMem : ("/" ++ d0) ∈ ["/usr", "/bin", "/sbin", "/lib", "/lib64"] := by
        simpa [formatAbsSegs, String.intercalate_singleton, allowlistedSystemRootPaths] using
          List.contains_iff_mem.mp hdAllow
      exact allowlisted_single_seg d0 hMem
    | cons d1 dRest =>
      exact absurd (List.contains_iff_mem.mp hdAllow) (formatAbsSegs_two_plus_not_allowlisted d0 d1 dRest)
  have hSegsHead : segs.head? = some d0 := by
    rw [List.isPrefixOf_iff_prefix] at hdSegsPref
    rcases hdSegsPref with ⟨tail, hEq⟩
    rw [← hEq]
    rfl
  have hRawNonEmpty : rawPSegs ≠ [] := by
    intro hNil
    have hSegsNil : segs = [] := by simp [segs, hNil, expandPresetTopSymlink]
    rw [hSegsNil] at hSegsHead
    cases hSegsHead
  obtain ⟨pTop, pRest, rfl⟩ := List.exists_cons_of_ne_nil hRawNonEmpty
  have hNotProc : (segs.head? == some "proc") = false := by
    rw [hSegsHead]
    rcases hdTop with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hNotDev : (segs.head? == some "dev") = false := by
    rw [hSegsHead]
    rcases hdTop with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hNotEtcHosts : (segs == ["etc", "hosts"]) = false := by
    rw [beq_eq_false_iff_ne]
    intro hEq
    have hHead := congrArg List.head? hEq
    rw [hSegsHead] at hHead
    have hD0Etc : d0 = "etc" := Option.some.inj hHead
    rcases hdTop with rfl | rfl | rfl | rfl | rfl <;> exact absurd hD0Etc (by decide)
  have hHSegsNotEmpty : (!hSegs.isEmpty) = true := by
    cases hSegs with
    | nil => simp at hdLen
    | cons _ _ => rfl
  have hMaskAny : plan.maskedPresetPaths.toList.any (fun mp =>
      match parseCleanAbsSegs mp with
      | some mSegs => !mSegs.isEmpty && mSegs.isPrefixOf segs
      | none => false) = true := by
    rw [List.any_eq_true]
    refine ⟨formatAbsSegs hSegs, hMaskContains, ?_⟩
    rw [hSegsParse]
    dsimp only
    simp only [hHSegsNotEmpty, hPrefSegs, Bool.and_self]
  unfold resolveBoxPath
  rw [hBoxParse]
  dsimp only
  change (if (expandPresetTopSymlink plan.presetSystemEntries.toList (pTop :: pRest)).head? == some "proc" then
      if plan.mountFreshProc then ResolvedBoxAccess.virtualProc else ResolvedBoxAccess.unmounted
    else if (expandPresetTopSymlink plan.presetSystemEntries.toList (pTop :: pRest)).head? == some "dev" then
      if plan.mountSafeDev && (safeVirtualDevPaths.contains (formatAbsSegs (expandPresetTopSymlink plan.presetSystemEntries.toList (pTop :: pRest))) || (expandPresetTopSymlink plan.presetSystemEntries.toList (pTop :: pRest)).take 2 == ["dev", "pts"]) then
        ResolvedBoxAccess.virtualSafeDev
      else
        ResolvedBoxAccess.unmounted
    else if expandPresetTopSymlink plan.presetSystemEntries.toList (pTop :: pRest) == ["etc", "hosts"] then
      if plan.emptyRoot then ResolvedBoxAccess.virtualEtcHosts else ResolvedBoxAccess.unmounted
    else if plan.maskedPresetPaths.toList.any (fun mp =>
        match parseCleanAbsSegs mp with
        | some mSegs => !mSegs.isEmpty && mSegs.isPrefixOf (expandPresetTopSymlink plan.presetSystemEntries.toList (pTop :: pRest))
        | none => false) then
      ResolvedBoxAccess.maskedPreset
    else _) = ResolvedBoxAccess.maskedPreset
  have hSegsDef : expandPresetTopSymlink plan.presetSystemEntries.toList (pTop :: pRest) = segs := rfl
  rw [hSegsDef]
  simp only [hNotProc, Bool.false_eq_true, ↓reduceIte, hNotDev, hNotEtcHosts, hMaskAny]

/-- Formal proof of `Model.SpecCompilePlanSound` for `validateSpecPure` and `compilePlan`. -/
theorem specCompilePlanSound : Model.SpecCompilePlanSound := by
  intro spec valid preset hVal
  obtain ⟨hCwdDef, hMountsNorm, hMountsDist, hHasTmp, hPortsZero, hPortsDist, _,
    hDefaultPath, hEnvSub, hValidEnv, hValidHasPath, hToutPos, hMemNe, hPidsNe,
    hPortFwdEq, _⟩ := validateSpecPure_ok_props spec valid hVal
  let plan := compilePlan valid preset
  let sysEntries := dedupByFirst presetEntryBoxPath
    (preset.systemEntries.toList.filterMap sanitizePresetSystemEntry)
  let etcEntries := dedupByFirst id
    (preset.etcPaths.toList.filterMap fun p =>
      match normalizeCleanAbsPath p with
      | some cleanP => if allowlistedEtcPaths.contains cleanP then some cleanP else none
      | none => none)
  let mountedSysDirSegs := sysEntries.filterMap fun
    | .readOnlyDir p => parseCleanAbsSegs p
    | .topSymlink _ _ => none
  let rawMasks := dedupByFirst id
    (preset.excludedHomePaths.toList.filterMap fun h =>
      match parseCleanAbsSegs h with
      | some rawHSegs =>
        let hSegs := expandPresetTopSymlink sysEntries rawHSegs
        if isStrictlyNestedInDirs mountedSysDirSegs hSegs then
          some (formatAbsSegs hSegs)
        else
          none
      | none => none)
  have hSysSan : ∀ e ∈ sysEntries, (sanitizePresetSystemEntry e).isSome = true := by
    intro e he
    have heFilt := mem_dedupByFirst presetEntryBoxPath _ he
    rw [List.mem_filterMap] at heFilt
    rcases heFilt with ⟨e0, _, he0Eq⟩
    rw [sanitizePresetSystemEntry_idempotent e0 e he0Eq]
    rfl
  have hSysAllow : ∀ e ∈ sysEntries, allowlistedSystemRootPaths.contains (presetEntryBoxPath e) = true := by
    intro e he
    have heFilt := mem_dedupByFirst presetEntryBoxPath _ he
    rw [List.mem_filterMap] at heFilt
    rcases heFilt with ⟨e0, _, he0Eq⟩
    exact sanitizePresetSystemEntry_allowlisted e0 e he0Eq
  have hSysDist : allDistinct (sysEntries.map presetEntryBoxPath) = true :=
    allDistinct_dedupByFirst presetEntryBoxPath _
  have hEtcAllow : etcEntries.all (fun p => allowlistedEtcPaths.contains p) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hpFilt := mem_dedupByFirst id _ hp
    rw [List.mem_filterMap] at hpFilt
    rcases hpFilt with ⟨p0, _, hp0Eq⟩
    split at hp0Eq
    · split at hp0Eq
      · next hAllow =>
        injection hp0Eq with hEq
        subst hEq
        exact hAllow
      · cases hp0Eq
    · cases hp0Eq
  have hEtcDist : allDistinct etcEntries = true := by
    simpa [etcEntries] using allDistinct_dedupByFirst id (preset.etcPaths.toList.filterMap fun p =>
      match normalizeCleanAbsPath p with
      | some cleanP => if allowlistedEtcPaths.contains cleanP then some cleanP else none
      | none => none)
  have hRawMasksValid : ∀ m ∈ rawMasks, ∃ segs, parseCleanAbsSegs m = some segs ∧ (!segs.isEmpty) = true ∧ formatAbsSegs segs = m := by
    intro m hm
    have hmFilt := mem_dedupByFirst id _ hm
    rw [List.mem_filterMap] at hmFilt
    rcases hmFilt with ⟨h0, _, hh0Eq⟩
    dsimp only at hh0Eq
    cases hParse : parseCleanAbsSegs h0 with
    | none => rw [hParse] at hh0Eq; cases hh0Eq
    | some rawHSegs =>
      rw [hParse] at hh0Eq
      dsimp only at hh0Eq
      split at hh0Eq
      · next hNested =>
        injection hh0Eq with hmEq
        let hSegs := expandPresetTopSymlink sysEntries rawHSegs
        have hSegsValid : ∀ s ∈ hSegs, ValidSeg s :=
          expandPresetTopSymlink_validSegs sysEntries rawHSegs (parseCleanAbsSegs_validSegs h0 rawHSegs hParse)
        have hParseFmt : parseCleanAbsSegs (formatAbsSegs hSegs) = some hSegs :=
          parseCleanAbsSegs_formatAbsSegs hSegs hSegsValid
        have hNonEmpty : (!hSegs.isEmpty) = true := by
          unfold isStrictlyNestedInDirs at hNested
          rw [List.any_eq_true] at hNested
          rcases hNested with ⟨dSegs, _, hProps⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hProps
          have hLenPos : 0 < hSegs.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hProps.2
          simp only [Bool.not_eq_true']
          cases hEq : hSegs with
          | nil => rw [hEq] at hLenPos; cases hLenPos
          | cons _ _ => rfl
        rw [← hmEq]
        exact ⟨hSegs, hParseFmt, hNonEmpty, rfl⟩
      · cases hh0Eq
  have hPlanValid : ValidCompiledPlan plan := by
    unfold ValidCompiledPlan isValidCompiledPlan
    dsimp only [plan, compilePlan]
    simp only [Bool.true_and, Bool.and_true, Bool.and_eq_true, and_assoc]
    simp only [hHasTmp, ↓reduceIte]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.all_eq_true]; exact hSysSan
    · exact hSysDist
    · exact hEtcAllow
    · exact hEtcDist
    · rw [List.all_eq_true]
      intro m hm
      rw [mem_sortByDepth_iff] at hm
      rcases hRawMasksValid m hm with ⟨segs, hParse, hNE, hFmt⟩
      rw [hParse]
      dsimp only
      simp only [hNE, hFmt, beq_self_eq_true, Bool.and_self]
    · rw [List.all_eq_true]
      intro m hm
      rw [mem_sortByDepth_iff] at hm
      rcases hMountsNorm m hm with ⟨m0, hm0⟩
      rw [validateAndNormalizeMount_idempotent m0 m hm0]
      exact beq_self_sandboxMount m
    · exact allDistinct_sortByDepth mountBoxDepth mountBoxPath valid.mounts.toList hMountsDist
    · rw [List.any_eq_true]
      rw [List.any_eq_true] at hHasTmp
      rcases hHasTmp with ⟨m, hm, hEq⟩
      exact ⟨m, (mem_sortByDepth_iff mountBoxDepth valid.mounts.toList m).mpr hm, hEq⟩
    · rw [hPortFwdEq, List.all_eq_true]
      intro pf hpf
      by_cases hZero : (pf.boxPort == 0 || pf.hostPort == 0) = true
      · exfalso
        have hNotZero := Bool.eq_false_iff.mp hPortsZero
        apply hNotZero
        rw [List.any_eq_true]
        exact ⟨pf, hpf, hZero⟩
      · have hZeroF : (pf.boxPort == 0 || pf.hostPort == 0) = false := Bool.eq_false_iff.mpr hZero
        by_cases hb : pf.boxPort = 0
        · simp [hb] at hZeroF
        · by_cases hh : pf.hostPort = 0
          · simp [hh] at hZeroF
          · simp [hb, hh]
    · rw [hPortFwdEq]; exact hPortsDist
    · exact hValidEnv
    · exact hValidHasPath
    · exact decide_eq_true hToutPos
    · exact hMemNe
    · exact hPidsNe
  have hEtcHosts : resolveBoxPath plan "/etc/hosts" = .virtualEtcHosts := by
    have hParseEtc : parseCleanAbsSegs "/etc/hosts" = some ["etc", "hosts"] := rfl
    have hNotInSys : sysEntries.find? (fun e => presetEntryBoxPath e == "/etc") = none := by
      cases hFind : sysEntries.find? (fun e => presetEntryBoxPath e == "/etc") with
      | none => rfl
      | some e =>
        exfalso
        have heMem : e ∈ sysEntries := List.mem_of_find?_eq_some hFind
        have hePred : (presetEntryBoxPath e == "/etc") = true :=
          List.find?_some (p := fun x => presetEntryBoxPath x == "/etc") hFind
        have heEq : presetEntryBoxPath e = "/etc" := beq_iff_eq.mp hePred
        have hAl := hSysAllow e heMem
        rw [heEq] at hAl
        simp [allowlistedSystemRootPaths] at hAl
    have hExpand : expandPresetTopSymlink sysEntries ["etc", "hosts"] = ["etc", "hosts"] := by
      unfold expandPresetTopSymlink
      dsimp only
      have hTop : ("/" ++ "etc" : String) = "/etc" := rfl
      rw [hTop, hNotInSys]
    unfold resolveBoxPath
    rw [hParseEtc]
    dsimp only [plan, compilePlan]
    change (let segs := expandPresetTopSymlink sysEntries ["etc", "hosts"]
      let canonBox := formatAbsSegs segs
      if segs.head? == some "proc" then
        if true then ResolvedBoxAccess.virtualProc else ResolvedBoxAccess.unmounted
      else if segs.head? == some "dev" then
        if true && (safeVirtualDevPaths.contains canonBox || segs.take 2 == ["dev", "pts"]) then
          ResolvedBoxAccess.virtualSafeDev
        else
          ResolvedBoxAccess.unmounted
      else if segs == ["etc", "hosts"] then
        if true then ResolvedBoxAccess.virtualEtcHosts else ResolvedBoxAccess.unmounted
      else _) = ResolvedBoxAccess.virtualEtcHosts
    rw [hExpand]
    rfl
  refine ⟨hPlanValid, rfl, rfl, rfl, rfl, rfl, rfl, hCwdDef, ?_, ?_, ?_, hEtcHosts, ?_⟩
  · dsimp only [plan, compilePlan]
    simp only [hHasTmp, ↓reduceIte, List.any_eq_true]
    rw [List.any_eq_true] at hHasTmp
    rcases hHasTmp with ⟨m, hm, hEq⟩
    exact ⟨m, (mem_sortByDepth_iff mountBoxDepth valid.mounts.toList m).mpr hm, hEq⟩
  · exact hDefaultPath
  · exact hEnvSub
  · intro h rawHSegs hhMem hRawH hSegs hSysEx
    rcases hSysEx with ⟨sysP, hSysPMem, dSegs, hSysPEq, hdNE, hdPref, hdLen⟩
    have hSysPMem' : sysP ∈ sysEntries := by simpa [plan, compilePlan] using hSysPMem
    have hAllowD : allowlistedSystemRootPaths.contains (formatAbsSegs dSegs) = true := by
      have := hSysAllow sysP hSysPMem'
      simpa [hSysPEq, presetEntryBoxPath] using this
    have hParseD : parseCleanAbsSegs (formatAbsSegs dSegs) = some dSegs :=
      formatAbsSegs_eq_allowlisted_parse dSegs hAllowD
    have hInMounted : dSegs ∈ mountedSysDirSegs := by
      dsimp only [mountedSysDirSegs]
      rw [List.mem_filterMap]
      refine ⟨sysP, hSysPMem', ?_⟩
      rw [hSysPEq]
      exact hParseD
    have hSegsEq : hSegs = expandPresetTopSymlink sysEntries rawHSegs := rfl
    have hNested : isStrictlyNestedInDirs mountedSysDirSegs hSegs = true := by
      unfold isStrictlyNestedInDirs
      rw [List.any_eq_true]
      exact ⟨dSegs, hInMounted, by simp [hdNE, hdPref, hdLen]⟩
    have hInRawMasks : formatAbsSegs hSegs ∈ rawMasks := by
      dsimp only [rawMasks]
      apply mem_dedupByFirst_id_of_mem [] _ _ (by rfl)
      rw [List.mem_filterMap]
      refine ⟨h, hhMem, ?_⟩
      rw [hRawH]
      dsimp only
      change (if isStrictlyNestedInDirs mountedSysDirSegs (expandPresetTopSymlink sysEntries rawHSegs) then
        some (formatAbsSegs (expandPresetTopSymlink sysEntries rawHSegs)) else none) = some (formatAbsSegs hSegs)
      rw [← hSegsEq]
      simp [hNested]
    have hInMasked : formatAbsSegs hSegs ∈ plan.maskedPresetPaths.toList := by
      dsimp only [plan, compilePlan]
      rw [List.toList_toArray, mem_sortByDepth_iff]
      exact hInRawMasks
    have hSegsValid : ∀ s ∈ hSegs, ValidSeg s := by
      rw [hSegsEq]
      exact expandPresetTopSymlink_validSegs sysEntries rawHSegs (parseCleanAbsSegs_validSegs h rawHSegs hRawH)
    have hParseHSegs : parseCleanAbsSegs (formatAbsSegs hSegs) = some hSegs :=
      parseCleanAbsSegs_formatAbsSegs hSegs hSegsValid
    refine ⟨List.contains_iff_mem.mpr hInMasked, ?_⟩
    intro boxP rawPSegs hBoxParse hPref
    have hdNE' : (!dSegs.isEmpty) = true := by simpa using hdNE
    exact resolveBoxPath_maskedPreset_of_prefix plan
      hSegs dSegs hdNE' hAllowD hdPref hdLen hInMasked hParseHSegs boxP rawPSegs hBoxParse hPref

private def threeCatValid : ValidBoxSpec :=
  { program := "/bin/sh"
    args := #[]
    cwd := "/tmp"
    stdin := ByteArray.empty
    mounts := #[.scratch "/tmp", .readOnly "/host/ro" "/ro", .readWrite "/host/rw" "/rw"]
    allowBoxLocalhost := true
    portForwards := #[{ boxPort := 8080, hostPort := 18080 }]
    env := #[("PATH", "/usr/bin:/bin")]
    limits :=
      { timeoutMs := 5000
        memoryMaxBytes := some 4096
        pidsMax := some 4
        fileSizeMaxBytes := some 16 } }

private def threeCatPlan : CompiledSandboxPlan :=
  compilePlan threeCatValid
    { systemEntries := #[.readOnlyDir "/usr", .topSymlink "/bin" "usr/bin"]
      etcPaths := #["/etc/passwd"]
      excludedHomePaths := #["/usr/local/homes/dev"] }

private theorem threeCatRes_home1 : resolveBoxPath threeCatPlan "/home/u/.ssh/id_rsa" = .unmounted := by cbv
private theorem threeCatRes_home2 : resolveBoxPath threeCatPlan "/usr/local/homes/dev/.ssh/id_rsa" = .maskedPreset := by cbv
private theorem threeCatRes_home3 : resolveBoxPath threeCatPlan "/usr/local/homes/dev" = .maskedPreset := by cbv
private theorem threeCatRes_ro : resolveBoxPath threeCatPlan "/ro/file.txt" = .userReadOnly "/host/ro/file.txt" := by cbv
private theorem threeCatRes_rwBig : resolveBoxPath threeCatPlan "/rw/big.txt" = .userReadWrite ["host", "rw"] "/host/rw/big.txt" := by cbv
private theorem threeCatRes_root : resolveBoxPath threeCatPlan "/" = .virtualRoot := by cbv
private theorem threeCatRes_etc : resolveBoxPath threeCatPlan "/etc/hosts" = .virtualEtcHosts := by cbv
private theorem threeCatRes_tmp : resolveBoxPath threeCatPlan "/tmp/scratch.txt" = .userScratch "/tmp/scratch.txt" := by cbv
private theorem threeCatRes_rwOut : resolveBoxPath threeCatPlan "/rw/out.txt" = .userReadWrite ["host", "rw"] "/host/rw/out.txt" := by cbv

private theorem threeCat_bigSize :
    16 < ("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" : String).utf8ByteSize := by
  decide

/-- Proof of `test_psandbox_model_threeCategorySyscallSemantics` for `stepGuestSyscall`. -/
theorem proof_psandbox_model_threeCategorySyscallSemantics :
    AllPass test_psandbox_model_threeCategorySyscallSemantics := by
  intro st₀ ⟨hMem, _⟩
  dsimp only [test_psandbox_model_threeCategorySyscallSemantics, Bind.bind, Pure.pure,
    AllPassRun, assert]
  let payload := "ok".toUTF8
  have hVal :
      validateSpecPure
        { program := "/bin/sh"
          mounts := #[.readOnly "/host/ro" "/ro", .readWrite "/host/rw" "/rw"]
          allowBoxLocalhost := true
          portForwards := #[{ boxPort := 8080, hostPort := 18080 }]
          limits :=
            { timeoutMs := 5000
              memoryMaxBytes := some 4096
              pidsMax := some 4
              fileSizeMaxBytes := some 16 } } = .ok threeCatValid := rfl
  have hPlan :
      compilePlan threeCatValid
        { systemEntries := #[.readOnlyDir "/usr", .topSymlink "/bin" "usr/bin"]
          etcPaths := #["/etc/passwd"]
          excludedHomePaths := #["/usr/local/homes/dev"] } = threeCatPlan := rfl
  have hFind9090 : threeCatPlan.portForwards.toList.find? (fun pf => pf.boxPort == 9090) = none := by cbv
  have hFind8080 : threeCatPlan.portForwards.toList.find? (fun pf => pf.boxPort == 8080) =
      some { boxPort := 8080, hostPort := 18080 } := by cbv
  have hAllowLo : threeCatPlan.allowBoxLocalhost = true := by cbv
  have hLimF : threeCatPlan.limits.fileSizeMaxBytes = some 16 := by cbv
  have hLimM : threeCatPlan.limits.memoryMaxBytes = some 4096 := by cbv
  have hSmallPayload : (payload.size > 16) = false := by decide
  have hSmallPayloadMem : (payload.size > 4096) = false := by decide
  have hTmpStep :
      stepGuestSyscall threeCatPlan st₀ (.fsWrite "/tmp/scratch.txt" payload) =
      .ok
        { st₀ with
          box :=
            { st₀.box with
              scratchFs := putFsBytes st₀.box.scratchFs "/tmp/scratch.txt" payload
              boxMemoryBytes := payload.size } } := by
    have hZeroSub : (st₀.box.boxMemoryBytes -
        ((lookupFsBytes st₀.box.scratchFs "/tmp/scratch.txt").map ByteArray.size |>.getD 0)) +
        payload.size = payload.size := by
      rw [hMem]; simp
    unfold stepGuestSyscall
    dsimp only
    rw [threeCatRes_tmp]
    dsimp only
    rw [hZeroSub, hLimF, hLimM]
    simp [hSmallPayload, hSmallPayloadMem]
  have hLoStep :
      stepGuestSyscall threeCatPlan st₀ (.tcpSend true 9090 payload) =
      .ok { st₀ with box := { st₀.box with boxLocalPorts := st₀.box.boxLocalPorts ++ [(9090, payload)] } } := by
    unfold stepGuestSyscall
    dsimp only
    have hNe : ((9090 : UInt16) == 0) = false := by decide
    simp only [Bool.not_true, Bool.false_or, hNe, Bool.false_eq_true, ↓reduceIte, hFind9090, hAllowLo]
  have hFwdStep :
      stepGuestSyscall threeCatPlan st₀ (.tcpSend true 8080 payload) =
      .ok { st₀ with host := { st₀.host with hostPorts := st₀.host.hostPorts ++ [(18080, payload)] } } := by
    unfold stepGuestSyscall
    dsimp only
    have hNe : ((8080 : UInt16) == 0) = false := by decide
    simp only [Bool.not_true, Bool.false_or, hNe, Bool.false_eq_true, ↓reduceIte, hFind8080]
  have hRwStep :
      stepGuestSyscall threeCatPlan st₀ (.fsWrite "/rw/out.txt" payload) =
      .ok { st₀ with host := { st₀.host with hostFs := putFsBytes st₀.host.hostFs "/host/rw/out.txt" payload } } := by
    unfold stepGuestSyscall
    dsimp only
    rw [threeCatRes_rwOut, hLimF]
    simp [hSmallPayload]
  rw [hVal]
  dsimp only
  rw [hPlan]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold stepGuestSyscall; dsimp only; rw [threeCatRes_home1]; rfl
  · unfold stepGuestSyscall; dsimp only; rw [threeCatRes_home2]; rfl
  · unfold stepGuestSyscall; dsimp only; rw [threeCatRes_ro]
  · unfold stepGuestSyscall; dsimp only; rw [threeCatRes_rwBig, hLimF]
    simp [threeCat_bigSize]
  · unfold stepGuestSyscall; dsimp only; rw [threeCatRes_root]
  · unfold stepGuestSyscall; dsimp only; rw [threeCatRes_root]
  · unfold stepGuestSyscall; dsimp only; rw [threeCatRes_etc]
  · unfold stepGuestSyscall; dsimp only; rw [threeCatRes_etc]
  · unfold stepGuestSyscall; dsimp only; rw [threeCatRes_home3]
  · rw [hTmpStep]
    refine ⟨⟨rfl, lookupFsBytes_putFsBytes_eq st₀.box.scratchFs "/tmp/scratch.txt" payload⟩, ?_⟩
    rw [hLoStep]
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    rw [hFwdStep]
    refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
    rw [hRwStep]
    refine ⟨⟨?_, rfl, rfl⟩, trivial⟩
    exact lookupFsBytes_putFsBytes_eq st₀.host.hostFs "/host/rw/out.txt" payload

/-- Non-vacuity `CanReach` witness for `test_psandbox_model_threeCategorySyscallSemantics`. -/
theorem reach_psandbox_model_threeCategorySyscallSemantics :
    CanReach test_psandbox_model_threeCategorySyscallSemantics := by
  let st₀ : SandboxWorldState := { box := { boxMemoryBytes := 0, boxProcs := [1] } }
  have hAll := proof_psandbox_model_threeCategorySyscallSemantics st₀ ⟨rfl, rfl⟩
  refine ⟨st₀, ⟨rfl, rfl⟩, ?_⟩
  simpa [Bind.bind, Pure.pure, CanReachRun, AllPassRun, assert] using hAll

/-- Proof of `test_psandbox_model_hostUnchangedOutsideGrants` for `stepGuestSyscall`. -/
theorem proof_psandbox_model_hostUnchangedOutsideGrants :
    AllPass test_psandbox_model_hostUnchangedOutsideGrants :=
  ⟨specHostUnchangedOutsideGrants, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_model_hostUnchangedOutsideGrants`. -/
theorem reach_psandbox_model_hostUnchangedOutsideGrants :
    CanReach test_psandbox_model_hostUnchangedOutsideGrants :=
  ⟨specHostUnchangedOutsideGrants, trivial⟩

/-- Proof of `test_psandbox_model_zeroSurvivingBoxProcs` for `stepGuestSyscall` and `reapAndTeardownBox`. -/
theorem proof_psandbox_model_zeroSurvivingBoxProcs :
    AllPass test_psandbox_model_zeroSurvivingBoxProcs :=
  ⟨specZeroSurvivingBoxProcs, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_model_zeroSurvivingBoxProcs`. -/
theorem reach_psandbox_model_zeroSurvivingBoxProcs :
    CanReach test_psandbox_model_zeroSurvivingBoxProcs :=
  ⟨specZeroSurvivingBoxProcs, trivial⟩

/-- Proof of `test_psandbox_model_compilePlanSound` for `validateSpecPure` and `compilePlan`. -/
theorem proof_psandbox_model_compilePlanSound :
    AllPass test_psandbox_model_compilePlanSound :=
  ⟨specCompilePlanSound, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_model_compilePlanSound`. -/
theorem reach_psandbox_model_compilePlanSound :
    CanReach test_psandbox_model_compilePlanSound :=
  ⟨specCompilePlanSound, trivial⟩

end LeanSwe.ProcessSandbox.Proofs
