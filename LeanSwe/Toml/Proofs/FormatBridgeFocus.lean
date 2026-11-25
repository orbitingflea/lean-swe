import LeanSwe.Toml.Proofs.FormatBridgeVal

/-!
# Path Focus & Statement Composition for `FormatBridge` (`FormatBridgeFocus`)

Proves `renderStmts_append_true` (homomorphic statement composition when `trailingNl = true`),
defines `FocusAtPath` lenses (`focusAtPath_root`, `focusAtPath_stepTable`, `focusAtPath_stepAot`),
and constructs `chooseInlineStmts` / `chooseSectionStmts` / `chooseAotStmts`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml LeanSwe.Toml.Model LeanSwe.Toml.Impl LeanSwe.NumParse

/-- Concatenate formatted lines with trailing `'\n'` on every line. -/
def concatLinesNl : List String → String
  | [] => ""
  | l :: ls => l ++ "\n" ++ concatLinesNl ls

/-- `concatLinesNl` distributes over `List.append`. -/
theorem concatLinesNl_append :
    ∀ l1 l2 : List String, concatLinesNl (l1 ++ l2) = concatLinesNl l1 ++ concatLinesNl l2
  | [], _ => by simp [concatLinesNl]
  | l :: ls, l2 => by simp [concatLinesNl, concatLinesNl_append ls l2, String.append_assoc]

/-- On non-empty lists, `concatLinesNl` equals `String.intercalate "\n" _ ++ "\n"`. -/
theorem concatLinesNl_cons (hd : String) :
    ∀ tl : List String, concatLinesNl (hd :: tl) = String.intercalate "\n" (hd :: tl) ++ "\n"
  | [] => by simp [concatLinesNl, String.intercalate_singleton]
  | b :: bs => by
    rw [concatLinesNl, concatLinesNl_cons b bs, String.intercalate_cons_cons]
    simp [String.append_assoc]

/-- Compute the active table path after executing `StmtTape` instructions from `act`. -/
def endActivePath (act : List String) : List StmtTape → List String
  | [] => act
  | .tableHeader _ _ dk _ _ :: rest => endActivePath dk.path rest
  | .aotHeader _ _ dk _ _ :: rest => endActivePath dk.path rest
  | .assign _ _ _ _ _ _ :: rest => endActivePath act rest

/-- When `trailingNl = true`, `Model.renderStmts` composes sequentially over `s1 ++ s2`. -/
theorem renderStmts_append_true (doc : List (String × TomlValue)) :
    ∀ (s1 s2 : List StmtTape) (act : List String) (sk1 sk2 sk3 : List (String × SkeletonNode)) (str1 str2 : String),
      renderStmts doc act sk1 true s1 = some (sk2, str1) →
      renderStmts doc (endActivePath act s1) sk2 true s2 = some (sk3, str2) →
      renderStmts doc act sk1 true (s1 ++ s2) = some (sk3, str1 ++ str2)
  | [], _, act, sk1, sk2, sk3, str1, str2, h1, h2 => by
    simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at h1
    rcases h1 with ⟨rfl, rfl⟩; simpa [endActivePath] using h2
  | stmt :: r1, s2, act, sk1, sk2, sk3, str1, str2, h1, h2 => by
    cases stmt with
    | tableHeader pre wsO dk wsC suf =>
      simp only [List.cons_append, renderStmts, ↓reduceIte, ite_self] at h1 ⊢
      split at h1 <;> try (simp at h1; done)
      rename_i hok; simp only [hok]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h1
      rcases h1 with ⟨rk, hrk, rsuf, hsuf, nsk, hhdr, ⟨fsk, tl1⟩, htl1, hp⟩
      dsimp only at hp h2; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      simp [hrk, hsuf, hhdr, renderStmts_append_true doc r1 s2 dk.path nsk fsk sk3 tl1 str2 htl1 h2, String.append_assoc]
    | aotHeader pre wsO dk wsC suf =>
      simp only [List.cons_append, renderStmts, ↓reduceIte, ite_self] at h1 ⊢
      split at h1 <;> try (simp at h1; done)
      rename_i hok; simp only [hok]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h1
      rcases h1 with ⟨rk, hrk, rsuf, hsuf, nsk, hhdr, ⟨fsk, tl1⟩, htl1, hp⟩
      dsimp only at hp h2; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      simp [hrk, hsuf, hhdr, renderStmts_append_true doc r1 s2 dk.path nsk fsk sk3 tl1 str2 htl1 h2, String.append_assoc]
    | assign pre dk wsL wsR vt suf =>
      simp only [List.cons_append, renderStmts, ↓reduceIte, ite_self] at h1 ⊢
      split at h1 <;> try (simp at h1; done)
      rename_i hok; simp only [hok]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h1
      rcases h1 with ⟨rk, hrk, rsuf, hsuf, ⟨nsk, v⟩, hins, rv, hrv, ⟨fsk, tl1⟩, htl1, hp⟩
      dsimp only at hrv htl1 hp h2; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      simp [hrk, hsuf, hins, hrv, renderStmts_append_true doc r1 s2 act nsk fsk sk3 tl1 str2 htl1 h2, String.append_assoc]

private def mkCanonDottedCont : List String → List DottedSegCont
  | [] => []
  | k :: ks => { wsBeforeDot := "", wsAfterDot := "", key := k, style := chooseKeyStyle k } :: mkCanonDottedCont ks

/-- Construct a canonical `DottedKeyTape` for `path ++ [kLast]`. -/
def mkCanonDottedKey (path : List String) (kLast : String) : DottedKeyTape :=
  match path with
  | [] => { firstKey := kLast, firstStyle := chooseKeyStyle kLast, rest := [] }
  | k0 :: ks => { firstKey := k0, firstStyle := chooseKeyStyle k0, rest := mkCanonDottedCont (ks ++ [kLast]) }

private theorem mkCanonDottedCont_keys : ∀ l : List String, (mkCanonDottedCont l).map DottedSegCont.key = l
  | [] => rfl
  | _ :: ks => by simp [mkCanonDottedCont, mkCanonDottedCont_keys ks]

/-- Logical path of `mkCanonDottedKey path k` is `path ++ [k]`. -/
theorem mkCanonDottedKey_path (path : List String) (k : String) :
    (mkCanonDottedKey path k).path = path ++ [k] := by
  cases path <;> simp [mkCanonDottedKey, DottedKeyTape.path, mkCanonDottedCont_keys]

private theorem renderDottedKey_canonAux (k0 : String) :
    ∀ l : List String,
      renderDottedKey { firstKey := k0, firstStyle := chooseKeyStyle k0, rest := mkCanonDottedCont l } =
        some (String.intercalate "." ((k0 :: l).map formatKey))
  | [] => by simp [mkCanonDottedCont, renderDottedKey, renderDottedKeyCont, renderKey_chooseKeyStyle, String.intercalate_singleton]
  | k1 :: ls => by
    have ih := renderDottedKey_canonAux k1 ls
    simp only [renderDottedKey, renderKey_chooseKeyStyle, Option.bind_eq_bind, Option.bind] at ih
    cases hcont : renderDottedKeyCont (mkCanonDottedCont ls) with
    | none => rw [hcont] at ih; nomatch ih
    | some tl =>
      rw [hcont] at ih; injection ih with htl
      simp only [mkCanonDottedCont, renderDottedKey, renderDottedKeyCont, renderKey_chooseKeyStyle,
        show isHorizWsStr "" = true by decide, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        hcont, Option.bind_eq_bind, Option.bind, List.map_cons, String.intercalate_cons_cons] at htl ⊢
      congr 1; rw [← htl]; rw [String.ext_iff]; simp [String.toList_append, List.append_assoc]

/-- `renderDottedKey` on `mkCanonDottedKey` emits `String.intercalate "." ...`. -/
theorem renderDottedKey_mkCanon (path : List String) (k : String) :
    renderDottedKey (mkCanonDottedKey path k) =
      some (String.intercalate "." (formatKey k :: path.reverse.map formatKey).reverse) := by
  have hrev : (formatKey k :: path.reverse.map formatKey).reverse = (path ++ [k]).map formatKey := by
    rw [List.reverse_cons, ← List.map_reverse, List.reverse_reverse, List.map_append, List.map_cons, List.map_nil]
  rw [hrev]
  cases path with
  | nil => simpa [mkCanonDottedKey, mkCanonDottedCont] using renderDottedKey_canonAux k []
  | cons k0 ks => simpa [mkCanonDottedKey] using renderDottedKey_canonAux k0 (ks ++ [k])

/-- Contextual path lens lifting local `insertAtActiveAndLookup` and `applyHeaderSkel` steps to `fullDoc`. -/
structure FocusAtPath (fullDoc : List (String × TomlValue)) (path : List String)
    (targetDoc : List (String × TomlValue))
    (wrap : List (String × SkeletonNode) → List (String × SkeletonNode)) : Prop where
  /-- Lift `insertAtActiveAndLookup` from `targetDoc` at `subAct` to `fullDoc` at `path ++ subAct`. -/
  active_at : ∀ locSk subAct rel locSk' v,
    insertAtActiveAndLookup targetDoc locSk subAct rel = some (locSk', v) →
    insertAtActiveAndLookup fullDoc (wrap locSk) (path ++ subAct) rel = some (wrap locSk', v)
  /-- Lift `applyHeaderSkel` from `targetDoc` at non-empty `sub` to `fullDoc` at `path ++ sub`. -/
  header_at : ∀ isAot locSk sub locSk',
    sub ≠ [] →
    applyHeaderSkel isAot locSk sub = some locSk' →
    applyHeaderSkel isAot (wrap locSk) (path ++ sub) = some (wrap locSk')

/-- Root `FocusAtPath` lens (`path = []`, `wrap = id`). -/
theorem focusAtPath_root (doc : List (String × TomlValue)) : FocusAtPath doc [] doc id :=
  ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- Step a `FocusAtPath` lens into an open `.table .explicit` sub-table at key `k`. -/
theorem focusAtPath_stepTable {fullDoc path parentDoc wrap k subDoc}
    (hf : FocusAtPath fullDoc path parentDoc wrap)
    (hlu : lookupKeyList k parentDoc = some (.table subDoc))
    (parentSk : List (String × SkeletonNode)) :
    FocusAtPath fullDoc (path ++ [k]) subDoc.toList
      (fun childSk => wrap (assocSetSkel k (.table .explicit childSk) parentSk)) where
  active_at childSk subAct rel childSk' v h := by
    rw [List.append_assoc, List.cons_append, List.nil_append]
    apply hf.active_at _ (k :: subAct)
    simp [insertAtActiveAndLookup, hlu, assocLookupSkel_set_self, h, assocSetSkel_idem]
  header_at isAot childSk sub childSk' hne h := by
    cases sub with
    | nil => exact absurd rfl hne
    | cons s0 sr =>
      rw [List.append_assoc, List.cons_append, List.nil_append]
      apply hf.header_at isAot _ (k :: s0 :: sr) _ (by simp)
      simp [applyHeaderSkel, assocLookupSkel_set_self, h, assocSetSkel_idem]

private theorem mapLastSkelWithDoc_snoc
    (f : List (String × TomlValue) → List (String × SkeletonNode) → Option (List (String × SkeletonNode) × TomlValue))
    (curDoc : TomlTable) (remDocs : List TomlValue) {curSk updSk : List (String × SkeletonNode)} {v : TomlValue}
    (hf_cur : f curDoc.toList curSk = some (updSk, v)) :
    ∀ (doneDocs : List TomlValue) (doneElems : List (List (String × SkeletonNode))),
      doneDocs.length = doneElems.length →
      (doneDocs.all fun x => match x with | .table _ => true | _ => false) = true →
      mapLastSkelWithDoc f (doneDocs ++ .table curDoc :: remDocs) (doneElems ++ [curSk]) =
        some (doneElems ++ [updSk], v) := by
  intro doneDocs
  induction doneDocs with
  | nil =>
    intro doneElems hlen _
    cases doneElems with
    | nil => simp [mapLastSkelWithDoc, hf_cur]
    | cons _ _ => simp at hlen
  | cons x0 dr ih =>
    intro doneElems hlen hall
    cases doneElems with
    | nil => simp at hlen
    | cons e0 er =>
      cases x0 with
      | table d0 =>
        simp only [List.all_cons, Bool.and_eq_true] at hall
        have hrec := ih er (by simp at hlen; omega) hall.2
        cases he_eq : er ++ [curSk] with
        | nil => have := congrArg List.length he_eq; simp at this
        | cons nx tl => rw [he_eq] at hrec; simp [mapLastSkelWithDoc, he_eq, hrec]
      | _ => nomatch hall

private theorem mapLastSkelAot_snoc
    {g : List (String × SkeletonNode) → Option (List (String × SkeletonNode))}
    {curSk updSk : List (String × SkeletonNode)} (hg : g curSk = some updSk) :
    ∀ doneElems : List (List (String × SkeletonNode)),
      mapLastSkelAot g (doneElems ++ [curSk]) = some (doneElems ++ [updSk])
  | [] => by simp [mapLastSkelAot, hg]
  | e0 :: er => by
    have hrec := mapLastSkelAot_snoc hg er
    cases he_eq : er ++ [curSk] with
    | nil => have := congrArg List.length he_eq; simp at this
    | cons nx tl => rw [he_eq] at hrec; simp [mapLastSkelAot, he_eq, hrec]

/-- Step a `FocusAtPath` lens into the active last element of an open `.aot` array at key `k`. -/
theorem focusAtPath_stepAot {fullDoc path parentDoc wrap k doneDocs curDoc remDocs doneElems}
    (hf : FocusAtPath fullDoc path parentDoc wrap)
    (hlu : lookupKeyList k parentDoc = some (.array ⟨doneDocs ++ .table curDoc :: remDocs⟩))
    (hlen : doneDocs.length = doneElems.length)
    (hall : (doneDocs.all fun x => match x with | .table _ => true | _ => false) = true)
    (parentSk : List (String × SkeletonNode)) :
    FocusAtPath fullDoc (path ++ [k]) curDoc.toList
      (fun childSk => wrap (assocSetSkel k (.aot (doneElems ++ [childSk])) parentSk)) where
  active_at childSk subAct rel childSk' v h := by
    rw [List.append_assoc, List.cons_append, List.nil_append]
    apply hf.active_at _ (k :: subAct)
    have hm := mapLastSkelWithDoc_snoc (fun elemDoc elemSk => insertAtActiveAndLookup elemDoc elemSk subAct rel)
      curDoc remDocs h doneDocs doneElems hlen hall
    simp [insertAtActiveAndLookup, hlu, assocLookupSkel_set_self, hm, assocSetSkel_idem]
  header_at isAot childSk sub childSk' hne h := by
    cases sub with
    | nil => exact absurd rfl hne
    | cons s0 sr =>
      rw [List.append_assoc, List.cons_append, List.nil_append]
      apply hf.header_at isAot _ (k :: s0 :: sr) _ (by simp)
      have hm := mapLastSkelAot_snoc (g := fun elem => applyHeaderSkel isAot elem (s0 :: sr)) h doneElems
      simp [applyHeaderSkel, assocLookupSkel_set_self, hm, assocSetSkel_idem]

/-- Check whether `v` is formatted as a `[table]` or `[[aot]]` section rather than inline. -/
def isSectionVal : TomlValue → Bool
  | .table _ => true
  | .array xs => isNonEmptyTableArray xs
  | _ => false

private theorem mkCanonDottedCont_clean :
    ∀ l : List String,
      (mkCanonDottedCont l).all (fun seg =>
        seg.wsBeforeDot.isEmpty && seg.wsAfterDot.isEmpty && isCleanKeyStyle seg.key seg.style) = true
  | [] => rfl
  | k :: ks => by simp [mkCanonDottedCont, isCleanKeyStyle_chooseKeyStyle k, mkCanonDottedCont_clean ks]

/-- `mkCanonDottedKey` always satisfies `Model.isCleanDottedKey`. -/
theorem mkCanonDottedKey_clean (path : List String) (k : String) :
    isCleanDottedKey (mkCanonDottedKey path k) = true := by
  cases path with
  | nil => simp [mkCanonDottedKey, isCleanDottedKey, isCleanKeyStyle_chooseKeyStyle]
  | cons k0 ks => simp [mkCanonDottedKey, isCleanDottedKey, isCleanKeyStyle_chooseKeyStyle, mkCanonDottedCont_clean]

/-- Canonical `StmtTape`s for `Impl.formatTableInlinePart`. -/
def chooseInlineStmts (numApi : NumParseApi) : List (String × TomlValue) → List StmtTape
  | [] => []
  | (k, v) :: rest =>
    if isSectionVal v then chooseInlineStmts numApi rest
    else .assign "" { firstKey := k, firstStyle := chooseKeyStyle k } " " " "
      (chooseValueTape numApi v) {} :: chooseInlineStmts numApi rest

mutual
  /-- Canonical `StmtTape`s for `Impl.formatTableSectionPart`. -/
  def chooseSectionStmts (numApi : NumParseApi) (path : List String) :
      List (String × TomlValue) → List StmtTape
    | [] => []
    | (k, .table ⟨subList⟩) :: rest =>
      .tableHeader "" "" (mkCanonDottedKey path k) "" {} ::
        (chooseInlineStmts numApi subList ++
          chooseSectionStmts numApi (path ++ [k]) subList ++
          chooseSectionStmts numApi path rest)
    | (k, .array ⟨xsList⟩) :: rest =>
      if isNonEmptyTableArray ⟨xsList⟩ then
        chooseAotStmts numApi path k xsList ++ chooseSectionStmts numApi path rest
      else chooseSectionStmts numApi path rest
    | _ :: rest => chooseSectionStmts numApi path rest
  termination_by es => sizeOf es
  decreasing_by all_goals simp +arith

  /-- Canonical `StmtTape`s for `Impl.formatAotElemList`. -/
  def chooseAotStmts (numApi : NumParseApi) (path : List String) (k : String) :
      List TomlValue → List StmtTape
    | [] => []
    | .table ⟨elemList⟩ :: rest =>
      .aotHeader "" "" (mkCanonDottedKey path k) "" {} ::
        (chooseInlineStmts numApi elemList ++
          chooseSectionStmts numApi (path ++ [k]) elemList ++
          chooseAotStmts numApi path k rest)
    | _ :: rest => chooseAotStmts numApi path k rest
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp +arith
end

/-- `chooseInlineStmts` preserves `activePath` and emits clean statements. -/
theorem chooseInlineStmts_endAct (numApi : NumParseApi) (act : List String) :
    ∀ es, endActivePath act (chooseInlineStmts numApi es) = act ∧
      (chooseInlineStmts numApi es).all isCleanStmt = true
  | [] => ⟨rfl, rfl⟩
  | (k, v) :: rest => by
    obtain ⟨h1, h2⟩ := chooseInlineStmts_endAct numApi act rest
    by_cases hs : isSectionVal v = true <;>
      simp [chooseInlineStmts, hs, endActivePath, isCleanStmt, isCleanDottedKey,
        isCleanKeyStyle_chooseKeyStyle k, chooseValueTape_clean numApi v, isCleanLineSuffix, h1, h2]

mutual
  /-- `chooseSectionStmts` emits only clean statements. -/
  theorem chooseSectionStmts_clean (numApi : NumParseApi) (path : List String)
      (es : List (String × TomlValue)) :
      (chooseSectionStmts numApi path es).all isCleanStmt = true := by
    match es with
    | [] => simp [chooseSectionStmts]
    | (k, .table ⟨subList⟩) :: rest =>
      have hinl := (chooseInlineStmts_endAct numApi [] subList).2
      have hsub := chooseSectionStmts_clean numApi (path ++ [k]) subList
      have htl := chooseSectionStmts_clean numApi path rest
      simp [chooseSectionStmts, isCleanStmt, mkCanonDottedKey_clean path k, isCleanLineSuffix, hinl, hsub, htl]
    | (k, .array ⟨xsList⟩) :: rest =>
      have hc_r := chooseSectionStmts_clean numApi path rest
      by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
      · simp [chooseSectionStmts, haot, chooseAotStmts_clean numApi path k xsList, hc_r]
      · simp [chooseSectionStmts, Bool.eq_false_iff.mpr haot, hc_r]
    | (_, .string _) :: rest | (_, .int _) :: rest | (_, .float _) :: rest | (_, .bool _) :: rest
    | (_, .offsetDateTime _) :: rest | (_, .localDateTime _) :: rest | (_, .localDate _) :: rest
    | (_, .localTime _) :: rest =>
      simpa [chooseSectionStmts] using chooseSectionStmts_clean numApi path rest
  termination_by sizeOf es
  decreasing_by all_goals simp +arith

  /-- `chooseAotStmts` emits only clean statements. -/
  theorem chooseAotStmts_clean (numApi : NumParseApi) (path : List String) (k : String)
      (xs : List TomlValue) :
      (chooseAotStmts numApi path k xs).all isCleanStmt = true := by
    match xs with
    | [] => simp [chooseAotStmts]
    | .table ⟨elemList⟩ :: rest =>
      have hinl := (chooseInlineStmts_endAct numApi [] elemList).2
      have hsub := chooseSectionStmts_clean numApi (path ++ [k]) elemList
      have htl := chooseAotStmts_clean numApi path k rest
      simp [chooseAotStmts, isCleanStmt, mkCanonDottedKey_clean path k, isCleanLineSuffix, hinl, hsub, htl]
    | .string _ :: rest | .int _ :: rest | .float _ :: rest | .bool _ :: rest
    | .offsetDateTime _ :: rest | .localDateTime _ :: rest | .localDate _ :: rest
    | .localTime _ :: rest | .array _ :: rest =>
      simpa [chooseAotStmts] using chooseAotStmts_clean numApi path k rest
  termination_by sizeOf xs
  decreasing_by all_goals simp +arith
end

/-- `chooseInlineStmts` renders `formatTableInlinePart` under any `FocusAtPath` lens. -/
theorem chooseInlineStmts_ok (numApi : NumParseApi) (hfmt : ValidFmt numApi)
    {fullDoc path targetDoc wrap} (hf : FocusAtPath fullDoc path targetDoc wrap) :
    ∀ (subEs : List (String × TomlValue)) (sk : List (String × SkeletonNode)),
      (∀ p ∈ subEs, lookupKeyList p.1 targetDoc = some p.2) →
      (∀ p ∈ subEs, assocLookupSkel p.1 sk = none) →
      noDupKeysBool subEs = true →
      wellFormedValueBool.wellFormedTableListBool subEs = true →
      let inlSk := (subEs.filter (fun p => !isSectionVal p.2)).map (fun p => (p.1, SkeletonNode.leaf))
      renderStmts fullDoc path (wrap sk) true (chooseInlineStmts numApi subEs) =
        some (wrap (sk ++ inlSk), concatLinesNl (formatTableInlinePart numApi subEs))
  | [], sk, _, _, _, _ => by simp [chooseInlineStmts, formatTableInlinePart, concatLinesNl, renderStmts]
  | (k, v) :: rest, sk, hlu, hdisj, hnd, hwf => by
    simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
    by_cases hs : isSectionVal v = true
    · have hf_eq : formatTableInlinePart numApi ((k, v) :: rest) = formatTableInlinePart numApi rest := by
        cases v with
        | table _ => rfl
        | array xs => simp [isSectionVal] at hs; simp [formatTableInlinePart, hs]
        | _ => nomatch hs
      rw [hf_eq]
      simpa [chooseInlineStmts, hs] using chooseInlineStmts_ok numApi hfmt hf rest sk
        (fun p hp => hlu p (List.mem_cons_of_mem _ hp))
        (fun p hp => hdisj p (List.mem_cons_of_mem _ hp)) hnd.2 hwf.2
    · have hsf : isSectionVal v = false := Bool.eq_false_iff.mpr hs
      have hk_none := hdisj (k, v) List.mem_cons_self
      have hk_lu := hlu (k, v) List.mem_cons_self
      have hins_loc : insertDottedAndLookup targetDoc sk [k] = some (sk ++ [(k, .leaf)], v) := by
        rw [← assocSetSkel_eq_append_of_none .leaf sk hk_none]
        cases v with
        | table _ => nomatch hsf
        | _ => simp [insertDottedAndLookup, hk_none, hk_lu]
      have hins_full : insertAtActiveAndLookup fullDoc (wrap sk) path [k] = some (wrap (sk ++ [(k, .leaf)]), v) := by
        simpa using hf.active_at sk [] [k] (sk ++ [(k, .leaf)]) v (by simpa [insertAtActiveAndLookup] using hins_loc)
      have hdisj_nx : ∀ p ∈ rest, assocLookupSkel p.1 (sk ++ [(k, .leaf)]) = none := by
        intro p hp
        have hne : p.1 ≠ k := fun he => by
          subst he; rw [(hasKeyList_eq_true_iff p.1 rest).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)] at hnd
          nomatch hnd.1
        rw [← assocSetSkel_eq_append_of_none .leaf sk hk_none, assocLookupSkel_set_ne hne,
            hdisj p (List.mem_cons_of_mem _ hp)]
      have ih := chooseInlineStmts_ok numApi hfmt hf rest (sk ++ [(k, .leaf)])
        (fun p hp => hlu p (List.mem_cons_of_mem _ hp)) hdisj_nx hnd.2 hwf.2
      have hrk : renderDottedKey { firstKey := k, firstStyle := chooseKeyStyle k } = some (formatKey k) := by
        simp [renderDottedKey, renderDottedKeyCont, renderKey_chooseKeyStyle]
      have hrv := renderValueInline_formatValueInline numApi hfmt v hwf.1
      have hfi_eq : formatTableInlinePart numApi ((k, v) :: rest) =
          (formatKey k ++ " = " ++ formatValueInline numApi v) :: formatTableInlinePart numApi rest := by
        cases v with
        | table _ => nomatch hsf
        | array xs => simp [isSectionVal] at hsf; simp [formatTableInlinePart, hsf]
        | _ => rfl
      rw [hfi_eq]
      simp only [chooseInlineStmts, hsf, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        List.filter_cons, List.map_cons, renderStmts, ite_self,
        show isClosedTrivia "" = true by decide, show isHorizWsStr " " = true by decide,
        Bool.not_true, Bool.or_self, hrk, show renderLineSuffix {} = some "" from rfl,
        DottedKeyTape.path, List.map_nil, hins_full, hrv, Option.bind_eq_bind, Option.bind]
      dsimp only at ih; rw [List.append_assoc] at ih
      rw [ih]; simp only [Option.some.injEq, Prod.mk.injEq, List.cons_append, List.nil_append, true_and, concatLinesNl]
      rw [String.ext_iff]; simp [String.toList_append, List.append_assoc]

/-- Snoc preservation of `skelMatchesAot`. -/
theorem skelMatchesAot_snoc {doneElems : List (List (String × SkeletonNode))}
    {doneDocs : List TomlValue} {eSk : List (String × SkeletonNode)} {eDoc : TomlTable}
    (haot : skelMatchesAot doneElems doneDocs = true)
    (he : skelMatchesEntries eSk eDoc.toList = true) :
    skelMatchesAot (doneElems ++ [eSk]) (doneDocs ++ [.table eDoc]) = true := by
  induction doneElems generalizing doneDocs with
  | nil =>
    cases doneDocs with
    | nil => simp [skelMatchesAot, he]
    | cons _ _ => simp [skelMatchesAot] at haot
  | cons s0 sr ih =>
    cases doneDocs with
    | nil => simp [skelMatchesAot] at haot
    | cons d0 dr =>
      cases d0 with
      | table td =>
        simp only [List.cons_append, skelMatchesAot, Bool.and_eq_true] at haot ⊢
        exact ⟨haot.1, ih haot.2⟩
      | _ => simp [skelMatchesAot] at haot

end LeanSwe.Toml.Proofs
