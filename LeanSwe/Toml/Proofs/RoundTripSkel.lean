import LeanSwe.Toml.Proofs.RoundTripScalar

/-!
# Skeleton Projection Soundness (`RoundTripSkel`)

Proves that `Model.insertDottedAndLookup`, `Model.applyHeaderSkel`, and
`Model.insertAtActiveAndLookup` step `Impl.insertDottedEntries`, `Impl.applyHeader`, and
`Impl.insertAtActivePath` to `.ok` states preserving `entriesToSkel entries = skel`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl

private theorem nodeToSkel_inv_table {n : Node} {kind : OpenTableKind} {subSkel : List (String × SkeletonNode)}
    (h : nodeToSkel n = .table kind subSkel) :
    ∃ kt sub, kt ≠ .inline ∧ n = .table kt sub ∧ entriesToSkel sub = subSkel ∧
      match kind with
      | .explicit => kt = .explicit
      | .subtableImplicit => kt = .subtableImplicit
      | .dotted => kt = .dotted := by
  cases n with
  | leaf lv => cases lv <;> simp [nodeToSkel] at h
  | aot _ => simp [nodeToSkel] at h
  | table kt sub =>
    cases kt with
    | inline => simp [nodeToSkel] at h
    | explicit =>
      simp only [nodeToSkel, SkeletonNode.table.injEq] at h; rcases h with ⟨rfl, rfl⟩
      exact ⟨.explicit, sub, by decide, rfl, rfl, rfl⟩
    | subtableImplicit =>
      simp only [nodeToSkel, SkeletonNode.table.injEq] at h; rcases h with ⟨rfl, rfl⟩
      exact ⟨.subtableImplicit, sub, by decide, rfl, rfl, rfl⟩
    | dotted =>
      simp only [nodeToSkel, SkeletonNode.table.injEq] at h; rcases h with ⟨rfl, rfl⟩
      exact ⟨.dotted, sub, by decide, rfl, rfl, rfl⟩

private theorem nodeToSkel_inv_aot {n : Node} {elemsSkel : List (List (String × SkeletonNode))}
    (h : nodeToSkel n = .aot elemsSkel) :
    ∃ elems, n = .aot elems ∧ aotToSkel elems = elemsSkel := by
  cases n with
  | leaf lv => cases lv <;> simp [nodeToSkel] at h
  | table kt _ => cases kt <;> simp [nodeToSkel] at h
  | aot elems =>
    simp only [nodeToSkel, SkeletonNode.aot.injEq] at h; subst h
    exact ⟨elems, rfl, rfl⟩

/-- `Model.insertDottedAndLookup` implies `Impl.insertDottedEntries` succeeds preserving `entriesToSkel`. -/
theorem insertDottedAndLookup_imp_insertDottedEntries (fullPath : List String)
    {v v' : TomlValue} (htab : isTableVal v' = isTableVal v) :
    ∀ (relPath : List String) (docEntries : List (String × TomlValue))
      (skel nextSkel : List (String × SkeletonNode)) (entries : List (String × Node)),
      entriesToSkel entries = skel →
      insertDottedAndLookup docEntries skel relPath = some (nextSkel, v) →
      ∃ nextEntries,
        insertDottedEntries fullPath entries relPath (valueToInlineNode v') = .ok nextEntries ∧
        entriesToSkel nextEntries = nextSkel
  | [], _, _, _, _, _, h => by simp [insertDottedAndLookup] at h
  | [k], docEntries, skel, nextSkel, entries, hsk, h => by
    subst hsk; simp only [insertDottedAndLookup] at h
    rw [assocLookupSkel_entriesToSkel] at h
    cases hlu : assocLookupNode k entries with
    | some _ => simp [hlu] at h
    | none =>
      rw [hlu] at h
      cases hk : lookupKeyList k docEntries with
      | none => simp [Option.map, hk] at h
      | some w =>
        rw [hk] at h; simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨assocSetNode k (valueToInlineNode v') entries, by simp [insertDottedEntries, hlu], ?_⟩
        rw [entriesToSkel_assocSetNode, nodeToSkel_valueToInlineNode]
        cases w <;> cases v' <;> first | rfl | nomatch htab
  | k :: k' :: rest, docEntries, skel, nextSkel, entries, hsk, h => by
    subst hsk; simp only [insertDottedAndLookup] at h
    cases hk : lookupKeyList k docEntries with
    | none => simp [hk] at h
    | some w =>
      rw [hk] at h
      cases w with
      | table subDoc =>
        rw [assocLookupSkel_entriesToSkel] at h
        cases hlu : assocLookupNode k entries with
        | none =>
          rw [hlu] at h; dsimp only [Option.map] at h
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨⟨ns, w'⟩, hi, ⟨rfl, rfl⟩⟩
          obtain ⟨nextSub, hsub_ok, hsub_sk⟩ :=
            insertDottedAndLookup_imp_insertDottedEntries fullPath htab (k' :: rest) subDoc.toList [] ns [] entriesToSkel_nil hi
          refine ⟨assocSetNode k (.table .dotted nextSub) entries, ?_, ?_⟩
          · simp [insertDottedEntries, hlu, bind, Except.bind, hsub_ok]
          · simp [entriesToSkel_assocSetNode, nodeToSkel, hsub_sk]
        | some node =>
          rw [hlu] at h; dsimp only [Option.map] at h
          cases hns : nodeToSkel node with
          | leaf | inlineTable | aot _ => rw [hns] at h; nomatch h
          | table kind subSkel =>
            rw [hns] at h
            obtain ⟨kt, sub, _, rfl, rfl, hkt⟩ := nodeToSkel_inv_table hns
            cases kind with
            | explicit => nomatch h
            | subtableImplicit =>
              dsimp only at hkt; rw [hkt] at hlu
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨⟨ns, w'⟩, hi, ⟨rfl, rfl⟩⟩
              obtain ⟨nextSub, hsub_ok, hsub_sk⟩ :=
                insertDottedAndLookup_imp_insertDottedEntries fullPath htab (k' :: rest) subDoc.toList (entriesToSkel sub) ns sub rfl hi
              exact ⟨assocSetNode k (.table .dotted nextSub) entries,
                by simp [insertDottedEntries, hlu, bind, Except.bind, hsub_ok],
                by simp [entriesToSkel_assocSetNode, nodeToSkel, hsub_sk]⟩
            | dotted =>
              dsimp only at hkt; rw [hkt] at hlu
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨⟨ns, w'⟩, hi, ⟨rfl, rfl⟩⟩
              obtain ⟨nextSub, hsub_ok, hsub_sk⟩ :=
                insertDottedAndLookup_imp_insertDottedEntries fullPath htab (k' :: rest) subDoc.toList (entriesToSkel sub) ns sub rfl hi
              exact ⟨assocSetNode k (.table .dotted nextSub) entries,
                by simp [insertDottedEntries, hlu, bind, Except.bind, hsub_ok],
                by simp [entriesToSkel_assocSetNode, nodeToSkel, hsub_sk]⟩
      | _ => simp at h

private theorem aotToSkel_append_nil :
    ∀ elems : List (List (String × Node)), aotToSkel (elems ++ [[]]) = aotToSkel elems ++ [[]]
  | [] => by simp [aotToSkel]
  | e :: rest => by simp [aotToSkel, aotToSkel_append_nil rest]

private theorem mapLastSkelAot_imp_mapLastAot
    {fSk : List (String × SkeletonNode) → Option (List (String × SkeletonNode))}
    {fNd : List (String × Node) → Except TomlError (List (String × Node))}
    (hf : ∀ es sk nsk, entriesToSkel es = sk → fSk sk = some nsk →
      ∃ nes, fNd es = .ok nes ∧ entriesToSkel nes = nsk) :
    ∀ (elems : List (List (String × Node))) (elemsSk nextSk : List (List (String × SkeletonNode))),
      aotToSkel elems = elemsSk →
      mapLastSkelAot fSk elemsSk = some nextSk →
      ∃ nextElems, mapLastAot fNd elems = .ok nextElems ∧ aotToSkel nextElems = nextSk
  | [], _, _, rfl, h => by rw [aotToSkel_nil] at h; nomatch h
  | [last], _, nextSk, rfl, h => by
    rw [aotToSkel, aotToSkel_nil] at h
    simp only [mapLastSkelAot, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    rcases h with ⟨updSk, hupd, rfl⟩
    obtain ⟨upd, hupd_ok, hupd_sk⟩ := hf last (entriesToSkel last) updSk rfl hupd
    exact ⟨[upd], by simp [mapLastAot, bind, Except.bind, hupd_ok], by rw [aotToSkel, aotToSkel_nil, hupd_sk]⟩
  | hd :: nxt :: tl, _, nextSk, rfl, h => by
    rw [aotToSkel, aotToSkel] at h
    simp only [mapLastSkelAot, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    rcases h with ⟨restSk, hrest, rfl⟩
    obtain ⟨restUpd, hrest_ok, hrest_sk⟩ :=
      mapLastSkelAot_imp_mapLastAot hf (nxt :: tl) (entriesToSkel nxt :: aotToSkel tl) restSk (by rw [aotToSkel]) hrest
    exact ⟨hd :: restUpd, by simp [mapLastAot, bind, Except.bind, hrest_ok], by rw [aotToSkel, hrest_sk]⟩

/-- `Model.applyHeaderSkel` implies `Impl.applyHeader` succeeds preserving `entriesToSkel`. -/
theorem applyHeaderSkel_imp_applyHeader (mode : HeaderMode) (fullPath : List String) :
    ∀ (path : List String) (skel nextSkel : List (String × SkeletonNode)) (entries : List (String × Node)),
      entriesToSkel entries = skel →
      applyHeaderSkel (mode == .aot) skel path = some nextSkel →
      ∃ nextEntries,
        applyHeader mode fullPath entries path = .ok nextEntries ∧
        entriesToSkel nextEntries = nextSkel
  | [], _, _, _, _, h => by simp [applyHeaderSkel] at h
  | [k], skel, nextSkel, entries, hsk, h => by
    subst hsk
    simp only [applyHeaderSkel, applyHeaderLeafSkel, assocLookupSkel_entriesToSkel] at h
    cases mode with
    | table =>
      rw [show (HeaderMode.table == .aot) = false from rfl] at h
      cases hlu : assocLookupNode k entries with
      | none =>
        rw [hlu] at h; simp only [Option.map, Option.some.injEq] at h; subst h
        exact ⟨assocSetNode k (.table .explicit []) entries,
          by simp [applyHeader, applyHeaderLeaf, hlu],
          by simp [entriesToSkel_assocSetNode, nodeToSkel]⟩
      | some node =>
        rw [hlu] at h; dsimp only [Option.map] at h
        cases hns : nodeToSkel node with
        | leaf | inlineTable | aot _ => rw [hns] at h; nomatch h
        | table kind subSkel =>
          rw [hns] at h
          obtain ⟨kt, sub, _, rfl, rfl, hkt⟩ := nodeToSkel_inv_table hns
          cases kind with
          | explicit | dotted => nomatch h
          | subtableImplicit =>
            dsimp only at hkt; rw [hkt] at hlu
            simp only [Option.some.injEq] at h; subst h
            exact ⟨assocSetNode k (.table .explicit sub) entries,
              by simp [applyHeader, applyHeaderLeaf, hlu],
              by simp [entriesToSkel_assocSetNode, nodeToSkel]⟩
    | aot =>
      rw [show (HeaderMode.aot == .aot) = true from rfl] at h
      cases hlu : assocLookupNode k entries with
      | none =>
        rw [hlu] at h; simp only [Option.map, Option.some.injEq] at h; subst h
        exact ⟨assocSetNode k (.aot [[]]) entries,
          by simp [applyHeader, applyHeaderLeaf, hlu],
          by simp [entriesToSkel_assocSetNode, nodeToSkel, aotToSkel]⟩
      | some node =>
        rw [hlu] at h; dsimp only [Option.map] at h
        cases hns : nodeToSkel node with
        | leaf | inlineTable | table _ _ => rw [hns] at h; nomatch h
        | aot elemsSk =>
          rw [hns] at h; simp only [Option.some.injEq] at h; subst h
          obtain ⟨elems, rfl, rfl⟩ := nodeToSkel_inv_aot hns
          exact ⟨assocSetNode k (.aot (elems ++ [[]])) entries,
            by simp [applyHeader, applyHeaderLeaf, hlu],
            by simp [entriesToSkel_assocSetNode, nodeToSkel, aotToSkel_append_nil]⟩
  | k :: k' :: rest, skel, nextSkel, entries, hsk, h => by
    subst hsk
    unfold applyHeaderSkel at h
    rw [assocLookupSkel_entriesToSkel] at h
    cases hlu : assocLookupNode k entries with
    | none =>
      rw [hlu] at h; simp only [Option.map, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with ⟨subSk, hsub, rfl⟩
      obtain ⟨nextSub, hsub_ok, hsub_sk⟩ := applyHeaderSkel_imp_applyHeader mode fullPath (k' :: rest) [] subSk [] entriesToSkel_nil hsub
      exact ⟨assocSetNode k (.table .subtableImplicit nextSub) entries,
        by simp [applyHeader, hlu, bind, Except.bind, hsub_ok],
        by simp [entriesToSkel_assocSetNode, nodeToSkel, hsub_sk]⟩
    | some node =>
      rw [hlu] at h; dsimp only [Option.map] at h
      cases hns : nodeToSkel node with
      | leaf | inlineTable => rw [hns] at h; nomatch h
      | table kind subSk =>
        rw [hns] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨nextSubSk, hsub, rfl⟩
        obtain ⟨kt, sub, hnot_inl, rfl, rfl, hkt⟩ := nodeToSkel_inv_table hns
        obtain ⟨nextSub, hsub_ok, hsub_sk⟩ :=
          applyHeaderSkel_imp_applyHeader mode fullPath (k' :: rest) (entriesToSkel sub) nextSubSk sub rfl hsub
        refine ⟨assocSetNode k (.table kt nextSub) entries, ?_, ?_⟩
        · cases kt <;> first | exact absurd rfl hnot_inl | simp [applyHeader, hlu, bind, Except.bind, hsub_ok]
        · cases kind <;> (dsimp only at hkt; rw [hkt]; simp [entriesToSkel_assocSetNode, nodeToSkel, hsub_sk])
      | aot elemsSk =>
        rw [hns] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨nextElemsSk, hm, rfl⟩
        obtain ⟨elems, rfl, rfl⟩ := nodeToSkel_inv_aot hns
        obtain ⟨nextElems, hm_ok, hm_sk⟩ := mapLastSkelAot_imp_mapLastAot
          (fun es sk nsk he hf => applyHeaderSkel_imp_applyHeader mode fullPath (k' :: rest) sk nsk es he hf)
          elems (aotToSkel elems) nextElemsSk rfl hm
        exact ⟨assocSetNode k (.aot nextElems) entries,
          by simp [applyHeader, hlu, bind, Except.bind, hm_ok],
          by simp [entriesToSkel_assocSetNode, nodeToSkel, hm_sk]⟩

private theorem mapLastSkelWithDoc_imp_mapLastAot {v : TomlValue}
    {fSk : List (String × TomlValue) → List (String × SkeletonNode) → Option (List (String × SkeletonNode) × TomlValue)}
    {fNd : List (String × Node) → Except TomlError (List (String × Node))}
    (hf : ∀ d sk nsk es, entriesToSkel es = sk → fSk d sk = some (nsk, v) →
      ∃ nes, fNd es = .ok nes ∧ entriesToSkel nes = nsk) :
    ∀ (elems : List (List (String × Node))) (xs : List TomlValue) (elemsSk nextSk : List (List (String × SkeletonNode))),
      aotToSkel elems = elemsSk →
      mapLastSkelWithDoc fSk xs elemsSk = some (nextSk, v) →
      ∃ nextElems, mapLastAot fNd elems = .ok nextElems ∧ aotToSkel nextElems = nextSk
  | [], xs, _, _, rfl, h => by
    rw [aotToSkel_nil] at h
    cases xs with | nil => nomatch h | cons x _ => cases x <;> nomatch h
  | [last], xs, _, nextSk, rfl, h => by
    rw [aotToSkel, aotToSkel_nil] at h
    cases xs with
    | nil => nomatch h
    | cons x xr =>
      cases x with
      | table curDoc =>
        simp only [mapLastSkelWithDoc, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨⟨updSk, w⟩, hupd, hpair⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        obtain ⟨upd, hupd_ok, hupd_sk⟩ := hf curDoc.toList (entriesToSkel last) updSk last rfl hupd
        exact ⟨[upd], by simp [mapLastAot, bind, Except.bind, hupd_ok], by rw [aotToSkel, aotToSkel_nil, hupd_sk]⟩
      | _ => nomatch h
  | hd :: nxt :: tl, xs, _, nextSk, rfl, h => by
    rw [aotToSkel, aotToSkel] at h
    cases xs with
    | nil => nomatch h
    | cons x xr =>
      cases x with
      | table _ =>
        simp only [mapLastSkelWithDoc, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨⟨restSk, w⟩, hrest, hpair⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        obtain ⟨restUpd, hrest_ok, hrest_sk⟩ :=
          mapLastSkelWithDoc_imp_mapLastAot hf (nxt :: tl) xr (entriesToSkel nxt :: aotToSkel tl) restSk (by rw [aotToSkel]) hrest
        exact ⟨hd :: restUpd, by simp [mapLastAot, bind, Except.bind, hrest_ok], by rw [aotToSkel, hrest_sk]⟩
      | _ => nomatch h

/-- `Model.insertAtActiveAndLookup` implies `Impl.insertAtActivePath` succeeds preserving `entriesToSkel`. -/
theorem insertAtActiveAndLookup_imp_insertAtActivePath (fullPath : List String)
    {v v' : TomlValue} (htab : isTableVal v' = isTableVal v) :
    ∀ (activePath : List String) (relPath : List String) (docEntries : List (String × TomlValue))
      (skel nextSkel : List (String × SkeletonNode)) (entries : List (String × Node)),
      entriesToSkel entries = skel →
      insertAtActiveAndLookup docEntries skel activePath relPath = some (nextSkel, v) →
      ∃ nextEntries,
        insertAtActivePath fullPath entries activePath relPath (valueToInlineNode v') = .ok nextEntries ∧
        entriesToSkel nextEntries = nextSkel
  | [], relPath, docEntries, skel, nextSkel, entries, hsk, h =>
    insertDottedAndLookup_imp_insertDottedEntries fullPath htab relPath docEntries skel nextSkel entries hsk h
  | k :: rest, relPath, docEntries, skel, nextSkel, entries, hsk, h => by
    subst hsk
    unfold insertAtActiveAndLookup at h
    rw [assocLookupSkel_entriesToSkel] at h
    cases hlu : assocLookupNode k entries with
    | none =>
      rw [hlu] at h
      cases hd : lookupKeyList k docEntries with
      | none => rw [hd] at h; nomatch h
      | some w => rw [hd] at h; cases w <;> nomatch h
    | some node =>
      rw [hlu] at h; dsimp only [Option.map] at h
      cases hns : nodeToSkel node with
      | leaf | inlineTable =>
        rw [hns] at h; cases hk : lookupKeyList k docEntries with
        | none => rw [hk] at h; nomatch h
        | some w => rw [hk] at h; cases w <;> nomatch h
      | table kind subSk =>
        rw [hns] at h
        cases hk : lookupKeyList k docEntries with
        | none => rw [hk] at h; nomatch h
        | some w =>
          rw [hk] at h; cases w with
          | table subDoc =>
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨⟨ns, w'⟩, hi, ⟨rfl, rfl⟩⟩
            obtain ⟨kt, sub, _, rfl, rfl, hkt⟩ := nodeToSkel_inv_table hns
            obtain ⟨nextSub, hsub_ok, hsub_sk⟩ :=
              insertAtActiveAndLookup_imp_insertAtActivePath fullPath htab rest relPath subDoc.toList (entriesToSkel sub) ns sub rfl hi
            refine ⟨assocSetNode k (.table kt nextSub) entries,
              by simp [insertAtActivePath, hlu, bind, Except.bind, hsub_ok], ?_⟩
            cases kind <;> (dsimp only at hkt; rw [hkt]; simp [entriesToSkel_assocSetNode, nodeToSkel, hsub_sk])
          | _ => nomatch h
      | aot elemsSk =>
        rw [hns] at h
        cases hk : lookupKeyList k docEntries with
        | none => rw [hk] at h; nomatch h
        | some w =>
          rw [hk] at h; cases w with
          | array xs =>
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨⟨neSk, w'⟩, hm, ⟨rfl, rfl⟩⟩
            obtain ⟨elems, rfl, rfl⟩ := nodeToSkel_inv_aot hns
            obtain ⟨nextElems, hm_ok, hm_sk⟩ := mapLastSkelWithDoc_imp_mapLastAot
              (fun d sk nsk es he hf =>
                insertAtActiveAndLookup_imp_insertAtActivePath fullPath htab rest relPath d sk nsk es he hf)
              elems xs.toList (aotToSkel elems) neSk rfl hm
            exact ⟨assocSetNode k (.aot nextElems) entries,
              by simp [insertAtActivePath, hlu, bind, Except.bind, hm_ok],
              by simp [entriesToSkel_assocSetNode, nodeToSkel, hm_sk]⟩
          | _ => nomatch h

/-- Any rendered `DottedKeyTape` begins with a character other than `'}'`. -/
theorem dk_head_not_rbrace {dk : DottedKeyTape} {rk : String} {c0 : Char} {r0 : List Char}
    (hrk : renderDottedKey dk = some rk) (hl : rk.toList = c0 :: r0) : c0 ≠ '}' := by
  unfold renderDottedKey at hrk
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hrk
  rcases hrk with ⟨rk0, hrk0, _, _, rfl⟩
  cases hfs : dk.firstStyle with
  | bare =>
    rw [hfs] at hrk0; dsimp only [renderKey] at hrk0
    split at hrk0
    · rename_i hb; injection hrk0 with e; subst e
      simp only [isValidBareKey, Bool.and_eq_true, String.toList_append] at hb hl
      cases hfl : dk.firstKey.toList with
      | nil =>
        have hfk : dk.firstKey = "" := by rw [← String.ofList_toList (s := dk.firstKey), hfl]
        rw [hfk] at hb; simp at hb
      | cons f0 fs =>
        rw [hfl, List.cons_append] at hl; obtain ⟨rfl, _⟩ := List.cons.inj hl
        exact (isBareKeyChar_not_special (List.all_eq_true.mp hb.2 f0 (by rw [hfl]; simp))).2.2.2.2.2.1
    · nomatch hrk0
  | basic a? =>
    rw [hfs] at hrk0
    cases a? with
    | none =>
      simp only [renderKey, Option.some.injEq] at hrk0
      subst hrk0; simp [String.toList_append] at hl; obtain ⟨rfl, _⟩ := hl; decide
    | some atoms =>
      simp only [renderKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hrk0
      rcases hrk0 with ⟨_, _, rfl⟩; simp [String.toList_append] at hl; obtain ⟨rfl, _⟩ := hl; decide
  | literal =>
    rw [hfs] at hrk0; dsimp only [renderKey] at hrk0
    split at hrk0
    · injection hrk0 with e; subst e; simp [String.toList_append] at hl; obtain ⟨rfl, _⟩ := hl; decide
    · nomatch hrk0

/-- `Impl.parseInlineTableFuel` is invariant under leading `skipHorizWs`. -/
theorem parseInlineTableFuel_skipHorizWs (numApi : CharNumApi) (fuel : Nat)
    (cs : List Char) (entries : List (String × Node)) :
    parseInlineTableFuel numApi fuel (skipHorizWs cs) entries = parseInlineTableFuel numApi fuel cs entries := by
  cases fuel with
  | zero => rfl
  | succ f => unfold parseInlineTableFuel; simp [skipHorizWs_idem]

/-- `String.intercalate` preserves `CleanNorm`. -/
theorem cleanNorm_intercalate {sep : String} {xs : List String}
    (hsep : CleanNorm sep.toList) (hxs : ∀ x ∈ xs, CleanNorm x.toList) :
    CleanNorm (String.intercalate sep xs).toList := by
  match xs with
  | [] => simp [CleanNorm, String.intercalate_nil]
  | [x] => simpa [String.intercalate_singleton] using hxs x List.mem_cons_self
  | x :: y :: rest =>
    rw [String.intercalate_cons_cons, String.toList_append, String.toList_append]
    exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨hxs x List.mem_cons_self, hsep⟩,
      cleanNorm_intercalate hsep (fun z hz => hxs z (List.mem_cons_of_mem _ hz))⟩

end LeanSwe.Toml.Proofs
