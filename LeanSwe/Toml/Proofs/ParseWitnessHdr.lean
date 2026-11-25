import LeanSwe.Toml.Proofs.ParseWitnessVal

/-!
# Header & Active-Path Builder-to-Skeleton Completeness Witnesses

Proves `applyHeader_witness` and `insertAtActivePath_witness` connecting `Toml.Impl`
table/AoT builders to `Model.applyHeaderSkel` and `Model.insertAtActiveAndLookup`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl

/-- Active header path invariant: every traversed node along `activePath` is a non-inline `.table` or non-empty `.aot`. -/
def ActivePathOpen : List String → List (String × Node) → Prop
  | [], _ => True
  | k :: rest, entries =>
    match assocLookupNode k entries with
    | some (.table kind sub) => kind ≠ .inline ∧ ActivePathOpen rest sub
    | some (.aot elems) => elems ≠ [] ∧ ∀ last, elems.getLast? = some last → ActivePathOpen rest last
    | _ => False

private theorem aotExtends_append_empty :
    ∀ elems : List (List (String × Node)), AotExtends elems (elems ++ [[]])
  | [] => by unfold AotExtends; trivial
  | e :: rest => by unfold AotExtends; exact ⟨entriesExtend_refl e, aotExtends_append_empty rest⟩

private theorem aotKeyNoDup_append_empty :
    ∀ elems : List (List (String × Node)), AotKeyNoDup elems = true → AotKeyNoDup (elems ++ [[]]) = true
  | [], _ => by simp [AotKeyNoDup]
  | e :: rest, h => by
    unfold AotKeyNoDup at h ⊢
    simp only [List.cons_append, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, aotKeyNoDup_append_empty rest h.2⟩

private theorem aotToSkel_append_empty :
    ∀ elems : List (List (String × Node)), aotToSkel (elems ++ [[]]) = aotToSkel elems ++ [[]]
  | [] => by simp [aotToSkel]
  | e :: rest => by simp [aotToSkel, aotToSkel_append_empty rest]

private theorem getLast?_append_singleton :
    ∀ elems : List (List (String × Node)), (elems ++ [[]]).getLast? = some []
  | [] => rfl
  | _ :: [] => rfl
  | _ :: b :: rest => getLast?_append_singleton (b :: rest)

private theorem mapLastAot_applyHeader_witness {mode : HeaderMode} {fullPath remPath : List String}
    (ih : ∀ entries nextEntries, EntriesKeyNoDup entries = true →
      applyHeader mode fullPath entries remPath = .ok nextEntries →
      EntriesKeyNoDup nextEntries = true ∧ EntriesExtend entries nextEntries ∧
      ActivePathOpen remPath nextEntries ∧
      applyHeaderSkel (mode == .aot) (entriesToSkel entries) remPath = some (entriesToSkel nextEntries)) :
    ∀ elems nextElems : List (List (String × Node)),
      AotKeyNoDup elems = true →
      mapLastAot (fun elem => applyHeader mode fullPath elem remPath) elems = .ok nextElems →
      AotKeyNoDup nextElems = true ∧ AotExtends elems nextElems ∧
      nextElems ≠ [] ∧ (∀ last, nextElems.getLast? = some last → ActivePathOpen remPath last) ∧
      mapLastSkelAot (fun elem => applyHeaderSkel (mode == .aot) elem remPath) (aotToSkel elems) =
        some (aotToSkel nextElems)
  | [], _, _, h => nomatch h
  | [last], nextElems, hnd, h => by
    have hlast_nd : EntriesKeyNoDup last = true := by unfold AotKeyNoDup at hnd; simpa [aotKeyNoDup_nil] using hnd
    simp only [mapLastAot, bind, Except.bind] at h
    cases hu : applyHeader mode fullPath last remPath with
    | error _ => rw [hu] at h; nomatch h
    | ok upd =>
      rw [hu] at h; obtain rfl := (Except.ok.inj h).symm
      obtain ⟨hupd_nd, hupd_ext, hupd_act, hupd_sk⟩ := ih last upd hlast_nd hu
      refine ⟨by unfold AotKeyNoDup; simp [hupd_nd, aotKeyNoDup_nil],
        by unfold AotExtends; exact ⟨hupd_ext, by unfold AotExtends; trivial⟩, by simp, ?_, ?_⟩
      · intro l hl; simp at hl; subst hl; exact hupd_act
      · simp [aotToSkel, mapLastSkelAot, hupd_sk]
  | hd :: nxt :: tl, nextElems, hnd, h => by
    rw [AotKeyNoDup] at hnd; simp only [Bool.and_eq_true] at hnd
    simp only [mapLastAot, bind, Except.bind] at h
    cases hr : mapLastAot (fun elem => applyHeader mode fullPath elem remPath) (nxt :: tl) with
    | error _ => rw [hr] at h; nomatch h
    | ok restUpd =>
      rw [hr] at h; obtain rfl := (Except.ok.inj h).symm
      obtain ⟨hr_nd, hr_ext, hr_ne, hr_act, hr_sk⟩ := mapLastAot_applyHeader_witness ih (nxt :: tl) restUpd hnd.2 hr
      refine ⟨by rw [AotKeyNoDup]; simp [hnd.1, hr_nd],
        by unfold AotExtends; exact ⟨entriesExtend_refl hd, hr_ext⟩, by simp, ?_, ?_⟩
      · intro l hl
        cases restUpd with
        | nil => exact absurd rfl hr_ne
        | cons _ _ => exact hr_act l hl
      · rw [aotToSkel] at hr_sk; simp [aotToSkel, mapLastSkelAot, hr_sk]

/-- `applyHeader` extends `entries`, establishes `ActivePathOpen path`, and matches `Model.applyHeaderSkel`. -/
theorem applyHeader_witness (mode : HeaderMode) (fullPath : List String) :
    ∀ (path : List String) (entries nextEntries : List (String × Node)),
      EntriesKeyNoDup entries = true →
      applyHeader mode fullPath entries path = .ok nextEntries →
      EntriesKeyNoDup nextEntries = true ∧
      EntriesExtend entries nextEntries ∧
      ActivePathOpen path nextEntries ∧
      applyHeaderSkel (mode == .aot) (entriesToSkel entries) path = some (entriesToSkel nextEntries)
  | [], _, _, _, h => by cases mode <;> nomatch h
  | [k], entries, nextEntries, hnd, h => by
    simp only [applyHeader, applyHeaderLeaf] at h
    cases mode with
    | table =>
      have hmode : (HeaderMode.table == HeaderMode.aot) = false := rfl
      cases hlu : assocLookupNode k entries with
      | none =>
        rw [hlu] at h; obtain rfl := (Except.ok.inj h).symm
        refine ⟨entriesKeyNoDup_assocSet hnd (by simp [NodeKeyNoDup]), entriesExtend_assocSet_none hlu, ?_, ?_⟩
        · simp [ActivePathOpen, assocLookupNode_assocSetNode]
        · simp [applyHeaderSkel, applyHeaderLeafSkel, hmode, assocLookupSkel_entriesToSkel, hlu,
            entriesToSkel_assocSetNode, nodeToSkel]
      | some n =>
        rw [hlu] at h
        cases n with
        | leaf lv => cases lv <;> nomatch h
        | aot _ => nomatch h
        | table kind sub =>
          cases kind with
          | explicit | dotted | inline => nomatch h
          | subtableImplicit =>
            obtain rfl := (Except.ok.inj h).symm
            have hsub_nd : EntriesKeyNoDup sub = true := by
              simpa [NodeKeyNoDup] using assocLookupNode_keyNoDup hnd hlu
            refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using hsub_nd),
              entriesExtend_assocSet_some hlu (by simp [NodeExtends]; exact entriesExtend_refl sub), ?_, ?_⟩
            · simp [ActivePathOpen, assocLookupNode_assocSetNode]
            · simp [applyHeaderSkel, applyHeaderLeafSkel, hmode, assocLookupSkel_entriesToSkel, hlu,
                entriesToSkel_assocSetNode, nodeToSkel]
    | aot =>
      have hmode : (HeaderMode.aot == HeaderMode.aot) = true := rfl
      cases hlu : assocLookupNode k entries with
      | none =>
        rw [hlu] at h; obtain rfl := (Except.ok.inj h).symm
        refine ⟨entriesKeyNoDup_assocSet hnd (by simp [NodeKeyNoDup, AotKeyNoDup]), entriesExtend_assocSet_none hlu, ?_, ?_⟩
        · simp [ActivePathOpen, assocLookupNode_assocSetNode]
        · simp [applyHeaderSkel, applyHeaderLeafSkel, hmode, assocLookupSkel_entriesToSkel, hlu,
            entriesToSkel_assocSetNode, nodeToSkel, aotToSkel]
      | some n =>
        rw [hlu] at h
        cases n with
        | leaf lv => cases lv <;> nomatch h
        | table kt _ => cases kt <;> nomatch h
        | aot elems =>
          obtain rfl := (Except.ok.inj h).symm
          have hel_nd : AotKeyNoDup elems = true := by
            simpa [NodeKeyNoDup] using assocLookupNode_keyNoDup hnd hlu
          refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using aotKeyNoDup_append_empty elems hel_nd),
            entriesExtend_assocSet_some hlu (by simpa [NodeExtends] using aotExtends_append_empty elems), ?_, ?_⟩
          · simp [ActivePathOpen, assocLookupNode_assocSetNode]
          · simp [applyHeaderSkel, applyHeaderLeafSkel, hmode, assocLookupSkel_entriesToSkel, hlu,
              entriesToSkel_assocSetNode, nodeToSkel, aotToSkel_append_empty]
  | k :: k' :: rest, entries, nextEntries, hnd, h => by
    unfold applyHeader at h
    cases hlu : assocLookupNode k entries with
    | none =>
      rw [hlu] at h; simp only [bind, Except.bind] at h
      cases hsub : applyHeader mode fullPath [] (k' :: rest) with
      | error _ => rw [hsub] at h; nomatch h
      | ok sub =>
        rw [hsub] at h; obtain rfl := (Except.ok.inj h).symm
        obtain ⟨hs_nd, _, hs_act, hs_sk⟩ := applyHeader_witness mode fullPath (k' :: rest) [] sub entriesKeyNoDup_nil hsub
        simp only [entriesToSkel_nil] at hs_sk
        refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using hs_nd),
          entriesExtend_assocSet_none hlu, ?_, ?_⟩
        · unfold ActivePathOpen; simp [assocLookupNode_assocSetNode, hs_act]
        · simp [applyHeaderSkel, assocLookupSkel_entriesToSkel, hlu,
            hs_sk, entriesToSkel_assocSetNode, nodeToSkel]
    | some n =>
      rw [hlu] at h
      cases n with
      | leaf lv => cases lv <;> nomatch h
      | table kind sub =>
        cases kind with
        | inline => nomatch h
        | explicit =>
          simp only [bind, Except.bind] at h
          cases hsub : applyHeader mode fullPath sub (k' :: rest) with
          | error _ => rw [hsub] at h; nomatch h
          | ok nextSub =>
            rw [hsub] at h; obtain rfl := (Except.ok.inj h).symm
            have hsub_nd0 : EntriesKeyNoDup sub = true := by simpa [NodeKeyNoDup] using assocLookupNode_keyNoDup hnd hlu
            obtain ⟨hs_nd, hs_ext, hs_act, hs_sk⟩ := applyHeader_witness mode fullPath (k' :: rest) sub nextSub hsub_nd0 hsub
            refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using hs_nd),
              entriesExtend_assocSet_some hlu (by simp [NodeExtends]; exact hs_ext),
              by unfold ActivePathOpen; simp [assocLookupNode_assocSetNode, hs_act],
              by simp [applyHeaderSkel, assocLookupSkel_entriesToSkel, hlu, hs_sk, entriesToSkel_assocSetNode, nodeToSkel]⟩
        | subtableImplicit =>
          simp only [bind, Except.bind] at h
          cases hsub : applyHeader mode fullPath sub (k' :: rest) with
          | error _ => rw [hsub] at h; nomatch h
          | ok nextSub =>
            rw [hsub] at h; obtain rfl := (Except.ok.inj h).symm
            have hsub_nd0 : EntriesKeyNoDup sub = true := by simpa [NodeKeyNoDup] using assocLookupNode_keyNoDup hnd hlu
            obtain ⟨hs_nd, hs_ext, hs_act, hs_sk⟩ := applyHeader_witness mode fullPath (k' :: rest) sub nextSub hsub_nd0 hsub
            refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using hs_nd),
              entriesExtend_assocSet_some hlu (by simp [NodeExtends]; exact hs_ext),
              by unfold ActivePathOpen; simp [assocLookupNode_assocSetNode, hs_act],
              by simp [applyHeaderSkel, assocLookupSkel_entriesToSkel, hlu, hs_sk, entriesToSkel_assocSetNode, nodeToSkel]⟩
        | dotted =>
          simp only [bind, Except.bind] at h
          cases hsub : applyHeader mode fullPath sub (k' :: rest) with
          | error _ => rw [hsub] at h; nomatch h
          | ok nextSub =>
            rw [hsub] at h; obtain rfl := (Except.ok.inj h).symm
            have hsub_nd0 : EntriesKeyNoDup sub = true := by simpa [NodeKeyNoDup] using assocLookupNode_keyNoDup hnd hlu
            obtain ⟨hs_nd, hs_ext, hs_act, hs_sk⟩ := applyHeader_witness mode fullPath (k' :: rest) sub nextSub hsub_nd0 hsub
            refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using hs_nd),
              entriesExtend_assocSet_some hlu (by simp [NodeExtends]; exact hs_ext),
              by unfold ActivePathOpen; simp [assocLookupNode_assocSetNode, hs_act],
              by simp [applyHeaderSkel, assocLookupSkel_entriesToSkel, hlu, hs_sk, entriesToSkel_assocSetNode, nodeToSkel]⟩
      | aot elems =>
        simp only [bind, Except.bind] at h
        cases hm : mapLastAot (fun elem => applyHeader mode fullPath elem (k' :: rest)) elems with
        | error _ => rw [hm] at h; nomatch h
        | ok nextElems =>
          rw [hm] at h; obtain rfl := (Except.ok.inj h).symm
          have hel_nd0 : AotKeyNoDup elems = true := by simpa [NodeKeyNoDup] using assocLookupNode_keyNoDup hnd hlu
          obtain ⟨he_nd, he_ext, he_ne, he_act, he_sk⟩ :=
            mapLastAot_applyHeader_witness (applyHeader_witness mode fullPath (k' :: rest)) elems nextElems hel_nd0 hm
          refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using he_nd),
            entriesExtend_assocSet_some hlu (by simpa [NodeExtends] using he_ext),
            by unfold ActivePathOpen; simp [assocLookupNode_assocSetNode, he_ne]; exact he_act,
            by simp [applyHeaderSkel, assocLookupSkel_entriesToSkel, hlu, he_sk, entriesToSkel_assocSetNode, nodeToSkel]⟩

private theorem mapLastAot_insert_witness {v : TomlValue} {remAct relPath fullPath : List String}
    (ih : ∀ entries nextEntries, EntriesKeyNoDup entries = true → ActivePathOpen remAct entries →
      insertAtActivePath fullPath entries remAct relPath (valueToInlineNode v) = .ok nextEntries →
      EntriesKeyNoDup nextEntries = true ∧ EntriesExtend entries nextEntries ∧
      ActivePathOpen remAct nextEntries ∧
      ∀ finalEntries, EntriesExtend nextEntries finalEntries →
        insertAtActiveAndLookup (entriesToTomlList finalEntries) (entriesToSkel entries) remAct relPath =
          some (entriesToSkel nextEntries, v)) :
    ∀ elems nextElems : List (List (String × Node)),
      AotKeyNoDup elems = true →
      (∀ last, elems.getLast? = some last → ActivePathOpen remAct last) →
      mapLastAot (fun elem => insertAtActivePath fullPath elem remAct relPath (valueToInlineNode v)) elems = .ok nextElems →
      AotKeyNoDup nextElems = true ∧ AotExtends elems nextElems ∧
      nextElems ≠ [] ∧ (∀ last, nextElems.getLast? = some last → ActivePathOpen remAct last) ∧
      ∀ elemsFin, AotExtends nextElems elemsFin →
        mapLastSkelWithDoc (fun elemDoc elemSkel => insertAtActiveAndLookup elemDoc elemSkel remAct relPath)
          (aotElemsToToml elemsFin) (aotToSkel elems) = some (aotToSkel nextElems, v)
  | [], _, _, _, h => nomatch h
  | [last], nextElems, hnd, hact, h => by
    have hlast_nd : EntriesKeyNoDup last = true := by unfold AotKeyNoDup at hnd; simpa [aotKeyNoDup_nil] using hnd
    simp only [mapLastAot, bind, Except.bind] at h
    cases hu : insertAtActivePath fullPath last remAct relPath (valueToInlineNode v) with
    | error _ => rw [hu] at h; nomatch h
    | ok upd =>
      rw [hu] at h; obtain rfl := (Except.ok.inj h).symm
      obtain ⟨hu_nd, hu_ext, hu_act, hu_lu⟩ := ih last upd hlast_nd (hact last rfl) hu
      refine ⟨by unfold AotKeyNoDup; simp [hu_nd, aotKeyNoDup_nil],
        by unfold AotExtends; exact ⟨hu_ext, by unfold AotExtends; trivial⟩, by simp, ?_, ?_⟩
      · intro l hl; simp at hl; subst hl; exact hu_act
      · intro elemsFin hfin
        cases elemsFin with
        | nil => simp [AotExtends] at hfin
        | cons fin0 restFin =>
          simp only [AotExtends] at hfin
          simp [aotToSkel, aotElemsToToml, mapLastSkelWithDoc, hu_lu fin0 hfin.1]
  | hd :: nxt :: tl, nextElems, hnd, hact, h => by
    rw [AotKeyNoDup] at hnd; simp only [Bool.and_eq_true] at hnd
    simp only [mapLastAot, bind, Except.bind] at h
    cases hr : mapLastAot (fun elem => insertAtActivePath fullPath elem remAct relPath (valueToInlineNode v)) (nxt :: tl) with
    | error _ => rw [hr] at h; nomatch h
    | ok restUpd =>
      rw [hr] at h; obtain rfl := (Except.ok.inj h).symm
      obtain ⟨hr_nd, hr_ext, hr_ne, hr_act, hr_lu⟩ :=
        mapLastAot_insert_witness ih (nxt :: tl) restUpd hnd.2 (fun l hl => hact l hl) hr
      refine ⟨by rw [AotKeyNoDup]; simp [hnd.1, hr_nd],
        by unfold AotExtends; exact ⟨entriesExtend_refl hd, hr_ext⟩, by simp, ?_, ?_⟩
      · intro l hl; cases restUpd with | nil => exact absurd rfl hr_ne | cons _ _ => exact hr_act l hl
      · intro elemsFin hfin
        cases elemsFin with
        | nil => simp [AotExtends] at hfin
        | cons fin0 restFin =>
          simp only [AotExtends] at hfin
          have hi := hr_lu restFin hfin.2
          rw [aotToSkel] at hi
          simp [aotToSkel, aotElemsToToml, mapLastSkelWithDoc, hi]

/-- `insertAtActivePath` preserves `EntriesKeyNoDup`/`ActivePathOpen` and matches `Model.insertAtActiveAndLookup`. -/
theorem insertAtActivePath_witness (fullPath : List String) (relPath : List String) (v : TomlValue) :
    ∀ (activePath : List String) (entries nextEntries : List (String × Node)),
      EntriesKeyNoDup entries = true →
      ActivePathOpen activePath entries →
      insertAtActivePath fullPath entries activePath relPath (valueToInlineNode v) = .ok nextEntries →
      EntriesKeyNoDup nextEntries = true ∧
      EntriesExtend entries nextEntries ∧
      ActivePathOpen activePath nextEntries ∧
      ∀ finalEntries, EntriesExtend nextEntries finalEntries →
        insertAtActiveAndLookup (entriesToTomlList finalEntries) (entriesToSkel entries) activePath relPath =
          some (entriesToSkel nextEntries, v)
  | [], entries, nextEntries, hnd, _, h => by
    obtain ⟨hnd', hext, hlu⟩ := insertDottedEntries_witness fullPath v relPath entries nextEntries hnd h
    exact ⟨hnd', hext, trivial, hlu⟩
  | k :: rest, entries, nextEntries, hnd, hact, h => by
    unfold insertAtActivePath at h
    unfold ActivePathOpen at hact
    cases hlu : assocLookupNode k entries with
    | none => rw [hlu] at h; nomatch h
    | some n =>
      rw [hlu] at h hact
      cases n with
      | leaf _ => nomatch h
      | table kind sub =>
        rcases hact with ⟨hnot_inl, hact_sub⟩
        have hsub_nd0 : EntriesKeyNoDup sub = true := by
          have hn := assocLookupNode_keyNoDup hnd hlu
          cases kind <;> first | exact absurd rfl hnot_inl | (simpa [NodeKeyNoDup] using hn)
        simp only [bind, Except.bind] at h
        cases hsub : insertAtActivePath fullPath sub rest relPath (valueToInlineNode v) with
        | error _ => rw [hsub] at h; nomatch h
        | ok nextSub =>
          rw [hsub] at h; obtain rfl := (Except.ok.inj h).symm
          obtain ⟨hs_nd, hs_ext, hs_act, hs_lu⟩ := insertAtActivePath_witness fullPath relPath v rest sub nextSub hsub_nd0 hact_sub hsub
          have hnode_nd : NodeKeyNoDup (.table kind nextSub) = true := by
            cases kind <;> first | exact absurd rfl hnot_inl | simpa [NodeKeyNoDup] using hs_nd
          have hnode_ext : NodeExtends (.table kind sub) (.table kind nextSub) := by
            cases kind <;> first | exact absurd rfl hnot_inl | (simp only [NodeExtends]; exact ⟨hnot_inl, hs_ext⟩)
          refine ⟨entriesKeyNoDup_assocSet hnd hnode_nd,
            entriesExtend_assocSet_some hlu hnode_ext,
            by simp [ActivePathOpen, assocLookupNode_assocSetNode, hnot_inl, hs_act],
            fun finalEntries hfin => ?_⟩
          have hself : assocLookupNode k (assocSetNode k (.table kind nextSub) entries) = some (.table kind nextSub) := by
            simp [assocLookupNode_assocSetNode]
          obtain ⟨nFin, hluFin, hextFin⟩ := hfin.lookup hself
          cases nFin with
          | leaf _ | aot _ => cases kind <;> first | exact absurd rfl hnot_inl | simp [NodeExtends] at hextFin
          | table kFin subFin =>
            have hextSub : EntriesExtend nextSub subFin := by
              cases kind <;> first | exact absurd rfl hnot_inl | (simp only [NodeExtends] at hextFin; exact hextFin.2)
            have hi := hs_lu subFin hextSub
            cases kind <;> first | exact absurd rfl hnot_inl |
              simp [insertAtActiveAndLookup, assocLookupSkel_entriesToSkel, hlu, lookupKeyList_entriesToTomlList,
                hluFin, nodeToTomlValue, entriesToSkel_assocSetNode, nodeToSkel, hi]
      | aot elems =>
        rcases hact with ⟨_, hact_el⟩
        have hel_nd0 : AotKeyNoDup elems = true := by simpa [NodeKeyNoDup] using assocLookupNode_keyNoDup hnd hlu
        simp only [bind, Except.bind] at h
        cases hm : mapLastAot (fun elem => insertAtActivePath fullPath elem rest relPath (valueToInlineNode v)) elems with
        | error _ => rw [hm] at h; nomatch h
        | ok nextElems =>
          rw [hm] at h; obtain rfl := (Except.ok.inj h).symm
          obtain ⟨he_nd, he_ext, he_ne, he_act, he_lu⟩ :=
            mapLastAot_insert_witness (insertAtActivePath_witness fullPath relPath v rest) elems nextElems hel_nd0 hact_el hm
          refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using he_nd),
            entriesExtend_assocSet_some hlu (by simpa [NodeExtends] using he_ext),
            by simp [ActivePathOpen, assocLookupNode_assocSetNode, he_ne]; exact he_act,
            fun finalEntries hfin => ?_⟩
          have hself : assocLookupNode k (assocSetNode k (.aot nextElems) entries) = some (.aot nextElems) := by
            simp [assocLookupNode_assocSetNode]
          obtain ⟨nFin, hluFin, hextFin⟩ := hfin.lookup hself
          cases nFin with
          | leaf _ | table _ _ => simp [NodeExtends] at hextFin
          | aot elemsFin =>
            simp only [NodeExtends] at hextFin
            have hi := he_lu elemsFin hextFin
            simp [insertAtActiveAndLookup, assocLookupSkel_entriesToSkel, hlu, lookupKeyList_entriesToTomlList,
              hluFin, nodeToTomlValue, entriesToSkel_assocSetNode, nodeToSkel, hi]

end LeanSwe.Toml.Proofs
