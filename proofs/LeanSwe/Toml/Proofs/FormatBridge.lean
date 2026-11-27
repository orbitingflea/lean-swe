import Core.NondetTest
import LeanSwe.Toml.SpecTests
import LeanSwe.Toml.Proofs.FormatBridgeFocus
import LeanSwe.Toml.Proofs.NumParseContract

/-!
# Document Formatter & Round-Trip Bridge (`FormatBridge`)

Proves `formatWithNum_allowedFormat` via `table_plan_ok` and lifts both `Model.render` and
`Impl.formatWithNum` round-trip theorems to `AllPass` and `CanReach`.
-/

namespace LeanSwe.Toml.Proofs

open Core LeanSwe.Toml LeanSwe.Toml.Model LeanSwe.Toml.Impl LeanSwe.NumParse

mutual
  private theorem table_plan_ok (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (fullDoc path entries : List _) (wrap : List (String × SkeletonNode) → List (String × SkeletonNode))
      (hf : FocusAtPath fullDoc path entries wrap)
      (hnd : noDupKeysBool entries = true)
      (hwf : wellFormedValueBool.wellFormedTableListBool entries = true) :
      ∃ finSk,
        skelMatchesEntries finSk entries = true ∧
        renderStmts fullDoc path (wrap []) true
          (chooseInlineStmts numApi entries ++ chooseSectionStmts numApi path entries) =
          some (wrap finSk,
            concatLinesNl (formatTableInlinePart numApi entries ++
              formatTableSectionPart numApi (path.reverse.map formatKey) entries)) := by
    let inlSk := (entries.filter (fun p => !isSectionVal p.2)).map (fun p => (p.1, SkeletonNode.leaf))
    have hinl := chooseInlineStmts_ok numApi hfmt hf entries []
      (fun p hp => lookupKeyList_mem_of_noDupKeys entries hnd p.1 p.2 hp)
      (fun _ _ => rfl) hnd hwf
    simp only [List.nil_append] at hinl
    have hdisj_sec : ∀ p ∈ entries, isSectionVal p.2 = true → assocLookupSkel p.1 inlSk = none := by
      intro p hp hsec
      suffices hnot : ∀ l : List (String × TomlValue),
          (∀ q ∈ l, q.1 = p.1 → q = p) →
          assocLookupSkel p.1 ((l.filter (fun q => !isSectionVal q.2)).map (fun q => (q.1, SkeletonNode.leaf))) = none by
        apply hnot entries
        intro q hq hk_eq
        have h1 := lookupKeyList_mem_of_noDupKeys entries hnd q.1 q.2 hq
        have h2 := lookupKeyList_mem_of_noDupKeys entries hnd p.1 p.2 hp
        rw [hk_eq, h2] at h1
        exact Prod.ext hk_eq (Option.some.inj h1).symm
      intro l huniq; induction l with
      | nil => rfl
      | cons q qs ih =>
        by_cases hqs : isSectionVal q.2 = true
        · simp [hqs, ih (fun r hr hrk => huniq r (List.mem_cons_of_mem _ hr) hrk)]
        · have hqf := Bool.eq_false_iff.mpr hqs
          have hne : p.1 ≠ q.1 := fun he => by
            have := huniq q List.mem_cons_self he.symm; subst this; rw [hsec] at hqf; cases hqf
          simp [hqf, assocLookupSkel, beq_false_of_ne hne, ih (fun r hr hrk => huniq r (List.mem_cons_of_mem _ hr) hrk)]
    obtain ⟨secSk, hsec_st, hsec_cov, hsec_all⟩ := section_entries_ok numApi hfmt fullDoc path entries entries
      wrap hf inlSk (fun p hp => lookupKeyList_mem_of_noDupKeys entries hnd p.1 p.2 hp)
      hdisj_sec hnd hwf (endActivePath path (chooseInlineStmts numApi entries))
    refine ⟨inlSk ++ secSk, ?_, ?_⟩
    · refine skelMatchesEntries_of_props (inlSk ++ secSk) entries (fun p hp => ?_) (fun k sn hm => ?_)
      · by_cases hs : isSectionVal p.2 = true
        · rcases hsec_cov p hp hs with ⟨sn, hmem⟩
          exact assocLookupSkel_isSome_of_mem (List.mem_append_right _ hmem)
        · have hpf := Bool.eq_false_iff.mpr hs
          have hmem : (p.1, SkeletonNode.leaf) ∈ inlSk :=
            List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp [hpf]⟩, rfl⟩
          exact assocLookupSkel_isSome_of_mem (List.mem_append_left _ hmem)
      · rcases List.mem_append.mp hm with hmi | hms
        · rcases List.mem_map.mp hmi with ⟨p, hpf, heq⟩
          obtain ⟨hp, hnot_sec⟩ := List.mem_filter.mp hpf
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          refine ⟨p.2, lookupKeyList_mem_of_noDupKeys entries hnd p.1 p.2 hp, ?_⟩
          cases hp2 : p.2 <;> first | (simp [skelNodeMatchesValue]; done) | (rw [hp2] at hnot_sec; simp [isSectionVal] at hnot_sec)
        · exact hsec_all k sn hms
    · rw [concatLinesNl_append]
      exact renderStmts_append_true fullDoc _ _ path (wrap []) (wrap inlSk) (wrap (inlSk ++ secSk)) _ _ hinl hsec_st
  termination_by sizeOf entries * 3 + 2
  decreasing_by simp +arith

  private theorem section_entries_ok (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (fullDoc path entries subEs : List _) (wrap : List (String × SkeletonNode) → List (String × SkeletonNode))
      (hf : FocusAtPath fullDoc path entries wrap)
      (curSk : List (String × SkeletonNode))
      (hlu : ∀ p ∈ subEs, lookupKeyList p.1 entries = some p.2)
      (hdisj : ∀ p ∈ subEs, isSectionVal p.2 = true → assocLookupSkel p.1 curSk = none)
      (hnd : noDupKeysBool subEs = true)
      (hwf : wellFormedValueBool.wellFormedTableListBool subEs = true)
      (act : List String) :
      ∃ secSk,
        renderStmts fullDoc act (wrap curSk) true (chooseSectionStmts numApi path subEs) =
          some (wrap (curSk ++ secSk),
            concatLinesNl (formatTableSectionPart numApi (path.reverse.map formatKey) subEs)) ∧
        (∀ p ∈ subEs, isSectionVal p.2 = true → ∃ sn, (p.1, sn) ∈ secSk) ∧
        (∀ k sn, (k, sn) ∈ secSk → ∃ v, lookupKeyList k entries = some v ∧ skelNodeMatchesValue sn v = true) := by
    match subEs with
    | [] =>
      exact ⟨[], by simp [chooseSectionStmts, formatTableSectionPart, concatLinesNl, renderStmts],
        (fun _ hm => nomatch hm), (fun _ _ hm => nomatch hm)⟩
    | (k, v) :: rest =>
      simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
      simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
      have hk_lu := hlu (k, v) List.mem_cons_self
      have hne_rest : ∀ p ∈ rest, p.1 ≠ k := fun p hp he => by
        subst he; rw [(hasKeyList_eq_true_iff p.1 rest).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)] at hnd
        nomatch hnd.1
      match hv : v with
      | .table ⟨subList⟩ =>
        have hwf_sub : noDupKeysBool subList = true ∧ wellFormedValueBool.wellFormedTableListBool subList = true := by
          simpa [WellFormedValue, wellFormedValueBool, Bool.and_eq_true] using hwf.1
        have hk_none := hdisj (k, .table ⟨subList⟩) List.mem_cons_self rfl
        have hhdr_loc : applyHeaderSkel false curSk [k] = some (assocSetSkel k (.table .explicit []) curSk) := by
          simp [applyHeaderSkel, applyHeaderLeafSkel, hk_none]
        have hhdr_full := hf.header_at false curSk [k] _ (by simp) hhdr_loc
        obtain ⟨subFinSk, hsub_m, hsub_st⟩ := table_plan_ok numApi hfmt fullDoc (path ++ [k]) subList
          (fun cSk => wrap (assocSetSkel k (.table .explicit cSk) curSk))
          (focusAtPath_stepTable hf hk_lu curSk) hwf_sub.1 hwf_sub.2
        have hset_eq : assocSetSkel k (.table .explicit subFinSk) curSk = curSk ++ [(k, .table .explicit subFinSk)] :=
          assocSetSkel_eq_append_of_none _ curSk hk_none
        have hdisj_nx : ∀ p ∈ rest, isSectionVal p.2 = true →
            assocLookupSkel p.1 (curSk ++ [(k, .table .explicit subFinSk)]) = none := by
          intro p hp hs
          rw [← hset_eq, assocLookupSkel_set_ne (hne_rest p hp), hdisj p (List.mem_cons_of_mem _ hp) hs]
        let bodyStmts := chooseInlineStmts numApi subList ++ chooseSectionStmts numApi (path ++ [k]) subList
        obtain ⟨restSec, hrest_st, hrest_cov, hrest_all⟩ := section_entries_ok numApi hfmt fullDoc path entries rest
          wrap hf (curSk ++ [(k, .table .explicit subFinSk)])
          (fun p hp => hlu p (List.mem_cons_of_mem _ hp)) hdisj_nx hnd.2 hwf.2
          (endActivePath (path ++ [k]) bodyStmts)
        have hsub_st' : renderStmts fullDoc (path ++ [k])
            (wrap (assocSetSkel k (.table .explicit []) curSk)) true bodyStmts =
            some (wrap (curSk ++ [(k, .table .explicit subFinSk)]),
              concatLinesNl (formatTableInlinePart numApi subList ++
                formatTableSectionPart numApi ((path ++ [k]).reverse.map formatKey) subList)) := by
          dsimp only [bodyStmts]; rw [← hset_eq]; exact hsub_st
        have hcomb := renderStmts_append_true fullDoc bodyStmts (chooseSectionStmts numApi path rest)
          (path ++ [k]) (wrap (assocSetSkel k (.table .explicit []) curSk))
          (wrap (curSk ++ [(k, .table .explicit subFinSk)]))
          (wrap ((curSk ++ [(k, .table .explicit subFinSk)]) ++ restSec)) _ _
          hsub_st' hrest_st
        have hrev_eq : ((path ++ [k]).reverse.map formatKey) = formatKey k :: path.reverse.map formatKey := by
          rw [List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append, List.map_cons]
        rw [hrev_eq] at hcomb
        refine ⟨(k, .table .explicit subFinSk) :: restSec, ?_, ?_, ?_⟩
        · simp only [chooseSectionStmts, renderStmts, ite_self,
            show isClosedTrivia "" = true by decide, show isHorizWsStr "" = true by decide,
            Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            renderDottedKey_mkCanon path k, show renderLineSuffix {} = some "" from rfl,
            mkCanonDottedKey_path path k, Option.bind_eq_bind, Option.bind]
          rw [hhdr_full]; dsimp only
          have hassoc_s : chooseInlineStmts numApi subList ++ chooseSectionStmts numApi (path ++ [k]) subList ++
              chooseSectionStmts numApi path rest = bodyStmts ++ chooseSectionStmts numApi path rest := rfl
          rw [hassoc_s, hcomb]; dsimp only
          simp only [Option.some.injEq, Prod.mk.injEq, List.append_assoc, List.cons_append, List.nil_append,
            true_and, formatTableSectionPart, concatLinesNl, concatLinesNl_append]
          rw [String.ext_iff]; simp [String.toList_append, List.append_assoc]
        · intro p hp hs
          rcases List.mem_cons.mp hp with rfl | hpr
          · exact ⟨_, List.mem_cons_self⟩
          · obtain ⟨sn, hsn⟩ := hrest_cov p hpr hs
            exact ⟨sn, List.mem_cons_of_mem _ hsn⟩
        · intro k' sn' hm
          rcases List.mem_cons.mp hm with hhd | htl
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhd
            exact ⟨.table ⟨subList⟩, hk_lu, by simpa [skelNodeMatchesValue] using hsub_m⟩
          · exact hrest_all k' sn' htl
      | .array ⟨xsList⟩ =>
        by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
        · have hall_xs := (Bool.and_eq_true_iff.mp haot).2
          have hne_xs : xsList ≠ [] := by
            intro hnil; subst hnil; simp [isNonEmptyTableArray] at haot
          have hk_none := hdisj (k, .array ⟨xsList⟩) List.mem_cons_self haot
          obtain ⟨elemsSk, haot_m, haot_st⟩ := aot_elems_ok numApi hfmt fullDoc path entries wrap hf
            k curSk hk_none [] xsList [] rfl rfl (by simp [skelMatchesAot]) hne_xs
            hk_lu hwf.1 hall_xs act
          have hset_eq : assocSetSkel k (.aot elemsSk) curSk = curSk ++ [(k, .aot elemsSk)] :=
            assocSetSkel_eq_append_of_none _ curSk hk_none
          have hdisj_nx : ∀ p ∈ rest, isSectionVal p.2 = true →
              assocLookupSkel p.1 (curSk ++ [(k, .aot elemsSk)]) = none := by
            intro p hp hs
            rw [← hset_eq, assocLookupSkel_set_ne (hne_rest p hp), hdisj p (List.mem_cons_of_mem _ hp) hs]
          obtain ⟨restSec, hrest_st, hrest_cov, hrest_all⟩ := section_entries_ok numApi hfmt fullDoc path entries rest
            wrap hf (curSk ++ [(k, .aot elemsSk)])
            (fun p hp => hlu p (List.mem_cons_of_mem _ hp)) hdisj_nx hnd.2 hwf.2
            (endActivePath act (chooseAotStmts numApi path k xsList))
          have hcomb := renderStmts_append_true fullDoc (chooseAotStmts numApi path k xsList)
            (chooseSectionStmts numApi path rest) act (wrap curSk) (wrap (curSk ++ [(k, .aot elemsSk)]))
            (wrap ((curSk ++ [(k, .aot elemsSk)]) ++ restSec)) _ _
            (by simpa [hset_eq] using haot_st) hrest_st
          refine ⟨(k, .aot elemsSk) :: restSec, ?_, ?_, ?_⟩
          · simp only [chooseSectionStmts, haot, ↓reduceIte, hcomb, formatTableSectionPart, concatLinesNl_append]
            simp [List.append_assoc]
          · intro p hp hs
            rcases List.mem_cons.mp hp with rfl | hpr
            · exact ⟨_, List.mem_cons_self⟩
            · obtain ⟨sn, hsn⟩ := hrest_cov p hpr hs
              exact ⟨sn, List.mem_cons_of_mem _ hsn⟩
          · intro k' sn' hm
            rcases List.mem_cons.mp hm with hhd | htl
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhd
              exact ⟨.array ⟨xsList⟩, hk_lu, by simpa [skelNodeMatchesValue] using haot_m⟩
            · exact hrest_all k' sn' htl
        · have haf := Bool.eq_false_iff.mpr haot
          obtain ⟨restSec, hrest_st, hrest_cov, hrest_all⟩ := section_entries_ok numApi hfmt fullDoc path entries rest
            wrap hf curSk (fun p hp => hlu p (List.mem_cons_of_mem _ hp))
            (fun p hp hs => hdisj p (List.mem_cons_of_mem _ hp) hs) hnd.2 hwf.2 act
          refine ⟨restSec, by simpa [chooseSectionStmts, haf, formatTableSectionPart] using hrest_st,
            fun p hp hs => ?_, hrest_all⟩
          rcases List.mem_cons.mp hp with rfl | hpr
          · simp [isSectionVal, haf] at hs
          · exact hrest_cov p hpr hs
      | .string _ | .int _ | .float _ | .bool _ | .offsetDateTime _ | .localDateTime _ | .localDate _ | .localTime _ =>
        obtain ⟨restSec, hrest_st, hrest_cov, hrest_all⟩ := section_entries_ok numApi hfmt fullDoc path entries rest
          wrap hf curSk (fun p hp => hlu p (List.mem_cons_of_mem _ hp))
          (fun p hp hs => hdisj p (List.mem_cons_of_mem _ hp) hs) hnd.2 hwf.2 act
        refine ⟨restSec, by simpa [chooseSectionStmts, formatTableSectionPart] using hrest_st,
          fun p hp hs => ?_, hrest_all⟩
        rcases List.mem_cons.mp hp with rfl | hpr
        · nomatch hs
        · exact hrest_cov p hpr hs
  termination_by sizeOf subEs * 3 + 1
  decreasing_by all_goals subst_vars; simp +arith

  private theorem aot_elems_ok (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (fullDoc path entries : List _) (wrap : List (String × SkeletonNode) → List (String × SkeletonNode))
      (hf : FocusAtPath fullDoc path entries wrap)
      (k : String) (curSk : List (String × SkeletonNode)) (hk_none : assocLookupSkel k curSk = none)
      (doneDocs remDocs : List TomlValue) (doneElems : List (List (String × SkeletonNode)))
      (hlen : doneDocs.length = doneElems.length)
      (hall_done : (doneDocs.all fun x => match x with | .table _ => true | _ => false) = true)
      (hm_done : skelMatchesAot doneElems doneDocs = true)
      (hne_total : doneDocs ++ remDocs ≠ [])
      (hlu_k : lookupKeyList k entries = some (.array ⟨doneDocs ++ remDocs⟩))
      (hwf_rem : wellFormedValueBool.wellFormedListBool remDocs = true)
      (hall_rem : (remDocs.all fun x => match x with | .table _ => true | _ => false) = true)
      (act : List String) :
      let startSk := if doneElems.isEmpty then curSk else assocSetSkel k (.aot doneElems) curSk
      let revNext := formatKey k :: path.reverse.map formatKey
      let hdr := "[[" ++ String.intercalate "." revNext.reverse ++ "]]"
      ∃ elemsSk,
        skelMatchesAot elemsSk (doneDocs ++ remDocs) = true ∧
        renderStmts fullDoc act (wrap startSk) true (chooseAotStmts numApi path k remDocs) =
          some (wrap (assocSetSkel k (.aot elemsSk) curSk),
            concatLinesNl (formatAotElemList numApi revNext hdr remDocs)) := by
    match remDocs with
    | [] =>
      cases doneElems with
      | nil =>
        cases doneDocs with
        | nil => exact absurd rfl hne_total
        | cons _ _ => simp at hlen
      | cons e0 er =>
        exact ⟨e0 :: er, by simpa using hm_done,
          by simp [chooseAotStmts, formatAotElemList, concatLinesNl, renderStmts]⟩
    | x :: rTail =>
      simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at hwf_rem
      simp only [List.all_cons, Bool.and_eq_true] at hall_rem
      match hx : x with
      | .table ⟨elemList⟩ =>
        have hwf_e : noDupKeysBool elemList = true ∧ wellFormedValueBool.wellFormedTableListBool elemList = true := by
          simpa [WellFormedValue, wellFormedValueBool, Bool.and_eq_true] using hwf_rem.1
        let startSk := if doneElems.isEmpty then curSk else assocSetSkel k (.aot doneElems) curSk
        have hhdr_loc : applyHeaderSkel true startSk [k] =
            some (assocSetSkel k (.aot (doneElems ++ [[]])) curSk) := by
          cases doneElems with
          | nil => simp [startSk, applyHeaderSkel, applyHeaderLeafSkel, hk_none]
          | cons e0 er => simp [startSk, applyHeaderSkel, applyHeaderLeafSkel, assocLookupSkel_set_self, assocSetSkel_idem]
        have hhdr_full := hf.header_at true startSk [k] _ (by simp) hhdr_loc
        dsimp only [startSk] at hhdr_full
        obtain ⟨elemFinSk, helem_m, helem_st⟩ := table_plan_ok numApi hfmt fullDoc (path ++ [k]) elemList
          (fun cSk => wrap (assocSetSkel k (.aot (doneElems ++ [cSk])) curSk))
          (focusAtPath_stepAot hf hlu_k hlen hall_done curSk) hwf_e.1 hwf_e.2
        let bodyStmts := chooseInlineStmts numApi elemList ++ chooseSectionStmts numApi (path ++ [k]) elemList
        have hdone_nx_ne : (doneElems ++ [elemFinSk]).isEmpty = false := by
          cases doneElems <;> rfl
        have hassoc_docs : (doneDocs ++ [.table ⟨elemList⟩]) ++ rTail = doneDocs ++ .table ⟨elemList⟩ :: rTail := by
          simp [List.append_assoc]
        obtain ⟨elemsSk, htail_m, htail_st⟩ := aot_elems_ok numApi hfmt fullDoc path entries wrap hf
          k curSk hk_none (doneDocs ++ [.table ⟨elemList⟩]) rTail (doneElems ++ [elemFinSk])
          (by simp [hlen]) (by simp [hall_done]) (skelMatchesAot_snoc hm_done helem_m)
          (by simp) (by rw [hassoc_docs]; exact hlu_k) hwf_rem.2 hall_rem.2
          (endActivePath (path ++ [k]) bodyStmts)
        rw [hdone_nx_ne] at htail_st
        have hcomb := renderStmts_append_true fullDoc bodyStmts (chooseAotStmts numApi path k rTail)
          (path ++ [k]) (wrap (assocSetSkel k (.aot (doneElems ++ [[]])) curSk))
          (wrap (assocSetSkel k (.aot (doneElems ++ [elemFinSk])) curSk))
          (wrap (assocSetSkel k (.aot elemsSk) curSk)) _ _ helem_st htail_st
        have hrev_eq : ((path ++ [k]).reverse.map formatKey) = formatKey k :: path.reverse.map formatKey := by
          rw [List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append, List.map_cons]
        rw [hrev_eq] at hcomb
        refine ⟨elemsSk, by rw [← hassoc_docs]; exact htail_m, ?_⟩
        simp only [chooseAotStmts, renderStmts, ite_self,
          show isClosedTrivia "" = true by decide, show isHorizWsStr "" = true by decide,
          Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
          renderDottedKey_mkCanon path k, show renderLineSuffix {} = some "" from rfl,
          mkCanonDottedKey_path path k, Option.bind_eq_bind, Option.bind]
        rw [hhdr_full]; dsimp only
        have hassoc_s : chooseInlineStmts numApi elemList ++ chooseSectionStmts numApi (path ++ [k]) elemList ++
            chooseAotStmts numApi path k rTail = bodyStmts ++ chooseAotStmts numApi path k rTail := rfl
        rw [hassoc_s, hcomb]; dsimp only
        simp only [Option.some.injEq, Prod.mk.injEq, true_and, formatAotElemList, concatLinesNl, concatLinesNl_append]
        rw [String.ext_iff]; simp [String.toList_append, List.append_assoc]
      | .string _ | .int _ | .float _ | .bool _ | .offsetDateTime _ | .localDateTime _ | .localDate _
      | .localTime _ | .array _ =>
        nomatch hall_rem.1
  termination_by sizeOf remDocs * 3
  decreasing_by all_goals subst_vars; simp +arith
end

private theorem formatSectionLines_nil_eq_nil (numApi : NumParseApi) (revPref : List String)
    (doc : TomlTable) (h : formatSectionLines numApi revPref doc = []) : doc.toList = [] := by
  cases hlist : doc.toList with
  | nil => rfl
  | cons hd _ =>
    rcases hd with ⟨_, v⟩; simp only [formatSectionLines, hlist, List.append_eq_nil_iff] at h
    cases v with
    | table sub => cases sub; simp [formatTableSectionPart] at h
    | array xs =>
      cases xs with
      | mk xsList =>
        by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
        · simp only [formatTableSectionPart, haot, ↓reduceIte] at h
          cases xsList with
          | nil => simp [isNonEmptyTableArray] at haot
          | cons x0 _ =>
            simp only [isNonEmptyTableArray, List.all_cons, Bool.and_eq_true] at haot
            cases x0 with | table elem => cases elem; simp [formatAotElemList] at h | _ => cases haot.2.1
        · simp [formatTableInlinePart, Bool.eq_false_iff.mpr haot] at h
    | _ => simp [formatTableInlinePart] at h

private theorem isPrefixOf_append_self : ∀ (sub suf : List Char), sub.isPrefixOf (sub ++ suf) = true
  | [], _ => rfl
  | _ :: cs, suf => by simp [isPrefixOf_append_self cs suf]

private theorem hasCharSublist_mid (sub : List Char) :
    ∀ (pre suf : List Char), hasCharSublist sub (pre ++ sub ++ suf) = true
  | [], suf => by
    cases sub with
    | nil => cases suf <;> simp [hasCharSublist]
    | cons _ cs => simp [hasCharSublist, isPrefixOf_append_self cs suf]
  | _ :: pre, suf => by
    simp only [List.cons_append, hasCharSublist, Bool.or_eq_true]
    exact Or.inr (hasCharSublist_mid sub pre suf)

private theorem intercalate_nl_decomp :
    ∀ (hd : String) (tl : List String),
      (String.intercalate "\n" (hd :: tl)).toList = hd.toList ++ tl.flatMap (fun s => '\n' :: s.toList)
  | _, [] => by simp [String.intercalate_singleton]
  | _, x :: xs => by
    rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, intercalate_nl_decomp x xs]
    simp [List.flatMap_cons, List.append_assoc]

private theorem intercalate_mem_sublist {ln : String} {lines : List String} (hmem : ln ∈ lines)
    {sub : List Char} (hsub : ∃ p s, ln.toList = p ++ sub ++ s) :
    hasCharSublist sub (String.intercalate "\n" lines ++ "\n").toList = true := by
  rcases hsub with ⟨p, s, hln⟩
  cases lines with
  | nil => nomatch hmem
  | cons hd tl =>
    rw [String.toList_append, intercalate_nl_decomp hd tl]
    rcases List.mem_cons.mp hmem with rfl | htl
    · rw [hln]
      have ha : p ++ sub ++ s ++ tl.flatMap (fun x => '\n' :: x.toList) ++ "\n".toList =
          p ++ sub ++ (s ++ tl.flatMap (fun x => '\n' :: x.toList) ++ "\n".toList) := by simp [List.append_assoc]
      rw [ha]; exact hasCharSublist_mid sub p _
    · rcases List.mem_iff_append.mp htl with ⟨before, after, hsplit⟩
      rw [hsplit, List.flatMap_append, List.flatMap_cons, hln]
      have ha : hd.toList ++ (before.flatMap (fun x => '\n' :: x.toList) ++
            ('\n' :: (p ++ sub ++ s) ++ after.flatMap (fun x => '\n' :: x.toList))) ++ "\n".toList =
          (hd.toList ++ before.flatMap (fun x => '\n' :: x.toList) ++ ('\n' :: p)) ++
            sub ++ (s ++ after.flatMap (fun x => '\n' :: x.toList) ++ "\n".toList) := by simp [List.append_assoc]
      rw [ha]; exact hasCharSublist_mid sub _ _

private theorem entry_emits_rendered_key (numApi : NumParseApi) (kvs : List (String × TomlValue))
    {k : String} {v : TomlValue} (hm : (k, v) ∈ kvs) :
    ∃ ln ∈ formatTableInlinePart numApi kvs ++ formatTableSectionPart numApi [] kvs,
      ∃ p s, ln.toList = p ++ (formatKey k).toList ++ s := by
  induction kvs with
  | nil => nomatch hm
  | cons kv rest ih =>
    rcases kv with ⟨k0, v0⟩
    rcases List.mem_cons.mp hm with hhead | htail
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
      cases hv : v with
      | table sub =>
        cases sub; refine ⟨"[" ++ formatKey k ++ "]", ?_, ['['], [']'], by simp [String.toList_append]⟩
        simp [formatTableInlinePart, formatTableSectionPart, String.intercalate_singleton]
      | array xs =>
        cases xs with
        | mk xsList =>
          by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
          · have haot0 := haot
            cases xsList with
            | nil => simp [isNonEmptyTableArray] at haot
            | cons x0 _ =>
              simp only [isNonEmptyTableArray, List.all_cons, Bool.and_eq_true] at haot
              cases x0 with
              | table elem =>
                cases elem; refine ⟨"[[" ++ formatKey k ++ "]]", ?_, ['[', '['], [']', ']'], by simp [String.toList_append]⟩
                simp [formatTableInlinePart, formatTableSectionPart, haot0, formatAotElemList, String.intercalate_singleton]
              | _ => nomatch haot.2.1
          · have haotF := Bool.eq_false_iff.mpr haot
            exact ⟨formatKey k ++ " = " ++ formatValueInline numApi (.array ⟨xsList⟩),
              by simp [formatTableInlinePart, haotF], [],
              (" = " ++ formatValueInline numApi (.array ⟨xsList⟩)).toList,
              by simp [String.toList_append, List.append_assoc]⟩
      | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
        exact ⟨formatKey k ++ " = " ++ formatValueInline numApi v,
          by simp [hv, formatTableInlinePart], [],
          (" = " ++ formatValueInline numApi v).toList,
          by simp [String.toList_append, List.append_assoc]⟩
    · obtain ⟨ln, hlnMem, hsub⟩ := ih htail
      refine ⟨ln, ?_, hsub⟩
      rcases List.mem_append.mp hlnMem with hinl | hsec
      · apply List.mem_append_left
        cases v0 with
        | table _ => simp [formatTableInlinePart, hinl]
        | array xs => by_cases haot : isNonEmptyTableArray xs = true <;> simp [formatTableInlinePart, haot, hinl]
        | _ => simp [formatTableInlinePart, hinl]
      · apply List.mem_append_right
        cases v0 with
        | table sub => cases sub; simp [formatTableSectionPart, hsec]
        | array xs =>
          cases xs with
          | mk xsList => by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true <;> simp [formatTableSectionPart, haot, hsec]
        | _ => simp [formatTableSectionPart, hsec]

private theorem expandNewlines_nil_id : ∀ cs : List Char, expandNewlines [] cs = some cs
  | [] => rfl
  | c :: cs => by
    by_cases hnl : c = '\n'
    · subst hnl; simp [expandNewlines, expandNewlines_nil_id cs]
    · have hst : expandNewlines [] (c :: cs) = (expandNewlines [] cs >>= fun r => some (c :: r)) := by
        (conv => lhs; unfold expandNewlines); split <;> simp_all
      rw [hst, expandNewlines_nil_id cs]; rfl

/-- `formatWithNum` satisfies `Model.allowedFormat` for any `ValidNumApi`. -/
theorem formatWithNum_allowedFormat (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (doc : TomlTable) : allowedFormat doc (formatWithNum numApi doc) := by
  unfold allowedFormat
  cases hdoc : doc.toList with
  | nil =>
    have hempty : doc = #[] := Array.ext' hdoc
    subst hempty
    simp [formatWithNum, formatSectionLines, formatTableInlinePart, formatTableSectionPart]
  | cons kv rest =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    by_cases hwf : wellFormedTableBool doc = true
    · simp only [hwf, ↓reduceIte]
      unfold formatWithNum
      cases hlines : formatSectionLines numApi [] doc with
      | nil =>
        have hnil := formatSectionLines_nil_eq_nil numApi [] doc hlines
        rw [hdoc] at hnil; nomatch hnil
      | cons hd tl =>
        have hwf_p : noDupKeysBool doc.toList = true ∧ wellFormedValueBool.wellFormedTableListBool doc.toList = true := by
          simpa [wellFormedTableBool, Bool.and_eq_true] using hwf
        obtain ⟨finSk, hm_fin, hst⟩ := table_plan_ok numApi (validNumApi_validFmt numApi hnum)
          doc.toList [] doc.toList id (focusAtPath_root doc.toList) hwf_p.1 hwf_p.2
        unfold formatSectionLines at hlines
        simp only [List.reverse_nil, List.map_nil, id_eq, hlines, concatLinesNl_cons] at hst
        let tape : RenderTape :=
          { stmts := chooseInlineStmts numApi doc.toList ++ chooseSectionStmts numApi [] doc.toList
          , trailingNewline := true
          , eofTrivia := ""
          , crlfMask := [] }
        have hclean : isCleanFormatTape tape = true := by
          have hc1 := (chooseInlineStmts_endAct numApi [] doc.toList).2
          have hc2 := chooseSectionStmts_clean numApi [] doc.toList
          dsimp only [isCleanFormatTape, tape]
          rw [List.all_append, hc1, hc2]; rfl
        have hlf : renderLF doc tape = some (String.intercalate "\n" (hd :: tl) ++ "\n") := by
          dsimp only [tape]
          simp [renderLF, hwf, show isEofTrivia "" = true by decide, hst, hm_fin]
        refine ⟨tape, hclean, ?_⟩
        rw [Model.render, hlf]
        dsimp only [tape, Option.bind_eq_bind, Option.bind]
        rw [expandNewlines_nil_id]; dsimp only
        rw [String.ofList_toList]
    · simp only [hwf, Bool.false_eq_true, ↓reduceIte]
      unfold formatWithNum
      cases hlines : formatSectionLines numApi [] doc with
      | nil =>
        have hnil := formatSectionLines_nil_eq_nil numApi [] doc hlines
        rw [hdoc] at hnil; nomatch hnil
      | cons hd tl =>
        refine ⟨by simp [String.toList_append, List.reverse_append], fun k v hmem => ?_⟩
        rw [← hdoc] at hmem
        obtain ⟨ln, hlnMem, hsub⟩ := entry_emits_rendered_key numApi doc.toList hmem
        unfold formatSectionLines at hlines; rw [hlines] at hlnMem
        exact ⟨formatKey k, renderKey_chooseKeyStyle k, intercalate_mem_sublist hlnMem hsub⟩

private theorem render_empty_default : Model.render #[] {} = some "" := by
  simp [Model.render, renderLF, wellFormedTableBool, noDupKeysBool,
    wellFormedValueBool.wellFormedTableListBool, show isEofTrivia "" = true by decide,
    renderStmts, skelMatchesEntries, skelMatchesEntriesAll, expandNewlines]

private theorem formatWithNum_roundTrip_model (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (doc : TomlTable) (hwf : WellFormedTable doc) :
    ∃ parsed, parseWithNum numApi (formatWithNum numApi doc) = .ok parsed ∧ TomlTableEquiv doc parsed := by
  have hfmt := formatWithNum_allowedFormat numApi hnum doc
  unfold allowedFormat at hfmt
  cases hdoc : doc.toList with
  | nil =>
    have hempty : doc = #[] := Array.ext' hdoc
    subst hempty
    simp only [List.isEmpty_nil, ↓reduceIte] at hfmt
    rw [hfmt]
    exact render_parse_roundTrip_model numApi hnum #[] {} "" render_empty_default
  | cons _ _ =>
    have hwf_b : wellFormedTableBool doc = true := hwf
    simp only [hdoc, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hwf_b] at hfmt
    rcases hfmt with ⟨tape, _, hr⟩
    exact render_parse_roundTrip_model numApi hnum doc tape (formatWithNum numApi doc) hr

section
attribute [local irreducible] parseWithNum

/-- Prove `test_toml_render_parse_roundTrip` for `Internal.mkApi` over any `numApi`. -/
theorem allPass_render_parse_roundTrip (numApi : NumParseApi) :
    Core.AllPass (test_toml_render_parse_roundTrip Internal.mkApi numApi) := by
  intro hobeys ⟨doc, tape⟩
  have hnum := validNumApi_of_obeysApi hobeys
  dsimp only [test_toml_render_parse_roundTrip, Internal.mkApi, makeTomlApi,
    Core.NondetTest.assume, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  cases hr : Model.render doc tape with
  | none => exact fun _ => trivial
  | some out =>
    obtain ⟨_, hp, heq⟩ := render_parse_roundTrip_model numApi hnum doc tape out hr
    dsimp only; rw [hp]; exact ⟨heq, trivial⟩

/-- Witness `CanReach` for `test_toml_render_parse_roundTrip` using `NumParse.Model.modelApi`. -/
theorem canReach_render_parse_roundTrip :
    Core.CanReach (test_toml_render_parse_roundTrip Internal.mkApi LeanSwe.NumParse.Model.modelApi) := by
  have hobeys := LeanSwe.NumParse.Model.modelApi_obeys
  have hnum := validNumApi_of_obeysApi hobeys
  have hr : Model.render #[] {} = some "" := render_empty_default
  obtain ⟨_, hp, heq⟩ := render_parse_roundTrip_model LeanSwe.NumParse.Model.modelApi hnum #[] {} "" hr
  refine ⟨hobeys, (#[], {}), ?_⟩
  dsimp only [test_toml_render_parse_roundTrip, Internal.mkApi, makeTomlApi,
    Core.NondetTest.assume, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  rw [hr]; dsimp only; rw [hp]; exact ⟨heq, trivial⟩

/-- Prove `test_toml_format_validAndRoundTrip` for `Internal.mkApi` over any `numApi`. -/
theorem allPass_format_validAndRoundTrip (numApi : NumParseApi) :
    Core.AllPass (test_toml_format_validAndRoundTrip Internal.mkApi numApi) := by
  intro hobeys doc hwf
  have hnum := validNumApi_of_obeysApi hobeys
  dsimp only [test_toml_format_validAndRoundTrip, Internal.mkApi, makeTomlApi,
    Core.NondetTest.assume, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  obtain ⟨_, hp, heq⟩ := formatWithNum_roundTrip_model numApi hnum doc hwf
  rw [hp]; exact ⟨heq, trivial⟩

/-- Witness `CanReach` for `test_toml_format_validAndRoundTrip` using `NumParse.Model.modelApi`. -/
theorem canReach_format_validAndRoundTrip :
    Core.CanReach (test_toml_format_validAndRoundTrip Internal.mkApi LeanSwe.NumParse.Model.modelApi) := by
  have hobeys := LeanSwe.NumParse.Model.modelApi_obeys
  have hnum := validNumApi_of_obeysApi hobeys
  have hwf : WellFormedTable #[] := rfl
  obtain ⟨_, hp, heq⟩ := formatWithNum_roundTrip_model LeanSwe.NumParse.Model.modelApi hnum #[] hwf
  refine ⟨hobeys, #[], hwf, ?_⟩
  dsimp only [test_toml_format_validAndRoundTrip, Internal.mkApi, makeTomlApi,
    Core.NondetTest.assume, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  rw [hp]; exact ⟨heq, trivial⟩

end

end LeanSwe.Toml.Proofs
