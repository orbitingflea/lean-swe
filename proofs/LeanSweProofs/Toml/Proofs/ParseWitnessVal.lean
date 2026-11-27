import LeanSweProofs.Toml.Proofs.ParseWitnessSkel
import LeanSweProofs.Toml.Proofs.RenderInjectiveArr

/-!
# Recursive Value, Array, and Inline-Table Parse-to-Render Witnesses

Proves `parseValArrInline_witness` and `parseValue_witness` constructing exact `ValueTape`
witnesses across all nested arrays, dotted-key inline tables, strings, and scalars.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse

private def prependWsAssigns (ws : String) :
    List (String × DottedKeyTape × String × String × ValueTape × String) →
      List (String × DottedKeyTape × String × String × ValueTape × String)
  | [] => []
  | (wsPre, dk, wsEqL, wsEqR, vt, wsPost) :: rest =>
    (ws ++ wsPre, dk, wsEqL, wsEqR, vt, wsPost) :: rest

private theorem renderInlineAssigns_prependWs {ws : String} (hws : isHorizWsStr ws = true)
    {tableEntries : List (String × TomlValue)} {sk fsk : List (String × SkeletonNode)}
    {assigns : List (String × DottedKeyTape × String × String × ValueTape × String)}
    {kv0 : String} {kvsTail : List String}
    (hr : renderInlineAssigns tableEntries sk assigns = some (fsk, kv0 :: kvsTail)) :
    renderInlineAssigns tableEntries sk (prependWsAssigns ws assigns) =
      some (fsk, (ws ++ kv0) :: kvsTail) := by
  cases assigns with
  | nil => simp [renderInlineAssigns] at hr
  | cons a0 rest =>
    rcases a0 with ⟨wsPre, dk, wsEqL, wsEqR, vt, wsPost⟩
    unfold renderInlineAssigns at hr
    split at hr <;> try (simp at hr; done)
    rename_i hok; simp at hok
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rk, hrk, ⟨nsk, v⟩, hins, rv, hrv, ⟨fsk', tl⟩, htl, ⟨rfl, hcons⟩⟩
    obtain ⟨rfl, rfl⟩ := List.cons.inj hcons
    have hws_comb := isHorizWsStr_append hws hok.1.1.1
    simp [prependWsAssigns, renderInlineAssigns, hws_comb, hok.1.1.2, hok.1.2, hok.2,
      hrk, hins, hrv, htl, String.append_assoc]

private theorem parseValArrInline_witness {numApi : NumParseApi} (hnum : ValidNumApi numApi) (fuel : Nat) :
    (∀ cs v after, CleanNorm cs →
      parseValueFuel (toCharNumApi numApi) fuel cs = .ok (v, after) →
      ∃ vt rv, renderValueInline v vt = some rv ∧ cs = rv.toList ++ after) ∧
    (∀ cs revAcc out after, CleanNorm cs →
      parseArrayFuel (toCharNumApi numApi) fuel cs revAcc = .ok (out, after) →
      (∃ tr, isClosedTrivia tr = true ∧ out = .array revAcc.reverse.toArray ∧ cs = tr.toList ++ ']' :: after) ∨
      (∃ vals tps strs trailOpt trailStr,
        vals ≠ [] ∧
        out = .array (revAcc.reverse ++ vals).toArray ∧
        renderArrayElems vals tps = some strs ∧
        (match trailOpt with | none => some "" | some trv => if isClosedTrivia trv then some ("," ++ trv) else none) = some trailStr ∧
        cs = (String.intercalate "," strs ++ trailStr).toList ++ ']' :: after)) ∧
    (∀ cs entries out after, CleanNorm cs → EntriesKeyNoDup entries = true →
      parseInlineTableFuel (toCharNumApi numApi) fuel cs entries = .ok (out, after) →
      ∃ finalEntries assigns kv0 kvsTail,
        assigns ≠ [] ∧
        EntriesKeyNoDup finalEntries = true ∧
        EntriesExtend entries finalEntries ∧
        out = .table (entriesToTomlList finalEntries).toArray ∧
        (∀ fullEntries, EntriesExtend finalEntries fullEntries →
          renderInlineAssigns (entriesToTomlList fullEntries) (entriesToSkel entries) assigns =
            some (entriesToSkel finalEntries, kv0 :: kvsTail)) ∧
        cs = (String.intercalate "," (kv0 :: kvsTail)).toList ++ '}' :: after) := by
  induction fuel with
  | zero =>
    exact ⟨(fun _ _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h), (fun _ _ _ _ _ _ h => nomatch h)⟩
  | succ fuel ih =>
    rcases ih with ⟨ihVal, ihArr, ihInl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro cs v after hcl h
      unfold parseValueFuel at h
      split at h
      · rename_i rest
        simp only [bind, Except.bind] at h
        cases hm : parseMultilineBasicString rest with
        | error _ => rw [hm] at h; nomatch h
        | ok p =>
          rcases p with ⟨s, af⟩; rw [hm] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
          have hcl_r := (cleanNorm_cons.mp (cleanNorm_cons.mp (cleanNorm_cons.mp hcl).2).2).2
          obtain ⟨st, rs, hrs, hcs⟩ := parseMultilineBasicString_witness hcl_r hm
          exact ⟨.string st, rs, by simpa [renderValueInline] using hrs, hcs⟩
      · rename_i rest _
        simp only [bind, Except.bind] at h
        cases hb : parseBasicStringBody rest with
        | error _ => rw [hb] at h; nomatch h
        | ok p =>
          rcases p with ⟨s, af⟩; rw [hb] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨atoms, enc, henc, hrest⟩ := parseBasicStringBody_witness (cleanNorm_cons.mp hcl).2 hb
          refine ⟨.string (.basic (some atoms)), "\"" ++ String.ofList enc ++ "\"", ?_, ?_⟩
          · simp [renderValueInline, renderStringLiteral, henc]
          · simp [hrest, String.toList_append, String.toList_ofList, List.append_assoc]
      · rename_i rest
        simp only [bind, Except.bind] at h
        cases hm : parseMultilineLiteralString rest with
        | error _ => rw [hm] at h; nomatch h
        | ok p =>
          rcases p with ⟨s, af⟩; rw [hm] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
          have hcl_r := (cleanNorm_cons.mp (cleanNorm_cons.mp (cleanNorm_cons.mp hcl).2).2).2
          obtain ⟨st, rs, hrs, hcs⟩ := parseMultilineLiteralString_witness hcl_r hm
          exact ⟨.string st, rs, by simpa [renderValueInline] using hrs, hcs⟩
      · rename_i rest _
        simp only [bind, Except.bind] at h
        cases hl : parseLiteralStringBody [] rest with
        | error _ => rw [hl] at h; nomatch h
        | ok p =>
          rcases p with ⟨s, af⟩; rw [hl] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨hclean, hnq, hrest⟩ := parseLiteralStringBody_witness (cleanNorm_cons.mp hcl).2 hl
          refine ⟨.string .literal, "'" ++ s ++ "'", ?_, ?_⟩
          · simp [renderValueInline, renderStringLiteral, hclean, hnq]
          · simp [hrest, String.toList_append, List.append_assoc]
      · rename_i rest
        rcases ihArr rest [] v after (cleanNorm_cons.mp hcl).2 h with
          ⟨tr, htr, rfl, hrest⟩ | ⟨vals, tps, strs, trOpt, trS, hne_v, rfl, hstrs, htrS, hrest⟩
        · refine ⟨.array [] (some tr), "[" ++ tr ++ "]", ?_, ?_⟩
          · unfold renderValueInline; simp [htr]
          · simp [hrest, String.toList_append, List.append_assoc]
        · cases vals with
          | nil => exact absurd rfl hne_v
          | cons v0 vr =>
            cases tps with
            | nil => simp [renderArrayElems] at hstrs
            | cons t0 tr =>
              refine ⟨.array (t0 :: tr) trOpt, "[" ++ String.intercalate "," strs ++ trS ++ "]", ?_, ?_⟩
              · exact renderValueInline_array_cons_mk (by simp) hstrs htrS
              · simp [hrest, String.toList_append, List.append_assoc]
      · rename_i rest
        have hcl_rest := (cleanNorm_cons.mp hcl).2
        obtain ⟨hrest_eq, hws_ok⟩ := skipHorizWs_witness rest
        have hcl_other := (cleanNorm_of_suffix hcl_rest hrest_eq).2
        cases hsw : skipHorizWs rest with
        | cons c0 r0 =>
          rw [hsw] at h hrest_eq hcl_other
          by_cases hrb : c0 = '}'
          · subst hrb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
            let wsOpen := String.ofList (takeHorizPrefix rest)
            refine ⟨.inlineTable [] wsOpen, "{" ++ wsOpen ++ "}", ?_, ?_⟩
            · unfold renderValueInline; simp [noDupKeysBool, wsOpen, hws_ok]
            · conv => lhs; rw [hrest_eq]
              dsimp only [wsOpen]
              simp [String.toList_append, String.toList_ofList, List.append_assoc]
          · split at h
            · rename_i ac heq; exact False.elim (hrb (List.cons.inj heq).1)
            · obtain ⟨finE, assigns, kv0, kvsTail, hne_a, hfin_nd, _, rfl, hrend_a, hother_eq⟩ :=
                ihInl (c0 :: r0) [] v after hcl_other entriesKeyNoDup_nil h
              let wsOpen := String.ofList (takeHorizPrefix rest)
              let assigns' := prependWsAssigns wsOpen assigns
              have hne_a' : assigns' ≠ [] := by cases assigns with | nil => exact absurd rfl hne_a | cons h0 _ => rcases h0 with ⟨_, _, _, _, _, _⟩; simp [assigns', prependWsAssigns]
              cases h_a' : assigns' with
              | nil => exact absurd h_a' hne_a'
              | cons a0' as' =>
                have hrend_self := renderInlineAssigns_prependWs hws_ok (hrend_a finE (entriesExtend_refl finE))
                dsimp only [assigns'] at h_a'
                rw [h_a', entriesToSkel_nil] at hrend_self
                have hnd_b : noDupKeysBool (entriesToTomlList finE) = true := by
                  rw [EntriesKeyNoDup] at hfin_nd
                  exact entriesNoDup_to_noDupKeysBool finE (Bool.and_eq_true_iff.mp hfin_nd).1
                have hcov : skelMatchesEntries (entriesToSkel finE) (entriesToTomlList finE) = true :=
                  skelMatchesEntries_entriesToSkel finE hfin_nd
                refine ⟨.inlineTable (a0' :: as') "",
                  "{" ++ String.intercalate "," ((wsOpen ++ kv0) :: kvsTail) ++ "}", ?_, ?_⟩
                · unfold renderValueInline; simp [wsOpen, hnd_b, hrend_self, hcov]
                · simp only [String.toList_append]; rw [intercalate_comma_cons]
                  rw [intercalate_comma_cons] at hother_eq
                  conv => lhs; rw [hrest_eq]
                  rw [hother_eq]; dsimp only [wsOpen]
                  simp [String.toList_append, String.toList_ofList, List.append_assoc]
        | nil =>
          rw [hsw] at h; unfold parseInlineTableFuel at h
          cases fuel <;> simp [skipHorizWs, parseDottedKey, parseDottedKeyFuel, parseKeySegment, takeBareKeyChars, bind, Except.bind] at h
      · have hsplit := takeUnquotedTokenChars_split cs
        rcases htk : takeUnquotedTokenChars cs with ⟨tok, af⟩
        rw [htk] at h hsplit; dsimp only [bind, Except.bind] at h hsplit
        cases hcls : classifyScalarChars (toCharNumApi numApi) tok with
        | error _ => rw [hcls] at h; nomatch h
        | ok val =>
          rw [hcls] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨vt, hvt⟩ := classifyScalarChars_witness hnum hcls
          exact ⟨vt, String.ofList tok, hvt, by simpa [String.toList_ofList] using hsplit⟩
    · intro cs revAcc out after hcl h
      unfold parseArrayFuel at h
      cases hst : skipTriviaNewlines cs with
      | nil => rw [hst] at h; nomatch h
      | cons c1 r1' =>
        rw [hst] at h
        obtain ⟨pre, hcs_pre, hpre_ok⟩ := skipTriviaNewlinesAux_cons_witness false cs hcl hst
        by_cases hrb : c1 = ']'
        · subst hrb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
          exact Or.inl ⟨String.ofList pre, by simpa [isClosedTrivia, String.toList_ofList] using hpre_ok,
            rfl, by simpa [String.toList_ofList] using hcs_pre⟩
        · split at h
          · rename_i ac heq; exact False.elim (hrb (List.cons.inj heq).1)
          · nomatch ‹c1 :: r1' = []›
          · simp only [bind, Except.bind] at h
            have hcl_cs1 := (cleanNorm_of_suffix hcl hcs_pre).2
            cases hpv : parseValueFuel (toCharNumApi numApi) fuel (c1 :: r1') with
            | error _ => rw [hpv] at h; nomatch h
            | ok vp =>
              rcases vp with ⟨v, r1⟩; rw [hpv] at h; dsimp only at h
              obtain ⟨vt, rv, hrv, hcs1_eq⟩ := ihVal (c1 :: r1') v r1 hcl_cs1 hpv
              have hcl_r1 := (cleanNorm_of_suffix hcl_cs1 hcs1_eq).2
              cases hst2 : skipTriviaNewlines r1 with
              | nil => rw [hst2] at h; nomatch h
              | cons c2 r2' =>
                rw [hst2] at h
                obtain ⟨post, hr1_post, hpost_ok⟩ := skipTriviaNewlinesAux_cons_witness false r1 hcl_r1 hst2
                let preS := String.ofList pre
                let postS := String.ofList post
                let s0 := preS ++ rv ++ postS
                have hpreS_ok : isClosedTrivia preS = true := by simpa [isClosedTrivia, preS, String.toList_ofList] using hpre_ok
                have hpostS_ok : isClosedTrivia postS = true := by simpa [isClosedTrivia, postS, String.toList_ofList] using hpost_ok
                by_cases hcm : c2 = ','
                · subst hcm
                  have hcl_acm := (cleanNorm_cons.mp (cleanNorm_of_suffix hcl_r1 hr1_post).2).2
                  rcases ihArr r2' (v :: revAcc) out after hcl_acm h with
                    ⟨tr, htr_ok, hout, hr2_eq⟩ | ⟨vals', tps', strs', trOpt, trS, hne_v', hout, hstrs', htrS, hr2_eq⟩
                  · refine Or.inr ⟨[v], [(preS, vt, postS)], [s0], some tr, "," ++ tr, by simp,
                      by simpa [List.reverse_cons] using hout,
                      by simp [renderArrayElems, hpreS_ok, hpostS_ok, hrv, s0],
                      by simp [htr_ok], ?_⟩
                    simp [hcs_pre, hcs1_eq, hr1_post, hr2_eq, s0, preS, postS, String.intercalate_singleton,
                      String.toList_append, String.toList_ofList, List.append_assoc]
                  · refine Or.inr ⟨v :: vals', (preS, vt, postS) :: tps', s0 :: strs', trOpt, trS, by simp,
                      by simpa [List.reverse_cons, List.append_assoc] using hout,
                      by simp [renderArrayElems, hpreS_ok, hpostS_ok, hrv, hstrs', s0],
                      htrS, ?_⟩
                    have hstrs'_ne : strs' ≠ [] := by
                      cases vals' with | nil => exact absurd rfl hne_v' | cons _ _ =>
                      cases tps' with | nil => simp [renderArrayElems] at hstrs' | cons h0 _ =>
                      rcases h0 with ⟨_, _, _⟩; unfold renderArrayElems at hstrs'
                      split at hstrs'
                      · nomatch hstrs'
                      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstrs'
                        rcases hstrs' with ⟨_, _, _, _, rfl⟩; simp
                    cases strs' with
                    | nil => exact absurd rfl hstrs'_ne
                    | cons s1 sr =>
                      rw [String.intercalate_cons_cons]
                      simp [hcs_pre, hcs1_eq, hr1_post, hr2_eq, s0, preS, postS,
                        String.toList_append, String.toList_ofList, List.append_assoc]
                · by_cases hrb2 : c2 = ']'
                  · subst hrb2; simp at h; rcases h with ⟨rfl, rfl⟩
                    refine Or.inr ⟨[v], [(preS, vt, postS)], [s0], none, "", by simp, rfl,
                      by simp [renderArrayElems, hpreS_ok, hpostS_ok, hrv, s0],
                      rfl, ?_⟩
                    simp [hcs_pre, hcs1_eq, hr1_post, s0, preS, postS, String.intercalate_singleton,
                      String.toList_append, String.toList_ofList, List.append_assoc]
                  · split at h
                    · rename_i _ heq; exact absurd (List.cons.inj heq).1 hcm
                    · rename_i _ heq; exact absurd (List.cons.inj heq).1 hrb2
                    · cases h
    · intro cs entries out after hcl hnd h
      unfold parseInlineTableFuel at h; dsimp only [bind, Except.bind] at h
      obtain ⟨hcs_eq, hwsPre_ok⟩ := skipHorizWs_witness cs
      have hcl_cs1 := (cleanNorm_of_suffix hcl hcs_eq).2
      cases hdk : parseDottedKey (skipHorizWs cs) with
      | error _ => rw [hdk] at h; nomatch h
      | ok kp =>
        rcases kp with ⟨relPath, r1⟩; rw [hdk] at h; dsimp only at h
        obtain ⟨dk, rdk, wsTrail, hdk_p, hrdk, hwsTr, hcs1_eq⟩ := parseDottedKey_witness hcl_cs1 hdk
        have hcl_r1 := (cleanNorm_of_suffix hcl_cs1 hcs1_eq).2
        obtain ⟨hr1_eq, hws1_ok⟩ := skipHorizWs_witness r1
        cases hr2 : skipHorizWs r1 with
        | nil => rw [hr2] at h; nomatch h
        | cons cEq r3 =>
          rw [hr2] at h hr1_eq
          by_cases heq_c : cEq = '='
          · subst heq_c
            split at h; rotate_left; · nomatch h
            rename_i r3' heq_eq; obtain ⟨_, rfl⟩ := List.cons.inj heq_eq
            have hcl_r3 := (cleanNorm_cons.mp (cleanNorm_of_suffix hcl_r1 hr1_eq).2).2
            obtain ⟨hr3_eq, hwsEqR_ok⟩ := skipHorizWs_witness r3
            have hcl_r4 := (cleanNorm_of_suffix hcl_r3 hr3_eq).2
            cases hpv : parseValueFuel (toCharNumApi numApi) fuel (skipHorizWs r3) with
            | error _ => rw [hpv] at h; nomatch h
            | ok vp =>
              rcases vp with ⟨v, r5⟩; rw [hpv] at h; dsimp only at h
              obtain ⟨vt, rv, hrv, hr4_eq⟩ := ihVal _ v r5 hcl_r4 hpv
              have hcl_r5 := (cleanNorm_of_suffix hcl_r4 hr4_eq).2
              cases hins : insertDottedEntries relPath entries relPath (valueToInlineNode v) with
              | error _ => rw [hins] at h; nomatch h
              | ok nextEntries =>
                rw [hins] at h; dsimp only at h
                obtain ⟨hnext_nd, hnext_ext, hnext_lu⟩ := insertDottedEntries_witness relPath v relPath entries nextEntries hnd hins
                obtain ⟨hr5_eq, hwsPost_ok⟩ := skipHorizWs_witness r5
                cases hr6 : skipHorizWs r5 with
                | nil => rw [hr6] at h; nomatch h
                | cons cSep r6' =>
                  rw [hr6] at h hr5_eq
                  let wsPre := String.ofList (takeHorizPrefix cs)
                  let wsEqL := wsTrail ++ String.ofList (takeHorizPrefix r1)
                  let wsEqR := String.ofList (takeHorizPrefix r3)
                  let wsPost := String.ofList (takeHorizPrefix r5)
                  have hwsEqL_ok := isHorizWsStr_append hwsTr hws1_ok
                  let kv0 := wsPre ++ rdk ++ wsEqL ++ "=" ++ wsEqR ++ rv ++ wsPost
                  by_cases hcm : cSep = ','
                  · subst hcm
                    split at h
                    · rename_i r6'' heq_cm; obtain ⟨_, rfl⟩ := List.cons.inj heq_cm
                      have hcl_acm := (cleanNorm_cons.mp (cleanNorm_of_suffix hcl_r5 hr5_eq).2).2
                      obtain ⟨hacm_eq, hwsAcm_ok⟩ := skipHorizWs_witness r6'
                      have hcl_nextCs := (cleanNorm_of_suffix hcl_acm hacm_eq).2
                      cases hsw_acm : skipHorizWs r6' with
                      | cons cN rN =>
                        rw [hsw_acm] at h hacm_eq hcl_nextCs
                        by_cases hrb_tr : cN = '}'
                        · subst hrb_tr; nomatch h
                        · split at h
                          · rename_i heq; exact False.elim (hrb_tr (List.cons.inj heq).1)
                          · obtain ⟨finE, assignsT, kv1, kvsT, hneT, hfin_nd, hfin_ext, hout, hrendT, hnextCs_eq⟩ :=
                              ihInl (cN :: rN) nextEntries out after hcl_nextCs hnext_nd h
                            let wsAcm := String.ofList (takeHorizPrefix r6')
                            let assignsT' := prependWsAssigns wsAcm assignsT
                            refine ⟨finE, (wsPre, dk, wsEqL, wsEqR, vt, wsPost) :: assignsT', kv0, (wsAcm ++ kv1) :: kvsT,
                              by simp, hfin_nd, entriesExtend_trans hnext_ext hfin_ext, hout,
                              fun fullEntries hfull => ?_, ?_⟩
                            · have hins_ok := hdk_p.symm ▸ hnext_lu fullEntries (entriesExtend_trans hfin_ext hfull)
                              have htail_ok := renderInlineAssigns_prependWs hwsAcm_ok (hrendT fullEntries hfull)
                              simp [renderInlineAssigns, wsPre, wsEqL, wsEqR, wsPost, wsAcm, assignsT',
                                hwsPre_ok, hwsEqL_ok, hwsEqR_ok, hwsPost_ok, hrdk, hins_ok, hrv, htail_ok, kv0]
                            · rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, intercalate_comma_cons]
                              rw [intercalate_comma_cons] at hnextCs_eq
                              conv => lhs; rw [hcs_eq, hcs1_eq, hr1_eq, hr3_eq, hr4_eq, hr5_eq, hacm_eq, hnextCs_eq]
                              dsimp only [kv0, wsPre, wsEqL, wsEqR, wsPost, wsAcm]
                              simp [String.toList_append, String.toList_ofList, List.append_assoc]
                      | nil =>
                        rw [hsw_acm] at h
                        cases fuel <;> simp [parseInlineTableFuel, skipHorizWs, parseDottedKey, parseDottedKeyFuel, parseKeySegment, takeBareKeyChars, bind, Except.bind] at h
                    · rename_i _ heq_cm; nomatch (List.cons.inj heq_cm).1
                    · nomatch h
                  · by_cases hrb : cSep = '}'
                    · subst hrb; simp at h; rcases h with ⟨rfl, rfl⟩
                      refine ⟨nextEntries, [(wsPre, dk, wsEqL, wsEqR, vt, wsPost)], kv0, [], by simp,
                        hnext_nd, hnext_ext, rfl, fun fullEntries hfull => ?_, ?_⟩
                      · have hins_ok := hdk_p.symm ▸ hnext_lu fullEntries hfull
                        simp [renderInlineAssigns, wsPre, wsEqL, wsEqR, wsPost,
                          hwsPre_ok, hwsEqL_ok, hwsEqR_ok, hwsPost_ok, hrdk, hins_ok, hrv, kv0]
                      · conv => lhs; rw [hcs_eq, hcs1_eq, hr1_eq, hr3_eq, hr4_eq, hr5_eq]
                        dsimp only [kv0, wsPre, wsEqL, wsEqR, wsPost]
                        simp [String.intercalate_singleton, String.toList_append, String.toList_ofList, List.append_assoc]
                    · split at h
                      · rename_i _ heq; exact absurd (List.cons.inj heq).1 hcm
                      · rename_i _ heq; exact absurd (List.cons.inj heq).1 hrb
                      · cases h
          · split at h
            · rename_i _ heq; exact absurd (List.cons.inj heq).1 heq_c
            · cases h

/-- `parseValue` produces a `ValueTape` rendering inline to the exact consumed slice. -/
theorem parseValue_witness {numApi : NumParseApi} (hnum : ValidNumApi numApi)
    {cs after : List Char} {v : TomlValue}
    (hcl : CleanNorm cs) (h : parseValue (toCharNumApi numApi) cs = .ok (v, after)) :
    ∃ vt rv, renderValueInline v vt = some rv ∧ cs = rv.toList ++ after :=
  (parseValArrInline_witness hnum (cs.length + 2)).1 cs v after hcl h

end LeanSwe.Toml.Proofs
