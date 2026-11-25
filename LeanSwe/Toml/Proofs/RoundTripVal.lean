import LeanSwe.Toml.Proofs.RoundTripSkel

/-!
# Inline Value Render-to-Parse Soundness (`RoundTripVal`)

Proves `renderValueInline_imp_parseValueFuel` over arbitrary nested `ValueTape`s (strings,
unquoted scalars, inline arrays, and inline tables with dotted keys).
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse

/-- Every value rendered inline via `renderValueInline` parses cleanly under `parseValueFuel` with matching `isTableVal`. -/
theorem renderValueInline_imp_parseValueFuel {numApi : NumParseApi} (hnum : ValidNumApi numApi) :
    ∀ (n : Nat) {v : TomlValue} {vt : ValueTape} {rs : String},
      sizeOf vt ≤ n →
      renderValueInline v vt = some rs →
      CleanNorm rs.toList ∧ rs.toList ≠ [] ∧
      ∀ rem, ModelDelimTail rem → ∀ fuel, rs.toList.length + 1 ≤ fuel →
        ∃ v', parseValueFuel (toCharNumApi numApi) fuel (rs.toList ++ rem) = .ok (v', rem) ∧
          isTableVal v' = isTableVal v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v vt rs hsz hr
    cases vt with
    | string st =>
      cases v <;> simp only [renderValueInline] at hr <;> try (simp at hr; done)
      rename_i s
      have nq (rem : List Char) (hd : ModelDelimTail rem) : ∀ c r, rem = c :: r → c ≠ '"' ∧ c ≠ '\'' := by
        intro c r hcr; have hm := (hd c r hcr).1
        exact ⟨fun h0 => by subst h0; revert hm; decide, fun h0 => by subst h0; revert hm; decide⟩
      obtain ⟨hcl, hne, _⟩ := renderStringLiteral_parseValueFuel (toCharNumApi numApi) hr (nq [] (fun _ _ e => nomatch e)) (fuel := 1) (Nat.le_refl 1)
      refine ⟨hcl, hne, fun rem hrem fuel hf => ?_⟩
      obtain ⟨_, _, hp⟩ := renderStringLiteral_parseValueFuel (toCharNumApi numApi) hr (nq rem hrem) (fuel := fuel) (by omega)
      exact ⟨.string s, hp, rfl⟩
    | array elemTapes trail =>
      cases v <;> try (simp [renderValueInline] at hr; done)
      rename_i xs
      cases hxl : xs.toList with
      | nil =>
        unfold renderValueInline at hr; rw [hxl] at hr
        cases elemTapes with
        | cons _ _ => simp at hr
        | nil =>
          dsimp only at hr; split at hr <;> try (simp at hr; done)
          rename_i hcl_tr; injection hr with hrs; subst hrs
          refine ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, cleanNorm_closedTrivia hcl_tr⟩, by decide⟩,
            by simp [String.toList_append], fun rem _ fuel hf => ?_⟩
          cases fuel with | zero => omega | succ f =>
          cases f with
          | zero => simp [String.toList_append] at hf
          | succ f' =>
            simp only [String.toList_append, show ("[" : String).toList = ['['] from rfl,
              show ("]" : String).toList = [']'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
            simp only [parseValueFuel, parseArrayFuel, skipTriviaNewlines_eq_dropTrivia,
              dropTrivia_closed_append false (trail.getD "").toList (']' :: rem) hcl_tr
                (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
            exact ⟨.array #[], rfl, rfl⟩
      | cons x0 xr =>
        cases elemTapes with
        | nil => unfold renderValueInline at hr; rw [hxl] at hr; simp at hr
        | cons t0 tr =>
          obtain ⟨strs, trS, hstrs, htrS, rfl⟩ := renderValueInline_array_cons hxl hr
          have htr_info : CleanNorm trS.toList ∧
              (∀ rem, trS.toList ++ (']' :: rem) = ']' :: rem ∨
                ∃ trv, isClosedTrivia trv = true ∧ trS.toList ++ (']' :: rem) = ',' :: (trv.toList ++ ']' :: rem)) := by
            cases trail with
            | none => simp at htrS; subst htrS; exact ⟨rfl, fun _ => Or.inl rfl⟩
            | some trv =>
              dsimp only at htrS; split at htrS <;> try (simp at htrS; done)
              rename_i hc; injection htrS with e; subst e
              exact ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨by decide, cleanNorm_closedTrivia hc⟩,
                fun _ => Or.inr ⟨trv, hc, by simp [String.toList_append]⟩⟩
          have harr_loop : ∀ (l : List TomlValue) (tps : List (String × ValueTape × String)) (ss : List String),
              l ≠ [] → sizeOf tps ≤ sizeOf (t0 :: tr) →
              renderArrayElems l tps = some ss →
              (∀ s ∈ ss, CleanNorm s.toList) ∧
              ∀ rem revAcc fuel_a,
                ((String.intercalate "," ss ++ trS).toList).length + 2 ≤ fuel_a →
                ∃ arrOut, parseArrayFuel (toCharNumApi numApi) fuel_a
                    ((String.intercalate "," ss ++ trS).toList ++ ']' :: rem) revAcc = .ok (arrOut, rem) ∧
                  isTableVal arrOut = false := by
            intro l; induction l with
            | nil => intro _ _ hne; exact absurd rfl hne
            | cons a as ihl =>
              intro tps ss _ hsz_t ha
              cases tps with | nil => simp [renderArrayElems] at ha | cons tp_hd tp_tl =>
              rcases tp_hd with ⟨pr, vt_e, po⟩
              unfold renderArrayElems at ha; split at ha <;> try (simp at ha; done)
              rename_i hcl_e; simp at hcl_e
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha
              rcases ha with ⟨sv, hsv, rss, hrss, rfl⟩
              have hlt_e : sizeOf vt_e < n := Nat.lt_of_lt_of_le (by simp +arith at hsz_t ⊢; omega) hsz
              obtain ⟨hcl_sv, hne_sv, hp_sv⟩ := ih (sizeOf vt_e) hlt_e (Nat.le_refl _) hsv
              obtain ⟨_, ch_sv, _, hsl_sv, hnd_sv, _⟩ := renderValueInline_head hsv
              have hnt_sv := not_triv_of_valHead hnd_sv
              have hcl_s0 : CleanNorm (pr ++ sv ++ po).toList := by
                simp only [String.toList_append]
                exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_closedTrivia hcl_e.1, hcl_sv⟩, cleanNorm_closedTrivia hcl_e.2⟩
              cases as with
              | nil =>
                cases tp_tl <;> simp [renderArrayElems] at hrss; subst hrss
                refine ⟨fun s hs => by rcases List.mem_singleton.mp hs with rfl; exact hcl_s0,
                  fun rem revAcc fuel_a hfa => ?_⟩
                cases fuel_a with | zero => omega | succ fa =>
                simp only [String.intercalate_singleton, String.toList_append, List.append_assoc] at hfa ⊢
                have hsv_pos : 1 ≤ sv.toList.length := by cases h : sv.toList with | nil => exact absurd h hne_sv | cons _ _ => simp +arith
                unfold parseArrayFuel
                rw [skipTriviaNewlines_eq_dropTrivia,
                    dropTrivia_closed_append false pr.toList _ hcl_e.1 (fun c r e => by
                      rw [hsl_sv, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e
                      exact ⟨hnt_sv.1, hnt_sv.2.1, hnt_sv.2.2.1⟩)]
                have hno_rb : ∀ r', sv.toList ++ (po.toList ++ (trS.toList ++ ']' :: rem)) ≠ ']' :: r' := by
                  intro r' hr'; rw [hsl_sv, List.cons_append] at hr'
                  exact hnt_sv.2.2.2.1 (List.cons.inj hr').1
                have hno_nil : sv.toList ++ (po.toList ++ (trS.toList ++ ']' :: rem)) ≠ [] := by simp [hsl_sv]
                rcases htr_info.2 rem with htr_n | ⟨trv, hcl_trv, htr_c⟩
                · rw [htr_n] at hno_rb hno_nil ⊢
                  have hdt_po : ModelDelimTail (po.toList ++ ']' :: rem) := closedTrivia_delimTail hcl_e.2 (Or.inr rfl)
                  obtain ⟨v', hp_v', _⟩ := hp_sv _ hdt_po fa (by simp [List.length_append] at hfa; omega)
                  refine ⟨.array (v' :: revAcc).reverse.toArray, ?_, rfl⟩
                  split
                  · rename_i ac heq; exact False.elim (hno_rb ac heq)
                  · exact False.elim (hno_nil ‹_›)
                  · simp only [bind, Except.bind, hp_v', skipTriviaNewlines_eq_dropTrivia,
                      dropTrivia_closed_append false po.toList (']' :: rem) hcl_e.2
                        (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
                · have htrS_pos : 1 ≤ trS.toList.length := by
                    have := congrArg List.length htr_c; simp [List.length_append] at this; omega
                  have hfa_gt0 : 0 < fa := by simp [List.length_append] at hfa; omega
                  rw [htr_c] at hno_rb hno_nil ⊢
                  have hdt_po : ModelDelimTail (po.toList ++ ',' :: (trv.toList ++ ']' :: rem)) := closedTrivia_delimTail hcl_e.2 (Or.inl rfl)
                  obtain ⟨v', hp_v', _⟩ := hp_sv _ hdt_po fa (by simp [List.length_append] at hfa; omega)
                  refine ⟨.array (v' :: revAcc).reverse.toArray, ?_, rfl⟩
                  split
                  · rename_i ac heq; exact False.elim (hno_rb ac heq)
                  · exact False.elim (hno_nil ‹_›)
                  · simp only [bind, Except.bind, hp_v', skipTriviaNewlines_eq_dropTrivia,
                      dropTrivia_closed_append false po.toList (',' :: (trv.toList ++ ']' :: rem)) hcl_e.2
                        (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
                    cases fa with
                    | zero => omega
                    | succ fa' =>
                      simp only [parseArrayFuel, skipTriviaNewlines_eq_dropTrivia,
                        dropTrivia_closed_append false trv.toList (']' :: rem) hcl_trv
                          (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
              | cons b bs =>
                cases tp_tl with | nil => simp [renderArrayElems] at hrss | cons hd_nx tl_nx =>
                have hrss_ne : rss ≠ [] := by
                  rcases hd_nx with ⟨_, _, _⟩; have h := hrss; unfold renderArrayElems at h
                  split at h
                  · nomatch h
                  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
                    rcases h with ⟨_, _, _, _, rfl⟩; simp
                cases rss with | nil => exact absurd rfl hrss_ne | cons s_nx sr_nx =>
                obtain ⟨hcl_rss, ih_run⟩ := ihl (hd_nx :: tl_nx) (s_nx :: sr_nx)
                  (by simp) (by simp +arith at hsz_t ⊢; omega) hrss
                refine ⟨fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ hcl_s0) (hcl_rss s),
                  fun rem revAcc fuel_a hfa => ?_⟩
                cases fuel_a with | zero => omega | succ fa =>
                rw [String.intercalate_cons_cons] at hfa ⊢
                let restStream := (String.intercalate "," (s_nx :: sr_nx)).toList ++ (trS.toList ++ ']' :: rem)
                simp only [String.toList_append, show ("," : String).toList = [','] from rfl, List.cons_append, List.nil_append, List.append_assoc] at hfa ⊢
                change ∃ arrOut, parseArrayFuel (toCharNumApi numApi) (fa + 1)
                    (pr.toList ++ (sv.toList ++ (po.toList ++ ',' :: restStream))) revAcc = .ok (arrOut, rem) ∧
                  isTableVal arrOut = false
                have hsv_pos : 1 ≤ sv.toList.length := by cases h : sv.toList with | nil => exact absurd h hne_sv | cons _ _ => simp +arith
                unfold parseArrayFuel
                rw [skipTriviaNewlines_eq_dropTrivia,
                    dropTrivia_closed_append false pr.toList _ hcl_e.1 (fun c r e => by
                      rw [hsl_sv, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e
                      exact ⟨hnt_sv.1, hnt_sv.2.1, hnt_sv.2.2.1⟩)]
                have hno_rb : ∀ r', sv.toList ++ (po.toList ++ ',' :: restStream) ≠ ']' :: r' := by
                  intro r' hr'; rw [hsl_sv, List.cons_append] at hr'; exact hnt_sv.2.2.2.1 (List.cons.inj hr').1
                have hno_nil : sv.toList ++ (po.toList ++ ',' :: restStream) ≠ [] := by simp [hsl_sv]
                have hdt_po : ModelDelimTail (po.toList ++ ',' :: restStream) := closedTrivia_delimTail hcl_e.2 (Or.inl rfl)
                obtain ⟨v', hp_v', _⟩ := hp_sv _ hdt_po fa (by simp only [List.length_append, List.length_cons] at hfa; omega)
                have hfa_rest : ((String.intercalate "," (s_nx :: sr_nx) ++ trS).toList).length + 2 ≤ fa := by
                  simp only [String.toList_append, List.length_append, List.length_cons] at hfa ⊢; omega
                obtain ⟨outArr, hrec_ok, hnt_out⟩ := ih_run rem (v' :: revAcc) fa hfa_rest
                refine ⟨outArr, ?_, hnt_out⟩
                split
                · rename_i ac heq; exact False.elim (hno_rb ac heq)
                · exact False.elim (hno_nil ‹_›)
                · simp only [bind, Except.bind, hp_v', skipTriviaNewlines_eq_dropTrivia,
                    dropTrivia_closed_append false po.toList (',' :: restStream) hcl_e.2
                      (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
                  dsimp only [restStream]
                  rw [← List.append_assoc, ← String.toList_append]
                  exact hrec_ok
          obtain ⟨hcl_strs, hrun⟩ := harr_loop (x0 :: xr) (t0 :: tr) strs (by simp) (Nat.le_refl _) hstrs
          refine ⟨by
              simp only [String.toList_append]
              exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, cleanNorm_intercalate (by decide) hcl_strs⟩, htr_info.1⟩, by decide⟩,
            by simp [String.toList_append], fun rem _ fuel hf => ?_⟩
          cases fuel with | zero => omega | succ f =>
          simp only [String.toList_append, show ("[" : String).toList = ['['] from rfl,
            show ("]" : String).toList = [']'] from rfl, List.cons_append, List.nil_append, List.append_assoc] at hf ⊢
          simp only [parseValueFuel]
          have hf_a : ((String.intercalate "," strs ++ trS).toList).length + 2 ≤ f := by
            simp only [String.toList_append, List.length_append, List.length_cons] at hf ⊢; omega
          rw [← List.append_assoc, ← String.toList_append]
          exact hrun rem [] f hf_a
    | inlineTable assigns emptyWs =>
      cases v <;> try (simp [renderValueInline] at hr; done)
      rename_i sub; unfold renderValueInline at hr; dsimp only at hr
      if hnd : (!noDupKeysBool sub.toList) = true then simp [hnd] at hr else
      simp only [hnd, Bool.false_eq_true, ↓reduceIte] at hr
      cases assigns with
      | nil =>
        dsimp only at hr; split at hr <;> try (simp at hr; done)
        rename_i hok; injection hr with hrs; subst hrs; simp only [Bool.and_eq_true] at hok
        refine ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, cleanNorm_horizWsStr hok.2⟩, by decide⟩,
          by simp [String.toList_append], fun rem _ fuel hf => ?_⟩
        cases fuel with | zero => omega | succ f =>
        simp only [String.toList_append, show ("{" : String).toList = ['{'] from rfl,
          show ("}" : String).toList = ['}'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
        simp only [parseValueFuel, skipHorizWs_eq_dropHoriz,
          dropHoriz_append hok.2 (rem := '}' :: rem) (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
        exact ⟨.table #[], rfl, rfl⟩
      | cons a0 as =>
        dsimp only at hr; split at hr <;> try (simp at hr; done)
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
        rcases hr with ⟨⟨lsk, kvs⟩, hkvs, hm⟩
        split at hm <;> try (simp at hm; done)
        injection hm with hrs; subst hrs
        have hdh_pref : ∀ (l1 l2 : List Char) c r, dropHoriz l1 = c :: r → dropHoriz (l1 ++ l2) = c :: (r ++ l2) := by
          intro l1 l2 c r hd; induction l1 with
          | nil => nomatch hd
          | cons x xs ihx =>
            unfold dropHoriz at hd ⊢; split at hd
            · rename_i hx; simp [hx, ihx hd]
            · rename_i hx; obtain ⟨rfl, rfl⟩ := List.cons.inj hd; simp [hx]
        have hinl_loop : ∀ (xs : List (String × DottedKeyTape × String × String × ValueTape × String))
            (sk fsk : List (String × SkeletonNode)) (ss : List String),
            xs ≠ [] → sizeOf xs ≤ sizeOf (a0 :: as) →
            renderInlineAssigns sub.toList sk xs = some (fsk, ss) →
            (∀ s ∈ ss, CleanNorm s.toList) ∧
            (∃ c0 r0, dropHoriz (String.intercalate "," ss).toList = c0 :: r0 ∧ c0 ≠ '}') ∧
            ∀ entries rem fuel_i,
              entriesToSkel entries = sk →
              (String.intercalate "," ss).toList.length + 1 ≤ fuel_i →
              ∃ inlOut, parseInlineTableFuel (toCharNumApi numApi) fuel_i
                  ((String.intercalate "," ss).toList ++ '}' :: rem) entries = .ok (inlOut, rem) ∧
                isTableVal inlOut = true := by
          intro xs; induction xs with
          | nil => intro _ _ _ hne; exact absurd rfl hne
          | cons hd tl ihl =>
            rcases hd with ⟨wP, dk, wL, wR, vt_c, wPo⟩
            intro sk fsk ss _ hsz_x hi
            unfold renderInlineAssigns at hi; split at hi <;> try (simp at hi; done)
            rename_i hws; simp at hws
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
            rcases hi with ⟨rk, hrk, ⟨nsk, vc⟩, hins, rv, hrv, ⟨fsk', rss⟩, hrss, hpair⟩
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
            dsimp only at hrv hrss
            have hlt_c : sizeOf vt_c < n := Nat.lt_of_lt_of_le (by simp +arith at hsz_x ⊢; omega) hsz
            obtain ⟨hcl_rv, hne_rv, hp_rv⟩ := ih (sizeOf vt_c) hlt_c (Nat.le_refl _) hrv
            obtain ⟨_, cv, _, hrv_l, hnd_v, _⟩ := renderValueInline_head hrv
            obtain ⟨_, _, ck, rkr, hrk_l, hck⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
            have hck_nb := dk_head_not_rbrace hrk hrk_l
            obtain ⟨hcl_rk, _, _⟩ := renderDottedKey_parseDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
            have hcl_kv : CleanNorm (wP ++ rk ++ wL ++ "=" ++ wR ++ rv ++ wPo).toList := by
              simp only [String.toList_append]
              exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr
                ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_horizWsStr hws.1.1.1, hcl_rk⟩,
                  cleanNorm_horizWsStr hws.1.1.2⟩, by decide⟩, cleanNorm_horizWsStr hws.1.2⟩, hcl_rv⟩,
                cleanNorm_horizWsStr hws.2⟩
            have hhead_ss : ∃ c0 r0, dropHoriz (String.intercalate "," ((wP ++ rk ++ wL ++ "=" ++ wR ++ rv ++ wPo) :: rss)).toList = c0 :: r0 ∧ c0 ≠ '}' := by
              rw [intercalate_comma_cons]
              simp only [String.toList_append, List.append_assoc]
              rw [dropHoriz_append hws.1.1.1 (fun c r e => by rw [hrk_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact hck.1)]
              rw [hrk_l, List.cons_append]
              exact ⟨ck, _, rfl, hck_nb⟩
            have hrk_pos : 1 ≤ rk.toList.length := by rw [hrk_l]; simp +arith
            cases tl with
            | nil =>
              simp only [renderInlineAssigns, Option.some.injEq, Prod.mk.injEq] at hrss
              rcases hrss with ⟨rfl, rfl⟩
              refine ⟨fun s hs => by rcases List.mem_singleton.mp hs with rfl; exact hcl_kv, hhead_ss,
                fun entries rem fuel_i hsk_e hfi => ?_⟩
              cases fuel_i with | zero => omega | succ fi =>
              simp only [String.intercalate_singleton, String.toList_append,
                show ("=" : String).toList = ['='] from rfl, List.cons_append, List.nil_append, List.append_assoc] at hfi ⊢
              unfold parseInlineTableFuel
              rw [skipHorizWs_eq_dropHoriz, dropHoriz_append hws.1.1.1 (fun c r e => by rw [hrk_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact hck.1)]
              have hp_dk := (renderDottedKey_parseDottedKey (rem := '=' :: (wR.toList ++ (rv.toList ++ (wPo.toList ++ '}' :: rem))))
                hrk hws.1.1.2 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)).2.2
              rw [List.append_assoc] at hp_dk
              simp only [bind, Except.bind, hp_dk, show skipHorizWs ('=' :: _) = '=' :: _ from rfl]
              rw [skipHorizWs_eq_dropHoriz, dropHoriz_append hws.1.2 (fun c r e => by rw [hrv_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact (not_triv_of_valHead hnd_v).1)]
              have hdt_po : ModelDelimTail (wPo.toList ++ '}' :: rem) := horizWs_delimTail hws.2 (Or.inr (Or.inl rfl))
              obtain ⟨vc', hp_vc', htab_vc'⟩ := hp_rv _ hdt_po fi (by simp only [List.length_append, List.length_cons] at hfi; omega)
              obtain ⟨nextEntries, hins_ok, _⟩ := insertDottedAndLookup_imp_insertDottedEntries dk.path htab_vc'
                dk.path sub.toList sk nsk entries hsk_e hins
              simp only [hp_vc', hins_ok, skipHorizWs_eq_dropHoriz,
                dropHoriz_append hws.2 (rem := '}' :: rem) (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
              exact ⟨_, rfl, rfl⟩
            | cons hd_nx tl_nx =>
              have hrss_ne : rss ≠ [] := by
                rcases hd_nx with ⟨_, _, _, _, _, _⟩; have h := hrss; unfold renderInlineAssigns at h
                split at h
                · nomatch h
                · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
                  rcases h with ⟨_, _, ⟨_, _⟩, _, _, _, ⟨_, _⟩, _, hp⟩
                  obtain ⟨_, rfl⟩ := Prod.mk.inj hp; simp
              cases rss with | nil => exact absurd rfl hrss_ne | cons s_nx sr_nx =>
              obtain ⟨hcl_rss, ⟨cn, rn, hdrop_nx, hcn_nb⟩, ih_run⟩ := ihl nsk fsk' (s_nx :: sr_nx)
                (by simp) (by simp +arith at hsz_x ⊢; omega) hrss
              refine ⟨fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ hcl_kv) (hcl_rss s),
                hhead_ss, fun entries rem fuel_i hsk_e hfi => ?_⟩
              cases fuel_i with | zero => omega | succ fi =>
              rw [String.intercalate_cons_cons] at hfi ⊢
              let restInl := (String.intercalate "," (s_nx :: sr_nx)).toList ++ '}' :: rem
              simp only [String.toList_append, show ("=" : String).toList = ['='] from rfl,
                show ("," : String).toList = [','] from rfl, List.cons_append, List.nil_append, List.append_assoc] at hfi ⊢
              change ∃ inlOut, parseInlineTableFuel (toCharNumApi numApi) (fi + 1)
                  (wP.toList ++ (rk.toList ++ (wL.toList ++ '=' :: (wR.toList ++ (rv.toList ++ (wPo.toList ++ ',' :: restInl)))))) entries =
                  .ok (inlOut, rem) ∧ isTableVal inlOut = true
              unfold parseInlineTableFuel
              rw [skipHorizWs_eq_dropHoriz, dropHoriz_append hws.1.1.1 (fun c r e => by rw [hrk_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact hck.1)]
              have hp_dk := (renderDottedKey_parseDottedKey (rem := '=' :: (wR.toList ++ (rv.toList ++ (wPo.toList ++ ',' :: restInl))))
                hrk hws.1.1.2 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)).2.2
              rw [List.append_assoc] at hp_dk
              simp only [bind, Except.bind, hp_dk, show skipHorizWs ('=' :: _) = '=' :: _ from rfl]
              rw [skipHorizWs_eq_dropHoriz, dropHoriz_append hws.1.2 (fun c r e => by rw [hrv_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact (not_triv_of_valHead hnd_v).1)]
              have hdt_po : ModelDelimTail (wPo.toList ++ ',' :: restInl) := horizWs_delimTail hws.2 (Or.inl rfl)
              obtain ⟨vc', hp_vc', htab_vc'⟩ := hp_rv _ hdt_po fi (by simp only [List.length_append, List.length_cons] at hfi; omega)
              obtain ⟨nextEntries, hins_ok, hsk_next⟩ := insertDottedAndLookup_imp_insertDottedEntries dk.path htab_vc'
                dk.path sub.toList sk nsk entries hsk_e hins
              simp only [hp_vc', hins_ok, skipHorizWs_eq_dropHoriz,
                dropHoriz_append hws.2 (rem := ',' :: restInl) (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
              have hnot_rb_nx : ∀ ac, dropHoriz restInl ≠ '}' :: ac := by
                intro ac hac
                have hd_rest := hdh_pref _ ('}' :: rem) cn rn hdrop_nx
                dsimp only [restInl] at hac; rw [hd_rest] at hac
                exact hcn_nb (List.cons.inj hac).1
              obtain ⟨inlOut, hrec_ok, htab_out⟩ := ih_run nextEntries rem fi hsk_next (by simp only [List.length_append, List.length_cons] at hfi; omega)
              refine ⟨inlOut, ?_, htab_out⟩
              split
              · rename_i ac heq; exact False.elim (hnot_rb_nx ac heq)
              · rw [← skipHorizWs_eq_dropHoriz, parseInlineTableFuel_skipHorizWs]; exact hrec_ok
        obtain ⟨hcl_kvs, ⟨c_hd, r_hd, hdrop_hd, hnb_hd⟩, hrun⟩ := hinl_loop (a0 :: as) [] lsk kvs (by simp) (Nat.le_refl _) hkvs
        refine ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, cleanNorm_intercalate (by decide) hcl_kvs⟩, by decide⟩,
          by simp [String.toList_append], fun rem _ fuel hf => ?_⟩
        cases fuel with | zero => omega | succ f =>
        simp only [String.toList_append, show ("{" : String).toList = ['{'] from rfl,
          show ("}" : String).toList = ['}'] from rfl, List.cons_append, List.nil_append, List.append_assoc] at hf ⊢
        simp only [parseValueFuel]
        have hsw_not_rb : ∀ ac, skipHorizWs ((String.intercalate "," kvs).toList ++ '}' :: rem) ≠ '}' :: ac := by
          intro ac hac; rw [skipHorizWs_eq_dropHoriz, hdh_pref _ _ c_hd r_hd hdrop_hd] at hac
          exact hnb_hd (List.cons.inj hac).1
        obtain ⟨vOut, hout, htv⟩ := hrun [] rem f entriesToSkel_nil (by simp only [List.length_cons, List.length_append] at hf; omega)
        refine ⟨vOut, ?_, htv⟩
        split
        · rename_i ac heq; exact False.elim (hsw_not_rb ac heq)
        · rw [parseInlineTableFuel_skipHorizWs]; exact hout
    | int _ | float _ | bool | offsetDateTime _ _ _ | localDateTime _ _ | localDate | localTime _ =>
      have hnt_v : isTableVal v = false := by
        cases v <;> first | rfl | ((try cases ‹Option String›) <;> simp [renderValueInline] at hr)
      obtain ⟨hcl, hne, hp_u⟩ := unquotedScalar_parseValueFuel hnum rfl hr
      refine ⟨hcl, hne, fun rem hrem fuel hf => ?_⟩
      obtain ⟨v', hp', hnt'⟩ := hp_u rem hrem fuel (by omega)
      exact ⟨v', hp', hnt'.trans hnt_v.symm⟩

end LeanSwe.Toml.Proofs
