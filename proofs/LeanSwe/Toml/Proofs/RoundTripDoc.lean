import LeanSwe.Toml.Proofs.RoundTripVal

/-!
# Document Render-to-Parse Round-Trip Soundness (`RoundTripDoc`)

Proves `renderStmts_imp_parseDocumentFuel` and `render_imp_parseWithNum_ok`, then combines
`render_imp_parseWithNum_ok`, `parseWithNum_ok_has_tape`, and `render_injective_model` to
establish `render_parse_roundTrip_model`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse

/-- Every statement list rendered by `renderStmts` parses cleanly via `Impl.parseDocumentFuel`. -/
theorem renderStmts_imp_parseDocumentFuel {numApi : NumParseApi} (hnum : ValidNumApi numApi)
    {docEntries : List (String × TomlValue)} {tnl : Bool} {eof : String}
    (heof : isEofTrivia eof = true) :
    ∀ (stmts : List StmtTape) (activePath : List String)
      (skel fsk : List (String × SkeletonNode)) (bodyStr : String),
      (tnl = false → stmts ≠ [] → eof = "") →
      renderStmts docEntries activePath skel tnl stmts = some (fsk, bodyStr) →
      CleanNorm bodyStr.toList ∧
      stmts.length ≤ bodyStr.toList.length ∧
      ∀ root fuel,
        entriesToSkel root = skel →
        stmts.length + 1 ≤ fuel →
        ∃ finRoot,
          parseDocumentFuel (toCharNumApi numApi) fuel (bodyStr.toList ++ eof.toList) activePath root = .ok finRoot ∧
          entriesToSkel finRoot = fsk
  | [], activePath, skel, fsk, bodyStr, _, hr => by
    simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩
    refine ⟨rfl, Nat.zero_le _, fun root fuel hsk hf => ?_⟩
    cases fuel with | zero => omega | succ f =>
    unfold parseDocumentFuel
    simp only [show ("" : String).toList = [] from rfl, List.nil_append,
      skipTriviaNewlines_eq_dropTrivia, dropTrivia_eof false eof.toList heof]
    exact ⟨root, rfl, hsk⟩
  | stmt :: rest, activePath, skel, fsk, bodyStr, heof_nil, hr => by
    have heof_f : tnl = false → eof = "" := fun ht => heof_nil ht (by simp)
    let le := if rest.isEmpty then (if tnl then "\n" else "") else "\n"
    have hcl_le : CleanNorm le.toList := by dsimp only [le]; cases rest.isEmpty <;> cases tnl <;> decide
    have cse_step {suf : LineSuffixTape} {rsuf tl : String} {nsk : List (String × SkeletonNode)}
        (hsuf : renderLineSuffix suf = some rsuf)
        (htl : renderStmts docEntries (match stmt with | .tableHeader _ _ dk _ _ | .aotHeader _ _ dk _ _ => dk.path | .assign _ _ _ _ _ _ => activePath) nsk tnl rest = some (fsk, tl)) :
        ModelDelimTail ((rsuf ++ le).toList ++ (tl.toList ++ eof.toList)) ∧
        ∃ nextCs, consumeStatementEnd ((rsuf ++ le).toList ++ (tl.toList ++ eof.toList)) = .ok nextCs ∧
          ((rest = [] ∧ tnl = false ∧ nextCs = []) ∨ nextCs = tl.toList ++ eof.toList) := by
      obtain ⟨_, hcse_nl, hcse_eof⟩ := consumeStatementEnd_of_renderLineSuffix hsuf
      cases rest with
      | cons _ _ =>
        have hle_eq : le = "\n" := rfl
        refine ⟨lineSuffix_delimTail hsuf (Or.inl hle_eq), tl.toList ++ eof.toList, ?_, Or.inr rfl⟩
        simpa [hle_eq, String.toList_append, List.append_assoc] using hcse_nl (tl.toList ++ eof.toList)
      | nil =>
        simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at htl
        rcases htl with ⟨_, rfl⟩
        cases tnl with
        | true =>
          have hle_eq : le = "\n" := rfl
          refine ⟨lineSuffix_delimTail hsuf (Or.inl hle_eq), [] ++ eof.toList, ?_, Or.inr rfl⟩
          simpa [hle_eq, String.toList_append, List.append_assoc] using hcse_nl eof.toList
        | false =>
          have hle_eq : le = "" := rfl
          have heof_e := heof_f rfl
          refine ⟨lineSuffix_delimTail hsuf (Or.inr ⟨hle_eq, by simp [heof_e]⟩), [], ?_, Or.inl ⟨rfl, rfl, rfl⟩⟩
          simpa [hle_eq, heof_e] using hcse_eof
    cases stmt with
    | tableHeader pre wsO dk wsC suf =>
      unfold renderStmts at hr; dsimp only at hr
      split at hr <;> try (simp at hr; done)
      rename_i hok; simp at hok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      rcases hr with ⟨rk, hrk, rsuf, hsuf, nsk, hhdr, ⟨fsk', tl⟩, htl, hpair⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      obtain ⟨hcl_rk, _, _⟩ := renderDottedKey_parseDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
      obtain ⟨_, _, ck, rkr, hrk_l, hck⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
      obtain ⟨hcl_suf, _, _⟩ := consumeStatementEnd_of_renderLineSuffix hsuf
      obtain ⟨hcl_tl, hlen_tl, ih_doc⟩ := renderStmts_imp_parseDocumentFuel hnum heof rest dk.path nsk fsk' tl
        (fun ht _ => heof_f ht) htl
      have hcl_body : CleanNorm (pre ++ "[" ++ wsO ++ rk ++ wsC ++ "]" ++ rsuf ++ le ++ tl).toList := by
        simp only [String.toList_append]
        exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr
          ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr
            ⟨cleanNorm_closedTrivia hok.1.1, by decide⟩, cleanNorm_horizWsStr hok.1.2⟩, hcl_rk⟩,
            cleanNorm_horizWsStr hok.2⟩, by decide⟩, hcl_suf⟩, hcl_le⟩, hcl_tl⟩
      have hlen_body : (StmtTape.tableHeader pre wsO dk wsC suf :: rest).length ≤
          (pre ++ "[" ++ wsO ++ rk ++ wsC ++ "]" ++ rsuf ++ le ++ tl).toList.length := by
        simp only [String.toList_append, List.length_append, List.length_cons]
        have : ("[" : String).toList.length = 1 := rfl
        omega
      refine ⟨hcl_body, hlen_body, fun root fuel hsk hf => ?_⟩
      cases fuel with | zero => omega | succ f =>
      simp only [String.toList_append, show ("[" : String).toList = ['['] from rfl,
        show ("]" : String).toList = [']'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
      unfold parseDocumentFuel
      rw [skipTriviaNewlines_eq_dropTrivia,
          dropTrivia_closed_append false pre.toList _ hok.1.1 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
      have hnot_aot : ∀ r', wsO.toList ++ (rk.toList ++ (wsC.toList ++ ']' :: (rsuf.toList ++ (le.toList ++ (tl.toList ++ eof.toList))))) ≠ '[' :: r' := by
        intro r' hr'
        cases hwl : wsO.toList with
        | nil => rw [hwl, List.nil_append, hrk_l, List.cons_append] at hr'; exact hck.2.2.2 (List.cons.inj hr').1
        | cons w0 ws =>
          rw [hwl, List.cons_append] at hr'; obtain ⟨rfl, _⟩ := List.cons.inj hr'
          have hw0 := List.all_eq_true.mp hok.1.2 '[' (by rw [hwl]; simp); revert hw0; decide
      have hp_dk := (renderDottedKey_parseDottedKey (rem := ']' :: (rsuf.toList ++ (le.toList ++ (tl.toList ++ eof.toList))))
        hrk hok.2 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)).2.2
      rw [List.append_assoc] at hp_dk
      obtain ⟨_, nextCs, hcse, hnc_cases⟩ := cse_step hsuf htl
      simp only [String.toList_append, List.append_assoc] at hcse
      dsimp only [le] at hp_dk hcse
      obtain ⟨nextRoot, hhdr_ok, hnr_sk⟩ := applyHeaderSkel_imp_applyHeader .table dk.path dk.path skel nsk root hsk hhdr
      have hfin : ∃ finRoot, parseDocumentFuel (toCharNumApi numApi) f nextCs dk.path nextRoot = .ok finRoot ∧
          entriesToSkel finRoot = fsk' := by
        rcases hnc_cases with ⟨rfl, rfl, rfl⟩ | rfl
        · simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at htl
          rcases htl with ⟨rfl, _⟩
          exact ⟨nextRoot, by cases f <;> rfl, hnr_sk⟩
        · exact ih_doc nextRoot f hnr_sk (by simp at hf; omega)
      obtain ⟨finRoot, hfin_ok, hfin_sk⟩ := hfin
      refine ⟨finRoot, ?_, hfin_sk⟩
      split
      · nomatch ‹'[' :: _ = []›
      · rename_i r' heq; exact False.elim (hnot_aot r' (List.cons.inj heq).2)
      · rename_i r' _ heq
        rw [← (List.cons.inj heq).2, skipHorizWs_eq_dropHoriz,
            dropHoriz_append hok.1.2 (fun c r e => by rw [hrk_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact hck.1)]
        simp only [bind, Except.bind, hp_dk, show skipHorizWs (']' :: _) = ']' :: _ from rfl, hcse, hhdr_ok]
        exact hfin_ok
      · rename_i hne; exact False.elim (hne _ rfl)
    | aotHeader pre wsO dk wsC suf =>
      unfold renderStmts at hr; dsimp only at hr
      split at hr <;> try (simp at hr; done)
      rename_i hok; simp at hok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      rcases hr with ⟨rk, hrk, rsuf, hsuf, nsk, hhdr, ⟨fsk', tl⟩, htl, hpair⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      obtain ⟨hcl_rk, _, _⟩ := renderDottedKey_parseDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
      obtain ⟨_, _, ck, rkr, hrk_l, hck⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
      obtain ⟨hcl_suf, _, _⟩ := consumeStatementEnd_of_renderLineSuffix hsuf
      obtain ⟨hcl_tl, hlen_tl, ih_doc⟩ := renderStmts_imp_parseDocumentFuel hnum heof rest dk.path nsk fsk' tl
        (fun ht _ => heof_f ht) htl
      have hcl_body : CleanNorm (pre ++ "[[" ++ wsO ++ rk ++ wsC ++ "]]" ++ rsuf ++ le ++ tl).toList := by
        simp only [String.toList_append]
        exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr
          ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr
            ⟨cleanNorm_closedTrivia hok.1.1, by decide⟩, cleanNorm_horizWsStr hok.1.2⟩, hcl_rk⟩,
            cleanNorm_horizWsStr hok.2⟩, by decide⟩, hcl_suf⟩, hcl_le⟩, hcl_tl⟩
      have hlen_body : (StmtTape.aotHeader pre wsO dk wsC suf :: rest).length ≤
          (pre ++ "[[" ++ wsO ++ rk ++ wsC ++ "]]" ++ rsuf ++ le ++ tl).toList.length := by
        simp only [String.toList_append, List.length_append, List.length_cons]
        have : ("[[" : String).toList.length = 2 := rfl
        omega
      refine ⟨hcl_body, hlen_body, fun root fuel hsk hf => ?_⟩
      cases fuel with | zero => omega | succ f =>
      simp only [String.toList_append, show ("[[" : String).toList = ['[', '['] from rfl,
        show ("]]" : String).toList = [']', ']'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
      unfold parseDocumentFuel
      rw [skipTriviaNewlines_eq_dropTrivia,
          dropTrivia_closed_append false pre.toList _ hok.1.1 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
      have hp_dk := (renderDottedKey_parseDottedKey (rem := ']' :: ']' :: (rsuf.toList ++ (le.toList ++ (tl.toList ++ eof.toList))))
        hrk hok.2 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)).2.2
      rw [List.append_assoc] at hp_dk
      obtain ⟨_, nextCs, hcse, hnc_cases⟩ := cse_step hsuf htl
      simp only [String.toList_append, List.append_assoc] at hcse
      dsimp only [le] at hp_dk hcse
      obtain ⟨nextRoot, hhdr_ok, hnr_sk⟩ := applyHeaderSkel_imp_applyHeader .aot dk.path dk.path skel nsk root hsk hhdr
      have hfin : ∃ finRoot, parseDocumentFuel (toCharNumApi numApi) f nextCs dk.path nextRoot = .ok finRoot ∧
          entriesToSkel finRoot = fsk' := by
        rcases hnc_cases with ⟨rfl, rfl, rfl⟩ | rfl
        · simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at htl
          rcases htl with ⟨rfl, _⟩
          exact ⟨nextRoot, by cases f <;> rfl, hnr_sk⟩
        · exact ih_doc nextRoot f hnr_sk (by simp at hf; omega)
      obtain ⟨finRoot, hfin_ok, hfin_sk⟩ := hfin
      refine ⟨finRoot, ?_, hfin_sk⟩
      split
      · nomatch ‹'[' :: _ = []›
      · rename_i r' heq
        obtain ⟨_, hb2_eq⟩ := List.cons.inj heq
        rw [← (List.cons.inj hb2_eq).2, skipHorizWs_eq_dropHoriz,
            dropHoriz_append hok.1.2 (fun c r e => by rw [hrk_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact hck.1)]
        simp only [bind, Except.bind, hp_dk, show skipHorizWs (']' :: ']' :: _) = ']' :: ']' :: _ from rfl, hcse, hhdr_ok]
        exact hfin_ok
      · rename_i rest' hne heq
        obtain ⟨_, rfl⟩ := List.cons.inj heq
        exact False.elim (hne _ rfl)
      · rename_i hne; exact False.elim (hne _ rfl)
    | assign pre dk wsL wsR vt suf =>
      unfold renderStmts at hr; dsimp only at hr
      split at hr <;> try (simp at hr; done)
      rename_i hok; simp at hok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      rcases hr with ⟨rk, hrk, rsuf, hsuf, ⟨nsk, v⟩, hins, rv, hrv, ⟨fsk', tl⟩, htl, hpair⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      dsimp only at hrv htl
      obtain ⟨hcl_rk, _, _⟩ := renderDottedKey_parseDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
      obtain ⟨_, _, ck, rkr, hrk_l, hck⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
      obtain ⟨hcl_rv, _, hp_rv⟩ := renderValueInline_imp_parseValueFuel hnum (sizeOf vt) (Nat.le_refl _) hrv
      obtain ⟨_, cv, _, hrv_l, hnd_v, _⟩ := renderValueInline_head hrv
      obtain ⟨hcl_suf, _, _⟩ := consumeStatementEnd_of_renderLineSuffix hsuf
      obtain ⟨hcl_tl, hlen_tl, ih_doc⟩ := renderStmts_imp_parseDocumentFuel hnum heof rest activePath nsk fsk' tl
        (fun ht _ => heof_f ht) htl
      have hcl_body : CleanNorm (pre ++ rk ++ wsL ++ "=" ++ wsR ++ rv ++ rsuf ++ le ++ tl).toList := by
        simp only [String.toList_append]
        exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr
          ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr
            ⟨cleanNorm_closedTrivia hok.1.1, hcl_rk⟩, cleanNorm_horizWsStr hok.1.2⟩, by decide⟩,
            cleanNorm_horizWsStr hok.2⟩, hcl_rv⟩, hcl_suf⟩, hcl_le⟩, hcl_tl⟩
      have hlen_body : (StmtTape.assign pre dk wsL wsR vt suf :: rest).length ≤
          (pre ++ rk ++ wsL ++ "=" ++ wsR ++ rv ++ rsuf ++ le ++ tl).toList.length := by
        simp only [String.toList_append, List.length_append, List.length_cons]
        have : ("=" : String).toList.length = 1 := rfl
        omega
      refine ⟨hcl_body, hlen_body, fun root fuel hsk hf => ?_⟩
      cases fuel with | zero => omega | succ f =>
      simp only [String.toList_append, show ("=" : String).toList = ['='] from rfl,
        List.cons_append, List.nil_append, List.append_assoc]
      unfold parseDocumentFuel
      rw [skipTriviaNewlines_eq_dropTrivia,
          dropTrivia_closed_append false pre.toList _ hok.1.1 (fun c r e => by
            rw [hrk_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e
            exact ⟨hck.1, hck.2.1, hck.2.2.1⟩)]
      let afterKey := wsL.toList ++ '=' :: (wsR.toList ++ (rv.toList ++ (rsuf.toList ++ (le.toList ++ (tl.toList ++ eof.toList)))))
      have hno_nil : rk.toList ++ afterKey ≠ [] := by simp [hrk_l]
      have hno_br : ∀ r', rk.toList ++ afterKey ≠ '[' :: r' := by
        intro r' hr'; rw [hrk_l, List.cons_append] at hr'; exact hck.2.2.2 (List.cons.inj hr').1
      have hp_dk := (renderDottedKey_parseDottedKey
        (rem := '=' :: (wsR.toList ++ (rv.toList ++ (rsuf.toList ++ (le.toList ++ (tl.toList ++ eof.toList))))))
        hrk hok.1.2 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)).2.2
      rw [List.append_assoc] at hp_dk
      obtain ⟨hdt_suf, nextCs, hcse, hnc_cases⟩ := cse_step hsuf htl
      simp only [String.toList_append, List.append_assoc] at hdt_suf hcse
      obtain ⟨val', hp_v', htab_v'⟩ := hp_rv _ hdt_suf
        ((rv.toList ++ (rsuf.toList ++ (le.toList ++ (tl.toList ++ eof.toList)))).length + 2)
        (by simp [List.length_append]; omega)
      dsimp only [le] at hp_dk hcse hp_v'
      obtain ⟨nextRoot, hins_ok, hnr_sk⟩ := insertAtActiveAndLookup_imp_insertAtActivePath
        (activePath ++ dk.path) htab_v' activePath dk.path docEntries skel nsk root hsk hins
      have hfin : ∃ finRoot, parseDocumentFuel (toCharNumApi numApi) f nextCs activePath nextRoot = .ok finRoot ∧
          entriesToSkel finRoot = fsk' := by
        rcases hnc_cases with ⟨rfl, rfl, rfl⟩ | rfl
        · simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at htl
          rcases htl with ⟨rfl, _⟩
          exact ⟨nextRoot, by cases f <;> rfl, hnr_sk⟩
        · exact ih_doc nextRoot f hnr_sk (by simp at hf; omega)
      obtain ⟨finRoot, hfin_ok, hfin_sk⟩ := hfin
      refine ⟨finRoot, ?_, hfin_sk⟩
      split
      · exact False.elim (hno_nil ‹_›)
      · exact False.elim (hno_br _ ‹_›)
      · exact False.elim (hno_br _ ‹_›)
      · simp only [bind, Except.bind, hp_dk, show skipHorizWs ('=' :: _) = '=' :: _ from rfl]
        rw [skipHorizWs_eq_dropHoriz,
            dropHoriz_append hok.2 (fun c r e => by rw [hrv_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact (not_triv_of_valHead hnd_v).1)]
        unfold parseValue
        simp only [hp_v', hcse, hins_ok]
        exact hfin_ok

/-- Every wire string produced by `Model.render` is accepted (`Except.ok`) by `Impl.parseWithNum`. -/
theorem render_imp_parseWithNum_ok (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (doc : TomlTable) (tape : RenderTape) (out : String)
    (hr : Model.render doc tape = some out) :
    ∃ parsed, parseWithNum numApi out = .ok parsed := by
  simp only [Model.render, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
  rcases hr with ⟨lfStr, hlf, rawCs, hexp, rfl⟩
  unfold renderLF at hlf
  if hw : (!wellFormedTableBool doc) = true then simp [hw] at hlf else
  if hg : (!tape.stmts.isEmpty && !tape.trailingNewline && !tape.eofTrivia.isEmpty) = true then simp [hw, hg] at hlf else
  if he : (!isEofTrivia tape.eofTrivia) = true then simp [hw, hg, he] at hlf else
  simp only [hw, hg, he, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlf
  rcases hlf with ⟨⟨fsk, bodyStr⟩, hst, hm⟩
  split at hm <;> try (simp at hm; done)
  injection hm with hlf_eq; subst hlf_eq
  dsimp only at hexp
  have heof_ok : isEofTrivia tape.eofTrivia = true := by cases h : isEofTrivia tape.eofTrivia <;> simp_all
  have hg_imp : tape.trailingNewline = false → tape.stmts ≠ [] → tape.eofTrivia = "" := by
    intro htnl hne
    have hne_b : (!tape.stmts.isEmpty) = true := by cases hts : tape.stmts with | nil => exact absurd hts hne | cons _ _ => rfl
    cases he_b : tape.eofTrivia.isEmpty
    · exfalso; apply hg; simp [hne_b, htnl, he_b]
    · exact String.isEmpty_iff.mp he_b
  obtain ⟨hcl_body, hlen_st, hdoc_run⟩ :=
    renderStmts_imp_parseDocumentFuel hnum heof_ok tape.stmts [] [] fsk bodyStr hg_imp hst
  have hcl_lf : CleanNorm (bodyStr ++ tape.eofTrivia).toList := by
    rw [String.toList_append]
    exact cleanNorm_append.mpr ⟨hcl_body, cleanNorm_eofTrivia heof_ok⟩
  have hnorm_ok := normalizeChars_of_expandNewlines hcl_lf hexp
  obtain ⟨finRoot, hp_doc, _⟩ := hdoc_run [] ((bodyStr ++ tape.eofTrivia).toList.length + 1)
    entriesToSkel_nil (by simp [String.toList_append, List.length_append]; omega)
  refine ⟨(entriesToTomlList finRoot).toArray, ?_⟩
  unfold parseWithNum parseCharsWithNum
  rw [String.toList_ofList]
  simp only [bind, Except.bind, hnorm_ok]
  rw [String.toList_append] at hp_doc ⊢
  rw [hp_doc]

/-- Every output of `Model.render doc tape` parses under `parseWithNum` to a `TomlTableEquiv` table. -/
theorem render_parse_roundTrip_model (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (doc : TomlTable) (tape : RenderTape) (out : String)
    (hr : Model.render doc tape = some out) :
    ∃ parsed, parseWithNum numApi out = .ok parsed ∧ TomlTableEquiv doc parsed := by
  obtain ⟨parsed, hp⟩ := render_imp_parseWithNum_ok numApi hnum doc tape out hr
  obtain ⟨_, tape', htape'⟩ := parseWithNum_ok_has_tape numApi hnum out parsed hp
  exact ⟨parsed, hp, render_injective_model doc parsed tape tape' out hr htape'⟩

end LeanSwe.Toml.Proofs
