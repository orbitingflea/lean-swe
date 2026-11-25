import LeanSwe.Toml.Proofs.RenderInjectiveVal

/-!
# Array Value Injectivity & Inline Value Delimiter Helpers

Proves `renderValueInline_head`, delimiter-tail lemmas, and the `.array` branch of
`renderValueInline_injective` without importing `Toml.Impl`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model

theorem renderValueInline_array_cons {xs : Array TomlValue} {x0 : TomlValue} {xr : List TomlValue}
    {t0 : String × ValueTape × String} {tr : List (String × ValueTape × String)}
    {trail : Option String} {rs : String}
    (hxl : xs.toList = x0 :: xr)
    (hr : renderValueInline (.array xs) (.array (t0 :: tr) trail) = some rs) :
    ∃ strs trStr,
      renderArrayElems (x0 :: xr) (t0 :: tr) = some strs ∧
      (match trail with | none => some "" | some trv => if isClosedTrivia trv then some ("," ++ trv) else none) = some trStr ∧
      rs = "[" ++ String.intercalate "," strs ++ trStr ++ "]" := by
  unfold renderValueInline at hr
  rw [hxl] at hr; dsimp only at hr
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
  rcases hr with ⟨strs, hstrs, hr⟩
  cases trail with
  | none =>
    simp only [Option.bind, Option.some.injEq] at hr
    exact ⟨strs, "", hstrs, rfl, hr.symm⟩
  | some trv =>
    dsimp only at hr; split at hr
    · rename_i hc; simp only [Option.bind, Option.some.injEq] at hr
      exact ⟨strs, "," ++ trv, hstrs, by simp [hc], hr.symm⟩
    · simp at hr

theorem renderValueInline_array_cons_mk {xs : Array TomlValue} {x0 : TomlValue} {xr : List TomlValue}
    {t0 : String × ValueTape × String} {tr : List (String × ValueTape × String)}
    {trail : Option String} {strs : List String} {trStr : String}
    (hxl : xs.toList = x0 :: xr)
    (hstrs : renderArrayElems (x0 :: xr) (t0 :: tr) = some strs)
    (htr : (match trail with | none => some "" | some trv => if isClosedTrivia trv then some ("," ++ trv) else none) = some trStr) :
    renderValueInline (.array xs) (.array (t0 :: tr) trail) =
      some ("[" ++ String.intercalate "," strs ++ trStr ++ "]") := by
  unfold renderValueInline
  rw [hxl]; dsimp only
  simp only [Option.bind_eq_bind, hstrs, Option.bind]
  cases trail with
  | none => simp at htr; subst htr; rfl
  | some trv =>
    dsimp only at htr ⊢; split at htr
    · rename_i hc; injection htr with e; subst e; simp [hc]
    · simp at htr

/-- Tail of comma-intercalated string list as characters. -/
def commaRestList (ss : List String) : List Char :=
  match ss with
  | [] => []
  | _ :: _ => ',' :: (String.intercalate "," ss).toList

theorem intercalate_comma_cons' (s : String) (ss : List String) :
    (String.intercalate "," (s :: ss)).toList = s.toList ++ commaRestList ss := by
  cases ss <;> simp [commaRestList, String.intercalate_singleton, String.intercalate_cons_cons,
    String.toList_append, show ("," : String).toList = [','] from rfl, List.cons_append, List.nil_append, List.append_assoc]

/-- Head-character and `NoCrStr` characterization for `renderValueInline`. -/
theorem renderValueInline_head :
    ∀ {v : TomlValue} {vt : ValueTape} {rs : String},
      renderValueInline v vt = some rs →
      NoCrStr rs ∧
      ∃ c0 r0, rs.toList = c0 :: r0 ∧ isModelDelim c0 = false ∧
        match vt with
        | .string _ => c0 = '"' ∨ c0 = '\''
        | .array _ _ => c0 = '['
        | .inlineTable _ _ => c0 = '{'
        | _ => c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{'
  | v, .string st, rs, hr => by
    cases v <;> try (simp [renderValueInline] at hr; done)
    rename_i s; simp only [renderValueInline] at hr
    obtain ⟨_, hnocr⟩ := readStringVal_renderStringLiteral (rem := []) hr (fun _ _ h => nomatch h)
    refine ⟨hnocr, ?_⟩
    cases st with
    | basic a? =>
      cases a? with
      | none => simp only [renderStringLiteral, Option.some.injEq] at hr; subst hr
                exact ⟨'"', _, by simp [String.toList_append]; rfl, by decide, Or.inl rfl⟩
      | some a => simp only [renderStringLiteral, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
                  rcases hr with ⟨_, _, rfl⟩; exact ⟨'"', _, by simp [String.toList_append]; rfl, by decide, Or.inl rfl⟩
    | multilineBasic c? =>
      cases c? with
      | none => simp only [renderStringLiteral, Option.some.injEq] at hr; subst hr
                exact ⟨'"', _, by simp [String.toList_append]; rfl, by decide, Or.inl rfl⟩
      | some p => simp only [renderStringLiteral, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
                  rcases hr with ⟨_, _, rfl⟩; cases p.1 <;> exact ⟨'"', _, by simp [String.toList_append]; rfl, by decide, Or.inl rfl⟩
    | literal =>
      simp only [renderStringLiteral] at hr; split at hr
      · injection hr with hrs; subst hrs; exact ⟨'\'', _, by simp [String.toList_append]; rfl, by decide, Or.inr rfl⟩
      · simp at hr
    | multilineLiteral l =>
      simp only [renderStringLiteral] at hr; split at hr
      · injection hr with hrs; subst hrs; cases l <;> exact ⟨'\'', _, by simp [String.toList_append]; rfl, by decide, Or.inr rfl⟩
      · simp at hr
  | v, .array elemTapes trail, rs, hr => by
    cases v <;> try (simp [renderValueInline] at hr; done)
    rename_i xs
    have arrElems_nocr : ∀ (l : List TomlValue) (ts : List (String × ValueTape × String)) (strs : List String),
        sizeOf ts ≤ sizeOf elemTapes →
        renderArrayElems l ts = some strs → ∀ s ∈ strs, NoCrStr s := by
      intro l ts; induction ts generalizing l with
      | nil => intro strs _ hs; cases l <;> simp [renderArrayElems] at hs; subst hs; intro _ hm; nomatch hm
      | cons hd tl ih =>
        rcases hd with ⟨pre, tp, post⟩
        intro strs hsz hs; cases l with
        | nil => simp [renderArrayElems] at hs
        | cons x xr =>
          unfold renderArrayElems at hs; split at hs
          · simp at hs
          · rename_i htr_ok; simp at htr_ok
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
            rcases hs with ⟨sv, hsv, rest, hrest, rfl⟩
            intro s hm; rcases List.mem_cons.mp hm with rfl | htl
            · exact noCrStr_append (noCrStr_append (noCr_closedTrivia htr_ok.1) (renderValueInline_head hsv).1) (noCr_closedTrivia htr_ok.2)
            · exact ih xr rest (by simp +arith at hsz ⊢; omega) hrest s htl
    cases hxl : xs.toList with
    | nil =>
      unfold renderValueInline at hr; rw [hxl] at hr
      cases elemTapes with
      | nil =>
        dsimp only at hr; split at hr
        · rename_i hcl; injection hr with hrs; subst hrs
          exact ⟨noCrStr_append (noCrStr_append (by decide) (noCr_closedTrivia hcl)) (by decide),
            '[', _, by simp [String.toList_append]; rfl, by decide, rfl⟩
        · simp at hr
      | cons _ _ => simp at hr
    | cons x0 xr =>
      cases elemTapes with
      | nil => unfold renderValueInline at hr; rw [hxl] at hr; simp at hr
      | cons t0 tr =>
        obtain ⟨strs, trStr, hstrs, htr, rfl⟩ := renderValueInline_array_cons hxl hr
        have htr_cr : NoCrStr trStr := by
          cases trail with
          | none => simp at htr; subst htr; decide
          | some trv =>
            dsimp only at htr; split at htr
            · rename_i hc; injection htr with e; subst e; exact noCrStr_append (by decide) (noCr_closedTrivia hc)
            · simp at htr
        exact ⟨noCrStr_append (noCrStr_append (noCrStr_append (by decide)
          (noCrStr_intercalate (by decide) (arrElems_nocr _ _ _ (Nat.le_refl _) hstrs))) htr_cr) (by decide),
          '[', _, by simp [String.toList_append]; rfl, by decide, rfl⟩
  | v, .inlineTable assigns emptyWs, rs, hr => by
    cases v <;> try (simp [renderValueInline] at hr; done)
    rename_i sub; unfold renderValueInline at hr; dsimp only at hr
    if hnd : (!noDupKeysBool sub.toList) = true then simp [hnd] at hr else
    simp only [hnd, Bool.false_eq_true, ↓reduceIte] at hr
    have inl_nocr : ∀ (sk : List (String × SkeletonNode))
        (as : List (String × DottedKeyTape × String × String × ValueTape × String))
        (fsk : List (String × SkeletonNode)) (kvs : List String),
        sizeOf as ≤ sizeOf assigns →
        renderInlineAssigns sub.toList sk as = some (fsk, kvs) → ∀ s ∈ kvs, NoCrStr s := by
      intro sk as; induction as generalizing sk with
      | nil => intro _ kvs _ hs; simp [renderInlineAssigns] at hs; rcases hs with ⟨_, rfl⟩; intro _ hm; nomatch hm
      | cons a rest ih =>
        rcases a with ⟨wP, dk, wL, wR, vt, wPo⟩
        intro fsk kvs hsz hs; unfold renderInlineAssigns at hs; split at hs
        · simp at hs
        · rename_i hws; simp at hws
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hs
          rcases hs with ⟨rk, hrk, ⟨nsk, vc⟩, _, rv, hrv, ⟨fsk', tl⟩, htl, ⟨rfl, rfl⟩⟩
          obtain ⟨_, hrk_cr, _⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ h => nomatch h)
          intro s hm; rcases List.mem_cons.mp hm with rfl | hmem
          · exact noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append
              (noCr_horizWsStr hws.1.1.1) hrk_cr) (noCr_horizWsStr hws.1.1.2)) (by decide))
              (noCr_horizWsStr hws.1.2)) (renderValueInline_head hrv).1) (noCr_horizWsStr hws.2)
          · exact ih nsk fsk' tl (by simp +arith at hsz ⊢; omega) htl s hmem
    cases assigns with
    | nil =>
      dsimp only at hr; split at hr
      · rename_i hok; injection hr with hrs; subst hrs
        simp only [Bool.and_eq_true] at hok
        exact ⟨noCrStr_append (noCrStr_append (by decide) (noCr_horizWsStr hok.2)) (by decide),
          '{', _, by simp [String.toList_append]; rfl, by decide, rfl⟩
      · simp at hr
    | cons a0 as =>
      dsimp only at hr; split at hr
      · simp at hr
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
        rcases hr with ⟨⟨lsk, kvs⟩, hkvs, hm⟩
        split at hm
        · injection hm with hrs; subst hrs
          exact ⟨noCrStr_append (noCrStr_append (by decide)
            (noCrStr_intercalate (by decide) (inl_nocr [] (a0 :: as) lsk kvs (Nat.le_refl _) hkvs))) (by decide),
            '{', _, by simp [String.toList_append]; rfl, by decide, rfl⟩
        · simp at hm
  | v, .int l, rs, hr => by
    obtain ⟨hcr, ⟨c0, r0, hl, hd, hs⟩, _⟩ := unquotedScalar_info rfl hr; exact ⟨hcr, c0, r0, hl, hd, hs⟩
  | v, .float l, rs, hr => by
    obtain ⟨hcr, ⟨c0, r0, hl, hd, hs⟩, _⟩ := unquotedScalar_info rfl hr; exact ⟨hcr, c0, r0, hl, hd, hs⟩
  | v, .bool, rs, hr => by
    obtain ⟨hcr, ⟨c0, r0, hl, hd, hs⟩, _⟩ := unquotedScalar_info rfl hr; exact ⟨hcr, c0, r0, hl, hd, hs⟩
  | v, .offsetDateTime s o f, rs, hr => by
    obtain ⟨hcr, ⟨c0, r0, hl, hd, hs⟩, _⟩ := unquotedScalar_info rfl hr; exact ⟨hcr, c0, r0, hl, hd, hs⟩
  | v, .localDateTime s f, rs, hr => by
    obtain ⟨hcr, ⟨c0, r0, hl, hd, hs⟩, _⟩ := unquotedScalar_info rfl hr; exact ⟨hcr, c0, r0, hl, hd, hs⟩
  | v, .localDate, rs, hr => by
    obtain ⟨hcr, ⟨c0, r0, hl, hd, hs⟩, _⟩ := unquotedScalar_info rfl hr; exact ⟨hcr, c0, r0, hl, hd, hs⟩
  | v, .localTime f, rs, hr => by
    obtain ⟨hcr, ⟨c0, r0, hl, hd, hs⟩, _⟩ := unquotedScalar_info rfl hr; exact ⟨hcr, c0, r0, hl, hd, hs⟩
termination_by _ vt _ => sizeOf vt
decreasing_by all_goals (simp +arith at *; omega)

theorem closedTrivia_delimTail {tr : String} {cEnd : Char} {after : List Char}
    (htr : isClosedTrivia tr = true) (hcEnd : cEnd = ',' ∨ cEnd = ']') :
    ModelDelimTail (tr.toList ++ cEnd :: after) := by
  have non_dig : ∀ l : List Char, checkClosedTriviaAux false l = true →
      ∀ c r, l ++ cEnd :: after = c :: r →
      isModelDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigitModel c2 = false) := by
    intro l hcl c r heq
    cases l with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq; rcases heq with ⟨rfl, _⟩
      rcases hcEnd with rfl | rfl <;> exact ⟨by decide, fun h => nomatch h⟩
    | cons l0 ls =>
      simp only [List.cons_append, List.cons.injEq] at heq; rcases heq with ⟨rfl, rfl⟩
      have h0 : l0 = '\n' ∨ isModelHorizWs l0 = true ∨ l0 = '#' := by
        by_cases hnl : l0 = '\n'
        · exact Or.inl hnl
        · have h' : (if isModelHorizWs l0 then checkClosedTriviaAux false ls
              else if l0 == '#' then checkClosedTriviaAux true ls else false) = true := by
            cases l0; simpa [checkClosedTriviaAux, hnl] using hcl
          split at h'
          · exact Or.inr (Or.inl ‹_›)
          · split at h'
            · exact Or.inr (Or.inr (eq_of_beq ‹_›))
            · cases h'
      refine ⟨by rcases h0 with rfl | hw | rfl <;> simp_all [isModelDelim], fun hsp c2 r2 hr2 => ?_⟩
      subst hsp
      have hls : checkClosedTriviaAux false ls = true := by simpa [checkClosedTriviaAux, isModelHorizWs] using hcl
      cases ls with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hr2; rcases hr2 with ⟨rfl, _⟩
        rcases hcEnd with rfl | rfl <;> decide
      | cons l1 ls' =>
        simp only [List.cons_append, List.cons.injEq] at hr2; rcases hr2 with ⟨rfl, _⟩
        by_cases hnl1 : l1 = '\n'
        · subst hnl1; decide
        · have h1' : (if isModelHorizWs l1 then checkClosedTriviaAux false ls'
              else if l1 == '#' then checkClosedTriviaAux true ls' else false) = true := by
            conv at hls => unfold checkClosedTriviaAux
            split at hls <;> simp_all
          split at h1'
          · rename_i hw1; simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hw1
            rcases hw1 with rfl | rfl <;> decide
          · split at h1'
            · rename_i hh1; rw [eq_of_beq hh1]; decide
            · cases h1'
  exact non_dig tr.toList htr

theorem horizWs_delimTail {ws : String} {cEnd : Char} {after : List Char}
    (hws : isHorizWsStr ws = true) (hcEnd : cEnd = ',' ∨ cEnd = '}' ∨ cEnd = '#' ∨ cEnd = '\n') :
    ModelDelimTail (ws.toList ++ cEnd :: after) := by
  intro c r heq
  cases hwl : ws.toList with
  | nil =>
    rw [hwl, List.nil_append] at heq; obtain ⟨rfl, _⟩ := List.cons.inj heq
    rcases hcEnd with rfl | rfl | rfl | rfl <;> exact ⟨by decide, fun h => nomatch h⟩
  | cons w0 ws' =>
    rw [hwl, List.cons_append] at heq; obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    have hw0 := List.all_eq_true.mp hws w0 (by rw [hwl]; simp)
    refine ⟨by simp [isModelDelim, hw0], fun hsp c2 r2 hr2 => ?_⟩
    cases ws' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hr2; rcases hr2 with ⟨rfl, _⟩
      rcases hcEnd with rfl | rfl | rfl | rfl <;> decide
    | cons w1 ws'' =>
      simp only [List.cons_append, List.cons.injEq] at hr2; rcases hr2 with ⟨rfl, _⟩
      have hw1 := List.all_eq_true.mp hws w1 (by rw [hwl]; simp)
      simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hw1
      rcases hw1 with rfl | rfl <;> decide

theorem lineSuffix_delimTail {suf : LineSuffixTape} {rsuf lineEnd : String} {tail : List Char}
    (hsuf : renderLineSuffix suf = some rsuf)
    (hle : (lineEnd = "\n") ∨ (lineEnd = "" ∧ tail = [])) :
    ModelDelimTail ((rsuf ++ lineEnd).toList ++ tail) := by
  unfold renderLineSuffix at hsuf
  split at hsuf
  · simp at hsuf
  · rename_i hws_not
    have hws : isHorizWsStr suf.ws = true := by cases h : isHorizWsStr suf.ws <;> simp_all
    cases hc : suf.comment with
    | none =>
      rw [hc] at hsuf; dsimp only at hsuf; injection hsuf with hrsuf; subst hrsuf
      rcases hle with rfl | ⟨rfl, rfl⟩
      · simpa [String.toList_append, List.append_assoc] using
          horizWs_delimTail (after := tail) hws (Or.inr (Or.inr (Or.inr rfl)))
      · simp only [String.append_empty, List.append_nil]
        intro c r heq
        have hc_ws := List.all_eq_true.mp hws c (by rw [heq]; simp)
        refine ⟨by simp [isModelDelim, hc_ws], fun _ c2 r2 hr2 => ?_⟩
        have hc2_ws := List.all_eq_true.mp hws c2 (by rw [heq, hr2]; simp)
        simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hc2_ws
        rcases hc2_ws with rfl | rfl <;> decide
    | some comm =>
      rw [hc] at hsuf; dsimp only at hsuf; split at hsuf
      · injection hsuf with hrsuf; subst hrsuf
        simpa [String.toList_append, List.append_assoc] using
          horizWs_delimTail (after := comm.toList ++ lineEnd.toList ++ tail) hws (Or.inr (Or.inr (Or.inl rfl)))
      · simp at hsuf

theorem intercalate_comma_cons (s : String) (ss : List String) :
    (String.intercalate "," (s :: ss)).toList =
      s.toList ++ (match ss with | [] => [] | _ :: _ => ',' :: (String.intercalate "," ss).toList) := by
  cases ss with
  | nil => simp [String.intercalate_singleton]
  | cons s2 rest => simp [String.intercalate_cons_cons, String.toList_append]

theorem not_triv_of_valHead {c0 : Char} (hd : isModelDelim c0 = false) :
    isModelHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ ']' ∧ c0 ≠ ',' := by
  simp only [isModelDelim, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hd
  exact ⟨hd.1.1.1.1.1, hd.1.1.1.1.2, hd.1.1.1.2, hd.1.2, hd.1.1.2⟩

/-- Array-vs-array case of `renderValueInline` prefix-injectivity modulo `TomlEquiv`. -/
theorem renderValueInline_array_injective
    {v1 v2 : TomlValue} {tps1 tps2 : List (String × ValueTape × String)}
    {tr1 tr2 : Option String} {rs1 rs2 : String} {rem1 rem2 : List Char}
    (ih : ∀ {w1 w2 : TomlValue} {wt1 wt2 : ValueTape} {s1 s2 : String} {rm1 rm2 : List Char},
      sizeOf wt1 < sizeOf (ValueTape.array tps1 tr1) →
      renderValueInline w1 wt1 = some s1 → renderValueInline w2 wt2 = some s2 →
      ModelDelimTail rm1 → ModelDelimTail rm2 →
      s1.toList ++ rm1 = s2.toList ++ rm2 →
      TomlEquiv w1 w2 ∧ rm1 = rm2)
    (hr1 : renderValueInline v1 (.array tps1 tr1) = some rs1)
    (hr2 : renderValueInline v2 (.array tps2 tr2) = some rs2)
    (heq : rs1.toList ++ rem1 = rs2.toList ++ rem2) :
    TomlEquiv v1 v2 ∧ rem1 = rem2 := by
  cases v1 <;> try (simp [renderValueInline] at hr1; done)
  cases v2 <;> try (simp [renderValueInline] at hr2; done)
  rename_i xs1 xs2
  cases hx1 : xs1.toList with
  | nil =>
    unfold renderValueInline at hr1; rw [hx1] at hr1
    cases tps1 with
    | nil =>
      dsimp only at hr1; split at hr1 <;> try (simp at hr1; done)
      rename_i hcl1; injection hr1 with hrs1; subst hrs1
      cases hx2 : xs2.toList with
      | nil =>
        unfold renderValueInline at hr2; rw [hx2] at hr2
        cases tps2 with
        | nil =>
          dsimp only at hr2; split at hr2 <;> try (simp at hr2; done)
          rename_i hcl2; injection hr2 with hrs2; subst hrs2
          simp only [String.toList_append, show ("[" : String).toList = ['['] from rfl,
            show ("]" : String).toList = [']'] from rfl, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at heq
          have hd := congrArg (dropTrivia false) heq.2
          rw [dropTrivia_closed_append false _ _ hcl1 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide),
              dropTrivia_closed_append false _ _ hcl2 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)] at hd
          injection hd with _ erem
          exact ⟨by simp [TomlEquiv, hx1, hx2, TomlListEquiv], erem⟩
        | cons _ _ => simp at hr2
      | cons y0 yr =>
        cases tps2 with
        | nil => unfold renderValueInline at hr2; rw [hx2] at hr2; simp at hr2
        | cons u0 ur =>
          exfalso
          obtain ⟨strs2, trS2, hstrs2, _, rfl⟩ := renderValueInline_array_cons hx2 hr2
          rcases u0 with ⟨pre2, tp2, post2⟩
          unfold renderArrayElems at hstrs2; split at hstrs2 <;> try (simp at hstrs2; done)
          rename_i htr2; simp at htr2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstrs2
          rcases hstrs2 with ⟨sv2, hsv2, rest2, _, rfl⟩
          obtain ⟨_, ch2, cr2, hsl2, hnd2, _⟩ := renderValueInline_head hsv2
          have hnt2 := not_triv_of_valHead hnd2
          simp only [String.toList_append, show ("[" : String).toList = ['['] from rfl,
            show ("]" : String).toList = [']'] from rfl, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at heq
          have hd := congrArg (dropTrivia false) heq.2
          rw [dropTrivia_closed_append false _ _ hcl1 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide),
              intercalate_comma_cons, List.append_assoc, String.toList_append, String.toList_append,
              List.append_assoc, List.append_assoc,
              dropTrivia_closed_append false pre2.toList _ htr2.1 (fun c r h => by
                rw [hsl2, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact ⟨hnt2.1, hnt2.2.1, hnt2.2.2.1⟩)] at hd
          rw [hsl2, List.cons_append] at hd; injection hd with hbr _; exact hnt2.2.2.2.1 hbr.symm
    | cons _ _ => simp at hr1
  | cons x0 xr =>
    cases tps1 with
    | nil => unfold renderValueInline at hr1; rw [hx1] at hr1; simp at hr1
    | cons t0 tr =>
      obtain ⟨strs1, trS1, hstrs1, htr1, rfl⟩ := renderValueInline_array_cons hx1 hr1
      cases hx2 : xs2.toList with
      | nil =>
        unfold renderValueInline at hr2; rw [hx2] at hr2
        cases tps2 with
        | nil =>
          exfalso
          dsimp only at hr2; split at hr2 <;> try (simp at hr2; done)
          rename_i hcl2; injection hr2 with hrs2; subst hrs2
          rcases t0 with ⟨pre1, tp1, post1⟩
          unfold renderArrayElems at hstrs1; split at hstrs1 <;> try (simp at hstrs1; done)
          rename_i htr1_ok; simp at htr1_ok
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hstrs1
          rcases hstrs1 with ⟨sv1, hsv1, rest1, _, rfl⟩
          obtain ⟨_, ch1, cr1, hsl1, hnd1, _⟩ := renderValueInline_head hsv1
          have hnt1 := not_triv_of_valHead hnd1
          simp only [String.toList_append, show ("[" : String).toList = ['['] from rfl,
            show ("]" : String).toList = [']'] from rfl, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at heq
          have hd := congrArg (dropTrivia false) heq.2
          rw [dropTrivia_closed_append false _ _ hcl2 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide),
              intercalate_comma_cons, List.append_assoc, String.toList_append, String.toList_append,
              List.append_assoc, List.append_assoc,
              dropTrivia_closed_append false pre1.toList _ htr1_ok.1 (fun c r h => by
                rw [hsl1, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact ⟨hnt1.1, hnt1.2.1, hnt1.2.2.1⟩)] at hd
          rw [hsl1, List.cons_append] at hd; injection hd with hbr _; exact hnt1.2.2.2.1 hbr
        | cons _ _ => simp at hr2
      | cons y0 yr =>
        cases tps2 with
        | nil => unfold renderValueInline at hr2; rw [hx2] at hr2; simp at hr2
        | cons u0 ur =>
          obtain ⟨strs2, trS2, hstrs2, htr2, rfl⟩ := renderValueInline_array_cons hx2 hr2
          simp only [String.toList_append, show ("[" : String).toList = ['['] from rfl,
            show ("]" : String).toList = [']'] from rfl, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at heq
          have htrail_spec (trOpt : Option String) (trS : String)
              (htr : (match trOpt with | none => some "" | some trv => if isClosedTrivia trv then some ("," ++ trv) else none) = some trS)
              (rem : List Char) :
              trS.toList ++ (']' :: rem) = ']' :: rem ∨
              ∃ trv, isClosedTrivia trv = true ∧ trS.toList ++ (']' :: rem) = ',' :: (trv.toList ++ ']' :: rem) := by
            cases trOpt with
            | none => simp at htr; subst htr; exact Or.inl rfl
            | some trv =>
              dsimp only at htr; split at htr <;> try (simp at htr; done)
              rename_i hc; injection htr with e; subst e
              exact Or.inr ⟨trv, hc, by simp [String.toList_append]⟩
          have hloop : ∀ (l1 l2 : List TomlValue) (ts1 ts2 : List (String × ValueTape × String))
              (ss1 ss2 : List String),
              l1 ≠ [] → l2 ≠ [] →
              sizeOf ts1 ≤ sizeOf (t0 :: tr) →
              renderArrayElems l1 ts1 = some ss1 → renderArrayElems l2 ts2 = some ss2 →
              (String.intercalate "," ss1).toList ++ (trS1.toList ++ (']' :: rem1)) =
              (String.intercalate "," ss2).toList ++ (trS2.toList ++ (']' :: rem2)) →
              TomlListEquiv l1 l2 ∧ rem1 = rem2 := by
            intro l1; induction l1 with
            | nil => intro _ _ _ _ _ hne; exact absurd rfl hne
            | cons a1 as1 ihl =>
              intro l2 ts1 ts2 ss1 ss2 _ hl2 hsz_ts ha1 ha2 hstr_eq
              cases l2 with | nil => exact absurd rfl hl2 | cons a2 as2 =>
              cases ts1 with | nil => simp [renderArrayElems] at ha1 | cons tp_hd1 tp_tl1 =>
              cases ts2 with | nil => simp [renderArrayElems] at ha2 | cons tp_hd2 tp_tl2 =>
              rcases tp_hd1 with ⟨pr1, vt_e1, po1⟩
              rcases tp_hd2 with ⟨pr2, vt_e2, po2⟩
              unfold renderArrayElems at ha1 ha2
              split at ha1 <;> try (simp at ha1; done)
              rename_i hcl_e1; simp at hcl_e1
              split at ha2 <;> try (simp at ha2; done)
              rename_i hcl_e2; simp at hcl_e2
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha1 ha2
              rcases ha1 with ⟨sv1, hsv1, rss1, hrss1, rfl⟩
              rcases ha2 with ⟨sv2, hsv2, rss2, hrss2, rfl⟩
              rw [intercalate_comma_cons', intercalate_comma_cons', List.append_assoc, List.append_assoc] at hstr_eq
              let sepTail1 := commaRestList rss1 ++ (trS1.toList ++ (']' :: rem1))
              let sepTail2 := commaRestList rss2 ++ (trS2.toList ++ (']' :: rem2))
              change (pr1 ++ sv1 ++ po1).toList ++ sepTail1 = (pr2 ++ sv2 ++ po2).toList ++ sepTail2 at hstr_eq
              obtain ⟨_, ch_e1, _, hsl_e1, hnd_e1, _⟩ := renderValueInline_head hsv1
              obtain ⟨_, ch_e2, _, hsl_e2, hnd_e2, _⟩ := renderValueInline_head hsv2
              have hnt_e1 := not_triv_of_valHead hnd_e1
              have hnt_e2 := not_triv_of_valHead hnd_e2
              have hdrop_pre := congrArg (dropTrivia false) hstr_eq
              simp only [String.toList_append, List.append_assoc] at hdrop_pre
              rw [dropTrivia_closed_append false pr1.toList _ hcl_e1.1 (fun c r h => by
                    rw [hsl_e1, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact ⟨hnt_e1.1, hnt_e1.2.1, hnt_e1.2.2.1⟩),
                  dropTrivia_closed_append false pr2.toList _ hcl_e2.1 (fun c r h => by
                    rw [hsl_e2, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact ⟨hnt_e2.1, hnt_e2.2.1, hnt_e2.2.2.1⟩)] at hdrop_pre
              have hsep_c (rss : List String) (trOpt : Option String) (trS : String)
                  (htr : (match trOpt with | none => some "" | some trv => if isClosedTrivia trv then some ("," ++ trv) else none) = some trS)
                  (rem : List Char) :
                  ∃ cEnd after, commaRestList rss ++ (trS.toList ++ (']' :: rem)) = cEnd :: after ∧ (cEnd = ',' ∨ cEnd = ']') := by
                cases rss with
                | cons _ _ => exact ⟨',', _, rfl, Or.inl rfl⟩
                | nil =>
                  rcases htrail_spec trOpt trS htr rem with h1 | ⟨trv, _, h2⟩
                  · exact ⟨']', rem, h1, Or.inr rfl⟩
                  · exact ⟨',', _, h2, Or.inl rfl⟩
              obtain ⟨ce1, af1, hsp1_eq, hce1⟩ := hsep_c rss1 tr1 trS1 htr1 rem1
              obtain ⟨ce2, af2, hsp2_eq, hce2⟩ := hsep_c rss2 tr2 trS2 htr2 rem2
              have hdt_po1 : ModelDelimTail (po1.toList ++ sepTail1) := by
                dsimp only [sepTail1]; rw [hsp1_eq]; exact closedTrivia_delimTail hcl_e1.2 hce1
              have hdt_po2 : ModelDelimTail (po2.toList ++ sepTail2) := by
                dsimp only [sepTail2]; rw [hsp2_eq]; exact closedTrivia_delimTail hcl_e2.2 hce2
              obtain ⟨heqv_a, hpo_eq⟩ := ih (by simp +arith at hsz_ts ⊢; omega) hsv1 hsv2 hdt_po1 hdt_po2 hdrop_pre
              have hsep_eq : sepTail1 = sepTail2 := by
                have hd := congrArg (dropTrivia false) hpo_eq
                have hc1_nt : ∀ c r, sepTail1 = c :: r → isModelHorizWs c = false ∧ c ≠ '\n' ∧ c ≠ '#' := by
                  dsimp only [sepTail1]; rw [hsp1_eq]; intro c r h; obtain ⟨rfl, _⟩ := List.cons.inj h
                  rcases hce1 with rfl | rfl <;> decide
                have hc2_nt : ∀ c r, sepTail2 = c :: r → isModelHorizWs c = false ∧ c ≠ '\n' ∧ c ≠ '#' := by
                  dsimp only [sepTail2]; rw [hsp2_eq]; intro c r h; obtain ⟨rfl, _⟩ := List.cons.inj h
                  rcases hce2 with rfl | rfl <;> decide
                rwa [dropTrivia_closed_append false po1.toList _ hcl_e1.2 hc1_nt,
                     dropTrivia_closed_append false po2.toList _ hcl_e2.2 hc2_nt] at hd
              cases as1 with
              | nil =>
                cases tp_tl1 <;> simp [renderArrayElems] at hrss1; subst hrss1
                cases as2 with
                | nil =>
                  cases tp_tl2 <;> simp [renderArrayElems] at hrss2; subst hrss2
                  dsimp only [sepTail1, sepTail2, commaRestList] at hsep_eq
                  simp only [List.nil_append] at hsep_eq
                  rcases htrail_spec tr1 trS1 htr1 rem1 with ht1_n | ⟨trv1, hcl_t1, ht1_s⟩ <;>
                    rcases htrail_spec tr2 trS2 htr2 rem2 with ht2_n | ⟨trv2, hcl_t2, ht2_s⟩
                  · rw [ht1_n, ht2_n] at hsep_eq; injection hsep_eq with _ erem
                    exact ⟨by simp [TomlListEquiv, heqv_a], erem⟩
                  · rw [ht1_n, ht2_s] at hsep_eq; cases hsep_eq
                  · rw [ht1_s, ht2_n] at hsep_eq; cases hsep_eq
                  · rw [ht1_s, ht2_s] at hsep_eq; injection hsep_eq with _ etrv
                    have hd := congrArg (dropTrivia false) etrv
                    rw [dropTrivia_closed_append false trv1.toList _ hcl_t1 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide),
                        dropTrivia_closed_append false trv2.toList _ hcl_t2 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)] at hd
                    injection hd with _ erem
                    exact ⟨by simp [TomlListEquiv, heqv_a], erem⟩
                | cons b2 bs2 =>
                  exfalso
                  cases tp_tl2 with | nil => simp [renderArrayElems] at hrss2 | cons hd2_nx tl2_nx =>
                  rcases hd2_nx with ⟨pr2_nx, vt2_nx, po2_nx⟩
                  unfold renderArrayElems at hrss2; split at hrss2 <;> try (simp at hrss2; done)
                  rename_i hcl2_nx; simp at hcl2_nx
                  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hrss2
                  rcases hrss2 with ⟨sv2_nx, hsv2_nx, rss2_nx, _, rfl⟩
                  obtain ⟨_, ch2_nx, _, hsl2_nx, hnd2_nx, _⟩ := renderValueInline_head hsv2_nx
                  have hnt2_nx := not_triv_of_valHead hnd2_nx
                  dsimp only [sepTail1, sepTail2, commaRestList] at hsep_eq
                  simp only [List.nil_append, List.cons_append] at hsep_eq
                  rcases htrail_spec tr1 trS1 htr1 rem1 with ht1_n | ⟨trv1, hcl_t1, ht1_s⟩
                  · rw [ht1_n] at hsep_eq; cases hsep_eq
                  · rw [ht1_s] at hsep_eq; injection hsep_eq with _ etail
                    have hd := congrArg (dropTrivia false) etail
                    rw [dropTrivia_closed_append false trv1.toList _ hcl_t1 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide),
                        intercalate_comma_cons, List.append_assoc, String.toList_append, String.toList_append,
                        List.append_assoc, List.append_assoc,
                        dropTrivia_closed_append false pr2_nx.toList _ hcl2_nx.1 (fun c r h => by
                          rw [hsl2_nx, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact ⟨hnt2_nx.1, hnt2_nx.2.1, hnt2_nx.2.2.1⟩)] at hd
                    rw [hsl2_nx, List.cons_append] at hd; injection hd with hbr _; exact hnt2_nx.2.2.2.1 hbr.symm
              | cons b1 bs1 =>
                cases tp_tl1 with | nil => simp [renderArrayElems] at hrss1 | cons hd1_nx tl1_nx =>
                cases as2 with
                | nil =>
                  exfalso
                  cases tp_tl2 <;> simp [renderArrayElems] at hrss2; subst hrss2
                  rcases hd1_nx with ⟨pr1_nx, vt1_nx, po1_nx⟩
                  unfold renderArrayElems at hrss1; split at hrss1 <;> try (simp at hrss1; done)
                  rename_i hcl1_nx; simp at hcl1_nx
                  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hrss1
                  rcases hrss1 with ⟨sv1_nx, hsv1_nx, rest1_nx, _, rfl⟩
                  obtain ⟨_, ch1_nx, _, hsl1_nx, hnd1_nx, _⟩ := renderValueInline_head hsv1_nx
                  have hnt1_nx := not_triv_of_valHead hnd1_nx
                  dsimp only [sepTail1, sepTail2, commaRestList] at hsep_eq
                  simp only [List.cons_append, List.nil_append] at hsep_eq
                  rcases htrail_spec tr2 trS2 htr2 rem2 with ht2_n | ⟨trv2, hcl_t2, ht2_s⟩
                  · rw [ht2_n] at hsep_eq; cases hsep_eq
                  · rw [ht2_s] at hsep_eq; injection hsep_eq with _ etail
                    have hd := congrArg (dropTrivia false) etail
                    rw [dropTrivia_closed_append false trv2.toList _ hcl_t2 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide),
                        intercalate_comma_cons, List.append_assoc, String.toList_append, String.toList_append,
                        List.append_assoc, List.append_assoc,
                        dropTrivia_closed_append false pr1_nx.toList _ hcl1_nx.1 (fun c r h => by
                          rw [hsl1_nx, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact ⟨hnt1_nx.1, hnt1_nx.2.1, hnt1_nx.2.2.1⟩)] at hd
                    rw [hsl1_nx, List.cons_append] at hd; injection hd with hbr _; exact hnt1_nx.2.2.2.1 hbr
                | cons b2 bs2 =>
                  have hrss1_ne : rss1 ≠ [] := by
                    rcases hd1_nx with ⟨_, _, _⟩; have h := hrss1; unfold renderArrayElems at h
                    split at h
                    · nomatch h
                    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
                      rcases h with ⟨_, _, _, _, rfl⟩; simp
                  have hrss2_ne : rss2 ≠ [] := by
                    cases tp_tl2 with
                    | nil => simp [renderArrayElems] at hrss2
                    | cons hd2_nx _ =>
                      rcases hd2_nx with ⟨_, _, _⟩; have h := hrss2; unfold renderArrayElems at h
                      split at h
                      · nomatch h
                      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
                        rcases h with ⟨_, _, _, _, rfl⟩; simp
                  dsimp only [sepTail1, sepTail2, commaRestList] at hsep_eq
                  cases rss1 with
                  | nil => exact absurd rfl hrss1_ne
                  | cons s1_nx sr1 =>
                    cases rss2 with
                    | nil => exact absurd rfl hrss2_ne
                    | cons s2_nx sr2 =>
                      simp only [List.cons_append, List.cons.injEq] at hsep_eq
                      obtain ⟨heqv_tl, erem⟩ := ihl (b2 :: bs2) (hd1_nx :: tl1_nx) tp_tl2
                        (s1_nx :: sr1) (s2_nx :: sr2) (by simp) (by simp) (by simp +arith at hsz_ts ⊢; omega)
                        hrss1 hrss2 hsep_eq.2
                      exact ⟨by unfold TomlListEquiv; exact ⟨heqv_a, heqv_tl⟩, erem⟩
          obtain ⟨heqv_l, erem⟩ := hloop (x0 :: xr) (y0 :: yr) (t0 :: tr) (u0 :: ur) strs1 strs2
            (by simp) (by simp) (Nat.le_refl _) hstrs1 hstrs2 heq.2
          exact ⟨by simpa [TomlEquiv, hx1, hx2] using heqv_l, erem⟩

end LeanSwe.Toml.Proofs
