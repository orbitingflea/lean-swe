import LeanSwe.Toml.Proofs.ModelCheckInlineAot

set_option Elab.async false

namespace LeanSwe.Toml.ProofsInternal

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.Toml.Proofs
open LeanSwe.Toml.ProofsInternal

/-- Non-delimiter token followed by a delimiter tail splits cleanly in `takeNonDelim`. -/
theorem takeNonDelim_append_end (acc tok sepRest : List Char)
    (htok : tok.all (fun c => !isUnquotedDelim c) = true)
    (hsep : ∀ c r, sepRest = c :: r → isUnquotedDelim c = true) :
    takeNonDelim acc (tok ++ sepRest) = (acc.reverse ++ tok, sepRest) := by
  induction tok generalizing acc with
  | nil =>
    cases sepRest with
    | nil => simp [takeNonDelim]
    | cons c r => simp [takeNonDelim, hsep c r rfl]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at htok
    simp only [List.cons_append, takeNonDelim, htok.1, Bool.false_eq_true, ↓reduceIte]
    rw [ih (c :: acc) htok.2]
    simp

/-- Case split on where a separator element `x` appears in `l1 ++ l2 = a ++ x :: b`. -/
theorem list_append_split_sp {α : Type} (l1 l2 a b : List α) (x : α)
    (h : l1 ++ l2 = a ++ x :: b) :
    (∃ c ∈ a, ∃ r, l2 = c :: r) ∨ (l1 = a ∧ l2 = x :: b) ∨ x ∈ l1 := by
  induction a generalizing l1 with
  | nil =>
    cases l1 with
    | nil => exact Or.inr (Or.inl ⟨rfl, h⟩)
    | cons y ys =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      rw [← h.1]
      exact Or.inr (Or.inr List.mem_cons_self)
  | cons d ds ih =>
    cases l1 with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      exact Or.inl ⟨d, List.mem_cons_self, ds ++ x :: b, h⟩
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      rcases ih ys h.2 with ⟨c, hc, r, hr⟩ | ⟨h1, h2⟩ | hx
      · exact Or.inl ⟨c, List.mem_cons_of_mem d hc, r, hr⟩
      · exact Or.inr (Or.inl ⟨by rw [h.1, h1], h2⟩)
      · exact Or.inr (Or.inr (List.mem_cons_of_mem y hx))

/-- No ASCII digit is an unquoted TOML delimiter. -/
theorem asciiDigit_not_unquotedDelim (c : Char)
    (hd : isAsciiDigit c = true) (hu : isUnquotedDelim c = true) : False := by
  simp only [isUnquotedDelim, isHorizWs, Bool.or_eq_true, beq_iff_eq, or_assoc] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hd

/-- Unquoted token without spaces terminates at a non-space delimiter. -/
theorem takeUnquotedToken_end_noSpace (tok sepRest : List Char)
    (htok : tok.all (fun c => !isUnquotedDelim c) = true)
    (hsep : ∀ c r, sepRest = c :: r → isUnquotedDelim c = true ∧ c ≠ ' ') :
    takeUnquotedToken (tok ++ sepRest) = (String.ofList tok, sepRest) := by
  have hnosp : ' ' ∉ tok := by
    intro hm
    have h1 := List.all_eq_true.mp htok ' ' hm
    cases h1
  unfold takeUnquotedToken
  split
  · rename_i y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 rest' heq
    by_cases hcond : (isAsciiDigit y1 && isAsciiDigit y2 && isAsciiDigit y3 && isAsciiDigit y4 &&
        isAsciiDigit m1 && isAsciiDigit m2 && isAsciiDigit d1 && isAsciiDigit d2 &&
        isAsciiDigit h1 && isAsciiDigit h2 && isAsciiDigit min1 && isAsciiDigit min2 &&
        isAsciiDigit s1 && isAsciiDigit s2) = true
    · exfalso
      simp only [Bool.and_eq_true] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩, hm1⟩, hm2⟩, hd1⟩, hd2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
      have heq' : tok ++ sepRest =
          [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] ++
            ' ' :: ([h1, h2, ':', min1, min2, ':', s1, s2] ++ rest') := by
        simpa [List.append_assoc] using heq
      rcases list_append_split_sp tok sepRest [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2]
          ([h1, h2, ':', min1, min2, ':', s1, s2] ++ rest') ' ' heq' with
        ⟨c, hc, r, hr⟩ | ⟨_, hr_eq⟩ | hmem
      · have hdel : isUnquotedDelim c = true := (hsep c r hr).1
        rcases List.mem_cons.mp hc with rfl | hc
        · exact asciiDigit_not_unquotedDelim _ hy1 hdel
        rcases List.mem_cons.mp hc with rfl | hc
        · exact asciiDigit_not_unquotedDelim _ hy2 hdel
        rcases List.mem_cons.mp hc with rfl | hc
        · exact asciiDigit_not_unquotedDelim _ hy3 hdel
        rcases List.mem_cons.mp hc with rfl | hc
        · exact asciiDigit_not_unquotedDelim _ hy4 hdel
        rcases List.mem_cons.mp hc with rfl | hc
        · exact absurd hdel (by decide)
        rcases List.mem_cons.mp hc with rfl | hc
        · exact asciiDigit_not_unquotedDelim _ hm1 hdel
        rcases List.mem_cons.mp hc with rfl | hc
        · exact asciiDigit_not_unquotedDelim _ hm2 hdel
        rcases List.mem_cons.mp hc with rfl | hc
        · exact absurd hdel (by decide)
        rcases List.mem_cons.mp hc with rfl | hc
        · exact asciiDigit_not_unquotedDelim _ hd1 hdel
        rcases List.mem_singleton.mp hc with rfl
        exact asciiDigit_not_unquotedDelim _ hd2 hdel
      · exact (hsep ' ' _ hr_eq).2 rfl
      · exact hnosp hmem
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      try rw [← heq]
      rw [takeNonDelim_append_end [] tok sepRest htok (fun c r h => (hsep c r h).1)]
      simp
  · rw [takeNonDelim_append_end [] tok sepRest htok (fun c r h => (hsep c r h).1)]
    simp

/-- Space-separated RFC 3339 date-time token splits cleanly in `takeUnquotedToken`. -/
theorem takeUnquotedToken_spaceDateTime
    (y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 : Char)
    (tail rest : List Char)
    (hy1 : isAsciiDigit y1 = true) (hy2 : isAsciiDigit y2 = true)
    (hy3 : isAsciiDigit y3 = true) (hy4 : isAsciiDigit y4 = true)
    (hm1 : isAsciiDigit m1 = true) (hm2 : isAsciiDigit m2 = true)
    (hd1 : isAsciiDigit d1 = true) (hd2 : isAsciiDigit d2 = true)
    (hh1 : isAsciiDigit h1 = true) (hh2 : isAsciiDigit h2 = true)
    (hmin1 : isAsciiDigit min1 = true) (hmin2 : isAsciiDigit min2 = true)
    (hs1 : isAsciiDigit s1 = true) (hs2 : isAsciiDigit s2 = true)
    (htail : tail.all (fun c => !isUnquotedDelim c) = true)
    (hrest : ∀ c r, rest = c :: r → isUnquotedDelim c = true) :
    takeUnquotedToken
      (([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++ tail) ++ rest) =
      (String.ofList ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++ tail),
        rest) := by
  rw [List.append_assoc]
  simp only [List.cons_append, List.nil_append, takeUnquotedToken,
    hy1, hy2, hy3, hy4, hm1, hm2, hd1, hd2, hh1, hh2, hmin1, hmin2, hs1, hs2,
    Bool.and_self, ↓reduceIte]
  rw [takeNonDelim_append_end [] tail rest htail hrest]
  simp

/-- Single bare key before `' ='` parses via `parseDottedKey`. -/
theorem parseDottedKey_single (k : String) (kc : Char) (kt : List Char)
    (hkc_list : k.toList = kc :: kt) (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (rest : List Char) :
    parseDottedKey (k.toList ++ ' ' :: '=' :: rest) = .ok ([k], '=' :: rest) := by
  have hkeyseg : parseKeySegment (k.toList ++ (' ' :: '=' :: rest)) = .ok (k, ' ' :: '=' :: rest) := by
    rw [hkc_list, List.cons_append, hkey_k _]
    rw [← List.cons_append, ← hkc_list]
    rw [takeBareKeyChars_append [] k.toList ' ' _ hk_bare (by decide)]
    simp only [List.reverse_nil, List.nil_append]
    have hne : k.toList.isEmpty = false := by simp [hkc_list]
    simp [hne, String.ofList_toList]
  unfold parseDottedKey
  have hlen : ∃ f, (k.toList ++ (' ' :: '=' :: rest)).length + 1 = f + 1 := ⟨_, rfl⟩
  rcases hlen with ⟨f, hf⟩
  rw [hf]
  have hdk_step : parseDottedKeyFuel (f + 1) (k.toList ++ (' ' :: '=' :: rest)) =
      (do
        let (k0, r1) ← parseKeySegment (k.toList ++ (' ' :: '=' :: rest))
        let r2 := skipHorizWs r1
        match r2 with
        | '.' :: r3 => do
          let (restKeys, r4) ← parseDottedKeyFuel f (skipHorizWs r3)
          .ok (k0 :: restKeys, r4)
        | other => .ok ([k0], other)) := rfl
  rw [hdk_step, hkeyseg]
  simp only [bind, Except.bind]
  have hws_eq : skipHorizWs (' ' :: '=' :: rest) = '=' :: rest := by
    simp [skipHorizWs, isHorizWs]
  rw [hws_eq]
  rfl

/-- Unquoted token value step for `parseValue modelNumApi`. -/
theorem parseValue_tok (vstr : String) (vc : Char) (vt : List Char)
    (hvc_list : vstr.toList = vc :: vt)
    (hval_v : ∀ fuel r, parseValueFuel modelNumApi (fuel + 1) (vc :: r) =
      (let (tok, after) := takeUnquotedToken (vc :: r)
       classifyScalarToken modelNumApi tok >>= fun v => .ok (v, after)))
    (v : TomlValue) (hcls : classifyScalarToken modelNumApi vstr = .ok v)
    (sepRest : List Char)
    (htok : takeUnquotedToken (vstr.toList ++ sepRest) = (vstr, sepRest)) :
    parseValue modelNumApi (vstr.toList ++ sepRest) = .ok (v, sepRest) := by
  unfold parseValue
  have hlen : ∃ f, (vstr.toList ++ sepRest).length + 2 = f + 1 := ⟨_, rfl⟩
  rcases hlen with ⟨f, hf⟩
  rw [hf, hvc_list, List.cons_append, hval_v f _]
  rw [← List.cons_append, ← hvc_list, htok]
  simp [hcls, bind, Except.bind]

/-- Generic `parseDocumentFuel` reduction across one bare-key assignment with unquoted value. -/
theorem parseDoc_step_bare_tok (k vstr : String)
    (kc : Char) (kt : List Char) (hkc_list : k.toList = kc :: kt)
    (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_k : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) (kc :: r) ap rt = docKeyValBody fuel (kc :: r) ap rt)
    (vc : Char) (vt : List Char) (hvc_list : vstr.toList = vc :: vt)
    (hvc_ws : isHorizWs vc = false)
    (hval_v : ∀ fuel r, parseValueFuel modelNumApi (fuel + 1) (vc :: r) =
      (let (tok, after) := takeUnquotedToken (vc :: r)
       classifyScalarToken modelNumApi tok >>= fun v => .ok (v, after)))
    (fuel : Nat) (sepRest nextRest : List Char)
    (htok : takeUnquotedToken (vstr.toList ++ sepRest) = (vstr, sepRest))
    (v : TomlValue) (hcls : classifyScalarToken modelNumApi vstr = .ok v)
    (activePath : List String) (root nextRoot : List (String × Node))
    (hins : insertAtActivePath (activePath ++ [k]) root activePath [k] (valueToInlineNode v) = .ok nextRoot)
    (hsep_end : consumeStatementEnd sepRest = .ok nextRest) :
    parseDocumentFuel modelNumApi (fuel + 1) ((k ++ " = " ++ vstr).toList ++ sepRest) activePath root =
      parseDocumentFuel modelNumApi fuel nextRest activePath nextRoot := by
  have hline : (k ++ " = " ++ vstr).toList ++ sepRest =
      k.toList ++ (' ' :: '=' :: ' ' :: (vstr.toList ++ sepRest)) := by
    have hsep : (" = " : String).toList = [' ', '=', ' '] := by cbv
    simp only [String.toList_append, hsep, List.cons_append, List.nil_append, List.append_assoc]
  have hdk : parseDottedKey ((k ++ " = " ++ vstr).toList ++ sepRest) =
      .ok ([k], '=' :: ' ' :: (vstr.toList ++ sepRest)) := by
    rw [hline]
    exact parseDottedKey_single k kc kt hkc_list hk_bare hkey_k (' ' :: (vstr.toList ++ sepRest))
  have hpv : parseValue modelNumApi (vstr.toList ++ sepRest) = .ok (v, sepRest) :=
    parseValue_tok vstr vc vt hvc_list hval_v v hcls sepRest htok
  have hskip_v : skipHorizWs (' ' :: (vstr.toList ++ sepRest)) = vstr.toList ++ sepRest := by
    have h1 : skipHorizWs (' ' :: (vstr.toList ++ sepRest)) = skipHorizWs (vstr.toList ++ sepRest) := by
      simp [skipHorizWs, isHorizWs]
    rw [h1, hvc_list, List.cons_append]
    have h2 : skipHorizWs (vc :: (vt ++ sepRest)) =
        if isHorizWs vc then skipHorizWs (vt ++ sepRest) else vc :: (vt ++ sepRest) := rfl
    rw [h2, hvc_ws]
    simp
  have hskip_eq : skipHorizWs ('=' :: ' ' :: (vstr.toList ++ sepRest)) =
      '=' :: ' ' :: (vstr.toList ++ sepRest) := by
    simp [skipHorizWs, isHorizWs]
  rw [hline, hkc_list, List.cons_append, hdoc_k]
  rw [← List.cons_append, ← hkc_list, ← hline]
  simp only [docKeyValBody, hdk, hskip_eq, hskip_v, hpv, hsep_end, hins, bind, Except.bind]

/-- Newline-terminated assignment step when value contains no spaces. -/
theorem parseDoc_step_nl_noSpace (k vstr : String)
    (kc : Char) (kt : List Char) (hkc_list : k.toList = kc :: kt)
    (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_k : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) (kc :: r) ap rt = docKeyValBody fuel (kc :: r) ap rt)
    (vc : Char) (vt : List Char) (hvc_list : vstr.toList = vc :: vt)
    (hvc_ws : isHorizWs vc = false)
    (hval_v : ∀ fuel r, parseValueFuel modelNumApi (fuel + 1) (vc :: r) =
      (let (tok, after) := takeUnquotedToken (vc :: r)
       classifyScalarToken modelNumApi tok >>= fun v => .ok (v, after)))
    (hv_clean : vstr.toList.all (fun c => !isUnquotedDelim c) = true)
    (v : TomlValue) (hcls : classifyScalarToken modelNumApi vstr = .ok v)
    (activePath : List String) (root nextRoot : List (String × Node))
    (hins : insertAtActivePath (activePath ++ [k]) root activePath [k] (valueToInlineNode v) = .ok nextRoot)
    (fuel : Nat) (rest : List Char) :
    parseDocumentFuel modelNumApi (fuel + 1) ((k ++ " = " ++ vstr).toList ++ '\n' :: rest) activePath root =
      parseDocumentFuel modelNumApi fuel rest activePath nextRoot :=
  parseDoc_step_bare_tok k vstr kc kt hkc_list hk_bare hkey_k hdoc_k vc vt hvc_list hvc_ws hval_v
    fuel ('\n' :: rest) rest
    (by
      rw [takeUnquotedToken_end_noSpace vstr.toList ('\n' :: rest) hv_clean
        (fun _ _ h => by injection h with hc _; subst hc; exact ⟨by decide, by decide⟩)]
      simp [String.ofList_toList])
    v hcls activePath root nextRoot hins
    (by simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs])

/-- Newline-terminated assignment step using an explicit `takeUnquotedToken` witness. -/
theorem parseDoc_step_nl_tok (k vstr : String)
    (kc : Char) (kt : List Char) (hkc_list : k.toList = kc :: kt)
    (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_k : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) (kc :: r) ap rt = docKeyValBody fuel (kc :: r) ap rt)
    (vc : Char) (vt : List Char) (hvc_list : vstr.toList = vc :: vt)
    (hvc_ws : isHorizWs vc = false)
    (hval_v : ∀ fuel r, parseValueFuel modelNumApi (fuel + 1) (vc :: r) =
      (let (tok, after) := takeUnquotedToken (vc :: r)
       classifyScalarToken modelNumApi tok >>= fun v => .ok (v, after)))
    (htok : ∀ rest, takeUnquotedToken (vstr.toList ++ '\n' :: rest) = (vstr, '\n' :: rest))
    (v : TomlValue) (hcls : classifyScalarToken modelNumApi vstr = .ok v)
    (activePath : List String) (root nextRoot : List (String × Node))
    (hins : insertAtActivePath (activePath ++ [k]) root activePath [k] (valueToInlineNode v) = .ok nextRoot)
    (fuel : Nat) (rest : List Char) :
    parseDocumentFuel modelNumApi (fuel + 1) ((k ++ " = " ++ vstr).toList ++ '\n' :: rest) activePath root =
      parseDocumentFuel modelNumApi fuel rest activePath nextRoot :=
  parseDoc_step_bare_tok k vstr kc kt hkc_list hk_bare hkey_k hdoc_k vc vt hvc_list hvc_ws hval_v
    fuel ('\n' :: rest) rest (htok rest) v hcls activePath root nextRoot hins
    (by simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs])

/-- EOF-terminated assignment step when value contains no spaces. -/
theorem parseDoc_step_eof_noSpace (k vstr : String)
    (kc : Char) (kt : List Char) (hkc_list : k.toList = kc :: kt)
    (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_k : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) (kc :: r) ap rt = docKeyValBody fuel (kc :: r) ap rt)
    (vc : Char) (vt : List Char) (hvc_list : vstr.toList = vc :: vt)
    (hvc_ws : isHorizWs vc = false)
    (hval_v : ∀ fuel r, parseValueFuel modelNumApi (fuel + 1) (vc :: r) =
      (let (tok, after) := takeUnquotedToken (vc :: r)
       classifyScalarToken modelNumApi tok >>= fun v => .ok (v, after)))
    (hv_clean : vstr.toList.all (fun c => !isUnquotedDelim c) = true)
    (v : TomlValue) (hcls : classifyScalarToken modelNumApi vstr = .ok v)
    (activePath : List String) (root nextRoot : List (String × Node))
    (hins : insertAtActivePath (activePath ++ [k]) root activePath [k] (valueToInlineNode v) = .ok nextRoot)
    (fuel : Nat) :
    parseDocumentFuel modelNumApi (fuel + 1) (k ++ " = " ++ vstr).toList activePath root = .ok nextRoot := by
  rw [← List.append_nil (k ++ " = " ++ vstr).toList]
  rw [parseDoc_step_bare_tok k vstr kc kt hkc_list hk_bare hkey_k hdoc_k vc vt hvc_list hvc_ws hval_v
    fuel [] []
    (by
      rw [takeUnquotedToken_end_noSpace vstr.toList [] hv_clean (fun _ _ h => by cases h)]
      simp [String.ofList_toList])
    v hcls activePath root nextRoot hins rfl]
  cases fuel <;> rfl

end LeanSwe.Toml.ProofsInternal

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.Toml.Proofs
open LeanSwe.Toml.ProofsInternal

private theorem docKeyVal_m :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('m' :: r) ap rt = docKeyValBody fuel ('m' :: r) ap rt :=
  docKeyVal_of 'm' (skipTriviaNewlines_eq_of 'm' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private theorem docKeyVal_h :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('h' :: r) ap rt = docKeyValBody fuel ('h' :: r) ap rt :=
  docKeyVal_of 'h' (skipTriviaNewlines_eq_of 'h' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private theorem docKeyVal_o :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('o' :: r) ap rt = docKeyValBody fuel ('o' :: r) ap rt :=
  docKeyVal_of 'o' (skipTriviaNewlines_eq_of 'o' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private theorem docKeyVal_b :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('b' :: r) ap rt = docKeyValBody fuel ('b' :: r) ap rt :=
  docKeyVal_of 'b' (skipTriviaNewlines_eq_of 'b' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private theorem cls_min :
    classifyScalarToken modelNumApi "-9223372036854775808" = .ok (.int (-9223372036854775808)) := by
  cbv

private theorem cls_max :
    classifyScalarToken modelNumApi "9223372036854775807" = .ok (.int 9223372036854775807) := by
  cbv

private theorem cls_hex :
    classifyScalarToken modelNumApi "0xdead_beef" = .ok (.int 0xdeadbeef) := by
  cbv

private theorem cls_oct :
    classifyScalarToken modelNumApi "0o755" = .ok (.int 0o755) := by
  cbv

private theorem cls_bin :
    classifyScalarToken modelNumApi "0b1010_0101" = .ok (.int 0b10100101) := by
  cbv

private theorem cls_bt :
    classifyScalarToken modelNumApi "true" = .ok (.bool true) := by
  cbv

private theorem cls_bf :
    classifyScalarToken modelNumApi "false" = .ok (.bool false) := by
  cbv

private def dt0Str : String :=
  "min = -9223372036854775808\nmax = 9223372036854775807\nhex = 0xdead_beef\noct = 0o755\nbin = 0b1010_0101\nbt = true\nbf = false"

private theorem elem0_clean :
    (dt0Str.toList.all (fun c => !isDisallowedControl c && c != '\r')) = true := by
  cbv

private theorem dt0_hs_eq :
    dt0Str.toList =
      ("min" ++ " = " ++ "-9223372036854775808").toList ++ '\n' ::
      (("max" ++ " = " ++ "9223372036854775807").toList ++ '\n' ::
      (("hex" ++ " = " ++ "0xdead_beef").toList ++ '\n' ::
      (("oct" ++ " = " ++ "0o755").toList ++ '\n' ::
      (("bin" ++ " = " ++ "0b1010_0101").toList ++ '\n' ::
      (("bt" ++ " = " ++ "true").toList ++ '\n' ::
      ("bf" ++ " = " ++ "false").toList))))) := by
  cbv

private def dt0R1 : List (String × Node) := [("min", .leaf (.int (-9223372036854775808)))]
private def dt0R2 : List (String × Node) := dt0R1 ++ [("max", .leaf (.int 9223372036854775807))]
private def dt0R3 : List (String × Node) := dt0R2 ++ [("hex", .leaf (.int 0xdeadbeef))]
private def dt0R4 : List (String × Node) := dt0R3 ++ [("oct", .leaf (.int 0o755))]
private def dt0R5 : List (String × Node) := dt0R4 ++ [("bin", .leaf (.int 0b10100101))]
private def dt0R6 : List (String × Node) := dt0R5 ++ [("bt", .leaf (.bool true))]
private def dt0R7 : List (String × Node) := dt0R6 ++ [("bf", .leaf (.bool false))]

private theorem dt0_hi1 : insertAtActivePath ["min"] [] [] ["min"] (valueToInlineNode (.int (-9223372036854775808))) = .ok dt0R1 := by cbv
private theorem dt0_hi2 : insertAtActivePath ["max"] dt0R1 [] ["max"] (valueToInlineNode (.int 9223372036854775807)) = .ok dt0R2 := by cbv
private theorem dt0_hi3 : insertAtActivePath ["hex"] dt0R2 [] ["hex"] (valueToInlineNode (.int 0xdeadbeef)) = .ok dt0R3 := by cbv
private theorem dt0_hi4 : insertAtActivePath ["oct"] dt0R3 [] ["oct"] (valueToInlineNode (.int 0o755)) = .ok dt0R4 := by cbv
private theorem dt0_hi5 : insertAtActivePath ["bin"] dt0R4 [] ["bin"] (valueToInlineNode (.int 0b10100101)) = .ok dt0R5 := by cbv
private theorem dt0_hi6 : insertAtActivePath ["bt"] dt0R5 [] ["bt"] (valueToInlineNode (.bool true)) = .ok dt0R6 := by cbv
private theorem dt0_hi7 : insertAtActivePath ["bf"] dt0R6 [] ["bf"] (valueToInlineNode (.bool false)) = .ok dt0R7 := by cbv

private theorem elem0_beq :
    tomlValueBeq
      (.table #[("min", .int (-9223372036854775808)), ("max", .int 9223372036854775807),
        ("hex", .int 0xdeadbeef), ("oct", .int 0o755), ("bin", .int 0b10100101),
        ("bt", .bool true), ("bf", .bool false)])
      (.table (entriesToTomlList dt0R7).toArray) = true := by
  cbv

private theorem dt0_hdoc :
    parseDocumentFuel modelNumApi (dt0Str.toList.length + 1) dt0Str.toList [] [] = .ok dt0R7 := by
  have hlen : dt0Str.toList.length + 1 ≥ 7 := by
    rw [dt0_hs_eq]
    simp only [List.length_append, List.length_cons]
    omega
  have hsplit : ∃ f, dt0Str.toList.length + 1 = ((((((f + 1) + 1) + 1) + 1) + 1) + 1) + 1 :=
    ⟨dt0Str.toList.length + 1 - 7, by omega⟩
  rcases hsplit with ⟨f, hf⟩
  rw [hf, dt0_hs_eq]
  rw [parseDoc_step_nl_noSpace "min" "-9223372036854775808" 'm' ['i', 'n'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_m '-' ("9223372036854775808".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    (.int (-9223372036854775808)) cls_min [] [] dt0R1 dt0_hi1]
  rw [parseDoc_step_nl_noSpace "max" "9223372036854775807" 'm' ['a', 'x'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_m '9' ("223372036854775807".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    (.int 9223372036854775807) cls_max [] dt0R1 dt0R2 dt0_hi2]
  rw [parseDoc_step_nl_noSpace "hex" "0xdead_beef" 'h' ['e', 'x'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_h '0' ("xdead_beef".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    (.int 0xdeadbeef) cls_hex [] dt0R2 dt0R3 dt0_hi3]
  rw [parseDoc_step_nl_noSpace "oct" "0o755" 'o' ['c', 't'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_o '0' ("o755".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    (.int 0o755) cls_oct [] dt0R3 dt0R4 dt0_hi4]
  rw [parseDoc_step_nl_noSpace "bin" "0b1010_0101" 'b' ['i', 'n'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_b '0' ("b1010_0101".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    (.int 0b10100101) cls_bin [] dt0R4 dt0R5 dt0_hi5]
  rw [parseDoc_step_nl_noSpace "bt" "true" 'b' ['t'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_b 't' ("rue".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    (.bool true) cls_bt [] dt0R5 dt0R6 dt0_hi6]
  exact parseDoc_step_eof_noSpace "bf" "false" 'b' ['f'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_b 'f' ("alse".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    (.bool false) cls_bf [] dt0R6 dt0R7 dt0_hi7 f

private theorem elem0_valid :
    checkOneOkModel
      (dt0Str,
        #[("min", .int (-9223372036854775808)),
          ("max", .int 9223372036854775807),
          ("hex", .int 0xdeadbeef),
          ("oct", .int 0o755),
          ("bin", .int 0b10100101),
          ("bt", .bool true),
          ("bf", .bool false)]) = true := by
  have hnorm : normalizeChars 1 1 dt0Str.toList = .ok dt0Str.toList :=
    normalizeChars_clean _ elem0_clean 1 1
  simp only [checkOneOkModel, parseWithNum, hnorm, dt0_hdoc, bind, Except.bind]
  exact elem0_beq

/-- Verify element 0 of `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_0 :
    ((numberDatetimeOkCases.drop 0).head?.map checkOneOkModel).getD false = true := by
  simp only [numberDatetimeOkCases, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]
  exact elem0_valid

end LeanSwe.Toml.Proofs
