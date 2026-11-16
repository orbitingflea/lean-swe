import LeanSwe.Toml.Proofs.ModelCheckKeysStrings

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.Toml.ProofsInternal

set_option Elab.async false

private theorem parseDottedKeyFuel_single_aot (f : Nat) (k : String) (kc : Char) (kt : List Char)
    (hkc_list : k.toList = kc :: kt) (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (d : Char) (hd_bare : isBareKeyChar d = false) (hd_ws : isHorizWs d = false) (hd_dot : d ≠ '.')
    (rest : List Char) :
    parseDottedKeyFuel (f + 1) (k.toList ++ d :: rest) = .ok ([k], d :: rest) := by
  have hkeyseg : parseKeySegment (k.toList ++ (d :: rest)) = .ok (k, d :: rest) := by
    rw [hkc_list, List.cons_append, hkey_k _]
    rw [← List.cons_append, ← hkc_list]
    rw [takeBareKeyChars_append [] k.toList d _ hk_bare hd_bare]
    simp only [List.reverse_nil, List.nil_append]
    have hne : k.toList.isEmpty = false := by simp [hkc_list]
    simp [hne, String.ofList_toList]
  have hdk_step : parseDottedKeyFuel (f + 1) (k.toList ++ (d :: rest)) =
      (do
        let (k0, r1) ← parseKeySegment (k.toList ++ (d :: rest))
        let r2 := skipHorizWs r1
        match r2 with
        | '.' :: r3 => do
          let (restKeys, r4) ← parseDottedKeyFuel f (skipHorizWs r3)
          .ok (k0 :: restKeys, r4)
        | other => .ok ([k0], other)) := rfl
  rw [hdk_step, hkeyseg]
  simp only [bind, Except.bind]
  have hws_eq : skipHorizWs (d :: rest) = d :: rest := by
    have h1 : skipHorizWs (d :: rest) = if isHorizWs d then skipHorizWs rest else d :: rest := rfl
    rw [h1, hd_ws]
    simp
  rw [hws_eq]
  split
  · first | exact absurd rfl hd_dot | (rename_i heq; injection heq with h1 _; exact absurd h1 hd_dot)
  · rfl

private theorem parseDottedKey_single_aot (k : String) (kc : Char) (kt : List Char)
    (hkc_list : k.toList = kc :: kt) (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (d : Char) (hd_bare : isBareKeyChar d = false) (hd_ws : isHorizWs d = false) (hd_dot : d ≠ '.')
    (rest : List Char) :
    parseDottedKey (k.toList ++ d :: rest) = .ok ([k], d :: rest) := by
  unfold parseDottedKey
  exact parseDottedKeyFuel_single_aot _ k kc kt hkc_list hk_bare hkey_k d hd_bare hd_ws hd_dot rest

private theorem bareKeyChar_not_horizWs (c : Char) (hb : isBareKeyChar c = true) :
    isHorizWs c = false := by
  by_cases hw : isHorizWs c = true
  · simp only [isHorizWs, Bool.or_eq_true, beq_iff_eq] at hw
    rcases hw with rfl | rfl <;> exact absurd hb (by decide)
  · exact Bool.eq_false_iff.mpr hw

private theorem parseDottedKeyFuel_dot_step (f : Nat) (k : String) (kc : Char) (kt rest : List Char)
    (hk_list : k.toList = kc :: kt) (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest))) :
    parseDottedKeyFuel (f + 1) (k.toList ++ '.' :: rest) =
      (do
        let (restKeys, r4) ← parseDottedKeyFuel f (skipHorizWs rest)
        .ok (k :: restKeys, r4)) := by
  have hkeyseg : parseKeySegment (k.toList ++ '.' :: rest) = .ok (k, '.' :: rest) := by
    rw [hk_list, List.cons_append, hkey_k _]
    rw [← List.cons_append, ← hk_list]
    rw [takeBareKeyChars_append [] k.toList '.' rest hk_bare (by decide)]
    simp only [List.reverse_nil, List.nil_append]
    have hne : k.toList.isEmpty = false := by simp [hk_list]
    simp [hne, String.ofList_toList]
  have hdk1 : parseDottedKeyFuel (f + 1) (k.toList ++ '.' :: rest) =
      (do
        let (k0, r1) ← parseKeySegment (k.toList ++ '.' :: rest)
        let r2 := skipHorizWs r1
        match r2 with
        | '.' :: r3 => do
          let (restKeys, r4) ← parseDottedKeyFuel f (skipHorizWs r3)
          .ok (k0 :: restKeys, r4)
        | other => .ok ([k0], other)) := rfl
  rw [hdk1, hkeyseg]
  simp only [bind, Except.bind]
  have hws_dot : skipHorizWs ('.' :: rest) = '.' :: rest := by
    simp [skipHorizWs, isHorizWs]
  rw [hws_dot]
  rfl

private theorem parseDottedKey_double_aot (k1 k2 : String)
    (kc1 : Char) (kt1 : List Char) (hk1_list : k1.toList = kc1 :: kt1)
    (hk1_bare : k1.toList.all isBareKeyChar = true)
    (hkey_k1 : ∀ r, parseKeySegment (kc1 :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc1 :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (kc2 : Char) (kt2 : List Char) (hk2_list : k2.toList = kc2 :: kt2)
    (hk2_bare : k2.toList.all isBareKeyChar = true)
    (hkey_k2 : ∀ r, parseKeySegment (kc2 :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc2 :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (d : Char) (hd_bare : isBareKeyChar d = false) (hd_ws : isHorizWs d = false) (hd_dot : d ≠ '.')
    (rest : List Char) :
    parseDottedKey (k1.toList ++ '.' :: (k2.toList ++ d :: rest)) = .ok ([k1, k2], d :: rest) := by
  have hk2_kc_bare : isBareKeyChar kc2 = true := by
    have ha := List.all_eq_true.mp hk2_bare kc2
    rw [hk2_list] at ha
    exact ha List.mem_cons_self
  unfold parseDottedKey
  have hlen : ∃ f, (k1.toList ++ '.' :: (k2.toList ++ d :: rest)).length + 1 = (f + 1) + 1 :=
    ⟨k1.toList.length + k2.toList.length + rest.length + 1, by simp [List.length_append]; omega⟩
  rcases hlen with ⟨f, hf⟩
  rw [hf, parseDottedKeyFuel_dot_step (f + 1) k1 kc1 kt1 (k2.toList ++ d :: rest) hk1_list hk1_bare hkey_k1]
  have hk2_ws : isHorizWs kc2 = false := bareKeyChar_not_horizWs kc2 hk2_kc_bare
  have hws_k2 : skipHorizWs (k2.toList ++ d :: rest) = k2.toList ++ d :: rest := by
    rw [hk2_list, List.cons_append]
    have h1 : skipHorizWs (kc2 :: (kt2 ++ d :: rest)) =
        if isHorizWs kc2 then skipHorizWs (kt2 ++ d :: rest) else kc2 :: (kt2 ++ d :: rest) := rfl
    rw [h1, hk2_ws]; simp
  rw [hws_k2, parseDottedKeyFuel_single_aot f k2 kc2 kt2 hk2_list hk2_bare hkey_k2 d hd_bare hd_ws hd_dot rest]
  rfl

private theorem parseBasicStringBodyFuel_step_char_aot (f : Nat) (acc : List Char) (c : Char)
    (rest : List Char) (hnl : c ≠ '\n') (hq : c ≠ '"') (hbs : c ≠ '\\') :
    parseBasicStringBodyFuel (f + 1) acc (c :: rest) = parseBasicStringBodyFuel f (c :: acc) rest := by
  conv => lhs; unfold parseBasicStringBodyFuel
  split <;> simp_all

private theorem parseBasicStringBodyFuel_clean_aot (cs acc rest : List Char) (fuel : Nat)
    (hfuel : cs.length + 1 ≤ fuel)
    (hclean : cs.all (fun c => c != '\n' && c != '"' && c != '\\') = true) :
    parseBasicStringBodyFuel fuel acc (cs ++ '"' :: rest) =
      .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc fuel with
  | nil =>
    cases fuel with
    | zero => simp at hfuel
    | succ f => simp [parseBasicStringBodyFuel]
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hclean
      rcases hclean with ⟨⟨⟨hnl, hq⟩, hbs⟩, hrest⟩
      simp only [List.cons_append]
      rw [parseBasicStringBodyFuel_step_char_aot f acc c (cs ++ '"' :: rest) hnl hq hbs]
      have hsub : cs.length + 1 ≤ f := by simp only [List.length_cons] at hfuel; omega
      rw [ih (c :: acc) f hsub hrest]
      simp

private theorem parseBasicStringBody_clean_aot (v : String) (rest : List Char)
    (hv_clean : v.toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true) :
    parseBasicStringBody (v.toList ++ '"' :: rest) = .ok (v, rest) := by
  unfold parseBasicStringBody
  have hlen2 : v.toList.length + 1 ≤ (v.toList ++ '"' :: rest).length + 1 := by
    simp only [List.length_append, List.length_cons]
    omega
  rw [parseBasicStringBodyFuel_clean_aot v.toList [] rest ((v.toList ++ '"' :: rest).length + 1) hlen2 hv_clean]
  simp only [List.reverse_nil, List.nil_append, String.ofList_toList]

private theorem docAot_eq (hskip : ∀ r, skipTriviaNewlines ('[' :: r) = '[' :: r) :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('[' :: '[' :: r) ap rt = docAotBody fuel r rt :=
  fun fuel r ap rt => by
    change (match skipTriviaNewlines ('[' :: '[' :: r) with
      | [] => .ok rt
      | '[' :: '[' :: rest => docAotBody fuel rest rt
      | '[' :: rest => docTableBody fuel rest rt
      | cs1 => docKeyValBody fuel cs1 ap rt) = docAotBody fuel r rt
    rw [hskip ('[' :: r)]
    rfl

private theorem docTable_f_aot (hskip : ∀ r, skipTriviaNewlines ('[' :: r) = '[' :: r) :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('[' :: 'f' :: r) ap rt = docTableBody fuel ('f' :: r) rt :=
  fun fuel r ap rt => by
    change (match skipTriviaNewlines ('[' :: 'f' :: r) with
      | [] => .ok rt
      | '[' :: '[' :: rest => docAotBody fuel rest rt
      | '[' :: rest => docTableBody fuel rest rt
      | cs1 => docKeyValBody fuel cs1 ap rt) = docTableBody fuel ('f' :: r) rt
    rw [hskip ('f' :: r)]
    rfl

private theorem parseValue_basic_aot (v : String) (vc : Char) (vt : List Char)
    (hvc_list : v.toList = vc :: vt)
    (hv_clean : v.toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true)
    (hval_v : ∀ fuel r, parseValueFuel modelNumApi (fuel + 1) ('"' :: vc :: r) =
      (parseBasicStringBody (vc :: r) >>= fun (s, after) => .ok (.string s, after)))
    (rest : List Char) :
    parseValue modelNumApi ('"' :: (v.toList ++ '"' :: rest)) = .ok (.string v, rest) := by
  unfold parseValue
  have hlen : ∃ f, ('"' :: (v.toList ++ '"' :: rest)).length + 2 = f + 1 := ⟨_, rfl⟩
  rcases hlen with ⟨f, hf⟩
  rw [hf, hvc_list, List.cons_append, hval_v f _]
  rw [← List.cons_append, ← hvc_list, parseBasicStringBody_clean_aot v rest hv_clean]
  rfl

private theorem docAotBody_step (fuel : Nat) (rest : List Char) (rt : List (String × Node))
    (path : List String) (r2 : List Char)
    (hdk : parseDottedKey (skipHorizWs rest) = .ok (path, ']' :: ']' :: r2))
    (nextCs : List Char) (hend : consumeStatementEnd r2 = .ok nextCs)
    (nextRoot : List (String × Node)) (hins : applyAotHeader path rt path = .ok nextRoot) :
    docAotBody fuel rest rt = parseDocumentFuel modelNumApi fuel nextCs path nextRoot := by
  have hskip_rb : skipHorizWs (']' :: ']' :: r2) = ']' :: ']' :: r2 := by
    simp [skipHorizWs, isHorizWs]
  simp only [docAotBody, hdk, hskip_rb, hend, hins, bind, Except.bind]

private theorem docTableBody_step (fuel : Nat) (rest : List Char) (rt : List (String × Node))
    (path : List String) (r2 : List Char)
    (hdk : parseDottedKey (skipHorizWs rest) = .ok (path, ']' :: r2))
    (nextCs : List Char) (hend : consumeStatementEnd r2 = .ok nextCs)
    (nextRoot : List (String × Node)) (hins : applyTableHeader path rt path = .ok nextRoot) :
    docTableBody fuel rest rt = parseDocumentFuel modelNumApi fuel nextCs path nextRoot := by
  have hskip_rb : skipHorizWs (']' :: r2) = ']' :: r2 := by
    simp [skipHorizWs, isHorizWs]
  simp only [docTableBody, hdk, hskip_rb, hend, hins, bind, Except.bind]

private theorem parseDoc_step_aot1_nl (k : String)
    (kc : Char) (kt : List Char) (hkc_list : k.toList = kc :: kt)
    (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_aot : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) ('[' :: '[' :: r) ap rt = docAotBody fuel r rt)
    (ap : List String) (root nextRoot : List (String × Node))
    (hins : applyAotHeader [k] root [k] = .ok nextRoot)
    (fuel : Nat) (rest : List Char) :
    parseDocumentFuel modelNumApi (fuel + 1) (("[[" ++ k ++ "]]").toList ++ '\n' :: rest) ap root =
      parseDocumentFuel modelNumApi fuel rest [k] nextRoot := by
  have hline : ("[[" ++ k ++ "]]").toList ++ '\n' :: rest =
      '[' :: '[' :: (k.toList ++ ']' :: ']' :: '\n' :: rest) := by
    have h1 : ("[[" : String).toList = ['[', '['] := by cbv
    have h2 : ("]]" : String).toList = [']', ']'] := by cbv
    simp only [String.toList_append, h1, h2, List.cons_append, List.nil_append, List.append_assoc]
  have hkc_bare : isBareKeyChar kc = true := by
    have ha := List.all_eq_true.mp hk_bare kc
    rw [hkc_list] at ha
    exact ha List.mem_cons_self
  have hkc_ws : isHorizWs kc = false := bareKeyChar_not_horizWs kc hkc_bare
  have hskip_k : skipHorizWs (k.toList ++ ']' :: ']' :: '\n' :: rest) =
      k.toList ++ ']' :: ']' :: '\n' :: rest := by
    rw [hkc_list, List.cons_append]
    have h1 : skipHorizWs (kc :: (kt ++ ']' :: ']' :: '\n' :: rest)) =
        if isHorizWs kc then skipHorizWs (kt ++ ']' :: ']' :: '\n' :: rest)
        else kc :: (kt ++ ']' :: ']' :: '\n' :: rest) := rfl
    rw [h1, hkc_ws]; simp
  have hdk : parseDottedKey (skipHorizWs (k.toList ++ ']' :: ']' :: '\n' :: rest)) =
      .ok ([k], ']' :: ']' :: '\n' :: rest) := by
    rw [hskip_k]
    exact parseDottedKey_single_aot k kc kt hkc_list hk_bare hkey_k ']' (by decide) (by decide) (by decide)
      (']' :: '\n' :: rest)
  have hend : consumeStatementEnd ('\n' :: rest) = .ok rest := by
    simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs]
  rw [hline, hdoc_aot]
  exact docAotBody_step fuel (k.toList ++ ']' :: ']' :: '\n' :: rest) root [k] ('\n' :: rest)
    hdk rest hend nextRoot hins

private theorem parseDoc_step_aot2_nl (k1 k2 : String)
    (kc1 : Char) (kt1 : List Char) (hk1_list : k1.toList = kc1 :: kt1)
    (hk1_bare : k1.toList.all isBareKeyChar = true)
    (hkey_k1 : ∀ r, parseKeySegment (kc1 :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc1 :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (kc2 : Char) (kt2 : List Char) (hk2_list : k2.toList = kc2 :: kt2)
    (hk2_bare : k2.toList.all isBareKeyChar = true)
    (hkey_k2 : ∀ r, parseKeySegment (kc2 :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc2 :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_aot : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) ('[' :: '[' :: r) ap rt = docAotBody fuel r rt)
    (ap : List String) (root nextRoot : List (String × Node))
    (hins : applyAotHeader [k1, k2] root [k1, k2] = .ok nextRoot)
    (fuel : Nat) (rest : List Char) :
    parseDocumentFuel modelNumApi (fuel + 1) (("[[" ++ k1 ++ "." ++ k2 ++ "]]").toList ++ '\n' :: rest) ap root =
      parseDocumentFuel modelNumApi fuel rest [k1, k2] nextRoot := by
  have hline : ("[[" ++ k1 ++ "." ++ k2 ++ "]]").toList ++ '\n' :: rest =
      '[' :: '[' :: (k1.toList ++ '.' :: (k2.toList ++ ']' :: ']' :: '\n' :: rest)) := by
    have h1 : ("[[" : String).toList = ['[', '['] := by cbv
    have hdot : ("." : String).toList = ['.'] := by cbv
    have h2 : ("]]" : String).toList = [']', ']'] := by cbv
    simp only [String.toList_append, h1, hdot, h2, List.cons_append, List.nil_append, List.append_assoc]
  have hk1_bare_c : isBareKeyChar kc1 = true := by
    have ha := List.all_eq_true.mp hk1_bare kc1
    rw [hk1_list] at ha
    exact ha List.mem_cons_self
  have hk1_ws : isHorizWs kc1 = false := bareKeyChar_not_horizWs kc1 hk1_bare_c
  have hskip_k : skipHorizWs (k1.toList ++ '.' :: (k2.toList ++ ']' :: ']' :: '\n' :: rest)) =
      k1.toList ++ '.' :: (k2.toList ++ ']' :: ']' :: '\n' :: rest) := by
    rw [hk1_list, List.cons_append]
    have h1 : skipHorizWs (kc1 :: (kt1 ++ '.' :: (k2.toList ++ ']' :: ']' :: '\n' :: rest))) =
        if isHorizWs kc1 then skipHorizWs (kt1 ++ '.' :: (k2.toList ++ ']' :: ']' :: '\n' :: rest))
        else kc1 :: (kt1 ++ '.' :: (k2.toList ++ ']' :: ']' :: '\n' :: rest)) := rfl
    rw [h1, hk1_ws]; simp
  have hdk : parseDottedKey (skipHorizWs (k1.toList ++ '.' :: (k2.toList ++ ']' :: ']' :: '\n' :: rest))) =
      .ok ([k1, k2], ']' :: ']' :: '\n' :: rest) := by
    rw [hskip_k]
    exact parseDottedKey_double_aot k1 k2 kc1 kt1 hk1_list hk1_bare hkey_k1
      kc2 kt2 hk2_list hk2_bare hkey_k2 ']' (by decide) (by decide) (by decide) (']' :: '\n' :: rest)
  have hend : consumeStatementEnd ('\n' :: rest) = .ok rest := by
    simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs]
  rw [hline, hdoc_aot]
  exact docAotBody_step fuel (k1.toList ++ '.' :: (k2.toList ++ ']' :: ']' :: '\n' :: rest)) root
    [k1, k2] ('\n' :: rest) hdk rest hend nextRoot hins

private theorem parseDoc_step_tbl2_nl (k1 k2 : String)
    (kt1 : List Char) (hk1_list : k1.toList = 'f' :: kt1)
    (hk1_bare : k1.toList.all isBareKeyChar = true)
    (hkey_k1 : ∀ r, parseKeySegment ('f' :: r) =
      (let (ks, rest) := takeBareKeyChars [] ('f' :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (kc2 : Char) (kt2 : List Char) (hk2_list : k2.toList = kc2 :: kt2)
    (hk2_bare : k2.toList.all isBareKeyChar = true)
    (hkey_k2 : ∀ r, parseKeySegment (kc2 :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc2 :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_tbl : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) ('[' :: 'f' :: r) ap rt = docTableBody fuel ('f' :: r) rt)
    (ap : List String) (root nextRoot : List (String × Node))
    (hins : applyTableHeader [k1, k2] root [k1, k2] = .ok nextRoot)
    (fuel : Nat) (rest : List Char) :
    parseDocumentFuel modelNumApi (fuel + 1) (("[" ++ k1 ++ "." ++ k2 ++ "]").toList ++ '\n' :: rest) ap root =
      parseDocumentFuel modelNumApi fuel rest [k1, k2] nextRoot := by
  have hline : ("[" ++ k1 ++ "." ++ k2 ++ "]").toList ++ '\n' :: rest =
      '[' :: 'f' :: (kt1 ++ '.' :: (k2.toList ++ ']' :: '\n' :: rest)) := by
    have h1 : ("[" : String).toList = ['['] := by cbv
    have hdot : ("." : String).toList = ['.'] := by cbv
    have h2 : ("]" : String).toList = [']'] := by cbv
    simp only [String.toList_append, h1, hdot, h2, hk1_list, List.cons_append, List.nil_append,
      List.append_assoc]
  have hskip_k : skipHorizWs (k1.toList ++ '.' :: (k2.toList ++ ']' :: '\n' :: rest)) =
      k1.toList ++ '.' :: (k2.toList ++ ']' :: '\n' :: rest) := by
    rw [hk1_list, List.cons_append]
    have h1 : skipHorizWs ('f' :: (kt1 ++ '.' :: (k2.toList ++ ']' :: '\n' :: rest))) =
        if isHorizWs 'f' then skipHorizWs (kt1 ++ '.' :: (k2.toList ++ ']' :: '\n' :: rest))
        else 'f' :: (kt1 ++ '.' :: (k2.toList ++ ']' :: '\n' :: rest)) := rfl
    rw [h1, (by decide : isHorizWs 'f' = false)]; simp
  have hdk : parseDottedKey (skipHorizWs (k1.toList ++ '.' :: (k2.toList ++ ']' :: '\n' :: rest))) =
      .ok ([k1, k2], ']' :: '\n' :: rest) := by
    rw [hskip_k]
    exact parseDottedKey_double_aot k1 k2 'f' kt1 hk1_list hk1_bare hkey_k1
      kc2 kt2 hk2_list hk2_bare hkey_k2 ']' (by decide) (by decide) (by decide) ('\n' :: rest)
  have hend : consumeStatementEnd ('\n' :: rest) = .ok rest := by
    simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs]
  rw [hline, hdoc_tbl]
  rw [← List.cons_append, ← hk1_list]
  exact docTableBody_step fuel (k1.toList ++ '.' :: (k2.toList ++ ']' :: '\n' :: rest)) root
    [k1, k2] ('\n' :: rest) hdk rest hend nextRoot hins

private theorem parseDottedKey_sp_eq_aot (k : String) (kc : Char) (kt : List Char)
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
    rw [takeBareKeyChars_append [] k.toList ' ' ('=' :: rest) hk_bare (by decide)]
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

private theorem parseDoc_step_str_gen (k v : String)
    (kc : Char) (kt : List Char) (hkc_list : k.toList = kc :: kt)
    (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_k : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) (kc :: r) ap rt = docKeyValBody fuel (kc :: r) ap rt)
    (vc : Char) (vt : List Char) (hvc_list : v.toList = vc :: vt)
    (hv_clean : v.toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true)
    (hval_v : ∀ fuel r, parseValueFuel modelNumApi (fuel + 1) ('"' :: vc :: r) =
      (parseBasicStringBody (vc :: r) >>= fun (s, after) => .ok (.string s, after)))
    (activePath : List String) (root nextRoot : List (String × Node))
    (hins : insertAtActivePath (activePath ++ [k]) root activePath [k] (valueToInlineNode (.string v)) = .ok nextRoot)
    (fuel : Nat) (sepRest nextRest : List Char)
    (hsep_end : consumeStatementEnd sepRest = .ok nextRest) :
    parseDocumentFuel modelNumApi (fuel + 1) ((k ++ " = \"" ++ v ++ "\"").toList ++ sepRest) activePath root =
      parseDocumentFuel modelNumApi fuel nextRest activePath nextRoot := by
  have hline : (k ++ " = \"" ++ v ++ "\"").toList ++ sepRest =
      k.toList ++ (' ' :: '=' :: ' ' :: '"' :: (v.toList ++ '"' :: sepRest)) := by
    have h1 : (" = \"" : String).toList = [' ', '=', ' ', '"'] := by cbv
    have h2 : ("\"" : String).toList = ['"'] := by cbv
    simp only [String.toList_append, h1, h2, List.cons_append, List.nil_append, List.append_assoc]
  have hdk : parseDottedKey ((k ++ " = \"" ++ v ++ "\"").toList ++ sepRest) =
      .ok ([k], '=' :: ' ' :: '"' :: (v.toList ++ '"' :: sepRest)) := by
    rw [hline]
    exact parseDottedKey_sp_eq_aot k kc kt hkc_list hk_bare hkey_k
      (' ' :: '"' :: (v.toList ++ '"' :: sepRest))
  have hpv : parseValue modelNumApi ('"' :: (v.toList ++ '"' :: sepRest)) = .ok (.string v, sepRest) :=
    parseValue_basic_aot v vc vt hvc_list hv_clean hval_v sepRest
  have hskip_eq : skipHorizWs ('=' :: ' ' :: '"' :: (v.toList ++ '"' :: sepRest)) =
      '=' :: ' ' :: '"' :: (v.toList ++ '"' :: sepRest) := by
    simp [skipHorizWs, isHorizWs]
  have hskip_q : skipHorizWs (' ' :: '"' :: (v.toList ++ '"' :: sepRest)) =
      '"' :: (v.toList ++ '"' :: sepRest) := by
    simp [skipHorizWs, isHorizWs]
  rw [hline, hkc_list, List.cons_append, hdoc_k]
  rw [← List.cons_append, ← hkc_list, ← hline]
  simp only [docKeyValBody, hdk, hskip_eq, hskip_q, hpv, hsep_end, hins, bind, Except.bind]

private theorem parseDoc_step_str_nl (k v : String)
    (kc : Char) (kt : List Char) (hkc_list : k.toList = kc :: kt)
    (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_k : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) (kc :: r) ap rt = docKeyValBody fuel (kc :: r) ap rt)
    (vc : Char) (vt : List Char) (hvc_list : v.toList = vc :: vt)
    (hv_clean : v.toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true)
    (hval_v : ∀ fuel r, parseValueFuel modelNumApi (fuel + 1) ('"' :: vc :: r) =
      (parseBasicStringBody (vc :: r) >>= fun (s, after) => .ok (.string s, after)))
    (activePath : List String) (root nextRoot : List (String × Node))
    (hins : insertAtActivePath (activePath ++ [k]) root activePath [k] (valueToInlineNode (.string v)) = .ok nextRoot)
    (fuel : Nat) (rest : List Char) :
    parseDocumentFuel modelNumApi (fuel + 1) ((k ++ " = \"" ++ v ++ "\"").toList ++ '\n' :: rest) activePath root =
      parseDocumentFuel modelNumApi fuel rest activePath nextRoot :=
  parseDoc_step_str_gen k v kc kt hkc_list hk_bare hkey_k hdoc_k vc vt hvc_list hv_clean hval_v
    activePath root nextRoot hins fuel ('\n' :: rest) rest
    (by simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs])

private theorem parseDoc_step_str_eof (k v : String)
    (kc : Char) (kt : List Char) (hkc_list : k.toList = kc :: kt)
    (hk_bare : k.toList.all isBareKeyChar = true)
    (hkey_k : ∀ r, parseKeySegment (kc :: r) =
      (let (ks, rest) := takeBareKeyChars [] (kc :: r)
       if ks.isEmpty then .error (mkErr .parseError "expected key")
       else .ok (String.ofList ks, rest)))
    (hdoc_k : ∀ fuel r ap rt,
      parseDocumentFuel modelNumApi (fuel + 1) (kc :: r) ap rt = docKeyValBody fuel (kc :: r) ap rt)
    (vc : Char) (vt : List Char) (hvc_list : v.toList = vc :: vt)
    (hv_clean : v.toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true)
    (hval_v : ∀ fuel r, parseValueFuel modelNumApi (fuel + 1) ('"' :: vc :: r) =
      (parseBasicStringBody (vc :: r) >>= fun (s, after) => .ok (.string s, after)))
    (activePath : List String) (root nextRoot : List (String × Node))
    (hins : insertAtActivePath (activePath ++ [k]) root activePath [k] (valueToInlineNode (.string v)) = .ok nextRoot)
    (fuel : Nat) :
    parseDocumentFuel modelNumApi (fuel + 1) (k ++ " = \"" ++ v ++ "\"").toList activePath root = .ok nextRoot := by
  rw [← List.append_nil (k ++ " = \"" ++ v ++ "\"").toList]
  rw [parseDoc_step_str_gen k v kc kt hkc_list hk_bare hkey_k hdoc_k vc vt hvc_list hv_clean hval_v
    activePath root nextRoot hins fuel [] [] rfl]
  cases fuel <;> rfl

private theorem skip_lb_aot : ∀ r, skipTriviaNewlines ('[' :: r) = '[' :: r :=
  skipTriviaNewlines_eq_of '[' (fun _ => rfl) (by decide) (by decide)

private theorem docAot_step :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('[' :: '[' :: r) ap rt = docAotBody fuel r rt :=
  docAot_eq skip_lb_aot

private theorem docTable_f_step :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('[' :: 'f' :: r) ap rt = docTableBody fuel ('f' :: r) rt :=
  docTable_f_aot skip_lb_aot

private theorem docKeyVal_n_aot :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('n' :: r) ap rt = docKeyValBody fuel ('n' :: r) ap rt :=
  docKeyVal_of 'n' (skipTriviaNewlines_eq_of 'n' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private theorem docKeyVal_c_aot :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('c' :: r) ap rt = docKeyValBody fuel ('c' :: r) ap rt :=
  docKeyVal_of 'c' (skipTriviaNewlines_eq_of 'c' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private def fruitsR1 : List (String × Node) := [("fruits", .aot [[]])]
private def fruitsR2 : List (String × Node) := [("fruits", .aot [[("name", valueToInlineNode (.string "apple"))]])]
private def fruitsR3 : List (String × Node) := [("fruits", .aot [[("name", valueToInlineNode (.string "apple")), ("physical", .table .explicit [])]])]
private def fruitsR4 : List (String × Node) := [("fruits", .aot [[("name", valueToInlineNode (.string "apple")), ("physical", .table .explicit [("color", valueToInlineNode (.string "red"))])]])]
private def fruitsR5 : List (String × Node) := [("fruits", .aot [[("name", valueToInlineNode (.string "apple")), ("physical", .table .explicit [("color", valueToInlineNode (.string "red"))]), ("varieties", .aot [[]])]])]
private def fruitsR6 : List (String × Node) := [("fruits", .aot [[("name", valueToInlineNode (.string "apple")), ("physical", .table .explicit [("color", valueToInlineNode (.string "red"))]), ("varieties", .aot [[("name", valueToInlineNode (.string "fuji"))]])]])]
private def fruitsR7 : List (String × Node) := [("fruits", .aot [[("name", valueToInlineNode (.string "apple")), ("physical", .table .explicit [("color", valueToInlineNode (.string "red"))]), ("varieties", .aot [[("name", valueToInlineNode (.string "fuji"))]])], []])]
private def fruitsR8 : List (String × Node) := [("fruits", .aot [[("name", valueToInlineNode (.string "apple")), ("physical", .table .explicit [("color", valueToInlineNode (.string "red"))]), ("varieties", .aot [[("name", valueToInlineNode (.string "fuji"))]])], [("name", valueToInlineNode (.string "orange"))]])]
private def fruitsR9 : List (String × Node) := [("fruits", .aot [[("name", valueToInlineNode (.string "apple")), ("physical", .table .explicit [("color", valueToInlineNode (.string "red"))]), ("varieties", .aot [[("name", valueToInlineNode (.string "fuji"))]])], [("name", valueToInlineNode (.string "orange")), ("varieties", .aot [[]])]])]
private def fruitsR10 : List (String × Node) := [("fruits", .aot [[("name", valueToInlineNode (.string "apple")), ("physical", .table .explicit [("color", valueToInlineNode (.string "red"))]), ("varieties", .aot [[("name", valueToInlineNode (.string "fuji"))]])], [("name", valueToInlineNode (.string "orange")), ("varieties", .aot [[("name", valueToInlineNode (.string "navel"))]])]])]

private theorem fruits_h1 : applyAotHeader ["fruits"] [] ["fruits"] = .ok fruitsR1 := by cbv
private theorem fruits_h2 : insertAtActivePath ["fruits", "name"] fruitsR1 ["fruits"] ["name"] (valueToInlineNode (.string "apple")) = .ok fruitsR2 := by cbv
private theorem fruits_h3 : applyTableHeader ["fruits", "physical"] fruitsR2 ["fruits", "physical"] = .ok fruitsR3 := by cbv
private theorem fruits_h4 : insertAtActivePath ["fruits", "physical", "color"] fruitsR3 ["fruits", "physical"] ["color"] (valueToInlineNode (.string "red")) = .ok fruitsR4 := by cbv
private theorem fruits_h5 : applyAotHeader ["fruits", "varieties"] fruitsR4 ["fruits", "varieties"] = .ok fruitsR5 := by cbv
private theorem fruits_h6 : insertAtActivePath ["fruits", "varieties", "name"] fruitsR5 ["fruits", "varieties"] ["name"] (valueToInlineNode (.string "fuji")) = .ok fruitsR6 := by cbv
private theorem fruits_h7 : applyAotHeader ["fruits"] fruitsR6 ["fruits"] = .ok fruitsR7 := by cbv
private theorem fruits_h8 : insertAtActivePath ["fruits", "name"] fruitsR7 ["fruits"] ["name"] (valueToInlineNode (.string "orange")) = .ok fruitsR8 := by cbv
private theorem fruits_h9 : applyAotHeader ["fruits", "varieties"] fruitsR8 ["fruits", "varieties"] = .ok fruitsR9 := by cbv
private theorem fruits_h10 : insertAtActivePath ["fruits", "varieties", "name"] fruitsR9 ["fruits", "varieties"] ["name"] (valueToInlineNode (.string "navel")) = .ok fruitsR10 := by cbv

private theorem fruits_beq :
    tomlValueBeq
      (.table #[("fruits", .array #[
        .table #[("name", .string "apple"),
                 ("physical", .table #[("color", .string "red")]),
                 ("varieties", .array #[.table #[("name", .string "fuji")]])],
        .table #[("name", .string "orange"),
                 ("varieties", .array #[.table #[("name", .string "navel")]])]])])
      (.table (entriesToTomlList fruitsR10).toArray) = true := by
  cbv

private def fruitsStr : String :=
  "[[fruits]]\nname = \"apple\"\n[fruits.physical]\ncolor = \"red\"\n[[fruits.varieties]]\nname = \"fuji\"\n[[fruits]]\nname = \"orange\"\n[[fruits.varieties]]\nname = \"navel\""

private theorem fruits_clean :
    fruitsStr.toList.all (fun c => !isDisallowedControl c && c != '\r') = true := by
  cbv

private def fruitsRest6 : List Char :=
  ("name" ++ " = \"" ++ "fuji" ++ "\"").toList ++ '\n' ::
  (("[[" ++ "fruits" ++ "]]").toList ++ '\n' ::
  (("name" ++ " = \"" ++ "orange" ++ "\"").toList ++ '\n' ::
  (("[[" ++ "fruits" ++ "." ++ "varieties" ++ "]]").toList ++ '\n' ::
  ("name" ++ " = \"" ++ "navel" ++ "\"").toList)))

private theorem fruits_hs_eq :
    fruitsStr.toList =
      ("[[" ++ "fruits" ++ "]]").toList ++ '\n' ::
      (("name" ++ " = \"" ++ "apple" ++ "\"").toList ++ '\n' ::
      (("[" ++ "fruits" ++ "." ++ "physical" ++ "]").toList ++ '\n' ::
      (("color" ++ " = \"" ++ "red" ++ "\"").toList ++ '\n' ::
      (("[[" ++ "fruits" ++ "." ++ "varieties" ++ "]]").toList ++ '\n' ::
      fruitsRest6)))) := by
  cbv

private theorem fruits_list : ("fruits" : String).toList = ['f', 'r', 'u', 'i', 't', 's'] := by cbv
private theorem fruits_bare : ("fruits" : String).toList.all isBareKeyChar = true := by cbv
private theorem name_list : ("name" : String).toList = ['n', 'a', 'm', 'e'] := by cbv
private theorem name_bare : ("name" : String).toList.all isBareKeyChar = true := by cbv
private theorem color_list : ("color" : String).toList = ['c', 'o', 'l', 'o', 'r'] := by cbv
private theorem color_bare : ("color" : String).toList.all isBareKeyChar = true := by cbv
private theorem physical_list : ("physical" : String).toList = ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l'] := by cbv
private theorem physical_bare : ("physical" : String).toList.all isBareKeyChar = true := by cbv
private theorem varieties_list : ("varieties" : String).toList = ['v', 'a', 'r', 'i', 'e', 't', 'i', 'e', 's'] := by cbv
private theorem varieties_bare : ("varieties" : String).toList.all isBareKeyChar = true := by cbv
private theorem apple_list : ("apple" : String).toList = ['a', 'p', 'p', 'l', 'e'] := by cbv
private theorem apple_clean : ("apple" : String).toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true := by cbv
private theorem red_list : ("red" : String).toList = ['r', 'e', 'd'] := by cbv
private theorem red_clean : ("red" : String).toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true := by cbv
private theorem fuji_list : ("fuji" : String).toList = ['f', 'u', 'j', 'i'] := by cbv
private theorem fuji_clean : ("fuji" : String).toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true := by cbv
private theorem orange_list : ("orange" : String).toList = ['o', 'r', 'a', 'n', 'g', 'e'] := by cbv
private theorem orange_clean : ("orange" : String).toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true := by cbv
private theorem navel_list : ("navel" : String).toList = ['n', 'a', 'v', 'e', 'l'] := by cbv
private theorem navel_clean : ("navel" : String).toList.all (fun c => c != '\n' && c != '"' && c != '\\') = true := by cbv

private theorem fruits_hdoc_tail (f : Nat) :
    parseDocumentFuel modelNumApi ((((f + 1) + 1) + 1) + 1 + 1) fruitsRest6 ["fruits", "varieties"] fruitsR5 = .ok fruitsR10 := by
  unfold fruitsRest6
  rw [parseDoc_step_str_nl "name" "fuji" 'n' ['a', 'm', 'e'] name_list name_bare
    (fun _ => rfl) docKeyVal_n_aot 'f' ['u', 'j', 'i'] fuji_list fuji_clean
    (fun _ _ => rfl) ["fruits", "varieties"] fruitsR5 fruitsR6 fruits_h6]
  rw [parseDoc_step_aot1_nl "fruits" 'f' ['r', 'u', 'i', 't', 's'] fruits_list fruits_bare
    (fun _ => rfl) docAot_step ["fruits", "varieties"] fruitsR6 fruitsR7 fruits_h7]
  rw [parseDoc_step_str_nl "name" "orange" 'n' ['a', 'm', 'e'] name_list name_bare
    (fun _ => rfl) docKeyVal_n_aot 'o' ['r', 'a', 'n', 'g', 'e'] orange_list orange_clean
    (fun _ _ => rfl) ["fruits"] fruitsR7 fruitsR8 fruits_h8]
  rw [parseDoc_step_aot2_nl "fruits" "varieties" 'f' ['r', 'u', 'i', 't', 's'] fruits_list fruits_bare
    (fun _ => rfl) 'v' ['a', 'r', 'i', 'e', 't', 'i', 'e', 's'] varieties_list varieties_bare
    (fun _ => rfl) docAot_step ["fruits"] fruitsR8 fruitsR9 fruits_h9]
  exact parseDoc_step_str_eof "name" "navel" 'n' ['a', 'm', 'e'] name_list name_bare
    (fun _ => rfl) docKeyVal_n_aot 'n' ['a', 'v', 'e', 'l'] navel_list navel_clean
    (fun _ _ => rfl) ["fruits", "varieties"] fruitsR9 fruitsR10 fruits_h10 f

private theorem fruits_hdoc :
    parseDocumentFuel modelNumApi (fruitsStr.toList.length + 1) fruitsStr.toList [] [] = .ok fruitsR10 := by
  have hlen_tail : fruitsRest6.length ≥ 4 := by
    unfold fruitsRest6
    simp only [List.length_append, List.length_cons]
    omega
  have hlen : fruitsStr.toList.length + 1 ≥ 10 := by
    rw [fruits_hs_eq]
    simp only [List.length_append, List.length_cons]
    omega
  have hsplit : ∃ f, fruitsStr.toList.length + 1 = (((((((((f + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 :=
    ⟨fruitsStr.toList.length + 1 - 10, by omega⟩
  rcases hsplit with ⟨f, hf⟩
  rw [hf, fruits_hs_eq]
  rw [parseDoc_step_aot1_nl "fruits" 'f' ['r', 'u', 'i', 't', 's'] fruits_list fruits_bare
    (fun _ => rfl) docAot_step [] [] fruitsR1 fruits_h1]
  rw [parseDoc_step_str_nl "name" "apple" 'n' ['a', 'm', 'e'] name_list name_bare
    (fun _ => rfl) docKeyVal_n_aot 'a' ['p', 'p', 'l', 'e'] apple_list apple_clean
    (fun _ _ => rfl) ["fruits"] fruitsR1 fruitsR2 fruits_h2]
  rw [parseDoc_step_tbl2_nl "fruits" "physical" ['r', 'u', 'i', 't', 's'] fruits_list fruits_bare
    (fun _ => rfl) 'p' ['h', 'y', 's', 'i', 'c', 'a', 'l'] physical_list physical_bare
    (fun _ => rfl) docTable_f_step ["fruits"] fruitsR2 fruitsR3 fruits_h3]
  rw [parseDoc_step_str_nl "color" "red" 'c' ['o', 'l', 'o', 'r'] color_list color_bare
    (fun _ => rfl) docKeyVal_c_aot 'r' ['e', 'd'] red_list red_clean
    (fun _ _ => rfl) ["fruits", "physical"] fruitsR3 fruitsR4 fruits_h4]
  rw [parseDoc_step_aot2_nl "fruits" "varieties" 'f' ['r', 'u', 'i', 't', 's'] fruits_list fruits_bare
    (fun _ => rfl) 'v' ['a', 'r', 'i', 'e', 't', 'i', 'e', 's'] varieties_list varieties_bare
    (fun _ => rfl) docAot_step ["fruits", "physical"] fruitsR4 fruitsR5 fruits_h5]
  exact fruits_hdoc_tail f

private theorem fruits_valid :
    checkOneOkModel
      (fruitsStr,
        #[("fruits", .array #[
          .table #[("name", .string "apple"),
                   ("physical", .table #[("color", .string "red")]),
                   ("varieties", .array #[.table #[("name", .string "fuji")]])],
          .table #[("name", .string "orange"),
                   ("varieties", .array #[.table #[("name", .string "navel")]])]])]) = true := by
  have hnorm : normalizeChars 1 1 fruitsStr.toList = .ok fruitsStr.toList :=
    normalizeChars_clean _ fruits_clean 1 1
  simp only [checkOneOkModel, parseWithNum, hnorm, fruits_hdoc, bind, Except.bind]
  exact fruits_beq

private theorem aotOk_0 :
    ((inlineAotOkCases.drop 0).head?.map checkOneOkModel).getD false = true := by
  simp only [inlineAotOkCases, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]
  cbv

set_option maxRecDepth 2048 in
private theorem aotOk_1 :
    ((inlineAotOkCases.drop 1).head?.map checkOneOkModel).getD false = true := by
  simp only [inlineAotOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  cbv

private theorem aotOk_2 :
    ((inlineAotOkCases.drop 2).head?.map checkOneOkModel).getD false = true := by
  simp only [inlineAotOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  cbv

set_option maxRecDepth 2048 in
private theorem aotOk_3 :
    ((inlineAotOkCases.drop 3).head?.map checkOneOkModel).getD false = true := by
  simp only [inlineAotOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  cbv

private theorem aotOk_4 :
    ((inlineAotOkCases.drop 4).head?.map checkOneOkModel).getD false = true := by
  simp only [inlineAotOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  have h := fruits_valid
  unfold fruitsStr at h
  exact h

private theorem aotOk_5 :
    ((inlineAotOkCases.drop 5).head?.map checkOneOkModel).getD false = true := by
  simp only [inlineAotOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  cbv

private theorem aotErr_0 :
    ((inlineAotErrCases.drop 0).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_1 :
    ((inlineAotErrCases.drop 1).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_2 :
    ((inlineAotErrCases.drop 2).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_3 :
    ((inlineAotErrCases.drop 3).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_4 :
    ((inlineAotErrCases.drop 4).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_5 :
    ((inlineAotErrCases.drop 5).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_6 :
    ((inlineAotErrCases.drop 6).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_7 :
    ((inlineAotErrCases.drop 7).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_8 :
    ((inlineAotErrCases.drop 8).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_9 :
    ((inlineAotErrCases.drop 9).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_10 :
    ((inlineAotErrCases.drop 10).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_11 :
    ((inlineAotErrCases.drop 11).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_12 :
    ((inlineAotErrCases.drop 12).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_13 :
    ((inlineAotErrCases.drop 13).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem aotErr_14 :
    ((inlineAotErrCases.drop 14).head?.map checkOneErrModel).getD false = true := by
  simp only [inlineAotErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

private theorem list_all_six_aot {α : Type} (p : α → Bool) (l : List α) (hlen : l.length = 6)
    (h0 : ((l.drop 0).head?.map p).getD false = true)
    (h1 : ((l.drop 1).head?.map p).getD false = true)
    (h2 : ((l.drop 2).head?.map p).getD false = true)
    (h3 : ((l.drop 3).head?.map p).getD false = true)
    (h4 : ((l.drop 4).head?.map p).getD false = true)
    (h5 : ((l.drop 5).head?.map p).getD false = true) :
    l.all p = true := by
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩ <;> simp at hlen
  simp only [List.drop_zero, List.drop_succ_cons, List.head?_cons, Option.map_some,
    Option.getD_some] at h0 h1 h2 h3 h4 h5
  simp [h0, h1, h2, h3, h4, h5]

private theorem list_all_fifteen_aot {α : Type} (p : α → Bool) (l : List α) (hlen : l.length = 15)
    (h0 : ((l.drop 0).head?.map p).getD false = true)
    (h1 : ((l.drop 1).head?.map p).getD false = true)
    (h2 : ((l.drop 2).head?.map p).getD false = true)
    (h3 : ((l.drop 3).head?.map p).getD false = true)
    (h4 : ((l.drop 4).head?.map p).getD false = true)
    (h5 : ((l.drop 5).head?.map p).getD false = true)
    (h6 : ((l.drop 6).head?.map p).getD false = true)
    (h7 : ((l.drop 7).head?.map p).getD false = true)
    (h8 : ((l.drop 8).head?.map p).getD false = true)
    (h9 : ((l.drop 9).head?.map p).getD false = true)
    (h10 : ((l.drop 10).head?.map p).getD false = true)
    (h11 : ((l.drop 11).head?.map p).getD false = true)
    (h12 : ((l.drop 12).head?.map p).getD false = true)
    (h13 : ((l.drop 13).head?.map p).getD false = true)
    (h14 : ((l.drop 14).head?.map p).getD false = true) :
    l.all p = true := by
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, t⟩⟩⟩⟩⟩ <;> simp at hlen
  rcases t with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, u⟩⟩⟩⟩⟩ <;> simp at hlen
  rcases u with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen
  simp only [List.drop_zero, List.drop_succ_cons, List.head?_cons, Option.map_some,
    Option.getD_some] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

/-- Verify `inlineAotOkCases` under `modelNumApi`. -/
theorem inlineAotOk_model_valid : inlineAotOkCases.all checkOneOkModel = true :=
  list_all_six_aot checkOneOkModel inlineAotOkCases rfl
    aotOk_0 aotOk_1 aotOk_2 aotOk_3 aotOk_4 aotOk_5

/-- Verify `inlineAotErrCases` under `modelNumApi`. -/
theorem inlineAotErr_model_valid : inlineAotErrCases.all checkOneErrModel = true :=
  list_all_fifteen_aot checkOneErrModel inlineAotErrCases rfl
    aotErr_0 aotErr_1 aotErr_2 aotErr_3 aotErr_4
    aotErr_5 aotErr_6 aotErr_7 aotErr_8 aotErr_9
    aotErr_10 aotErr_11 aotErr_12 aotErr_13 aotErr_14

end LeanSwe.Toml.Proofs
