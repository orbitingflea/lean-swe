import LeanSweProofs.Toml.Proofs.RenderInjectiveMlStr

/-!
# Unified String Literal Left-Inverse for `Toml.Model.render`

Proves `readMlLiteralBody_list` and `readStringVal_renderStringLiteral` across all
four TOML 1.0 string literal forms (`"..."`, `"""..."""`, `'...'`, `'''...'''`).
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model

/-- Pure left-inverse decoder for multiline literal string bodies after `'''` (and optional opener `\n`). -/
def readMlLiteralBody : List Char → Option (List Char × List Char)
  | [] => none
  | '\'' :: '\'' :: '\'' :: '\'' :: '\'' :: '\'' :: _ => none
  | '\'' :: '\'' :: '\'' :: '\'' :: '\'' :: rest => some (['\'', '\''], rest)
  | '\'' :: '\'' :: '\'' :: '\'' :: rest => some (['\''], rest)
  | '\'' :: '\'' :: '\'' :: rest => some ([], rest)
  | c :: rest => (readMlLiteralBody rest).map fun (cs, rem) => (c :: cs, rem)

private def utf8SumM : List Char → Nat | [] => 0 | c :: cs => c.utf8Size + utf8SumM cs

private theorem utf8SumM_append (a b : List Char) : utf8SumM (a ++ b) = utf8SumM a + utf8SumM b := by
  induction a <;> simp_all [utf8SumM, Nat.add_assoc]

private theorem utf8ByteSize_eq_utf8SumM (s : String) : s.utf8ByteSize = utf8SumM s.toList := by
  suffices ∀ cs, (String.ofList cs).utf8ByteSize = utf8SumM cs by simpa [String.ofList_toList] using this s.toList
  intro cs; induction cs with
  | nil => rfl
  | cons c cs ih => rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih, utf8SumM]

private theorem utf8GetAux_append_addM (a b : List Char) (i₀ : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (a ++ b) i₀ ⟨i₀.byteIdx + utf8SumM a⟩ =
      String.Pos.Raw.utf8GetAux b ⟨i₀.byteIdx + utf8SumM a⟩ ⟨i₀.byteIdx + utf8SumM a⟩ := by
  induction a generalizing i₀ with
  | nil => simp [utf8SumM]
  | cons c cs ih =>
    simp only [List.cons_append, utf8SumM]; rw [String.Pos.Raw.utf8GetAux.eq_def]
    have hpos := Char.utf8Size_pos c
    have hne : i₀ ≠ ⟨i₀.byteIdx + (c.utf8Size + utf8SumM cs)⟩ := fun heq => by
      have : i₀.byteIdx = i₀.byteIdx + (c.utf8Size + utf8SumM cs) := congrArg String.Pos.Raw.byteIdx heq; omega
    simp only [hne, ↓reduceIte, show i₀ + c = ⟨i₀.byteIdx + c.utf8Size⟩ from String.Pos.Raw.ext String.Pos.Raw.byteIdx_add_char]
    rw [show i₀.byteIdx + (c.utf8Size + utf8SumM cs) = (i₀.byteIdx + c.utf8Size) + utf8SumM cs by omega]
    exact ih _

private theorem get_at_utf8SumM (s : String) (a : List Char) (c : Char) (b : List Char) (h : s.toList = a ++ c :: b) :
    String.Pos.Raw.get s ⟨utf8SumM a⟩ = c ∧ String.Pos.Raw.next s ⟨utf8SumM a⟩ = ⟨utf8SumM a + c.utf8Size⟩ ∧
      String.Pos.Raw.atEnd s ⟨utf8SumM a⟩ = false := by
  have hget : String.Pos.Raw.get s ⟨utf8SumM a⟩ = c := by
    change String.Pos.Raw.utf8GetAux s.toList 0 ⟨utf8SumM a⟩ = c
    rw [h, show (⟨utf8SumM a⟩ : String.Pos.Raw) = ⟨(0 : String.Pos.Raw).byteIdx + utf8SumM a⟩ by simp [String.Pos.Raw.byteIdx_zero],
      utf8GetAux_append_addM a (c :: b) 0, String.Pos.Raw.utf8GetAux.eq_def]; simp
  refine ⟨hget, String.Pos.Raw.ext (by change ((⟨utf8SumM a⟩ : String.Pos.Raw) + String.Pos.Raw.get s ⟨utf8SumM a⟩).byteIdx = _; rw [hget]; exact String.Pos.Raw.byteIdx_add_char), ?_⟩
  rw [String.Pos.Raw.atEnd.eq_1, decide_eq_false_iff_not]
  have hsz : s.utf8ByteSize = utf8SumM a + (c.utf8Size + utf8SumM b) := by rw [utf8ByteSize_eq_utf8SumM, h, utf8SumM_append, utf8SumM]
  have := Char.utf8Size_pos c; dsimp only; omega

private theorem splitOnAux_length_geM (s sep : String) (b i j : String.Pos.Raw) (r : List String) :
    r.length + 1 ≤ (s.splitOnAux sep b i j r).length := by
  fun_induction String.splitOnAux s sep b i j r <;> simp_all +zetaDelta <;> omega

private theorem splitOnAux_tripleQuoteM (s : String) (b i j : String.Pos.Raw) (r : List String) :
    ∀ (pref rem : List Char) (k : Nat), k < 3 → j = ⟨k⟩ → i = ⟨utf8SumM pref + k⟩ →
      s.toList = pref ++ (List.replicate k '\'' ++ rem) →
      (∃ a b', List.replicate k '\'' ++ rem = a ++ ['\'', '\'', '\''] ++ b') →
      r.length + 2 ≤ (s.splitOnAux "'''" b i j r).length := by
  have hrep_sum : ∀ pref k, utf8SumM (pref ++ List.replicate k '\'') = utf8SumM pref + k := fun pref k => by
    rw [utf8SumM_append]; suffices utf8SumM (List.replicate k '\'') = k by rw [this]
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, utf8SumM, ih]; change 1 + k = k + 1; omega
  have hsep_all : ∀ k, k < 3 → String.Pos.Raw.get "'''" ⟨k⟩ = '\'' ∧ String.Pos.Raw.next "'''" ⟨k⟩ = ⟨k + 1⟩ ∧
      String.Pos.Raw.atEnd "'''" ⟨k + 1⟩ = decide (k = 2) :=
    fun k hk => by match k with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => omega
  fun_induction String.splitOnAux s "'''" b i j r with
  | case1 b i j r hati =>
    intro pref rem k _ _ hi hs ⟨a, b', hab⟩
    cases rem with
    | nil => have := congrArg List.length hab; simp at this; omega
    | cons c rem' =>
      have hat := (get_at_utf8SumM s (pref ++ List.replicate k '\'') c rem' (by simp [hs])).2.2
      rw [hrep_sum, ← hi] at hat; simp [hat] at hati
  | case2 b i j r _ _ _ _ _ _ =>
    intro _ _ _ _ _ _ _ _
    have hge := splitOnAux_length_geM s "'''" (String.Pos.Raw.next s i) (String.Pos.Raw.next s i) 0
      (String.Pos.Raw.extract s b ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next "'''" j)) :: r)
    simp at hge; omega
  | case3 b i j r _ hmatch _ _ hatj ih =>
    intro pref rem k hk hj hi hs ⟨a, b', hab⟩
    cases rem with
    | nil => have := congrArg List.length hab; simp at this; omega
    | cons c rem' =>
      have hsep := hsep_all k hk
      obtain ⟨hget, hnext, _⟩ := get_at_utf8SumM s (pref ++ List.replicate k '\'') c rem' (by simp [hs])
      rw [hrep_sum] at hget hnext
      have hc : c = '\'' := by simpa [hi, hj, hget, hsep.1] using hmatch
      subst hc
      have hk2 : k + 1 < 3 := by
        have hatj' : ¬ String.Pos.Raw.atEnd "'''" (String.Pos.Raw.next "'''" j) = true := hatj
        rw [hj, hsep.2.1, hsep.2.2] at hatj'; simp at hatj'; omega
      have hrep : List.replicate (k + 1) '\'' ++ rem' = List.replicate k '\'' ++ '\'' :: rem' := by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      exact ih pref rem' (k + 1) hk2 (by change String.Pos.Raw.next "'''" j = _; rw [hj, hsep.2.1])
        (by change String.Pos.Raw.next s i = _; rw [hi, hnext]; exact String.Pos.Raw.ext (by dsimp; change utf8SumM pref + k + 1 = _; omega))
        (by rw [hrep]; exact hs) ⟨a, b', by rw [hrep]; exact hab⟩
  | case4 b i j r _ hmatch ih =>
    intro pref rem k hk hj hi hs ⟨a, b', hab⟩
    cases rem with
    | nil => have := congrArg List.length hab; simp at this; omega
    | cons c rem' =>
      have hsep := (hsep_all k hk).1
      obtain ⟨hget, _, _⟩ := get_at_utf8SumM s (pref ++ List.replicate k '\'') c rem' (by simp [hs])
      rw [hrep_sum] at hget
      have hc : c ≠ '\'' := by simpa [hi, hj, hget, hsep] using hmatch
      have hun : i.unoffsetBy j = ⟨utf8SumM pref⟩ := by rw [hi, hj]; apply String.Pos.Raw.ext; dsimp [String.Pos.Raw.unoffsetBy]; omega
      cases hrep_eq : List.replicate k '\'' ++ c :: rem' with
      | nil => cases k <;> simp at hrep_eq
      | cons c0 suf' =>
        obtain ⟨_, hnext0, _⟩ := get_at_utf8SumM s pref c0 suf' (by rw [hs, hrep_eq])
        have ha_ne : a ≠ [] := by
          rintro rfl; have h1 := congrArg (·[k]?) hab; rw [List.getElem?_append_right (by simp)] at h1
          simp only [List.length_replicate, Nat.sub_self, List.getElem?_cons_zero] at h1
          rw [show (([] ++ ['\'', '\'', '\''] ++ b')[k]?) = some '\'' by match k with | 0 => rfl | 1 => rfl | 2 => rfl | _ + 3 => omega] at h1
          exact hc (Option.some.inj h1)
        rcases List.exists_cons_of_ne_nil ha_ne with ⟨a0, as, rfl⟩
        rw [hrep_eq] at hab; injection hab with _ hsuf'
        exact ih (pref ++ [c0]) suf' 0 (by decide) rfl
          (by rw [hun, hnext0]; simp [utf8SumM_append, utf8SumM]) (by simp [hs, hrep_eq]) ⟨as, b', by simpa using hsuf'⟩

/-- `!containsSubstr s "'''"` implies `s.toList` has no 3 consecutive single quotes. -/
theorem no_triple_single_quote_of_not_containsSubstr (s : String) (h : containsSubstr s "'''" = false) :
    ∀ a b : List Char, s.toList ≠ a ++ ['\'', '\'', '\''] ++ b := by
  intro a b hab
  simp only [containsSubstr, decide_eq_false_iff_not, Nat.not_lt] at h
  rw [show s.splitOn "'''" = s.splitOnAux "'''" 0 0 0 [] by simp [String.splitOn, show ("'''" == "") = false from rfl]] at h
  have hge := splitOnAux_tripleQuoteM s 0 0 0 [] [] s.toList 0 (by decide) rfl rfl (by simp) ⟨a, b, hab⟩
  simp at hge; omega

private theorem readMlLiteralBody_close3 {rem : List Char} (hrem : ∀ c r, rem = c :: r → c ≠ '\'') :
    readMlLiteralBody ('\'' :: '\'' :: '\'' :: rem) = some ([], rem) := by
  (conv => lhs; unfold readMlLiteralBody)
  split
  · contradiction
  · rename_i _ heq; exact False.elim (hrem '\'' _ (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2 rfl)
  · rename_i _ heq; exact False.elim (hrem '\'' _ (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2 rfl)
  · rename_i _ heq; exact False.elim (hrem '\'' _ (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2 rfl)
  · rename_i r heq; obtain ⟨_, rfl⟩ := List.cons.inj (List.cons.inj (List.cons.inj heq).2).2; rfl
  · rename_i _ _ _ _ hnot3 heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hnot3 rem rfl h1.symm)

private theorem readMlLiteralBody_close4 {rem : List Char} (hrem : ∀ c r, rem = c :: r → c ≠ '\'') :
    readMlLiteralBody ('\'' :: '\'' :: '\'' :: '\'' :: rem) = some (['\''], rem) := by
  (conv => lhs; unfold readMlLiteralBody)
  split
  · contradiction
  · rename_i _ heq; exact False.elim (hrem '\'' _ (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2 rfl)
  · rename_i _ heq; exact False.elim (hrem '\'' _ (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2 rfl)
  · rename_i r heq; obtain ⟨_, rfl⟩ := List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2; rfl
  · rename_i _ hnot4 heq; exact False.elim (hnot4 rem (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2.symm)
  · rename_i _ _ _ _ hnot3 heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hnot3 ('\'' :: rem) rfl h1.symm)

private theorem readMlLiteralBody_close5 {rem : List Char} (hrem : ∀ c r, rem = c :: r → c ≠ '\'') :
    readMlLiteralBody ('\'' :: '\'' :: '\'' :: '\'' :: '\'' :: rem) = some (['\'', '\''], rem) := by
  (conv => lhs; unfold readMlLiteralBody)
  split
  · contradiction
  · rename_i _ heq; exact False.elim (hrem '\'' _ (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2).2 rfl)
  · rename_i r heq; obtain ⟨_, rfl⟩ := List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2; rfl
  · rename_i _ _ hnot5 heq; exact False.elim (hnot5 rem (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2.symm)
  · rename_i _ _ hnot4 heq; exact False.elim (hnot4 ('\'' :: rem) (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2.symm)
  · rename_i _ _ _ _ hnot3 heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hnot3 ('\'' :: '\'' :: rem) rfl h1.symm)

theorem readMlLiteralBody_list :
    ∀ (cs rem : List Char), (∀ a b, cs ≠ a ++ ['\'', '\'', '\''] ++ b) →
      (∀ c r, rem = c :: r → c ≠ '\'') →
      readMlLiteralBody (cs ++ ['\'', '\'', '\''] ++ rem) = some (cs, rem)
  | [], rem, _, hrem => readMlLiteralBody_close3 hrem
  | c :: cs, rem, hno3, hrem => by
    have hstep (tail : List Char) (hn3 : ¬(c = '\'' ∧ ∃ t, tail = '\'' :: '\'' :: t)) :
        readMlLiteralBody (c :: tail) = (readMlLiteralBody tail).map fun (out, r) => (c :: out, r) := by
      (conv => lhs; unfold readMlLiteralBody)
      split
      · contradiction
      · rename_i r heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hn3 ⟨rfl, _, h1⟩)
      · rename_i r heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hn3 ⟨rfl, _, h1⟩)
      · rename_i r heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hn3 ⟨rfl, _, h1⟩)
      · rename_i r heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hn3 ⟨rfl, _, h1⟩)
      · rename_i c' rest' _ _ _ _ heq; obtain ⟨rfl, rfl⟩ := List.cons.inj heq; rfl
    rcases cs with _ | ⟨c1, _ | ⟨c2, cs2⟩⟩
    · by_cases hc : c = '\''
      · subst hc; exact readMlLiteralBody_close4 hrem
      · change readMlLiteralBody (c :: (['\'', '\'', '\''] ++ rem)) = some ([c], rem)
        rw [hstep _ (fun ⟨heq, _⟩ => hc heq)]
        change (readMlLiteralBody ('\'' :: '\'' :: '\'' :: rem)).map _ = _
        rw [readMlLiteralBody_close3 hrem]; rfl
    · by_cases hboth : c = '\'' ∧ c1 = '\''
      · rcases hboth with ⟨rfl, rfl⟩; exact readMlLiteralBody_close5 hrem
      · have hn3 : ¬(c = '\'' ∧ ∃ t, (c1 :: ['\'', '\'', '\''] ++ rem) = '\'' :: '\'' :: t) := by
          rintro ⟨hc, t, ht⟩; simp only [List.cons_append, List.cons.injEq] at ht; exact hboth ⟨hc, ht.1⟩
        change readMlLiteralBody (c :: (c1 :: ['\'', '\'', '\''] ++ rem)) = _
        rw [hstep _ hn3]
        simpa using readMlLiteralBody_list [c1] rem (fun a b h => hno3 (c :: a) b (by simp [h])) hrem
    · have hn3 : ¬(c = '\'' ∧ ∃ t, (c1 :: c2 :: cs2 ++ ['\'', '\'', '\''] ++ rem) = '\'' :: '\'' :: t) := by
        rintro ⟨rfl, t, ht⟩; simp only [List.cons_append, List.cons.injEq] at ht
        exact hno3 [] cs2 (by simp [ht.1, ht.2.1])
      change readMlLiteralBody (c :: (c1 :: c2 :: cs2 ++ ['\'', '\'', '\''] ++ rem)) = _
      rw [hstep _ hn3]
      simpa [List.cons_append, List.append_assoc] using
        readMlLiteralBody_list (c1 :: c2 :: cs2) rem (fun a b h => hno3 (c :: a) b (by simp [h])) hrem

/-- Unified left-inverse decoder for all four TOML 1.0 string literal forms. -/
def readStringVal : List Char → Option (String × List Char)
  | '"' :: '"' :: '"' :: '\n' :: rest => (readMlBasicBody rest).map fun (cs, rem) => (String.ofList cs, rem)
  | '"' :: '"' :: '"' :: rest => (readMlBasicBody rest).map fun (cs, rem) => (String.ofList cs, rem)
  | '"' :: rest => (readBasicBody rest).map fun (cs, rem) => (String.ofList cs, rem)
  | '\'' :: '\'' :: '\'' :: '\n' :: rest => (readMlLiteralBody rest).map fun (cs, rem) => (String.ofList cs, rem)
  | '\'' :: '\'' :: '\'' :: rest => (readMlLiteralBody rest).map fun (cs, rem) => (String.ofList cs, rem)
  | '\'' :: rest => (readLiteralBody rest).map fun (cs, rem) => (String.ofList cs, rem)
  | _ => none

private theorem readStringVal_basic {xs : List Char} (hnot2 : ∀ r', xs ≠ '"' :: '"' :: r') :
    readStringVal ('"' :: xs) = (readBasicBody xs).map fun (cs, r) => (String.ofList cs, r) := by
  (conv => lhs; unfold readStringVal)
  split
  · rename_i r heq; exact False.elim (hnot2 ('\n' :: r) (List.cons.inj heq).2)
  · rename_i r _ heq; exact False.elim (hnot2 r (List.cons.inj heq).2)
  · rename_i r _ _ heq; rw [← (List.cons.inj heq).2]
  · rename_i _ heq; cases heq
  · rename_i _ _ heq; cases heq
  · rename_i _ _ _ heq; cases heq
  · rename_i _ _ _ hnot1 _ _ _; exact False.elim (hnot1 xs rfl)

private theorem readStringVal_mlBasic_noNl {xs : List Char} (hno_nl : ∀ r', xs ≠ '\n' :: r') :
    readStringVal ('"' :: '"' :: '"' :: xs) =
      (readMlBasicBody xs).map fun (cs, r) => (String.ofList cs, r) := by
  (conv => lhs; unfold readStringVal)
  split
  · rename_i r heq
    exact False.elim (hno_nl r (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2)
  · rename_i r _ heq; rw [← (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2]
  · rename_i r _ hnot3 heq
    exact False.elim (hnot3 xs (List.cons.inj heq).2.symm)
  · rename_i _ heq; cases heq
  · rename_i _ _ heq; cases heq
  · rename_i _ _ _ heq; cases heq
  · rename_i _ _ hnot3 _ _ _ _; exact False.elim (hnot3 xs rfl)

private theorem readStringVal_literal {xs : List Char} (hnot2 : ∀ r', xs ≠ '\'' :: '\'' :: r') :
    readStringVal ('\'' :: xs) = (readLiteralBody xs).map fun (cs, r) => (String.ofList cs, r) := by
  (conv => lhs; unfold readStringVal)
  split
  · rename_i _ heq; cases heq
  · rename_i _ _ heq; cases heq
  · rename_i _ _ _ heq; cases heq
  · rename_i r heq; exact False.elim (hnot2 ('\n' :: r) (List.cons.inj heq).2)
  · rename_i r _ heq; exact False.elim (hnot2 r (List.cons.inj heq).2)
  · rename_i r _ _ heq; rw [← (List.cons.inj heq).2]
  · rename_i _ _ _ _ _ _ hnot1; exact False.elim (hnot1 xs rfl)

private theorem readStringVal_mlLiteral_noNl {xs : List Char} (hno_nl : ∀ r', xs ≠ '\n' :: r') :
    readStringVal ('\'' :: '\'' :: '\'' :: xs) =
      (readMlLiteralBody xs).map fun (cs, r) => (String.ofList cs, r) := by
  (conv => lhs; unfold readStringVal)
  split
  · rename_i _ heq; cases heq
  · rename_i _ _ heq; cases heq
  · rename_i _ _ _ heq; cases heq
  · rename_i r heq
    exact False.elim (hno_nl r (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2)
  · rename_i r _ heq; rw [← (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2]
  · rename_i r _ hnot3 heq
    exact False.elim (hnot3 xs (List.cons.inj heq).2.symm)
  · rename_i _ _ _ _ _ hnot3 _; exact False.elim (hnot3 xs rfl)

theorem readStringVal_renderStringLiteral {s : String} {st : StringStyle} {rs : String} {rem : List Char}
    (hr : renderStringLiteral s st = some rs) (hrem : ∀ c r, rem = c :: r → c ≠ '"' ∧ c ≠ '\'') :
    readStringVal (rs.toList ++ rem) = some (s, rem) ∧ NoCrStr rs := by
  cases st with
  | basic atoms? =>
    cases atoms? with
    | none =>
      simp only [renderStringLiteral, Option.some.injEq] at hr; subst hr
      have hnocr : NoCrStr ("\"" ++ escapeBasicBody false s ++ "\"") :=
        noCrStr_append (noCrStr_append (by decide) (noCr_escapeBasicBody false s)) (by decide)
      refine ⟨?_, hnocr⟩
      simp only [String.toList_append, show ("\"" : String).toList = ['"'] from rfl,
        List.cons_append, List.nil_append, List.append_assoc]
      have hnot2 : ∀ r', ((escapeBasicBody false s).toList ++ '"' :: rem) ≠ '"' :: '"' :: r' := by
        intro r' hr'
        cases hsl : s.toList with
        | nil =>
          have hb : (escapeBasicBody false s).toList = [] := by simp [escapeBasicBody, hsl]
          rw [hb, List.nil_append] at hr'
          cases rem with
          | nil => simp at hr'
          | cons c r => simp only [List.cons.injEq] at hr'; exact (hrem c r rfl).1 hr'.2.1
        | cons c0 cs0 =>
          have hb : (escapeBasicBody false s).toList =
              (escapeBasicChar false c0).toList ++ cs0.flatMap (fun x => (escapeBasicChar false x).toList) := by
            simp [escapeBasicBody, String.toList_join, List.flatMap_map, hsl]
          rw [hb, List.append_assoc] at hr'
          rcases escapeBasicChar_atom false c0 with ⟨hc0, hq0, _⟩ | ⟨esc, hd, hesc⟩
          · rw [hc0, List.singleton_append] at hr'; injection hr' with h1 _; exact hq0 h1
          · obtain ⟨_, hr_esc, _⟩ := readBasicEscape_renderBasicEscapeChars hd []
            rw [hesc, hr_esc, List.cons_append] at hr'; cases hr'
      rw [readStringVal_basic hnot2, readBasicBody_escapeBasicBody s rem]
      simp [String.ofList_toList]
    | some atoms =>
      simp only [renderStringLiteral, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      rcases hr with ⟨enc, henc, rfl⟩
      have hnocr : NoCrStr ("\"" ++ String.ofList enc ++ "\"") := by
        refine noCrStr_append (noCrStr_append (by decide) ?_) (by decide)
        simpa [NoCrStr, String.toList_ofList] using noCr_renderBasicAtoms s.toList atoms enc henc
      refine ⟨?_, hnocr⟩
      simp only [String.toList_append, String.toList_ofList, show ("\"" : String).toList = ['"'] from rfl,
        List.cons_append, List.nil_append, List.append_assoc]
      have hnot2 : ∀ r', (enc ++ '"' :: rem) ≠ '"' :: '"' :: r' := by
        intro r' hr'
        cases atoms with
        | nil =>
          cases hsl : s.toList with
          | nil =>
            rw [hsl] at henc
            simp only [renderBasicAtoms, Option.some.injEq] at henc; subst henc
            cases rem with
            | nil => simp at hr'
            | cons c r => simp only [List.nil_append, List.cons.injEq] at hr'; exact (hrem c r rfl).1 hr'.2.1
          | cons _ _ => rw [hsl] at henc; simp [renderBasicAtoms] at henc
        | cons a0 as =>
          cases hsl : s.toList with
          | nil => rw [hsl] at henc; simp [renderBasicAtoms] at henc
          | cons c0 cs0 =>
            rw [hsl] at henc
            cases a0 with
            | plain =>
              simp only [renderBasicAtoms] at henc; split at henc
              · rename_i hok; simp only [Bool.and_eq_true, bne_iff_ne] at hok
                simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                rcases henc with ⟨_, _, rfl⟩; injection hr' with h1 _; exact hok.1.1.1.1 h1
              · cases henc
            | escape esc =>
              simp only [renderBasicAtoms] at henc
              cases hd : decodeBasicEscape esc with
              | none => simp [hd] at henc
              | some c' =>
                simp only [hd] at henc; split at henc
                · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                  rcases henc with ⟨_, _, rfl⟩
                  obtain ⟨_, hrend, _⟩ := readBasicEscape_renderBasicEscapeChars hd []
                  rw [hrend, List.cons_append] at hr'; cases hr'
                · cases henc
      rw [readStringVal_basic hnot2, readBasicBody_renderBasicAtoms s.toList atoms enc rem henc]
      simp [String.ofList_toList]
  | multilineBasic custom? =>
    cases custom? with
    | none =>
      simp only [renderStringLiteral, Option.some.injEq] at hr; subst hr
      refine ⟨?_, noCrStr_append (noCrStr_append (by decide) (noCr_escapeBasicBody true s)) (by decide)⟩
      simp only [String.toList_append, show ("\"\"\"\n" : String).toList = ['"', '"', '"', '\n'] from rfl,
        show ("\"\"\"" : String).toList = ['"', '"', '"'] from rfl, List.cons_append, List.nil_append,
        readStringVal]
      rw [readMlBasicBody_escapeBasicBody s rem (fun c r h => (hrem c r h).1)]
      simp [String.ofList_toList]
    | some pair =>
      rcases pair with ⟨leadNl, atoms⟩
      simp only [renderStringLiteral, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      rcases hr with ⟨enc, henc, rfl⟩
      have hnocr_enc : NoCrStr (String.ofList enc) := by
        simpa [NoCrStr, String.toList_ofList] using noCr_renderMultilineAtoms (!leadNl) false 0 s.toList atoms enc henc
      cases leadNl with
      | true =>
        refine ⟨?_, noCrStr_append (noCrStr_append (by decide) hnocr_enc) (by decide)⟩
        simp only [↓reduceIte, String.toList_append, String.toList_ofList,
          show ("\"\"\"\n" : String).toList = ['"', '"', '"', '\n'] from rfl,
          show ("\"\"\"" : String).toList = ['"', '"', '"'] from rfl, List.cons_append, List.nil_append,
          readStringVal]
        rw [readMlBasicBody_atoms false false 0 s.toList atoms enc rem henc (fun c r h => (hrem c r h).1)]
        simp [String.ofList_toList]
      | false =>
        refine ⟨?_, noCrStr_append (noCrStr_append (by decide) hnocr_enc) (by decide)⟩
        have hno_nl : ∀ r', (enc ++ ['"', '"', '"'] ++ rem) ≠ '\n' :: r' := by
          intro r' hr'
          cases atoms with
          | nil =>
            cases hsl : s.toList with
            | nil =>
              rw [hsl] at henc
              simp only [renderMultilineAtoms, Option.some.injEq] at henc; subst henc; simp at hr'
            | cons _ _ => rw [hsl] at henc; simp [renderMultilineAtoms] at henc
          | cons a0 as =>
            cases a0 with
            | plain =>
              cases hsl : s.toList with
              | nil => rw [hsl] at henc; simp [renderMultilineAtoms] at henc
              | cons c0 cs0 =>
                rw [hsl] at henc; unfold renderMultilineAtoms at henc
                if hc : (c0 == '\\' || c0 == '\r' || isDisallowedControl c0) = true then simp [hc] at henc else
                simp only [hc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and] at henc
                split at henc
                · cases henc
                · rename_i hnl_ne
                  split at henc
                  · cases henc
                  · split at henc
                    · split at henc
                      · cases henc
                      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                        rcases henc with ⟨_, _, rfl⟩; simp only [List.cons_append, List.cons.injEq] at hr'
                        exact hnl_ne (beq_iff_eq.mpr hr'.1)
                    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                      rcases henc with ⟨_, _, rfl⟩; simp only [List.cons_append, List.cons.injEq] at hr'
                      exact hnl_ne (beq_iff_eq.mpr hr'.1)
            | escape esc =>
              cases hsl : s.toList with
              | nil => rw [hsl] at henc; simp [renderMultilineAtoms] at henc
              | cons c0 cs0 =>
                rw [hsl] at henc; unfold renderMultilineAtoms at henc
                cases hd : decodeBasicEscape esc with
                | none => simp [hd] at henc
                | some c' =>
                  simp only [hd] at henc; split at henc
                  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                    rcases henc with ⟨_, _, rfl⟩
                    obtain ⟨_, hrend, _⟩ := readBasicEscape_renderBasicEscapeChars hd []
                    rw [hrend] at hr'; simp at hr'
                  · cases henc
            | lineTrim ws1 ws2 =>
              cases hsl : s.toList <;> simp only [hsl, renderMultilineAtoms] at henc
              all_goals
                split at henc
                · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                  rcases henc with ⟨_, _, rfl⟩; simp at hr'
                · cases henc
        simp only [Bool.false_eq_true, ↓reduceIte, String.toList_append, String.toList_ofList,
          show ("\"\"\"" : String).toList = ['"', '"', '"'] from rfl, List.cons_append, List.nil_append]
        rw [readStringVal_mlBasic_noNl hno_nl,
          readMlBasicBody_atoms true false 0 s.toList atoms enc rem henc (fun c r h => (hrem c r h).1)]
        simp [String.ofList_toList]
  | literal =>
    simp only [renderStringLiteral] at hr; split at hr
    · rename_i hcond; injection hr with hrs; subst hrs
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hnq : '\'' ∉ s.toList := by simpa [String.contains_char_eq] using hcond.2
      have hnocr : NoCrStr ("'" ++ s ++ "'") := by
        refine noCrStr_append (noCrStr_append (by decide) ?_) (by decide)
        intro hm; have hc := List.all_eq_true.mp hcond.1 '\r' hm; simp at hc
      refine ⟨?_, hnocr⟩
      have hnot2 : ∀ r', (s.toList ++ '\'' :: rem) ≠ '\'' :: '\'' :: r' := by
        intro r' hr'
        cases hsl : s.toList with
        | nil =>
          rw [hsl, List.nil_append] at hr'
          cases rem with
          | nil => simp at hr'
          | cons c r => simp only [List.cons.injEq] at hr'; exact (hrem c r rfl).2 hr'.2.1
        | cons c0 cs0 =>
          rw [hsl, List.cons_append] at hr'; injection hr' with hc0 _; exact hnq (by rw [hsl, hc0]; simp)
      simp only [String.toList_append, show ("'" : String).toList = ['\''] from rfl,
        List.cons_append, List.nil_append, List.append_assoc]
      rw [readStringVal_literal hnot2, readLiteralBody_append s.toList rem hnq]
      simp [String.ofList_toList]
    · cases hr
  | multilineLiteral leadNl =>
    simp only [renderStringLiteral] at hr; split at hr
    · rename_i hcond; injection hr with hrs; subst hrs
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      rcases hcond with ⟨⟨hclean, hlead⟩, hno_sub⟩
      have hnocr_s : NoCrStr s := fun hm => by
        have hc := List.all_eq_true.mp hclean '\r' hm; simp at hc
      have hno3 := no_triple_single_quote_of_not_containsSubstr s hno_sub
      cases leadNl with
      | true =>
        refine ⟨?_, noCrStr_append (noCrStr_append (by decide) hnocr_s) (by decide)⟩
        simp only [↓reduceIte, String.toList_append,
          show ("'''\n" : String).toList = ['\'', '\'', '\'', '\n'] from rfl,
          show ("'''" : String).toList = ['\'', '\'', '\''] from rfl, List.cons_append, List.nil_append,
          readStringVal]
        rw [readMlLiteralBody_list s.toList rem hno3 (fun c r h => (hrem c r h).2)]
        simp [String.ofList_toList]
      | false =>
        refine ⟨?_, noCrStr_append (noCrStr_append (by decide) hnocr_s) (by decide)⟩
        simp only [Bool.false_or, bne_iff_ne] at hlead
        have hno_nl : ∀ r', (s.toList ++ ['\'', '\'', '\''] ++ rem) ≠ '\n' :: r' := by
          intro r' hr'
          cases hsl : s.toList with
          | nil => simp [hsl] at hr'
          | cons c0 cs0 =>
            rw [hsl, List.cons_append, List.cons_append] at hr'
            injection hr' with hc0 _; exact hlead (by simp [hsl, hc0])
        simp only [Bool.false_eq_true, ↓reduceIte, String.toList_append,
          show ("'''" : String).toList = ['\'', '\'', '\''] from rfl, List.cons_append, List.nil_append]
        rw [readStringVal_mlLiteral_noNl hno_nl,
          readMlLiteralBody_list s.toList rem hno3 (fun c r h => (hrem c r h).2)]
        simp [String.ofList_toList]
    · cases hr

end LeanSwe.Toml.Proofs
