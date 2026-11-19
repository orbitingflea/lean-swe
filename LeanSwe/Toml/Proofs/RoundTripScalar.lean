import LeanSwe.Toml.Proofs.Core

/-!
# Scalar TOML Render and Parse Round-Trip Proofs

Proves round-trip correctness and character-class invariants for TOML keys,
strings, RFC 3339 datetimes, integers, and IEEE 754 floats.
-/

namespace LeanSwe.Toml.Proofs
open LeanSwe.Toml LeanSwe.Toml.Model LeanSwe.Toml.Impl LeanSwe.NumParse LeanSwe.NumParse.Model

private abbrev isCleanTokChar (c : Char) : Bool := !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c
private theorem forall_ascii_of_decide (p q : Char → Bool) (hascii : ∀ c, p c = true → c.toNat < 128)
    (hdec : (List.range 128).all (fun n => !p (Char.ofNat n) || q (Char.ofNat n)) = true) (c : Char) (hp : p c = true) : q c = true := by
  simpa [Char.ofNat_toNat, hp] using List.all_eq_true.mp hdec c.toNat (List.mem_range.mpr (hascii c hp))
private theorem normalizeCharsAux_clean (acc cs : List Char)
    (h : cs.all (fun c => !isDisallowedControl c && c != '\r') = true) (line col : Nat) :
    normalizeCharsAux line col acc cs = .ok (acc.reverse ++ cs) := by
  fun_induction normalizeCharsAux line col acc cs <;> simp_all [List.reverse_cons]

/-- Internal TOML scalar round-trip lemma `normalizeChars_clean`. -/
theorem normalizeChars_clean (cs : List Char) (h : cs.all (fun c => !isDisallowedControl c && c != '\r') = true) (line col : Nat) :
    normalizeChars line col cs = .ok cs := by
  unfold normalizeChars
  simpa using normalizeCharsAux_clean [] cs h line col
/-- Internal TOML scalar round-trip lemma `isBareKeyChar_clean`. -/
theorem isBareKeyChar_clean (c : Char) (h : isBareKeyChar c = true) :
    (!isDisallowedControl c && c != '\r' && c != '\n' && !isHorizWs c &&
     c != '.' && c != '"' && c != '\'' && c != '#' && c != ',' && c != ']' && c != '}' && c != '=') = true := by
  refine forall_ascii_of_decide isBareKeyChar
    (fun x => !isDisallowedControl x && x != '\r' && x != '\n' && !isHorizWs x && x != '.' && x != '"' && x != '\'' && x != '#' && x != ',' && x != ']' && x != '}' && x != '=')
    (fun x hx => ?_) (by decide) c h
  simp only [isBareKeyChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
  rcases hx with ((((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | rfl) | rfl) <;> first | decide | (have : x.toNat ≤ 122 := Nat.le_trans h2 (by decide); omega)
private theorem isAsciiDigit_lt_128 (c : Char) (h : isAsciiDigit c = true) : c.toNat < 128 := by
  simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at h; have : c.toNat ≤ 57 := Nat.le_trans h.2 (by decide); omega
private theorem isAsciiDigit_clean (c : Char) (h : isAsciiDigit c = true) : isCleanTokChar c = true :=
  forall_ascii_of_decide isAsciiDigit isCleanTokChar isAsciiDigit_lt_128 (by decide) c h
/-- Internal TOML scalar round-trip lemma `toString_lt10_char`. -/
theorem toString_lt10_char (r : Nat) (hr : r < 10) :
    (toString r).toList = [Nat.digitChar r] ∧ isAsciiDigit (Nat.digitChar r) = true ∧ digitVal (Nat.digitChar r) = r ∧
      (!isDisallowedControl (Nat.digitChar r) && Nat.digitChar r != '\r' && Nat.digitChar r != '\n' && !isUnquotedDelim (Nat.digitChar r)) = true := by
  match r with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide | _ + 10 => omega
private theorem nat_toDigitsCore_acc (fuel n : Nat) (acc : List Char) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => simp [Nat.toDigitsCore]
  | succ _ ih =>
    rw [Nat.toDigitsCore, Nat.toDigitsCore]; split
    · simp
    · rw [ih (n / 10) (_ :: acc), ih (n / 10) [_]]; simp [List.append_assoc]
private theorem toDigitsCore_fuel_mono (f1 f2 n : Nat) (hf1 : n < f1) (hf2 : n < f2) :
    Nat.toDigitsCore 10 f1 n [] = Nat.toDigitsCore 10 f2 n [] := by
  induction f1 generalizing f2 n with
  | zero => omega
  | succ f1' ih =>
    cases f2 with | zero => omega | succ f2' =>
    rw [Nat.toDigitsCore, Nat.toDigitsCore]
    if hdiv : n / 10 = 0 then simp [hdiv] else
      simp only [hdiv, ↓reduceIte]; rw [nat_toDigitsCore_acc f1' (n / 10) [_], nat_toDigitsCore_acc f2' (n / 10) [_], ih f2' (n / 10) (by omega) (by omega)]
/-- Internal TOML scalar round-trip lemma `toString_two_digits_split`. -/
theorem toString_two_digits_split (q r : Nat) (hq : 0 < q) (hr : r < 10) :
    (toString (q * 10 + r)).toList = (toString q).toList ++ [Nat.digitChar r] := by
  change (Nat.repr (q * 10 + r)).toList = (Nat.repr q).toList ++ [Nat.digitChar r]
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits]; rw [Nat.toDigitsCore]
  simp only [show (q * 10 + r) / 10 = q by omega, show (q * 10 + r) % 10 = r by omega, show q ≠ 0 by omega, ↓reduceIte]
  rw [nat_toDigitsCore_acc _ q [Nat.digitChar r], toDigitsCore_fuel_mono (q * 10 + r) (q + 1) q (by omega) (by omega)]
/-- Internal TOML scalar round-trip lemma `pow10Nat_pos`. -/
theorem pow10Nat_pos (k : Nat) : 0 < pow10Nat k := by induction k with | zero => decide | succ _ ih => simp only [pow10Nat]; omega
/-- Internal TOML scalar round-trip lemma `pow10Nat_add`. -/
theorem pow10Nat_add (a b : Nat) : pow10Nat (a + b) = pow10Nat a * pow10Nat b := by
  induction a with | zero => simp [pow10Nat] | succ a ih => rw [Nat.succ_add, pow10Nat, ih, pow10Nat, Nat.mul_assoc]
/-- Internal TOML scalar round-trip lemma `pow10Nat_9`. -/
theorem pow10Nat_9 : pow10Nat 9 = 1000000000 := rfl
private theorem toString_length_eq_toList (n : Nat) : (toString n).length = (toString n).toList.length := by
  change (Nat.repr n).length = (Nat.repr n).toList.length; simp [Nat.repr]
/-- Internal TOML scalar round-trip lemma `toString_length_le_pow10`. -/
theorem toString_length_le_pow10 (w n : Nat) (hw : 1 ≤ w) (hn : n < pow10Nat w) : (toString n).length ≤ w := by
  induction w generalizing n with
  | zero => omega
  | succ w ih =>
    if h10 : n < 10 then obtain ⟨hch, _⟩ := toString_lt10_char n h10; rw [toString_length_eq_toList, hch]; simp else
      have hw1 : 1 ≤ w := by cases w with | zero => simp [pow10Nat] at hn; omega | succ _ => omega
      have hsub := ih (n / 10) hw1 (by simp only [pow10Nat] at hn; omega)
      have hsplit := toString_two_digits_split (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      rw [show n / 10 * 10 + n % 10 = n by omega] at hsplit; rw [toString_length_eq_toList n, toString_length_eq_toList (n / 10)] at *
      rw [hsplit, List.length_append, List.length_singleton]; omega
/-- Internal TOML scalar round-trip lemma `padNatZero_eq_of_toList`. -/
theorem padNatZero_eq_of_toList (w n : Nat) (cs : List Char) (hcs : (toString n).toList = cs) (hlen : cs.length ≤ w) :
    (padNatZero w n).toList = List.replicate (w - cs.length) '0' ++ cs := by
  unfold padNatZero; have hlen_str : (toString n).length = cs.length := by rw [toString_length_eq_toList, hcs]
  change (if (toString n).length ≥ w then toString n else String.ofList (List.replicate (w - (toString n).length) '0') ++ toString n).toList = _
  rw [hlen_str]; if hge : cs.length ≥ w then
    simp only [hge, ↓reduceIte]; rw [show cs.length = w by omega, Nat.sub_self, List.replicate_zero, List.nil_append, hcs]
  else simp only [hge, ↓reduceIte, String.toList_append, String.toList_ofList, hcs]
private theorem toString_all_digit_and_foldl (n : Nat) :
    (toString n).toList.all isAsciiDigit = true ∧ (toString n).toList.foldl (fun a c => a * 10 + digitVal c) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    if h10 : n < 10 then
      obtain ⟨hch, hd, hdv, _⟩ := toString_lt10_char n h10; rw [hch]
      simp only [List.all_cons, List.all_nil, Bool.and_true, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add, hd, hdv, and_self]
    else
      have hsplit := toString_two_digits_split (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      rw [show n / 10 * 10 + n % 10 = n by omega] at hsplit
      obtain ⟨ihd, ihf⟩ := ih (n / 10) (by omega); obtain ⟨_, hd, hdv, _⟩ := toString_lt10_char (n % 10) (Nat.mod_lt n (by decide))
      rw [hsplit]; refine ⟨by simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, ihd, hd], ?_⟩
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ihf, hdv]; omega
private theorem padNatZero_all_digit_and_foldl (w n : Nat) :
    (padNatZero w n).toList.all isAsciiDigit = true ∧ (padNatZero w n).toList.all isCleanTokChar = true ∧
    (padNatZero w n).toList.foldl (fun a c => a * 10 + digitVal c) 0 = n := by
  obtain ⟨hd, hf⟩ := toString_all_digit_and_foldl n
  have hall : (padNatZero w n).toList.all isAsciiDigit = true := by
    unfold padNatZero; dsimp only; split
    · exact hd
    · simp only [String.toList_append, String.toList_ofList, List.all_append, hd, Bool.and_true, List.all_replicate]; split <;> decide
  refine ⟨hall, List.all_eq_true.mpr fun c hc => isAsciiDigit_clean c (List.all_eq_true.mp hall c hc), ?_⟩
  unfold padNatZero; dsimp only; split
  · exact hf
  · simp only [String.toList_append, String.toList_ofList, List.foldl_append]
    have hz : ∀ k, (List.replicate k '0').foldl (fun a c => a * 10 + digitVal c) 0 = 0 := fun k => by
      induction k with | zero => rfl | succ _ ih => rw [List.replicate_succ, List.foldl_cons]; exact ih
    rw [hz, hf]
private theorem padNatZero_length_of_lt (w n : Nat) (hw : 1 ≤ w) (hn : n < pow10Nat w) : (padNatZero w n).toList.length = w := by
  have hle : (toString n).toList.length ≤ w := by rw [← toString_length_eq_toList]; exact toString_length_le_pow10 w n hw hn
  rw [padNatZero_eq_of_toList w n _ rfl hle, List.length_append, List.length_replicate]; omega
private theorem twoDigits_padNatZero (n : Nat) (hn : n < 100) :
    ∃ c1 c2, (padNatZero 2 n).toList = [c1, c2] ∧ twoDigitsNat? c1 c2 = some n ∧ isAsciiDigit c1 = true ∧ isAsciiDigit c2 = true := by
  have hlen := padNatZero_length_of_lt 2 n (by decide) hn; obtain ⟨hd, _, hf⟩ := padNatZero_all_digit_and_foldl 2 n
  rcases hcs : (padNatZero 2 n).toList with _ | ⟨c1, _ | ⟨c2, _ | _⟩⟩ <;> rw [hcs] at hlen <;> try (simp at hlen)
  rw [hcs] at hd hf; simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add] at hd hf
  exact ⟨c1, c2, rfl, by simp [twoDigitsNat?, hd.1, hd.2, hf], hd.1, hd.2⟩
private theorem fourDigits_padNatZero (y : Nat) (hy : y < 10000) :
    ∃ c1 c2 c3 c4, (padNatZero 4 y).toList = [c1, c2, c3, c4] ∧ fourDigitsNat? c1 c2 c3 c4 = some y ∧
      isAsciiDigit c1 = true ∧ isAsciiDigit c2 = true ∧ isAsciiDigit c3 = true ∧ isAsciiDigit c4 = true := by
  have hlen := padNatZero_length_of_lt 4 y (by decide) hy; obtain ⟨hd, _, hf⟩ := padNatZero_all_digit_and_foldl 4 y
  rcases hcs : (padNatZero 4 y).toList with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | _⟩⟩⟩⟩ <;> rw [hcs] at hlen <;> try (simp at hlen)
  rw [hcs] at hd hf; simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add] at hd hf
  exact ⟨c1, c2, c3, c4, rfl, by simp [fourDigitsNat?, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, hf], hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩
private def utf8Sum : List Char → Nat | [] => 0 | c :: cs => c.utf8Size + utf8Sum cs
private theorem utf8Sum_append (a b : List Char) : utf8Sum (a ++ b) = utf8Sum a + utf8Sum b := by induction a <;> simp_all [utf8Sum, Nat.add_assoc]
private theorem utf8ByteSize_eq_utf8Sum (s : String) : s.utf8ByteSize = utf8Sum s.toList := by
  suffices ∀ cs, (String.ofList cs).utf8ByteSize = utf8Sum cs by simpa [String.ofList_toList] using this s.toList
  intro cs; induction cs with | nil => rfl | cons c cs ih => rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih, utf8Sum]
private theorem utf8GetAux_append_add (a b : List Char) (i₀ : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (a ++ b) i₀ ⟨i₀.byteIdx + utf8Sum a⟩ = String.Pos.Raw.utf8GetAux b ⟨i₀.byteIdx + utf8Sum a⟩ ⟨i₀.byteIdx + utf8Sum a⟩ := by
  induction a generalizing i₀ with
  | nil => simp [utf8Sum]
  | cons c cs ih =>
    simp only [List.cons_append, utf8Sum]; rw [String.Pos.Raw.utf8GetAux.eq_def]; have hpos := Char.utf8Size_pos c
    have hne : i₀ ≠ ⟨i₀.byteIdx + (c.utf8Size + utf8Sum cs)⟩ := fun heq => by
      have : i₀.byteIdx = i₀.byteIdx + (c.utf8Size + utf8Sum cs) := congrArg String.Pos.Raw.byteIdx heq; omega
    simp only [hne, ↓reduceIte, show i₀ + c = ⟨i₀.byteIdx + c.utf8Size⟩ from String.Pos.Raw.ext String.Pos.Raw.byteIdx_add_char]
    rw [show i₀.byteIdx + (c.utf8Size + utf8Sum cs) = (i₀.byteIdx + c.utf8Size) + utf8Sum cs by omega]; exact ih _
private theorem get_at_utf8Sum (s : String) (a : List Char) (c : Char) (b : List Char) (h : s.toList = a ++ c :: b) :
    String.Pos.Raw.get s ⟨utf8Sum a⟩ = c ∧ String.Pos.Raw.next s ⟨utf8Sum a⟩ = ⟨utf8Sum a + c.utf8Size⟩ ∧ String.Pos.Raw.atEnd s ⟨utf8Sum a⟩ = false := by
  have hget : String.Pos.Raw.get s ⟨utf8Sum a⟩ = c := by
    change String.Pos.Raw.utf8GetAux s.toList 0 ⟨utf8Sum a⟩ = c
    rw [h, show (⟨utf8Sum a⟩ : String.Pos.Raw) = ⟨(0 : String.Pos.Raw).byteIdx + utf8Sum a⟩ by simp [String.Pos.Raw.byteIdx_zero],
      utf8GetAux_append_add a (c :: b) 0, String.Pos.Raw.utf8GetAux.eq_def]; simp
  refine ⟨hget, String.Pos.Raw.ext (by change ((⟨utf8Sum a⟩ : String.Pos.Raw) + String.Pos.Raw.get s ⟨utf8Sum a⟩).byteIdx = _; rw [hget]; exact String.Pos.Raw.byteIdx_add_char), ?_⟩
  rw [String.Pos.Raw.atEnd.eq_1, decide_eq_false_iff_not]
  have hsz : s.utf8ByteSize = utf8Sum a + (c.utf8Size + utf8Sum b) := by rw [utf8ByteSize_eq_utf8Sum, h, utf8Sum_append, utf8Sum]
  have := Char.utf8Size_pos c; dsimp only; omega
private theorem splitOnAux_length_ge (s sep : String) (b i j : String.Pos.Raw) (r : List String) :
    r.length + 1 ≤ (s.splitOnAux sep b i j r).length := by fun_induction String.splitOnAux s sep b i j r <;> simp_all +zetaDelta <;> omega
private theorem splitOnAux_tripleQuote (s : String) (b i j : String.Pos.Raw) (r : List String) :
    ∀ (pref rem : List Char) (k : Nat), k < 3 → j = ⟨k⟩ → i = ⟨utf8Sum pref + k⟩ → s.toList = pref ++ (List.replicate k '\'' ++ rem) →
      (∃ a b', List.replicate k '\'' ++ rem = a ++ ['\'', '\'', '\''] ++ b') → r.length + 2 ≤ (s.splitOnAux "'''" b i j r).length := by
  have hrep_sum : ∀ pref k, utf8Sum (pref ++ List.replicate k '\'') = utf8Sum pref + k := fun pref k => by
    rw [utf8Sum_append]; suffices utf8Sum (List.replicate k '\'') = k by rw [this]
    induction k with | zero => rfl | succ k ih => rw [List.replicate_succ, utf8Sum, ih]; change 1 + k = k + 1; omega
  have hsep_all : ∀ k, k < 3 → String.Pos.Raw.get "'''" ⟨k⟩ = '\'' ∧ String.Pos.Raw.next "'''" ⟨k⟩ = ⟨k + 1⟩ ∧
      String.Pos.Raw.atEnd "'''" ⟨k + 1⟩ = decide (k = 2) := fun k hk => by match k with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => omega
  fun_induction String.splitOnAux s "'''" b i j r with
  | case1 b i j r hati =>
    intro pref rem k _ _ hi hs ⟨a, b', hab⟩; cases rem with
    | nil => have := congrArg List.length hab; simp at this; omega
    | cons c rem' => have hat := (get_at_utf8Sum s (pref ++ List.replicate k '\'') c rem' (by simp [hs])).2.2; rw [hrep_sum, ← hi] at hat; simp [hat] at hati
  | case2 b i j r _ _ _ _ _ _ =>
    intro _ _ _ _ _ _ _ _
    have hge := splitOnAux_length_ge s "'''" (String.Pos.Raw.next s i) (String.Pos.Raw.next s i) 0
      (String.Pos.Raw.extract s b ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next "'''" j)) :: r); simp at hge; omega
  | case3 b i j r _ hmatch _ _ hatj ih =>
    intro pref rem k hk hj hi hs ⟨a, b', hab⟩; cases rem with
    | nil => have := congrArg List.length hab; simp at this; omega
    | cons c rem' =>
      have hsep := hsep_all k hk; obtain ⟨hget, hnext, _⟩ := get_at_utf8Sum s (pref ++ List.replicate k '\'') c rem' (by simp [hs])
      rw [hrep_sum] at hget hnext; have hc : c = '\'' := by simpa [hi, hj, hget, hsep.1] using hmatch
      subst hc; have hk2 : k + 1 < 3 := by have hatj' : ¬ String.Pos.Raw.atEnd "'''" (String.Pos.Raw.next "'''" j) = true := hatj; rw [hj, hsep.2.1, hsep.2.2] at hatj'; simp at hatj'; omega
      have hrep : List.replicate (k + 1) '\'' ++ rem' = List.replicate k '\'' ++ '\'' :: rem' := by rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      exact ih pref rem' (k + 1) hk2 (by change String.Pos.Raw.next "'''" j = _; rw [hj, hsep.2.1])
        (by change String.Pos.Raw.next s i = _; rw [hi, hnext]; exact String.Pos.Raw.ext (by dsimp; change utf8Sum pref + k + 1 = _; omega))
        (by rw [hrep]; exact hs) ⟨a, b', by rw [hrep]; exact hab⟩
  | case4 b i j r _ hmatch ih =>
    intro pref rem k hk hj hi hs ⟨a, b', hab⟩; cases rem with
    | nil => have := congrArg List.length hab; simp at this; omega
    | cons c rem' =>
      have hsep := (hsep_all k hk).1; obtain ⟨hget, _, _⟩ := get_at_utf8Sum s (pref ++ List.replicate k '\'') c rem' (by simp [hs]); rw [hrep_sum] at hget
      have hc : c ≠ '\'' := by simpa [hi, hj, hget, hsep] using hmatch
      have hun : i.unoffsetBy j = ⟨utf8Sum pref⟩ := by rw [hi, hj]; apply String.Pos.Raw.ext; dsimp [String.Pos.Raw.unoffsetBy]; omega
      cases hrep_eq : List.replicate k '\'' ++ c :: rem' with
      | nil => cases k <;> simp at hrep_eq
      | cons c0 suf' =>
        obtain ⟨_, hnext0, _⟩ := get_at_utf8Sum s pref c0 suf' (by rw [hs, hrep_eq])
        have ha_ne : a ≠ [] := by
          rintro rfl; have h1 := congrArg (·[k]?) hab; rw [List.getElem?_append_right (by simp)] at h1
          simp only [List.length_replicate, Nat.sub_self, List.getElem?_cons_zero] at h1
          rw [show (([] ++ ['\'', '\'', '\''] ++ b')[k]?) = some '\'' by match k with | 0 => rfl | 1 => rfl | 2 => rfl | _ + 3 => omega] at h1
          exact hc (Option.some.inj h1)
        rcases List.exists_cons_of_ne_nil ha_ne with ⟨a0, as, rfl⟩; rw [hrep_eq] at hab; injection hab with _ hsuf'
        exact ih (pref ++ [c0]) suf' 0 (by decide) rfl (by rw [hun, hnext0]; simp [utf8Sum_append, utf8Sum]) (by simp [hs, hrep_eq]) ⟨as, b', by simpa using hsuf'⟩
private theorem no_triple_quote_of_not_containsSubstr (s : String) (h : containsSubstr s "'''" = false) :
    ∀ a b : List Char, s.toList ≠ a ++ ['\'', '\'', '\''] ++ b := by
  intro a b hab; simp only [containsSubstr, decide_eq_false_iff_not, Nat.not_lt] at h
  rw [show s.splitOn "'''" = s.splitOnAux "'''" 0 0 0 [] by simp [String.splitOn, show ("'''" == "") = false from rfl]] at h
  have hge := splitOnAux_tripleQuote s 0 0 0 [] [] s.toList 0 (by decide) rfl rfl (by simp) ⟨a, b, hab⟩; simp at hge; omega
private theorem getLast_ne_quote_of_not_endsWith (s : String) (h : s.endsWith "'" = false) : ∀ a : List Char, s.toList ≠ a ++ ['\''] := by
  intro a ha; rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_eq_false_iff] at h
  exact h (by rw [String.copy_toSlice, ha]; exact ⟨a, rfl⟩)
private theorem hexDigitUpper_spec (n : Nat) (hn : n < 16) :
    hexVal? (hexDigitUpper n) = some n ∧ (!isDisallowedControl (hexDigitUpper n) && hexDigitUpper n != '\r' && hexDigitUpper n != '\n') = true := by
  have h1 : (List.range 16).all (fun m => (hexVal? (hexDigitUpper m) == some m) &&
      (!isDisallowedControl (hexDigitUpper m) && hexDigitUpper m != '\r' && hexDigitUpper m != '\n')) = true := by decide
  have hm := List.all_eq_true.mp h1 n (List.mem_range.mpr hn); simp only [Bool.and_eq_true, beq_iff_eq] at hm; exact ⟨hm.1, by simp [hm.2]⟩
private inductive EscapedCharSpec (allowNl : Bool) (c : Char) : Prop where
  | plain (heq : (escapeBasicChar allowNl c).toList = [c]) (hctrl : !isDisallowedControl c = true) (hcr : c ≠ '\r')
      (hnl : (allowNl || c != '\n') = true) (hq : c ≠ '"') (hbs : c ≠ '\\')
  | escaped (esc : List Char) (heq : (escapeBasicChar allowNl c).toList = '\\' :: esc)
      (hparse : ∀ tail, parseBasicEscape (esc ++ tail) = .ok (c, tail))
      (hclean : (('\\' :: esc).all fun ch => !isDisallowedControl ch && ch != '\r' && ch != '\n') = true)
private theorem escapeBasicChar_spec (allowNl : Bool) (c : Char) : EscapedCharSpec allowNl c := by
  if h1 : c = '\\' then subst h1; exact .escaped ['\\'] (by cases allowNl <;> rfl) (fun _ => rfl) (by decide) else
  if h2 : c = '"' then subst h2; exact .escaped ['"'] (by cases allowNl <;> rfl) (fun _ => rfl) (by decide) else
  if h3 : c = '\x08' then subst h3; exact .escaped ['b'] (by cases allowNl <;> rfl) (fun _ => rfl) (by decide) else
  if h4 : c = '\t' then subst h4; exact .escaped ['t'] (by cases allowNl <;> rfl) (fun _ => rfl) (by decide) else
  if h5 : c = '\n' then subst h5; cases allowNl <;> first | exact .escaped ['n'] rfl (fun _ => rfl) (by decide) | exact .plain rfl (by decide) (by decide) (by decide) (by decide) (by decide) else
  if h6 : c = '\x0c' then subst h6; exact .escaped ['f'] (by cases allowNl <;> rfl) (fun _ => rfl) (by decide) else
  if h7 : c = '\r' then subst h7; exact .escaped ['r'] (by cases allowNl <;> rfl) (fun _ => rfl) (by decide) else
  if hc : isDisallowedControl c = true then
    have hlt : c.toNat < 256 := by simp only [isDisallowedControl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc; omega
    obtain ⟨hv1, hcl1⟩ := hexDigitUpper_spec (c.toNat / 16) (by omega); obtain ⟨hv2, hcl2⟩ := hexDigitUpper_spec (c.toNat % 16) (Nat.mod_lt _ (by decide))
    refine .escaped ['u', '0', '0', hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] ?_ (fun tail => ?_) ?_
    · rw [show escapeBasicChar allowNl c = "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] by
        simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc], String.toList_append, show ("\\u00" : String).toList = ['\\', 'u', '0', '0'] from rfl, String.toList_ofList]; rfl
    · have hrange : (c.toNat > 0x10FFFF || (0xD800 ≤ c.toNat && c.toNat ≤ 0xDFFF)) = false := by simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp only [List.cons_append, List.nil_append, parseBasicEscape, parseUnicodeHex, takeHexDigits, show hexVal? '0' = some 0 from rfl, hv1, hv2]
      rw [show ((0 * 16 + 0) * 16 + c.toNat / 16) * 16 + c.toNat % 16 = c.toNat by omega]; simp [hrange, Char.ofNat_toNat]
    · rw [show ('\\' :: ['u', '0', '0', hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)]) = ['\\', 'u', '0', '0'] ++ [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] from rfl]
      simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, hcl1, hcl2]; decide
  else
    exact .plain (by rw [show escapeBasicChar allowNl c = String.singleton c by simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc], String.toList_singleton])
      (by simpa using hc) h7 (by simp [bne_iff_ne, h5]) h2 h1
private theorem escapeBasicBody_clean (allowNl : Bool) (s : String) :
    ((escapeBasicBody allowNl s).toList.all fun ch => !isDisallowedControl ch && ch != '\r' && (allowNl || ch != '\n')) = true := by
  simp only [escapeBasicBody, String.toList_join, List.all_flatMap, List.all_map, Function.comp_def]; rw [List.all_eq_true]; intro c _
  rcases escapeBasicChar_spec allowNl c with ⟨heq, hctrl, hcr, hnl, _, _⟩ | ⟨esc, heq, _, hcl⟩
  · rw [heq]; simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]; exact ⟨⟨hctrl, bne_iff_ne.mpr hcr⟩, hnl⟩
  · rw [heq, List.all_eq_true]; intro ch hch; have h1 := List.all_eq_true.mp hcl ch hch; simp only [Bool.and_eq_true] at h1 ⊢; exact ⟨h1.1, by simp [h1.2]⟩
private theorem parseBasicStringBodyFuel_escape (cs acc rest : List Char) (fuel : Nat)
    (hfuel : (cs.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 ≤ fuel) :
    parseBasicStringBodyFuel fuel acc (cs.flatMap (fun c => (escapeBasicChar false c).toList) ++ '"' :: rest) = .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc fuel with
  | nil => cases fuel with | zero => omega | succ _ => simp [parseBasicStringBodyFuel]
  | cons c cs ih =>
    cases fuel with | zero => omega | succ f =>
    simp only [List.flatMap_cons, List.append_assoc] at hfuel ⊢
    rcases escapeBasicChar_spec false c with ⟨heq, _, _, hnl, hq, hbs⟩ | ⟨esc, heq, hparse, _⟩
    · rw [heq] at hfuel ⊢; simp only [List.singleton_append, List.length_cons] at hfuel ⊢
      have hnl' : c ≠ '\n' := by simpa using hnl
      simp only [parseBasicStringBodyFuel]; simpa using ih (c :: acc) f (by omega)
    · rw [heq] at hfuel ⊢; simp only [List.length_append, List.length_cons] at hfuel
      simp only [List.cons_append, parseBasicStringBodyFuel, hparse, bind, Except.bind]; simpa using ih (c :: acc) f (by omega)
private theorem renderBasicQuoted_spec (s : String) (rest : List Char) (hrest : ∀ c r, rest = c :: r → c ≠ '"') :
    (∀ r', ((escapeBasicBody false s).toList ++ '"' :: rest) ≠ '"' :: '"' :: r') ∧
    parseBasicStringBody ((escapeBasicBody false s).toList ++ '"' :: rest) = .ok (s, rest) ∧
    (("\"" ++ escapeBasicBody false s ++ "\"").toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  have heq_b : (escapeBasicBody false s).toList = s.toList.flatMap (fun c => (escapeBasicChar false c).toList) := by simp [escapeBasicBody, String.toList_join, List.flatMap_map]
  refine ⟨fun r' hr' => ?_, ?_, ?_⟩
  · cases hs : s.toList with
    | nil => rw [heq_b, hs, List.flatMap_nil, List.nil_append] at hr'; cases rest with | nil => simp at hr' | cons c t => simp only [List.cons.injEq] at hr'; exact hrest c t rfl hr'.2.1
    | cons c0 cs0 =>
      rw [heq_b, hs, List.flatMap_cons, List.append_assoc] at hr'
      rcases escapeBasicChar_spec false c0 with ⟨heq, _, _, _, hq, _⟩ | ⟨_, heq, _, _⟩
      · rw [heq, List.singleton_append] at hr'; injection hr' with h1 _; exact hq h1
      · rw [heq, List.cons_append] at hr'; cases hr'
  · unfold parseBasicStringBody
    have hlen : (s.toList.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 ≤ ((escapeBasicBody false s).toList ++ '"' :: rest).length + 1 := by
      rw [heq_b]; simp only [List.length_append, List.length_cons]; omega
    rw [heq_b] at hlen ⊢; rw [parseBasicStringBodyFuel_escape s.toList [] rest _ hlen]; simp [String.ofList_toList]
  · simp only [String.toList_append, List.all_append, (by decide : (("\"" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true), Bool.true_and, Bool.and_true]
    simpa [Bool.and_assoc] using escapeBasicBody_clean false s
private theorem parseMultilineBasicBodyFuel_escape (cs acc rest : List Char) (fuel : Nat) (hrest : ∀ c r, rest = c :: r → c ≠ '"')
    (hfuel : (cs.flatMap (fun c => (escapeBasicChar true c).toList)).length + 1 ≤ fuel) :
    parseMultilineBasicBodyFuel fuel acc (cs.flatMap (fun c => (escapeBasicChar true c).toList) ++ ['"', '"', '"'] ++ rest) = .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc fuel with
  | nil =>
    cases fuel with | zero => omega | succ _ =>
    simp only [List.flatMap_nil, List.nil_append, List.cons_append]; cases rest with
    | nil => simp [parseMultilineBasicBodyFuel]
    | cons c r =>
      have hne : c ≠ '"' := hrest c r rfl; conv => lhs; unfold parseMultilineBasicBodyFuel
      split <;> first | (simp_all; done) | (rename_i _ hq1 _ _ heq; cases heq; exact absurd rfl (hq1 (c :: r) rfl))
  | cons c cs ih =>
    cases fuel with | zero => omega | succ f =>
    simp only [List.flatMap_cons, List.append_assoc] at hfuel ⊢
    rcases escapeBasicChar_spec true c with ⟨heq, _, _, _, hq, hbs⟩ | ⟨esc, heq, hparse, _⟩
    · rw [heq] at hfuel ⊢; simp only [List.singleton_append, List.length_cons] at hfuel ⊢
      have hstep (tail) : parseMultilineBasicBodyFuel (f + 1) acc (c :: tail) = parseMultilineBasicBodyFuel f (c :: acc) tail := by
        conv => lhs; unfold parseMultilineBasicBodyFuel
        split <;> simp_all
      rw [hstep]; simpa [List.append_assoc] using ih (c :: acc) f (by omega)
    · rw [heq] at hfuel ⊢; simp only [List.length_append, List.length_cons] at hfuel
      simp only [List.cons_append, parseMultilineBasicBodyFuel, hparse]; simpa [List.append_assoc] using ih (c :: acc) f (by omega)
private theorem renderLiteralQuoted_spec (s : String) (hclean : isSingleLineClean s = true)
    (hnoq : s.contains '\'' = false) (rest : List Char) (hrest : ∀ c r, rest = c :: r → c ≠ '\'') :
    (∀ r', (s.toList ++ '\'' :: rest) ≠ '\'' :: '\'' :: r') ∧ parseLiteralStringBody [] (s.toList ++ '\'' :: rest) = .ok (s, rest) ∧
    (("'" ++ s ++ "'").toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  have hnq : '\'' ∉ s.toList := by simpa [String.contains_char_eq] using hnoq
  have hnl : '\n' ∉ s.toList := fun hm => by have h1 := List.all_eq_true.mp hclean '\n' hm; simp at h1
  have hp_body : ∀ cs acc, '\n' ∉ cs → '\'' ∉ cs → parseLiteralStringBody acc (cs ++ '\'' :: rest) = .ok (String.ofList (acc.reverse ++ cs), rest) := by
    intro cs; induction cs with
    | nil => intro acc _ _; simp [parseLiteralStringBody]
    | cons c cs ih =>
      intro acc hnl' hq'; have hc_nl : c ≠ '\n' := fun h => hnl' (by simp [h]); have hc_q : c ≠ '\'' := fun h => hq' (by simp [h])
      simp only [List.cons_append]; unfold parseLiteralStringBody
      split
      · rename_i heq; simp at heq
      · rename_i heq; injection heq with hc; exact absurd hc hc_nl
      · rename_i heq; injection heq with hc; exact absurd hc hc_q
      · rename_i heq; injection heq with hc hr; subst hc hr; rw [ih (c :: acc) (fun h => hnl' (by simp [h])) (fun h => hq' (by simp [h]))]; simp
  refine ⟨fun r' hr' => ?_, by simpa [String.ofList_toList] using hp_body s.toList [] hnl hnq, ?_⟩
  · cases hs : s.toList with
    | nil => rw [hs, List.nil_append] at hr'; cases rest with | nil => simp at hr' | cons c t => simp only [List.cons.injEq] at hr'; exact hrest c t rfl hr'.2.1
    | cons c0 _ => rw [hs, List.cons_append] at hr'; injection hr' with hc0; exact hnq (by rw [hs, hc0]; simp)
  · simp only [String.toList_append, List.all_append, (by decide : (("'" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true), Bool.true_and, Bool.and_true]
    simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true] at hclean ⊢; exact fun c hc => ⟨⟨(hclean c hc).1.1, (hclean c hc).2⟩, (hclean c hc).1.2⟩
private theorem parseMultilineLiteralBodyFuel_list (cs acc rest : List Char) (fuel : Nat)
    (hno3 : ∀ a b, cs ≠ a ++ ['\'', '\'', '\''] ++ b) (hnoend : ∀ a, cs ≠ a ++ ['\'']) (hrest : ∀ c r, rest = c :: r → c ≠ '\'') (hfuel : cs.length + 1 ≤ fuel) :
    parseMultilineLiteralBodyFuel fuel acc (cs ++ ['\'', '\'', '\''] ++ rest) = .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc fuel with
  | nil =>
    cases fuel with | zero => omega | succ _ =>
    simp only [List.nil_append, List.cons_append]; cases rest with
    | nil => simp [parseMultilineLiteralBodyFuel]
    | cons c r =>
      have hne : c ≠ '\'' := hrest c r rfl; conv => lhs; unfold parseMultilineLiteralBodyFuel
      split <;> first | (simp_all; done) | (rename_i hq1 _ heq; cases heq; exact absurd rfl (hq1 (c :: r) rfl))
  | cons c cs ih =>
    cases fuel with | zero => omega | succ f =>
    have hnot3 : ¬ (c = '\'' ∧ ∃ t, cs ++ ['\'', '\'', '\''] ++ rest = '\'' :: '\'' :: t) := by
      rintro ⟨rfl, t, ht⟩; rcases cs with _ | ⟨c1, _ | ⟨c2, cs2⟩⟩
      · exact hnoend [] rfl
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht; exact hnoend ['\''] (by simp [ht.1])
      · simp only [List.cons_append, List.cons.injEq] at ht; exact hno3 [] cs2 (by simp [ht.1, ht.2.1])
    have hstep (tail) (hn3 : ¬ (c = '\'' ∧ ∃ t, tail = '\'' :: '\'' :: t)) :
        parseMultilineLiteralBodyFuel (f + 1) acc (c :: tail) = parseMultilineLiteralBodyFuel f (c :: acc) tail := by
      conv => lhs; unfold parseMultilineLiteralBodyFuel
      split <;> first | simp_all | (exfalso; apply hn3; simp_all)
    change parseMultilineLiteralBodyFuel (f + 1) acc (c :: (cs ++ ['\'', '\'', '\''] ++ rest)) = _
    rw [hstep _ hnot3, ih (c :: acc) f (fun a b h => hno3 (c :: a) b (by simp [h])) (fun a h => hnoend (c :: a) (by simp [h])) (by simp at hfuel; omega)]; simp
private theorem takeBareKeyChars_append (acc ks rest : List Char)
    (hks : ks.all isBareKeyChar = true) (hrest : ∀ c tail, rest = c :: tail → isBareKeyChar c = false) :
    takeBareKeyChars acc (ks ++ rest) = (acc.reverse ++ ks, rest) := by
  induction ks generalizing acc with
  | nil => cases rest with | nil => simp [takeBareKeyChars] | cons c r => simp [takeBareKeyChars, hrest c r rfl]
  | cons k ks ih => simp only [List.all_cons, Bool.and_eq_true] at hks; simp [takeBareKeyChars, hks.1, ih (k :: acc) hks.2]
/-- Internal TOML scalar round-trip lemma `renderKey_parseKeySegment`. -/
theorem renderKey_parseKeySegment (k : String) (ks : KeyStyle) (rk : String) (hr : renderKey k ks = some rk) (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'') :
    parseKeySegment (rk.toList ++ rest) = .ok (k, rest) ∧ (rk.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  cases ks with
  | bare =>
    simp only [renderKey] at hr; split at hr
    · rename_i hbare; injection hr with hrk; subst hrk
      simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare; rcases hbare with ⟨hne, hall⟩
      cases hlist : k.toList with
      | nil => have hk0 : k = "" := (by rw [← String.ofList_toList (s := k), hlist]); subst hk0; simp at hne
      | cons c0 cs0 =>
        have hcl0 := isBareKeyChar_clean c0 (List.all_eq_true.mp hall c0 (by rw [hlist]; simp)); simp only [Bool.and_eq_true, bne_iff_ne] at hcl0
        have hq1 : c0 ≠ '"' := hcl0.1.1.1.1.1.1.2; have hq2 : c0 ≠ '\'' := hcl0.1.1.1.1.1.2
        have hseg : parseKeySegment (c0 :: (cs0 ++ rest)) =
            let (ks', rest') := takeBareKeyChars [] (c0 :: (cs0 ++ rest))
            if ks'.isEmpty then .error (mkErr .parseError "expected key") else .ok (String.ofList ks', rest') := by unfold parseKeySegment; split <;> first | simp_all | rfl
        have htake := takeBareKeyChars_append [] k.toList rest hall (fun c t h => by simpa using (hrest c t h).1)
        refine ⟨by rw [List.cons_append, hseg, ← List.cons_append, ← hlist, htake]; simp only [show k.toList.isEmpty = false by simp [hlist], List.reverse_nil, List.nil_append, Bool.false_eq_true, ↓reduceIte, String.ofList_toList],
          List.all_eq_true.mpr fun c hc => ?_⟩
        rw [hlist] at hall; have hcl := isBareKeyChar_clean c (List.all_eq_true.mp hall c hc)
        simp only [Bool.and_eq_true] at hcl ⊢; exact ⟨⟨hcl.1.1.1.1.1.1.1.1.1.1.1, hcl.1.1.1.1.1.1.1.1.1.1.2⟩, hcl.1.1.1.1.1.1.1.1.1.2⟩
    · simp at hr
  | basic =>
    simp only [renderKey, Option.some.injEq] at hr; subst hr
    obtain ⟨hno3, hp, hcl⟩ := renderBasicQuoted_spec k rest (fun c t h => (hrest c t h).2.1)
    exact ⟨by simp only [String.toList_append, show ("\"" : String).toList = ['"'] from rfl, List.cons_append, List.nil_append, List.append_assoc, parseKeySegment, hp], hcl⟩
  | literal =>
    simp only [renderKey] at hr; split at hr
    · rename_i hcond; injection hr with hrk; subst hrk; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      obtain ⟨hno3, hp, hcl⟩ := renderLiteralQuoted_spec k hcond.1 hcond.2 rest (fun c t h => (hrest c t h).2.2)
      exact ⟨by simp only [String.toList_append, show ("'" : String).toList = ['\''] from rfl, List.cons_append, List.nil_append, List.append_assoc, parseKeySegment, hp], hcl⟩
    · simp at hr
/-- Internal TOML scalar round-trip lemma `renderStringLiteral_parseValueFuel`. -/
theorem renderStringLiteral_parseValueFuel (numApi : CharNumApi) (s : String) (st : StringStyle)
    (rs : String) (hr : renderStringLiteral s st = some rs) (rest : List Char) (fuel : Nat) (hf : fuel ≥ 1)
    (hrest : ∀ c r, rest = c :: r → c ≠ '"' ∧ c ≠ '\'') :
    parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (.string s, rest) ∧ (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
    ((st = .basic ∨ st = .literal) → (rs.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) := by
  cases fuel with | zero => omega | succ f =>
  cases st with
  | basic =>
    simp only [renderStringLiteral, Option.some.injEq] at hr; subst hr
    obtain ⟨hno3, hp, hcl_in⟩ := renderBasicQuoted_spec s rest (fun c t h => (hrest c t h).1)
    exact ⟨by simp only [String.toList_append, show ("\"" : String).toList = ['"'] from rfl, List.cons_append, List.nil_append, List.append_assoc, parseValueFuel, hp, bind, Except.bind],
      List.all_eq_true.mpr fun c hc => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcl_in c hc)).1, fun _ => hcl_in⟩
  | multilineBasic =>
    simp only [renderStringLiteral, Option.some.injEq] at hr; subst hr
    have heq : (escapeBasicBody true s).toList = s.toList.flatMap (fun c => (escapeBasicChar true c).toList) := by simp [escapeBasicBody, String.toList_join, List.flatMap_map]
    refine ⟨?_, ?_, fun h => by rcases h with h | h <;> cases h⟩
    · simp only [String.toList_append, show ("\"\"\"\n" : String).toList = ['"', '"', '"', '\n'] from rfl,
        show ("\"\"\"" : String).toList = ['"', '"', '"'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
      let body := (escapeBasicBody true s).toList ++ ('"' :: '"' :: '"' :: rest)
      rw [show parseValueFuel numApi (f + 1) ('"' :: '"' :: '"' :: '\n' :: body) =
        (parseMultilineBasicBodyFuel (body.length + 1) [] body >>= fun (s', after) => .ok (.string s', after)) by unfold parseValueFuel; rfl]
      have hlen : (s.toList.flatMap (fun c => (escapeBasicChar true c).toList)).length + 1 ≤ body.length + 1 := by
        dsimp only [body]; rw [heq]; simp only [List.length_append, List.length_cons]; omega
      have hm := parseMultilineBasicBodyFuel_escape s.toList [] rest (body.length + 1) (fun c r h => (hrest c r h).1) hlen
      simp only [List.reverse_nil, List.nil_append, String.ofList_toList, List.append_assoc, List.cons_append, ← heq] at hm; dsimp only [body] at hm ⊢; rw [hm]; rfl
    · simp only [String.toList_append, List.all_append, (by decide : (("\"\"\"\n" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true),
        (by decide : (("\"\"\"" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true), Bool.true_and, Bool.and_true]; simpa using escapeBasicBody_clean true s
  | literal =>
    simp only [renderStringLiteral] at hr; split at hr
    · rename_i hcond; injection hr with hrs; subst hrs; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      obtain ⟨hno3, hp, hcl_in⟩ := renderLiteralQuoted_spec s hcond.1 hcond.2 rest (fun c t h => (hrest c t h).2)
      exact ⟨by simp only [String.toList_append, show ("'" : String).toList = ['\''] from rfl, List.cons_append, List.nil_append, List.append_assoc, parseValueFuel, hp, bind, Except.bind],
        List.all_eq_true.mpr fun c hc => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcl_in c hc)).1, fun _ => hcl_in⟩
    · simp at hr
  | multilineLiteral =>
    simp only [renderStringLiteral] at hr; split at hr
    · rename_i hcond; injection hr with hrs; subst hrs; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond; rcases hcond with ⟨⟨hclean, hno_sub⟩, hno_end⟩
      refine ⟨?_, ?_, fun h => by rcases h with h | h <;> cases h⟩
      · simp only [String.toList_append, show ("'''\n" : String).toList = ['\'', '\'', '\'', '\n'] from rfl,
          show ("'''" : String).toList = ['\'', '\'', '\''] from rfl, List.cons_append, List.nil_append, List.append_assoc]
        let body := s.toList ++ ('\'' :: '\'' :: '\'' :: rest)
        rw [show parseValueFuel numApi (f + 1) ('\'' :: '\'' :: '\'' :: '\n' :: body) =
          (parseMultilineLiteralBodyFuel (body.length + 1) [] body >>= fun (s', after) => .ok (.string s', after)) by unfold parseValueFuel; rfl]
        have hm := parseMultilineLiteralBodyFuel_list s.toList [] rest (body.length + 1)
          (no_triple_quote_of_not_containsSubstr s hno_sub) (getLast_ne_quote_of_not_endsWith s hno_end)
          (fun c r h => (hrest c r h).2) (by dsimp only [body]; simp only [List.length_append, List.length_cons]; omega)
        simp only [List.reverse_nil, List.nil_append, String.ofList_toList, List.append_assoc, List.cons_append] at hm; dsimp only [body] at hm ⊢; rw [hm]; rfl
      · simp only [String.toList_append, List.all_append, (by decide : (("'''\n" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true),
          (by decide : (("'''" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true), Bool.true_and, Bool.and_true]; simpa using hclean
    · simp at hr
private theorem dite_true {α : Type} {P : Prop} [Decidable P] {f : P → α} {g : ¬ P → α} (h : P) : dite P f g = f h := by split <;> first | rfl | contradiction
private theorem renderDate_spec (d : Std.Time.PlainDate) (ds : String) (hr : renderDate d = some ds) :
    (∃ y1 y2 y3 y4 m1 m2 d1 d2, ds.toList = [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] ∧ ([y1, y2, y3, y4, m1, m2, d1, d2].all isAsciiDigit = true)) ∧
    (∀ rest, parseDatePart (ds.toList ++ rest) = .ok (d, rest) ∧ hasDatePrefix (ds.toList ++ rest) = true) ∧ ds.toList.all isCleanTokChar = true := by
  simp only [renderDate] at hr; split at hr
  · rename_i hvd; injection hr with hds; subst hds
    have hv : (0 : Int) ≤ d.year ∧ d.year ≤ 9999 := by simpa [validTomlDate] using hvd
    have hy_eq : Int.ofNat d.year.toNat = (d.year : Int) := Int.toNat_of_nonneg hv.1
    have hy_nat : d.year.toNat < 10000 := Int.ofNat_lt.mp (by have : Int.ofNat d.year.toNat ≤ 9999 := hy_eq ▸ hv.2; omega)
    have hm_prop := d.month.property; have hd_prop := d.day.property
    obtain ⟨y1, y2, y3, y4, hy_l, hy_f, ay1, ay2, ay3, ay4⟩ := fourDigits_padNatZero d.year.toNat hy_nat
    obtain ⟨m1, m2, hm_l, hm_t, am1, am2⟩ := twoDigits_padNatZero d.month.val.toNat (by omega); obtain ⟨d1, d2, hd_l, hd_t, ad1, ad2⟩ := twoDigits_padNatZero d.day.val.toNat (by omega)
    have hlist : (padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++ padNatZero 2 d.day.val.toNat).toList =
        [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] := by simp only [String.toList_append, hy_l, show ("-" : String).toList = ['-'] from rfl, hm_l, hd_l]; rfl
    have hm_ok : d.month.val.toNat ≥ 1 ∧ d.month.val.toNat ≤ 12 := ⟨by omega, by omega⟩; have hd_ok : d.day.val.toNat ≥ 1 ∧ d.day.val.toNat ≤ 31 := ⟨by omega, by omega⟩
    have hcal : Std.Time.PlainDate.ofYearMonthDay? (Std.Time.Year.Offset.ofInt (Int.ofNat d.year.toNat))
        (Std.Time.Month.Ordinal.ofNat d.month.val.toNat hm_ok) (Std.Time.Day.Ordinal.ofNat d.day.val.toNat hd_ok) = some d := by
      rw [show Std.Time.Year.Offset.ofInt (Int.ofNat d.year.toNat) = d.year from Int.toNat_of_nonneg hv.1,
        show Std.Time.Month.Ordinal.ofNat d.month.val.toNat hm_ok = d.month from Subtype.ext (Int.toNat_of_nonneg (by omega)),
        show Std.Time.Day.Ordinal.ofNat d.day.val.toNat hd_ok = d.day from Subtype.ext (Int.toNat_of_nonneg (by omega)), Std.Time.PlainDate.ofYearMonthDay?]; exact dite_true d.valid
    exact ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hlist, by simp [ay1, ay2, ay3, ay4, am1, am2, ad1, ad2]⟩,
      fun rest => ⟨by rw [hlist]; simp only [List.cons_append, List.nil_append, parseDatePart, hy_f, hm_t, hd_t]; rw [dite_true hm_ok, dite_true hd_ok, hcal]; simp [hvd],
        by rw [hlist]; simp [hasDatePrefix, ay1, ay2, ay3, ay4, am1, am2, ad1, ad2]⟩,
      by simp only [String.toList_append, List.all_append, (padNatZero_all_digit_and_foldl _ _).2.1, (by decide : "-".toList.all isCleanTokChar = true), Bool.and_self]⟩
  · simp at hr
private theorem foldl_digits_add (ds : List Char) (init : Nat) :
    ds.foldl (fun a c => a * 10 + digitVal c) init = init * pow10Nat ds.length + ds.foldl (fun a c => a * 10 + digitVal c) 0 := by
  induction ds generalizing init with
  | nil => simp [pow10Nat]
  | cons c cs ih => simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]; rw [ih (init * 10 + digitVal c), ih (digitVal c), pow10Nat, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
private theorem takeDigits_append (acc ds rest : List Char) (hds : ds.all isAsciiDigit = true) (hrest : ∀ c r, rest = c :: r → isAsciiDigit c = false) :
    takeDigits acc (ds ++ rest) = (acc.reverse ++ ds, rest) := by
  induction ds generalizing acc with
  | nil => cases rest with | nil => simp [takeDigits] | cons c r => simp [takeDigits, hrest c r rfl]
  | cons d ds ih => simp only [List.all_cons, Bool.and_eq_true] at hds; simp [takeDigits, hds.1, ih (d :: acc) hds.2]
private theorem fracDigitsToNanosAux_append (k acc : Nat) (ds1 ds2 : List Char) (hlen : ds1.length ≤ k) :
    fracDigitsToNanosAux k acc (ds1 ++ ds2) = fracDigitsToNanosAux (k - ds1.length) (acc * pow10Nat ds1.length + ds1.foldl (fun a c => a * 10 + digitVal c) 0) ds2 := by
  induction ds1 generalizing k acc with
  | nil => simp [pow10Nat]
  | cons d ds ih =>
    cases k with | zero => simp at hlen | succ k' =>
    simp only [List.length_cons] at hlen; simp only [List.cons_append, fracDigitsToNanosAux, List.length_cons]
    rw [ih k' (acc * 10 + digitVal d) (by omega), show (d :: ds).foldl (fun a c => a * 10 + digitVal c) 0 =
      digitVal d * pow10Nat ds.length + ds.foldl (fun a c => a * 10 + digitVal c) 0 by simpa using foldl_digits_add ds (digitVal d), pow10Nat]
    congr 1
    · omega
    · rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
private theorem fracDigitsToNanosAux_nil (k acc : Nat) : fracDigitsToNanosAux k acc [] = acc * pow10Nat k := by
  induction k generalizing acc with
  | zero => simp [fracDigitsToNanosAux, pow10Nat]
  | succ k ih => simp [fracDigitsToNanosAux, pow10Nat, ih (acc * 10), Nat.mul_assoc, Nat.mul_comm 10]
private theorem renderTime_spec (t : Std.Time.PlainTime) (fd : Nat) (ts : String) (hr : renderTime t fd = some ts) :
    (∃ h1 h2 m1 m2 s1 s2 fracCs, ts.toList = [h1, h2, ':', m1, m2, ':', s1, s2] ++ fracCs ∧
      ([h1, h2, m1, m2, s1, s2].all isAsciiDigit = true) ∧ (fracCs.all fun c => !isUnquotedDelim c) = true) ∧
    (∀ rest, (∀ c r, rest = c :: r → isAsciiDigit c = false ∧ (fd = 0 → c ≠ '.')) →
      parseTimePart (ts.toList ++ rest) = .ok (t, rest) ∧ hasTimePrefix (ts.toList ++ rest) = true) ∧ ts.toList.all isCleanTokChar = true := by
  simp only [renderTime] at hr; split at hr
  · simp at hr
  · rename_i hvt; simp only [Bool.not_eq_true] at hvt; have hvt_sec : t.second.val ≤ 59 := by simpa [validTomlTime] using hvt
    cases hfrac : formatNanosExact t.nanosecond.val.toNat fd with
    | none => simp [hfrac] at hr
    | some frac =>
      rw [hfrac] at hr; injection hr with hts; subst hts
      have hh_prop := t.hour.property; have hm_prop := t.minute.property; have hs_prop := t.second.property; have hn_prop := t.nanosecond.property
      obtain ⟨h1, h2, hh_l, hh_t, ah1, ah2⟩ := twoDigits_padNatZero t.hour.val.toNat (by omega)
      obtain ⟨m1, m2, hm_l, hm_t, am1, am2⟩ := twoDigits_padNatZero t.minute.val.toNat (by omega); obtain ⟨s1, s2, hs_l, hs_t, as1, as2⟩ := twoDigits_padNatZero t.second.val.toNat (by omega)
      have hh_ok : t.hour.val.toNat ≤ 23 := (by omega); have mm_ok : t.minute.val.toNat ≤ 59 := (by omega); have ss_ok : t.second.val.toNat ≤ 59 := (by omega)
      have mk_tm (ns : Std.Time.Nanosecond.Ordinal) (hns : ns = t.nanosecond) :
          Std.Time.PlainTime.mk (Std.Time.Hour.Ordinal.ofNat t.hour.val.toNat hh_ok) (Std.Time.Minute.Ordinal.ofNat t.minute.val.toNat mm_ok)
            (Std.Time.Second.Ordinal.ofNat t.second.val.toNat (Nat.le_trans ss_ok (by decide))) ns = t :=
        Std.Time.PlainTime.ext (Subtype.ext (Int.toNat_of_nonneg (by omega))) (Subtype.ext (Int.toNat_of_nonneg (by omega))) (Subtype.ext (Int.toNat_of_nonneg (by omega))) hns
      have hbase : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat).toList =
          [h1, h2, ':', m1, m2, ':', s1, s2] := by simp only [String.toList_append, hh_l, show (":" : String).toList = [':'] from rfl, hm_l, hs_l]; rfl
      have hcol_cl : ":".toList.all isCleanTokChar = true := by decide
      have hfull_eq : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat ++ frac).toList =
          [h1, h2, ':', m1, m2, ':', s1, s2] ++ frac.toList := by rw [String.toList_append, hbase]
      have hpref (rest) : hasTimePrefix ((padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat ++ frac).toList ++ rest) = true := by
        rw [hfull_eq]; simp [hasTimePrefix, ah1, ah2, am1, am2, as1, as2]
      simp only [formatNanosExact] at hfrac
      if hgt9 : fd > 9 then simp [hgt9] at hfrac else
      simp only [hgt9, ↓reduceIte] at hfrac
      if hfd0 : fd = 0 then
        subst hfd0; simp only [beq_self_eq_true, ↓reduceIte] at hfrac
        if hn0 : t.nanosecond.val.toNat = 0 then
          simp only [hn0, beq_self_eq_true, ↓reduceIte] at hfrac; injection hfrac with hfr; subst hfr
          have htm := mk_tm 0 (Subtype.ext (by change (0 : Int) = t.nanosecond.val; omega))
          refine ⟨⟨h1, h2, m1, m2, s1, s2, [], by simpa using hfull_eq, by simp [ah1, ah2, am1, am2, as1, as2], rfl⟩, fun rest hrest => ⟨?_, hpref rest⟩,
            by simp only [String.append_empty, String.toList_append, List.all_append, (padNatZero_all_digit_and_foldl _ _).2.1, hcol_cl, Bool.and_self]⟩
          rw [String.append_empty, hbase]; have hndot : ∀ r, rest ≠ '.' :: r := fun r hr' => (hrest '.' r hr').2 rfl rfl
          simp only [List.cons_append, List.nil_append, parseTimePart, hh_t, hm_t, hs_t, hh_ok, mm_ok, ss_ok, ↓reduceDIte, htm]
        else simp [hn0] at hfrac
      else
        simp only [beq_false_of_ne hfd0, Bool.false_eq_true, ↓reduceIte] at hfrac
        if hmod : t.nanosecond.val.toNat % pow10Nat (9 - fd) = 0 then
          simp only [hmod, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hfrac; injection hfrac with hfr; subst hfr
          have h9 : fd + (9 - fd) = 9 := by omega
          have hdiv_lt : t.nanosecond.val.toNat / pow10Nat (9 - fd) < pow10Nat fd := by
            have hn_lt9 : t.nanosecond.val.toNat < pow10Nat 9 := by rw [pow10Nat_9]; omega
            exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← pow10Nat_add, h9]; exact hn_lt9)
          generalize hq_def : t.nanosecond.val.toNat / pow10Nat (9 - fd) = q at hdiv_lt hfull_eq hpref ⊢
          have hlen_pad := padNatZero_length_of_lt fd q (by omega) hdiv_lt; obtain ⟨hpad_d, hpad_cl, hpad_f⟩ := padNatZero_all_digit_and_foldl fd q
          have hfrac_nd : (("." ++ padNatZero fd q).toList.all fun c => !isUnquotedDelim c) = true := List.all_eq_true.mpr fun c hc => by
            simp only [String.toList_append, show ("." : String).toList = ['.'] from rfl, List.singleton_append, List.mem_cons] at hc
            exact hc.elim (fun e => e ▸ by decide) fun hc' => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hpad_cl c hc')).2
          refine ⟨⟨h1, h2, m1, m2, s1, s2, ("." ++ padNatZero fd q).toList, hfull_eq, by simp [ah1, ah2, am1, am2, as1, as2], hfrac_nd⟩, fun rest hrest => ⟨?_, hpref rest⟩,
            by simp only [String.toList_append, List.all_append, (padNatZero_all_digit_and_foldl _ _).2.1, hcol_cl, (by decide : ".".toList.all isCleanTokChar = true), Bool.and_self]⟩
          have htake : takeDigits [] ((padNatZero fd q).toList ++ rest) = ((padNatZero fd q).toList, rest) := by
            simpa using takeDigits_append [] (padNatZero fd q).toList rest hpad_d (fun c r h => (hrest c r h).1)
          have hne_empty : ((padNatZero fd q).toList).isEmpty = false := by
            cases hpl : (padNatZero fd q).toList with | nil => rw [hpl] at hlen_pad; simp at hlen_pad; omega | cons _ _ => rfl
          have hnano_eq : fracDigitsToNanos (padNatZero fd q).toList = t.nanosecond.val.toNat := by
            simp only [fracDigitsToNanos]; rw [← List.append_nil (padNatZero fd q).toList, fracDigitsToNanosAux_append 9 0 _ [] (by rw [hlen_pad]; omega), Nat.zero_mul, Nat.zero_add, hpad_f, fracDigitsToNanosAux_nil, hlen_pad]
            have hd := Nat.div_add_mod t.nanosecond.val.toNat (pow10Nat (9 - fd)); rw [hq_def, hmod, Nat.add_zero, Nat.mul_comm] at hd; rw [hd]; exact Nat.min_eq_right (by omega)
          have htm := mk_tm (Std.Time.Nanosecond.Ordinal.ofNat (fracDigitsToNanos (padNatZero fd q).toList) (Nat.min_le_left _ _))
            (Subtype.ext (by change Int.ofNat (fracDigitsToNanos (padNatZero fd q).toList) = t.nanosecond.val; rw [hnano_eq]; exact Int.toNat_of_nonneg (by omega)))
          rw [hfull_eq, String.toList_append, show ("." : String).toList = ['.'] from rfl]
          simp only [List.cons_append, List.nil_append, parseTimePart, hh_t, hm_t, hs_t, hh_ok, mm_ok, ss_ok, ↓reduceDIte, htake, hne_empty, Bool.false_eq_true, ↓reduceIte, htm]
        else simp [hmod] at hfrac
private theorem renderOffset_spec (o : Std.Time.TimeZone.Offset) (style : OffsetStyle) (os : String) (hr : renderOffset o style = some os) :
    parseOffsetPart os.toList = .ok o ∧ os.toList.all isCleanTokChar = true ∧ (∀ c r, os.toList = c :: r → isAsciiDigit c = false ∧ c ≠ '.') := by
  simp only [renderOffset] at hr; split at hr
  · simp at hr
  · rename_i hvo; simp only [Bool.not_eq_true] at hvo
    have hvo' : o.second.val % 60 = 0 ∧ -86340 ≤ o.second.val ∧ o.second.val ≤ 86340 := by simpa [validTomlOffset] using hvo
    if hz : o.second.val = 0 then
      have ho_eq : Std.Time.TimeZone.Offset.ofSeconds 0 = o := Std.Time.TimeZone.Offset.ext (Std.Time.Internal.UnitVal.ext hz.symm)
      simp only [hz, beq_self_eq_true, ↓reduceIte] at hr; cases style <;> simp only [Option.some.injEq] at hr <;> subst hr
      · exact ⟨by rw [show ("Z" : String).toList = ['Z'] from rfl, parseOffsetPart, ho_eq], by decide, fun c r h => by rw [show ("Z" : String).toList = ['Z'] from rfl] at h; injection h with hc _; subst hc; decide⟩
      · exact ⟨by rw [show ("z" : String).toList = ['z'] from rfl, parseOffsetPart, ho_eq], by decide, fun c r h => by rw [show ("z" : String).toList = ['z'] from rfl] at h; injection h with hc _; subst hc; decide⟩
      · have hlist : ("+00:00" : String).toList = ['+', '0', '0', ':', '0', '0'] := rfl
        exact ⟨by rw [hlist, show parseOffsetPart ['+', '0', '0', ':', '0', '0'] = .ok (Std.Time.TimeZone.Offset.ofSeconds 0) by simp [parseOffsetPart, show twoDigitsNat? '0' '0' = some 0 from rfl, validTomlOffset]; rfl, ho_eq],
          by decide, fun c r h => by rw [hlist] at h; injection h with hc _; subst hc; decide⟩
    else
      simp only [beq_false_of_ne hz, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hr; subst hr
      let hh := o.second.val.natAbs / 60 / 60; let mm := (o.second.val.natAbs / 60) % 60
      have hdiv_lt : hh ≤ 23 := (by dsimp [hh]; omega); have hmod_lt : mm ≤ 59 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
      obtain ⟨h1, h2, hh_l, hh_t, _, _⟩ := twoDigits_padNatZero hh (by omega); obtain ⟨m1, m2, hm_l, hm_t, _, _⟩ := twoDigits_padNatZero mm (by omega)
      have htotal_nat : hh * 3600 + mm * 60 = o.second.val.natAbs := by dsimp [hh, mm]; omega
      have hsign_char : (if o.second.val < 0 then "-" else "+").toList = [if o.second.val < 0 then '-' else '+'] := by split <;> rfl
      have hlist : ((if o.second.val < 0 then "-" else "+") ++ padNatZero 2 hh ++ ":" ++ padNatZero 2 mm).toList =
          [if o.second.val < 0 then '-' else '+', h1, h2, ':', m1, m2] := by simp only [String.toList_append, hsign_char, hh_l, show (":" : String).toList = [':'] from rfl, hm_l]; rfl
      have hsec_eq : (if Int.ofNat (hh * 3600 + mm * 60) == 0 then (0 : Int) else if (if o.second.val < 0 then '-' else '+') == '-' then
          -Int.ofNat (hh * 3600 + mm * 60) else Int.ofNat (hh * 3600 + mm * 60)) = o.second.val := by
        rw [htotal_nat]; simp only [beq_false_of_ne (by change (o.second.val.natAbs : Int) ≠ 0; omega : Int.ofNat o.second.val.natAbs ≠ 0), Bool.false_eq_true, ↓reduceIte]
        if hneg : o.second.val < 0 then simp only [hneg, ↓reduceIte, beq_self_eq_true]; change -(o.second.val.natAbs : Int) = o.second.val; omega
        else simp only [hneg, ↓reduceIte, show ('+' == '-') = false from rfl, Bool.false_eq_true]; change (o.second.val.natAbs : Int) = o.second.val; omega
      have ho_eq : Std.Time.TimeZone.Offset.ofSeconds (Std.Time.Second.Offset.ofInt o.second.val) = o := Std.Time.TimeZone.Offset.ext (Std.Time.Internal.UnitVal.ext rfl)
      refine ⟨?_, by simp only [String.toList_append, List.all_append, (by split <;> decide : (if o.second.val < 0 then "-" else "+").toList.all isCleanTokChar = true),
        (padNatZero_all_digit_and_foldl _ _).2.1, (by decide : ":".toList.all isCleanTokChar = true), Bool.and_self],
        fun c r hcr => by rw [hlist] at hcr; injection hcr with hc _; subst hc; split <;> exact ⟨rfl, by decide⟩⟩
      rw [hlist]; simp only [parseOffsetPart, hh_t, hm_t,
        (by split <;> decide : ((if o.second.val < 0 then '-' else '+') == '+' || (if o.second.val < 0 then '-' else '+') == '-') = true),
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hdiv_lt, hmod_lt⟩ : (decide (hh ≤ 23) && decide (mm ≤ 59)) = true), ↓reduceIte]
      rw [hsec_eq, ho_eq, show validTomlOffset o = true by simpa using hvo]; simp only [↓reduceIte]
/-- Internal TOML scalar round-trip lemma `renderOffset_parseOffsetPart`. -/
theorem renderOffset_parseOffsetPart (o : Std.Time.TimeZone.Offset) (style : OffsetStyle) (os : String) (hr : renderOffset o style = some os) :
    parseOffsetPart os.toList = .ok o ∧ (os.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true :=
  ⟨(renderOffset_spec o style os hr).1, (renderOffset_spec o style os hr).2.1⟩
private theorem takeNonDelim_append (acc tok rest : List Char)
    (htok : tok.all (fun c => !isUnquotedDelim c) = true) (hrest : ∀ c r, rest = c :: r → isUnquotedDelim c = true) :
    takeNonDelim acc (tok ++ rest) = (acc.reverse ++ tok, rest) := by
  induction tok generalizing acc with
  | nil => cases rest with | nil => simp [takeNonDelim] | cons c r => simp [takeNonDelim, hrest c r rfl]
  | cons c cs ih => simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at htok; simp [takeNonDelim, htok.1, ih (c :: acc) htok.2]
/-- Internal TOML scalar round-trip lemma `takeUnquotedToken_noSpace`. -/
theorem takeUnquotedToken_noSpace (tok rest : List Char) (htok : tok.all (fun c => !isUnquotedDelim c) = true)
    (hrest : ∀ c r, rest = c :: r → isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) :
    takeUnquotedTokenChars (tok ++ rest) = (tok, rest) := by
  unfold takeUnquotedTokenChars; split
  · rename_i y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 rest' heq
    if hcond : (isAsciiDigit y1 && isAsciiDigit y2 && isAsciiDigit y3 && isAsciiDigit y4 && isAsciiDigit m1 && isAsciiDigit m2 && isAsciiDigit d1 &&
        isAsciiDigit d2 && isAsciiDigit h1 && isAsciiDigit h2 && isAsciiDigit min1 && isAsciiDigit min2 && isAsciiDigit s1 && isAsciiDigit s2) = true then
      exfalso; simp only [Bool.and_eq_true] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩, hm1⟩, hm2⟩, hd1⟩, hd2⟩, hh1⟩, _⟩, _⟩, _⟩, _⟩, _⟩
      let pfx10 : List Char := [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2]
      have hpfx_nd : pfx10.all (fun c => !isUnquotedDelim c) = true := by
        have had_nd : ∀ x, isAsciiDigit x = true → (!isUnquotedDelim x) = true := fun x hx => ((Bool.and_eq_true _ _).mp (isAsciiDigit_clean x hx)).2
        simp [pfx10, had_nd _ hy1, had_nd _ hy2, had_nd _ hy3, had_nd _ hy4, had_nd _ hm1, had_nd _ hm2, had_nd _ hd1, had_nd _ hd2, show (!isUnquotedDelim '-') = true by decide]
      have heq' : tok ++ rest = pfx10 ++ (' ' :: h1 :: h2 :: ':' :: min1 :: min2 :: ':' :: s1 :: s2 :: rest') := heq
      if hlt10 : tok.length < 10 then
        cases hrest_eq : rest with
        | nil => have hlen := congrArg List.length heq'; simp [hrest_eq, pfx10] at hlen; omega
        | cons c r =>
          have hget := congrArg (·[tok.length]?) heq'
          rw [hrest_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, List.getElem?_append_left (by simp [pfx10]; omega)] at hget
          have hnd := List.all_eq_true.mp hpfx_nd c (List.mem_of_getElem? hget.symm); simp [(hrest c r hrest_eq).1] at hnd
      else if heq10 : tok.length = 10 then
        have hinj := List.append_inj heq' (by simp [pfx10, heq10]); have hnd := (hrest ' ' _ hinj.2).2 rfl h1 _ rfl; simp [hh1] at hnd
      else
        have hget := congrArg (·[10]?) heq'; rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by simp [pfx10])] at hget
        simp only [pfx10, List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero] at hget
        have hnd := List.all_eq_true.mp htok ' ' (List.mem_of_getElem? hget); simp [show isUnquotedDelim ' ' = true from rfl] at hnd
    else simp only [hcond, Bool.false_eq_true, ↓reduceIte]; simpa using takeNonDelim_append [] tok rest htok (fun c r h => (hrest c r h).1)
  · simpa using takeNonDelim_append [] tok rest htok (fun c r h => (hrest c r h).1)
/-- Internal TOML scalar round-trip lemma `renderDate_localDate`. -/
theorem renderDate_localDate (d : Std.Time.PlainDate) (ds : String) (hr : renderDate d = some ds) :
    parseDateTimeChars ds.toList = some (.ok (.localDate d)) ∧
    (ds.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧ (∀ c r, ds.toList = c :: r → isAsciiDigit c = true) := by
  obtain ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hlist, hdigs⟩, hp, hcl⟩ := renderDate_spec d ds hr; obtain ⟨hp0, hpref0⟩ := hp []; simp only [List.append_nil] at hp0 hpref0
  exact ⟨by simp [parseDateTimeChars, hpref0, hp0], hcl, fun c r hcr => by rw [hlist] at hcr; injection hcr with hc _; subst hc; exact List.all_eq_true.mp hdigs _ (by simp)⟩
/-- Internal TOML scalar round-trip lemma `renderTime_localTime`. -/
theorem renderTime_localTime (t : Std.Time.PlainTime) (fd : Nat) (ts : String) (hr : renderTime t fd = some ts) :
    parseDateTimeChars ts.toList = some (.ok (.localTime t)) ∧
    (ts.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧ (∀ c r, ts.toList = c :: r → isAsciiDigit c = true) := by
  obtain ⟨⟨h1, h2, m1, m2, s1, s2, fracCs, hlist, hdigs, _⟩, hp, hcl⟩ := renderTime_spec t fd ts hr
  obtain ⟨hp0, hpref0⟩ := hp [] (fun _ _ h => by cases h); simp only [List.append_nil] at hp0 hpref0
  have hno_date : hasDatePrefix ts.toList = false := by
    rw [hlist]; unfold hasDatePrefix; split
    · rename_i heq; rw [← (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).1]; simp [show isAsciiDigit ':' = false from rfl]
    · rfl
  exact ⟨by simp [parseDateTimeChars, hno_date, hpref0, hp0], hcl, fun c r hcr => by rw [hlist] at hcr; injection hcr with hc _; subst hc; exact List.all_eq_true.mp hdigs _ (by simp)⟩
private theorem renderDateTimeSep_spec (sep : DateTimeSep) : ∃ ch : Char, (renderDateTimeSep sep).toList = [ch] ∧ (ch == 'T' || ch == 't' || ch == ' ') = true := by
  cases sep <;> exact ⟨_, rfl, rfl⟩
/-- Internal TOML scalar round-trip lemma `renderDateTime_localDateTime`. -/
theorem renderDateTime_localDateTime (dt : Std.Time.PlainDateTime) (sep : DateTimeSep) (fd : Nat)
    (ds ts : String) (hdr : renderDate dt.date = some ds) (htr : renderTime dt.time fd = some ts) :
    parseDateTimeChars (ds ++ renderDateTimeSep sep ++ ts).toList = some (.ok (.localDateTime dt)) := by
  obtain ⟨_, hdp_all, _⟩ := renderDate_spec dt.date ds hdr; obtain ⟨_, htp_all, _⟩ := renderTime_spec dt.time fd ts htr
  obtain ⟨htp, _⟩ := htp_all [] (fun _ _ h => by cases h); simp only [List.append_nil] at htp
  obtain ⟨ch, hsep_l, hsep_ok⟩ := renderDateTimeSep_spec sep; obtain ⟨hdp, hdpref⟩ := hdp_all (ch :: ts.toList)
  rw [show (ds ++ renderDateTimeSep sep ++ ts).toList = ds.toList ++ ch :: ts.toList by simp [String.toList_append, hsep_l]]
  simp [parseDateTimeChars, hdpref, hdp, hsep_ok, htp, show Std.Time.PlainDateTime.mk dt.date dt.time = dt by cases dt; rfl]
/-- Internal TOML scalar round-trip lemma `renderOffsetDateTime_offsetDateTime`. -/
theorem renderOffsetDateTime_offsetDateTime (odt : TomlOffsetDateTime)
    (sep : DateTimeSep) (oStyle : OffsetStyle) (fd : Nat) (ds ts os : String)
    (hdr : renderDate odt.dateTime.date = some ds) (htr : renderTime odt.dateTime.time fd = some ts) (hor : renderOffset odt.offset oStyle = some os) :
    parseDateTimeChars (ds ++ renderDateTimeSep sep ++ ts ++ os).toList = some (.ok (.offsetDateTime odt)) := by
  obtain ⟨_, hdp_all, _⟩ := renderDate_spec odt.dateTime.date ds hdr; obtain ⟨_, htp_all, _⟩ := renderTime_spec odt.dateTime.time fd ts htr
  obtain ⟨hop, _, hohd⟩ := renderOffset_spec odt.offset oStyle os hor
  obtain ⟨htp, _⟩ := htp_all os.toList (fun c r h => ⟨(hohd c r h).1, fun _ => (hohd c r h).2⟩)
  obtain ⟨ch, hsep_l, hsep_ok⟩ := renderDateTimeSep_spec sep; obtain ⟨hdp, hdpref⟩ := hdp_all (ch :: (ts.toList ++ os.toList))
  cases hos : os.toList with
  | nil => rw [hos] at hop; cases hop
  | cons o0 os' =>
    rw [show (ds ++ renderDateTimeSep sep ++ ts ++ os).toList = ds.toList ++ ch :: (ts.toList ++ o0 :: os') by simp [String.toList_append, hsep_l, hos, List.append_assoc]]
    rw [hos] at htp hop hdp hdpref
    simp [parseDateTimeChars, hdpref, hdp, hsep_ok, htp, hop, show TomlOffsetDateTime.mk (Std.Time.PlainDateTime.mk odt.dateTime.date odt.dateTime.time) odt.offset = odt by rcases odt with ⟨⟨_, _⟩, _⟩; rfl]
/-- Internal TOML scalar round-trip lemma `clean_all_not_unquotedDelim`. -/
theorem clean_all_not_unquotedDelim (cs : List Char)
    (h : (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true) : cs.all (fun c => !isUnquotedDelim c) = true :=
  List.all_eq_true.mpr fun c hc => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h c hc)).2
/-- Internal TOML scalar round-trip lemma `dateTime_space_takeUnquotedToken`. -/
theorem dateTime_space_takeUnquotedToken (d : Std.Time.PlainDate) (t : Std.Time.PlainTime) (fd : Nat) (ds ts suffix : String)
    (hdr : renderDate d = some ds) (htr : renderTime t fd = some ts) (hsuf : suffix.toList.all (fun c => !isUnquotedDelim c) = true)
    (rest : List Char) (hrest : ∀ c r, rest = c :: r → isUnquotedDelim c = true) :
    takeUnquotedTokenChars ((ds ++ " " ++ ts ++ suffix).toList ++ rest) = ((ds ++ " " ++ ts ++ suffix).toList, rest) := by
  obtain ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, hd_digs⟩, _, _⟩ := renderDate_spec d ds hdr
  obtain ⟨⟨h1, h2, min1, min2, s1, s2, fracCs, hts, ht_digs, hfrac_nd⟩, _, _⟩ := renderTime_spec t fd ts htr
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hd_digs ht_digs
  rw [show (ds ++ " " ++ ts ++ suffix).toList =
    [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++ (fracCs ++ suffix.toList) by
      simp [String.toList_append, hds, show (" " : String).toList = [' '] from rfl, hts], List.append_assoc]
  simp only [List.cons_append, List.nil_append, takeUnquotedTokenChars,
    hd_digs.1, hd_digs.2.1, hd_digs.2.2.1, hd_digs.2.2.2.1, hd_digs.2.2.2.2.1, hd_digs.2.2.2.2.2.1, hd_digs.2.2.2.2.2.2.1, hd_digs.2.2.2.2.2.2.2,
    ht_digs.1, ht_digs.2.1, ht_digs.2.2.1, ht_digs.2.2.2.1, ht_digs.2.2.2.2.1, ht_digs.2.2.2.2.2, Bool.and_self, ↓reduceIte]
  rw [takeNonDelim_append [] (fracCs ++ suffix.toList) rest (by simp [List.all_append, hfrac_nd, hsuf]) hrest]; simp
private def isIntModelChar (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') || c == '_'
private theorem isIntModelChar_props (c : Char) (h : isIntModelChar c = true) : c ≠ ':' ∧ c ≠ '.' ∧ c ≠ '-' := by
  have hlt : ∀ x, isIntModelChar x = true → x.toNat < 128 := fun x hx => by
    simp only [isIntModelChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
    rcases hx with (((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | rfl) <;> first | decide | (have : x.toNat ≤ 102 := Nat.le_trans h2 (by decide); omega)
  have hq := forall_ascii_of_decide isIntModelChar (fun x => x != ':' && x != '.' && x != '-') hlt (by decide) c h
  simp only [Bool.and_eq_true, bne_iff_ne] at hq; exact ⟨hq.1.1, hq.1.2, hq.2⟩
private theorem digitVal?_isIntModelChar (b : NumBase) (c : Char) (d : Nat) (h : NumParse.Model.digitVal? b c = some d) : isIntModelChar c = true := by
  cases b <;> simp only [NumParse.Model.digitVal?] at h
  · repeat (split at h; · rename_i hc; simp only [beq_iff_eq] at hc; subst hc; rfl)
    cases h
  · split at h <;> first | (rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; simp [isIntModelChar, hc.1, show c ≤ '9' from Nat.le_trans hc.2 (by decide)]; done) | cases h
  · split at h <;> first | (rename_i hc; simp [isIntModelChar, hc]; done) | cases h
  · repeat (split at h; · rename_i hc; simp [isIntModelChar, hc])
    cases h
private theorem consumeIntDigits_chars (b : NumBase) (acc : Nat) (cs : List Char) (n : Nat)
    (h : NumParse.Model.consumeIntDigits b acc cs = .ok n) : ∀ c ∈ cs, isIntModelChar c = true := by
  fun_induction NumParse.Model.consumeIntDigits b acc cs <;> simp_all
  · exact ⟨rfl, digitVal?_isIntModelChar b _ _ ‹_›⟩
  · exact digitVal?_isIntModelChar b _ _ ‹_›
private theorem parseDecAfterSign_props (neg : Bool) (cs : List Char) (m : Int) (h : NumParse.Model.parseDecAfterSign neg cs = .ok m) :
    (∃ c0 rest, cs = c0 :: rest ∧ isAsciiDigit c0 = true) ∧ (∀ c ∈ cs, c ≠ ':' ∧ c ≠ '.' ∧ c ≠ '-') := by
  unfold NumParse.Model.parseDecAfterSign at h; split at h <;> try cases h
  · split at h
    · exact ⟨⟨'0', [], rfl, rfl⟩, fun c hc => by rcases List.mem_singleton.mp hc with rfl; decide⟩
    · repeat (split at h; all_goals try cases h)
  · rename_i c rest _ _; split at h <;> try cases h
    rename_i d hdv; split at h <;> try cases h
    rename_i n hn; have hd_c : isAsciiDigit c = true := by simp only [NumParse.Model.digitVal?] at hdv; split at hdv <;> first | (rename_i hc; exact hc) | cases hdv
    exact ⟨⟨c, rest, rfl, hd_c⟩, fun ch hch => isIntModelChar_props ch
      ((List.mem_cons.mp hch).elim (fun e => e ▸ digitVal?_isIntModelChar .dec c d hdv) (consumeIntDigits_chars .dec d rest n hn ch))⟩
/-- Internal TOML scalar round-trip lemma `parseIntModelChars_props`. -/
theorem parseIntModelChars_props (cs : List Char) (m : Int) (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    (∃ c0 rest, cs = c0 :: rest ∧ (c0 = '+' ∨ c0 = '-' ∨ isAsciiDigit c0 = true) ∧ (∀ c1 r1, (c0 = '+' ∨ c0 = '-') → rest = c1 :: r1 → isAsciiDigit c1 = true)) ∧
    (∀ c ∈ cs, c ≠ ':' ∧ c ≠ '.') ∧ (∀ c0 r0, cs = c0 :: r0 → ∀ c ∈ r0, c ≠ '-') := by
  have hsigned (sgn : Char) (neg : Bool) (tail : List Char) (hsgn : sgn = '+' ∨ sgn = '-') (hp : NumParse.Model.parseDecAfterSign neg tail = .ok m) :
      (∃ c0 rest, sgn :: tail = c0 :: rest ∧ (c0 = '+' ∨ c0 = '-' ∨ isAsciiDigit c0 = true) ∧ (∀ c1 r1, (c0 = '+' ∨ c0 = '-') → rest = c1 :: r1 → isAsciiDigit c1 = true)) ∧
      (∀ c ∈ sgn :: tail, c ≠ ':' ∧ c ≠ '.') ∧ (∀ c0 r0, sgn :: tail = c0 :: r0 → ∀ c ∈ r0, c ≠ '-') := by
    obtain ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩ := parseDecAfterSign_props neg tail m hp
    exact ⟨⟨sgn, tail, rfl, hsgn.elim Or.inl (Or.inr ∘ Or.inl), fun c1 r1 _ h1 => by rw [h1] at hdr; injection hdr with hc1 _; exact hc1 ▸ hd_dig⟩,
      List.forall_mem_cons.mpr ⟨by rcases hsgn with rfl | rfl <;> decide, fun c hc => ⟨(hchars c hc).1, (hchars c hc).2.1⟩⟩,
      fun _ r0 hcr c hc => by injection hcr with _ hr; subst hr; exact (hchars c hc).2.2⟩
  unfold NumParse.Model.parseIntModelChars at h; split at h
  · cases h
  · split at h <;> first | cases h | exact hsigned '+' false _ (Or.inl rfl) h
  · split at h <;> first | cases h | exact hsigned '-' true _ (Or.inr rfl) h
  · exact hsigned '+' false _ (Or.inl rfl) h
  · exact hsigned '-' true _ (Or.inr rfl) h
  · rename_i _ b rest; cases hbp : NumParse.Model.basePrefix? b with
    | none =>
      rw [hbp] at h; dsimp only at h; obtain ⟨_, hchars⟩ := parseDecAfterSign_props false ('0' :: b :: rest) m h
      exact ⟨⟨'0', b :: rest, rfl, Or.inr (Or.inr rfl), fun _ _ hs => by rcases hs with h1 | h1 <;> cases h1⟩,
        fun c hc => ⟨(hchars c hc).1, (hchars c hc).2.1⟩, fun _ r0 hcr c hc => by injection hcr with _ hr; subst hr; exact (hchars c (List.mem_cons_of_mem _ hc)).2.2⟩
    | some base =>
      rw [hbp] at h; dsimp only at h; split at h <;> try cases h
      rename_i _ c1 cs1 _
      cases hdv : NumParse.Model.digitVal? base c1 with | none => simp [hdv] at h | some d =>
      rw [hdv] at h; dsimp only at h
      cases hn : NumParse.Model.consumeIntDigits base d cs1 with | error => simp [hn] at h | ok n =>
      have hb_ne : b ≠ ':' ∧ b ≠ '.' ∧ b ≠ '-' := by unfold NumParse.Model.basePrefix? at hbp; split at hbp <;> first | decide | cases hbp
      have hbody : ∀ c ∈ c1 :: cs1, c ≠ ':' ∧ c ≠ '.' ∧ c ≠ '-' := List.forall_mem_cons.mpr
        ⟨isIntModelChar_props c1 (digitVal?_isIntModelChar base c1 d hdv), fun c hc => isIntModelChar_props c (consumeIntDigits_chars base d cs1 n hn c hc)⟩
      exact ⟨⟨'0', b :: c1 :: cs1, rfl, Or.inr (Or.inr rfl), fun _ _ hs => by rcases hs with h1 | h1 <;> cases h1⟩,
        List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨⟨hb_ne.1, hb_ne.2.1⟩, fun c hc => ⟨(hbody c hc).1, (hbody c hc).2.1⟩⟩⟩,
        fun _ r0 hcr => by injection hcr with _ hr; subst hr; exact List.forall_mem_cons.mpr ⟨hb_ne.2.2, fun c hc => (hbody c hc).2.2⟩⟩
  · obtain ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩ := parseDecAfterSign_props false cs m h
    have hne_sgn : d0 ≠ '+' ∧ d0 ≠ '-' := ⟨fun he => by subst he; revert hd_dig; decide, fun he => by subst he; revert hd_dig; decide⟩
    exact ⟨⟨d0, dr, hdr, Or.inr (Or.inr hd_dig), fun _ _ hs _ => hs.elim (absurd · hne_sgn.1) (absurd · hne_sgn.2)⟩,
      fun c hc => ⟨(hchars c hc).1, (hchars c hc).2.1⟩, fun _ r0 hcr c hc => by rw [hcr] at hchars; exact (hchars c (List.mem_cons_of_mem _ hc)).2.2⟩
private theorem toString_nat_head_nonzero (n : Nat) (hn : 0 < n) : ∃ d0 ds, (toString n).toList = d0 :: ds ∧ isAsciiDigit d0 = true ∧ d0 ≠ '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    if h10 : n < 10 then
      obtain ⟨hch, had, hdv, _⟩ := toString_lt10_char n h10
      exact ⟨n.digitChar, [], hch, had, fun heq => by have := congrArg digitVal heq; have : digitVal '0' = 0 := rfl; omega⟩
    else
      obtain ⟨d0, ds, hd_l, hd_d, hd_ne0⟩ := ih (n / 10) (by omega) (by omega)
      have hsplit := toString_two_digits_split (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      rw [show n / 10 * 10 + n % 10 = n by omega, hd_l] at hsplit; exact ⟨d0, ds ++ [(n % 10).digitChar], hsplit, hd_d, hd_ne0⟩
private theorem parseDecAfterSign_toString_nat (neg : Bool) (n : Nat) :
    NumParse.Model.parseDecAfterSign neg (toString n).toList = .ok (if neg then -Int.ofNat n else Int.ofNat n) := by
  have hdig_val (c) (hc : isAsciiDigit c = true) : NumParse.Model.digitVal? .dec c = some (digitVal c) := by
    have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigit] using hc
    simp [NumParse.Model.digitVal?, h1.1, h1.2, digitVal]
  have hcons_dec : ∀ (acc : Nat) (ds : List Char), ds.all isAsciiDigit = true →
      NumParse.Model.consumeIntDigits .dec acc ds = .ok (ds.foldl (fun a c => a * 10 + digitVal c) acc) := by
    intro acc ds hds; induction ds generalizing acc with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hds; have hnot_u : c ≠ '_' := fun heq => by subst heq; exact absurd hds.1 (by decide)
      unfold NumParse.Model.consumeIntDigits
      split <;> first | contradiction | (rename_i heq; injection heq with h1 _; exact absurd h1 hnot_u)
                      | (rename_i c1 cs1 _ _ heq; injection heq with h1 h2; subst h1 h2; simp only [hdig_val c hds.1, NumParse.Model.NumBase.radix, List.foldl_cons]; exact ih (acc * 10 + digitVal c) hds.2)
  if hn : n = 0 then subst hn; rw [show (toString (0 : Nat)).toList = ['0'] from rfl]; simp [NumParse.Model.parseDecAfterSign] else
    obtain ⟨d0, ds, hlist, hd0, hne0⟩ := toString_nat_head_nonzero n (by omega)
    obtain ⟨hall, hfold⟩ := toString_all_digit_and_foldl n; rw [hlist] at hall hfold ⊢
    simp only [List.all_cons, Bool.and_eq_true, List.foldl_cons, Nat.zero_mul, Nat.zero_add] at hall hfold
    have hnot_u : d0 ≠ '_' := fun heq => by subst heq; revert hd0; decide
    unfold NumParse.Model.parseDecAfterSign
    split <;> first | contradiction | (rename_i heq; injection heq with h1 _; first | exact absurd h1 hnot_u | exact absurd h1 hne0)
                    | (rename_i c1 rest1 _ _ _ heq; injection heq with h1 h2; subst h1 h2; simp [hdig_val d0 hd0, hcons_dec (digitVal d0) ds hall.2, hfold])
/-- Internal TOML scalar round-trip lemma `formatInt64Canonical_isValidIntLex`. -/
theorem formatInt64Canonical_isValidIntLex (n : Int64) : isValidIntLex (formatInt64Canonical n) n = true := by
  let isCanonChar (c : Char) : Bool := c == '-' || isAsciiDigit c
  have hcanon_props : ∀ c, isCanonChar c = true →
      (!c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && c != '.' && !isDisallowedControl c && c != 'X' && c != 'O' && c != 'B' && c != 'e' && c != 'E') = true :=
    forall_ascii_of_decide isCanonChar
      (fun x => !x.isWhitespace && x != '#' && x != ',' && x != ']' && x != '}' && x != '.' && !isDisallowedControl x && x != 'X' && x != 'O' && x != 'B' && x != 'e' && x != 'E')
      (fun c hc => by simp only [isCanonChar, Bool.or_eq_true, beq_iff_eq] at hc; exact hc.elim (fun e => e ▸ by decide) (isAsciiDigit_lt_128 c)) (by decide)
  have hstr_neg (k) : (toString (Int.negSucc k)).toList = '-' :: (toString (k + 1)).toList := by
    change (("-" ++ (k + 1).repr) : String).toList = '-' :: (toString (k + 1)).toList; simp [String.toList_append, toString]
  have honly : ∀ c ∈ (formatInt64Canonical n).toList, isCanonChar c = true := by
    intro c hc; simp only [formatInt64Canonical] at hc; cases hni : n.toInt with
    | ofNat m => rw [hni, show toString (Int.ofNat m) = toString m from rfl] at hc; simp [isCanonChar, List.all_eq_true.mp (toString_all_digit_and_foldl m).1 c hc]
    | negSucc k => rw [hni, hstr_neg k] at hc; exact (List.mem_cons.mp hc).elim (fun e => e ▸ rfl) fun hc' => by simp [isCanonChar, List.all_eq_true.mp (toString_all_digit_and_foldl (k + 1)).1 c hc']
  have hp_int : NumParse.Model.parseIntModel (formatInt64Canonical n) = .ok n.toInt := by
    simp only [formatInt64Canonical, NumParse.Model.parseIntModel]; cases hni : n.toInt with
    | ofNat m =>
      rw [show toString (Int.ofNat m) = toString m from rfl]; cases m with
      | zero => rw [show (toString (0 : Nat)).toList = ['0'] from rfl]; rfl
      | succ k =>
        obtain ⟨d0, ds, hlist, hd0, hne0⟩ := toString_nat_head_nonzero (k + 1) (by omega)
        have hd := parseDecAfterSign_toString_nat false (k + 1); rw [hlist] at hd ⊢; simp only [Bool.false_eq_true, ↓reduceIte] at hd
        have hnp : d0 ≠ '+' ∧ d0 ≠ '-' := ⟨fun h => by subst h; revert hd0; decide, fun h => by subst h; revert hd0; decide⟩
        unfold NumParse.Model.parseIntModelChars
        split <;> first | contradiction | (rename_i heq; injection heq with h1 _; first | exact absurd h1 hnp.1 | exact absurd h1 hnp.2 | exact absurd h1 hne0) | exact hd
    | negSucc k =>
      rw [hstr_neg k]; obtain ⟨d0, ds, hlist, _, hne0⟩ := toString_nat_head_nonzero (k + 1) (by omega)
      have hd := parseDecAfterSign_toString_nat true (k + 1); rw [hlist] at hd ⊢; simp only [↓reduceIte] at hd
      change NumParse.Model.parseIntModelChars ('-' :: d0 :: ds) = .ok (-Int.ofNat (k + 1)); unfold NumParse.Model.parseIntModelChars
      split <;> first | contradiction | (rename_i heq; cases heq; done) | (rename_i heq; injection heq with _ h2; injection h2 with h3 _; exact absurd h3 hne0)
                      | (rename_i _ _ _ heq; injection heq with _ h2; subst h2; exact hd) | (rename_i _ _ _ _ hne _; exact False.elim (hne (d0 :: ds) rfl))
  have hbounds : NumParse.Model.inInt64Range n.toInt = true := by
    have := Int64.le_toInt n; have := Int64.toInt_le n; have : Int64.maxValue.toInt = 9223372036854775807 := by decide
    rw [NumParse.Model.inInt64Range, decide_eq_true_eq]; simp only [NumParse.Model.int64MinInt, NumParse.Model.int64MaxInt]; omega
  have hp64 : NumParse.Model.parseInt64Model (formatInt64Canonical n) = .ok n := by simp [NumParse.Model.parseInt64Model, hp_int, hbounds, Int64.ofInt_toInt]
  have hclean : ((formatInt64Canonical n).toList.all fun c => !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && c != '.' && !isDisallowedControl c) = true :=
    List.all_eq_true.mpr fun c hc => by have hp := hcanon_props c (honly c hc); simp only [Bool.and_eq_true] at hp ⊢; exact hp.1.1.1.1.1
  have hnot_mem (ch) (hch : ch = 'X' ∨ ch = 'O' ∨ ch = 'B' ∨ ch = 'e' ∨ ch = 'E') : ch ∉ (formatInt64Canonical n).toList := fun hm => by
    have hp := hcanon_props ch (honly ch hm); simp only [Bool.and_eq_true, bne_iff_ne] at hp
    rcases hch with rfl | rfl | rfl | rfl | rfl <;> first | exact hp.1.1.1.1.2 rfl | exact hp.1.1.1.2 rfl | exact hp.1.1.2 rfl | exact hp.1.2 rfl | exact hp.2 rfl
  have hnot_sw (p : String) (ch) (hmem : ch ∈ p.toList) (hch : ch = 'X' ∨ ch = 'O' ∨ ch = 'B') : (formatInt64Canonical n).startsWith p = false := by
    rw [Bool.eq_false_iff]; intro hsw; rcases String.startsWith_string_iff.mp hsw with ⟨t, ht⟩
    exact hnot_mem ch (hch.elim Or.inl fun h => h.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inl)) (by rw [← ht]; exact List.mem_append_left t hmem)
  simp only [isValidIntLex, hp64, hclean, beq_self_eq_true, Bool.not_false, Bool.true_and, Bool.and_true, Bool.or_self,
    hnot_sw "0X" 'X' (by decide) (by decide), hnot_sw "0O" 'O' (by decide) (by decide), hnot_sw "0B" 'B' (by decide) (by decide),
    hnot_sw "+0X" 'X' (by decide) (by decide), hnot_sw "+0O" 'O' (by decide) (by decide), hnot_sw "+0B" 'B' (by decide) (by decide),
    hnot_sw "-0X" 'X' (by decide) (by decide), hnot_sw "-0O" 'O' (by decide) (by decide), hnot_sw "-0B" 'B' (by decide) (by decide)]
  split <;> first | rfl | simp [String.contains, hnot_mem 'e' (by decide), hnot_mem 'E' (by decide)]
/-- Character alphabet accepted by `NumParse.Model.parseFloatModelChars`. -/
def isFloatModelChar (c : Char) : Bool :=
  c == '+' || c == '-' || c == '.' || c == 'e' || c == 'E' || c == '_' || c == 'i' || c == 'n' || c == 'f' || c == 'a' || isAsciiDigit c
private theorem isFloatModelChar_props (c : Char) (h : isFloatModelChar c = true) :
    c ≠ ':' ∧ c ≠ 'x' ∧ c ≠ 'X' ∧ (!c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c) = true ∧ isCleanTokChar c = true := by
  have hlt : ∀ x, isFloatModelChar x = true → x.toNat < 128 := fun x hx => by
    simp only [isFloatModelChar, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | hd)
    all_goals first | decide | exact isAsciiDigit_lt_128 x hd
  have hq := forall_ascii_of_decide isFloatModelChar
    (fun x => x != ':' && x != 'x' && x != 'X' && (!x.isWhitespace && x != '#' && x != ',' && x != ']' && x != '}' && !isDisallowedControl x) && isCleanTokChar x) hlt (by decide) c h
  rcases Bool.and_eq_true_iff.mp hq with ⟨hq1, hcl2⟩; rcases Bool.and_eq_true_iff.mp hq1 with ⟨hq2, hcl1⟩
  simp only [Bool.and_eq_true, bne_iff_ne] at hq2; exact ⟨hq2.1.1, hq2.1.2, hq2.2, hcl1, hcl2⟩
private theorem consumeDecFloatDigits_props (acc cnt : Nat) (cs : List Char)
    (m cnt' : Nat) (rest : List Char) (h : NumParse.Model.consumeDecFloatDigits acc cnt cs = .ok (m, cnt', rest)) :
    ∃ pfx, cs = pfx ++ rest ∧ (∀ ch ∈ pfx, ch = '_' ∨ isAsciiDigit ch = true) := by
  fun_induction NumParse.Model.consumeDecFloatDigits acc cnt cs with
  | case1 => simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨[], by simp [← h.2.2], by simp⟩
  | case2 _ _ c cs hd ih => obtain ⟨pfx, hcs, hpfx⟩ := ih h; exact ⟨'_' :: c :: pfx, by simp [hcs], List.forall_mem_cons.mpr ⟨Or.inl rfl, List.forall_mem_cons.mpr ⟨Or.inr hd, hpfx⟩⟩⟩
  | case3 _ _ _ _ => simp at h
  | case4 => simp at h
  | case5 _ _ c cs _ _ hd ih => obtain ⟨pfx, hcs, hpfx⟩ := ih h; exact ⟨c :: pfx, by simp [hcs], List.forall_mem_cons.mpr ⟨Or.inr hd, hpfx⟩⟩
  | case6 _ _ _ _ _ _ _ => simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨[], by simp [← h.2.2], by simp⟩
private theorem parseFloatIntPart_props (cs : List Char) (m : Nat) (rest : List Char) (h : NumParse.Model.parseFloatIntPart cs = .ok (m, rest)) :
    ∃ pfx d0 ptail, cs = pfx ++ rest ∧ pfx = d0 :: ptail ∧ isAsciiDigit d0 = true ∧ (∀ ch ∈ pfx, ch = '_' ∨ isAsciiDigit ch = true) := by
  unfold NumParse.Model.parseFloatIntPart at h; split at h <;> try cases h
  · split at h
    · split at h <;> try cases h
      split at h
      · repeat (split at h; all_goals try cases h)
      · cases h; exact ⟨['0'], '0', [], rfl, rfl, rfl, List.forall_mem_singleton.mpr (Or.inr rfl)⟩
    · cases h; exact ⟨['0'], '0', [], rfl, rfl, rfl, List.forall_mem_singleton.mpr (Or.inr rfl)⟩
  · rename_i c rest' _ _; split at h <;> try cases h
    rename_i hd0; split at h <;> try cases h
    rename_i _ _ rem hc; obtain ⟨pfx, hcs0, hpfx⟩ := consumeDecFloatDigits_props _ _ _ _ _ _ hc
    exact ⟨c :: pfx, c, pfx, by simp [hcs0], rfl, hd0, List.forall_mem_cons.mpr ⟨Or.inr hd0, hpfx⟩⟩
private theorem parseFloatExpSuffix_chars (afterE : List Char) (g : Int → Float) (f : Float)
    (h : (match NumParse.Model.parseFloatExpPart afterE with
      | Except.error k => Except.error k
      | Except.ok (expVal, afterExp) => if afterExp.isEmpty then Except.ok (g expVal) else Except.error NumParseErrorKind.trailingChars) = Except.ok f) :
    ∀ c ∈ afterE, isFloatModelChar c = true := by
  cases hexp : NumParse.Model.parseFloatExpPart afterE with
  | error => simp [hexp] at h
  | ok res =>
    rcases res with ⟨expVal, afterExp⟩; rw [hexp] at h; dsimp only at h
    cases afterExp with | cons _ _ => simp at h | nil =>
    simp only [NumParse.Model.parseFloatExpPart.eq_def] at hexp; split at hexp <;> try cases hexp
    rename_i c0 r0 _ heq; split at hexp <;> try cases hexp
    rename_i hd0; split at hexp <;> try cases hexp
    rename_i _ _ _ hc; obtain ⟨pfx, hr0, hpfx⟩ := consumeDecFloatDigits_props _ _ _ _ _ _ hc; rw [List.append_nil] at hr0; subst pfx
    have hbody : ∀ ch ∈ c0 :: r0, isFloatModelChar ch = true := List.forall_mem_cons.mpr
      ⟨by simp [isFloatModelChar, show isAsciiDigit c0 = true from hd0], fun ch hch => (hpfx ch hch).elim (fun e => e ▸ rfl) fun hd => by simp [isFloatModelChar, hd]⟩
    have hcases : afterE = '+' :: c0 :: r0 ∨ afterE = '-' :: c0 :: r0 ∨ afterE = c0 :: r0 := by split at heq <;> dsimp only at heq <;> rw [heq] <;> simp
    rcases hcases with rfl | rfl | rfl <;> first | exact List.forall_mem_cons.mpr ⟨rfl, hbody⟩ | exact hbody
private theorem hasDatePrefix_false_of_digit_or_us_before_sep
    (pfx : List Char) (sep : Char) (tail : List Char) (hpfx : ∀ c ∈ pfx, c = '_' ∨ isAsciiDigit c = true) (hsep : sep = '.' ∨ sep = 'e' ∨ sep = 'E') :
    hasDatePrefix (pfx ++ sep :: tail) = false := by
  have hd : isAsciiDigit sep = false := by rcases hsep with rfl | rfl | rfl <;> rfl
  have hne_sep : sep ≠ '-' := by rcases hsep with rfl | rfl | rfl <;> decide
  rcases pfx with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨e, _⟩⟩⟩⟩⟩ <;> simp only [List.nil_append, List.cons_append, hasDatePrefix]
  all_goals split <;> try rfl
  all_goals rename_i heq; simp only [List.cons.injEq] at heq
  all_goals first | (rw [← heq.1]; simp [hd]; done) | (rw [← heq.2.1]; simp [hd]; done) | (rw [← heq.2.2.1]; simp [hd]; done) | (rw [← heq.2.2.2.1]; simp [hd]; done)
                  | exact absurd heq.2.2.2.2.1 hne_sep
                  | (exfalso; exact (hpfx e (by simp)).elim (fun hr => absurd (hr ▸ heq.2.2.2.2.1) (by decide)) fun h => by rw [heq.2.2.2.2.1] at h; revert h; decide)
/-- Internal TOML scalar round-trip lemma `parseFloatModelChars_props`. -/
theorem parseFloatModelChars_props (cs : List Char) (f : Float) (h : NumParse.Model.parseFloatModelChars cs = .ok f) :
    (∃ c0 rest, cs = c0 :: rest ∧ (c0 = '+' ∨ c0 = '-' ∨ c0 = 'i' ∨ c0 = 'n' ∨ isAsciiDigit c0 = true)) ∧
    (∀ c ∈ cs, isFloatModelChar c = true) ∧ hasDatePrefix cs = false ∧ hasTimePrefix cs = false ∧ isFloatTokenCandidateChars cs = true := by
  have hnot_time (l : List Char) (hl : ∀ c ∈ l, isFloatModelChar c = true) : hasTimePrefix l = false := by
    unfold hasTimePrefix; split <;> first | rfl | exact absurd rfl (isFloatModelChar_props ':' (hl ':' (by simp))).1
  have hcand_of_sep (l : List Char) (hl : ∀ c ∈ l, isFloatModelChar c = true)
      (hsep : (l.contains '.' || l.contains 'e' || l.contains 'E') = true) : isFloatTokenCandidateChars l = true := by
    revert hl; unfold isFloatTokenCandidateChars; dsimp only; split <;> intro hl
    all_goals first | (refine absurd rfl (isFloatModelChar_props 'x' (hl 'x' ?_)).2.1; simp; done)
                    | (refine absurd rfl (isFloatModelChar_props 'X' (hl 'X' ?_)).2.2.1; simp; done)
                    | (simp only [Bool.or_eq_true, Bool.not_false, Bool.true_and] at hsep ⊢; exact Or.inr hsep)
  unfold NumParse.Model.parseFloatModelChars at h; split at h
  · cases h
  · split at h; rename_i _ _ _ neg body hsign
    have hcases : cs = '+' :: body ∨ cs = '-' :: body ∨ cs = body := by split at hsign <;> (injection hsign with _ hb; subst hb; simp)
    have hbody_props : (∃ b0 br, body = b0 :: br ∧ (b0 = 'i' ∨ b0 = 'n' ∨ isAsciiDigit b0 = true)) ∧
        (∀ c ∈ body, isFloatModelChar c = true) ∧ hasDatePrefix body = false ∧
        (body = ['i', 'n', 'f'] ∨ body = ['n', 'a', 'n'] ∨ (body.contains '.' || body.contains 'e' || body.contains 'E') = true) := by
      split at h
      · split at h <;> first | exact ⟨⟨'i', ['n', 'f'], rfl, Or.inl rfl⟩, by decide, by decide, Or.inl rfl⟩ | cases h
      · split at h <;> first | exact ⟨⟨'n', ['a', 'n'], rfl, Or.inr (Or.inl rfl)⟩, by decide, by decide, Or.inr (Or.inl rfl)⟩ | cases h
      · split at h <;> try cases h
        rename_i intVal afterInt hip; obtain ⟨pfx, d0, ptail, hbody_eq, hpfx_eq, hd0, hpfx_ch⟩ := parseFloatIntPart_props body intVal afterInt hip
        have hpfx_fmc : ∀ c ∈ pfx, isFloatModelChar c = true := fun c hc => (hpfx_ch c hc).elim (fun e => e ▸ rfl) fun hd => by simp [isFloatModelChar, hd]
        have hhead : ∃ b0 br, body = b0 :: br ∧ (b0 = 'i' ∨ b0 = 'n' ∨ isAsciiDigit b0 = true) := ⟨d0, ptail ++ afterInt, by rw [hbody_eq, hpfx_eq, List.cons_append], Or.inr (Or.inr hd0)⟩
        split at h <;> try cases h
        · rename_i afterDot; split at h <;> try cases h
          rename_i c1 r1 _; split at h <;> try cases h
          rename_i hd1; split at h <;> try cases h
          rename_i _ _ afterFrac hcf; obtain ⟨fpfx, hr1, hfpfx⟩ := consumeDecFloatDigits_props _ _ _ _ _ _ hcf
          have hfpfx_fmc : ∀ c ∈ fpfx, isFloatModelChar c = true := fun c hc => (hfpfx c hc).elim (fun e => e ▸ rfl) fun hd => by simp [isFloatModelChar, hd]
          have haf_fmc : ∀ c ∈ afterFrac, isFloatModelChar c = true := by
            split at h <;> first | exact List.forall_mem_cons.mpr ⟨rfl, parseFloatExpSuffix_chars _ _ f h⟩ | (cases h; simp; done) | cases h
          exact ⟨hhead, by rw [hbody_eq, hr1]; simp only [List.forall_mem_append, List.forall_mem_cons]; exact ⟨hpfx_fmc, rfl, by simp [isFloatModelChar, show isAsciiDigit c1 = true from hd1], hfpfx_fmc, haf_fmc⟩,
            by rw [hbody_eq]; exact hasDatePrefix_false_of_digit_or_us_before_sep pfx '.' _ hpfx_ch (Or.inl rfl), Or.inr (Or.inr (by rw [hbody_eq]; simp))⟩
        · rename_i afterE
          exact ⟨hhead, by rw [hbody_eq]; simp only [List.forall_mem_append, List.forall_mem_cons]; exact ⟨hpfx_fmc, rfl, parseFloatExpSuffix_chars afterE _ f h⟩,
            by rw [hbody_eq]; exact hasDatePrefix_false_of_digit_or_us_before_sep pfx 'e' afterE hpfx_ch (Or.inr (Or.inl rfl)), Or.inr (Or.inr (by rw [hbody_eq]; simp))⟩
        · rename_i afterE
          exact ⟨hhead, by rw [hbody_eq]; simp only [List.forall_mem_append, List.forall_mem_cons]; exact ⟨hpfx_fmc, rfl, parseFloatExpSuffix_chars afterE _ f h⟩,
            by rw [hbody_eq]; exact hasDatePrefix_false_of_digit_or_us_before_sep pfx 'E' afterE hpfx_ch (Or.inr (Or.inr rfl)), Or.inr (Or.inr (by rw [hbody_eq]; simp))⟩
    obtain ⟨⟨b0, br, hb_eq, hb0⟩, hfmc, hnd_body, hkind⟩ := hbody_props
    have hsigned_finish (sgn : Char) (hsgn : sgn = '+' ∨ sgn = '-') :
        (∃ d0 rest, sgn :: body = d0 :: rest ∧ (d0 = '+' ∨ d0 = '-' ∨ d0 = 'i' ∨ d0 = 'n' ∨ isAsciiDigit d0 = true)) ∧
        (∀ c ∈ sgn :: body, isFloatModelChar c = true) ∧ hasDatePrefix (sgn :: body) = false ∧ hasTimePrefix (sgn :: body) = false ∧
        isFloatTokenCandidateChars (sgn :: body) = true := by
      have hfmc_all : ∀ c ∈ sgn :: body, isFloatModelChar c = true := List.forall_mem_cons.mpr ⟨by rcases hsgn with rfl | rfl <;> rfl, hfmc⟩
      have hnd : hasDatePrefix (sgn :: body) = false := by
        unfold hasDatePrefix; split <;> first | rfl | (rename_i heq; injection heq with h1 _; subst h1; rcases hsgn with rfl | rfl <;> rfl)
      refine ⟨⟨sgn, body, rfl, hsgn.elim Or.inl (Or.inr ∘ Or.inl)⟩, hfmc_all, hnd, hnot_time _ hfmc_all, ?_⟩
      rcases hkind with rfl | rfl | hsep
      · rcases hsgn with rfl | rfl <;> decide
      · rcases hsgn with rfl | rfl <;> decide
      · apply hcand_of_sep _ hfmc_all; simp only [List.contains_iff_mem, Bool.or_eq_true] at hsep ⊢
        exact hsep.elim (fun h12 => Or.inl (h12.elim (Or.inl ∘ List.mem_cons_of_mem _) (Or.inr ∘ List.mem_cons_of_mem _))) (Or.inr ∘ List.mem_cons_of_mem _)
    rcases hcases with hplus | hminus | hnosign
    · rw [hplus]; exact hsigned_finish '+' (Or.inl rfl)
    · rw [hminus]; exact hsigned_finish '-' (Or.inr rfl)
    · subst hnosign
      have hhead : b0 = '+' ∨ b0 = '-' ∨ b0 = 'i' ∨ b0 = 'n' ∨ isAsciiDigit b0 = true :=
        hb0.elim (Or.inr ∘ Or.inr ∘ Or.inl) fun h => h.elim (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr)
      refine ⟨⟨b0, br, hb_eq, hhead⟩, hfmc, hnd_body, hnot_time _ hfmc, ?_⟩
      rcases hkind with h1 | h2 | hsep <;> first | (rw [h1]; decide) | (rw [h2]; decide) | exact hcand_of_sep _ hfmc hsep
private theorem parseIntModelChars_no_datePrefix (cs : List Char) (m : Int) (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    hasDatePrefix cs = false ∧ hasTimePrefix cs = false := by
  obtain ⟨⟨c0, rest, hcs, _, _⟩, hno_cd, hno_dash⟩ := parseIntModelChars_props cs m h; refine ⟨?_, ?_⟩
  · cases hdp : hasDatePrefix cs
    · rfl
    · unfold hasDatePrefix at hdp; split at hdp
      · have hcs' := hcs.symm.trans rfl; injection hcs' with _ hrest; exact absurd rfl (hno_dash c0 rest hcs '-' (by rw [hrest]; simp))
      · cases hdp
  · cases htp : hasTimePrefix cs
    · rfl
    · unfold hasTimePrefix at htp; split at htp <;> first | cases htp | exact absurd rfl (hno_cd ':' (by simp)).1
private theorem unquotedNumHead_props (cs : List Char) (c0 : Char) (rest : List Char) (hlist : cs = c0 :: rest)
    (hc0 : c0 = '+' ∨ c0 = '-' ∨ c0 = 'i' ∨ c0 = 'n' ∨ isAsciiDigit c0 = true) :
    cs ≠ [] ∧ cs ≠ ['t', 'r', 'u', 'e'] ∧ cs ≠ ['f', 'a', 'l', 's', 'e'] ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
  refine ⟨by simp [hlist], fun heq => ?_, fun heq => ?_, ?_⟩
  · rw [hlist] at heq; injection heq with h0 _; subst h0; rcases hc0 with h1 | h1 | h1 | h1 | h1 <;> revert h1 <;> decide
  · rw [hlist] at heq; injection heq with h0 _; subst h0; rcases hc0 with h1 | h1 | h1 | h1 | h1 <;> revert h1 <;> decide
  · rcases hc0 with rfl | rfl | rfl | rfl | hdig <;> first | decide | (refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide)
/-- Internal TOML scalar round-trip lemma `isValidIntLex_classifyScalarToken`. -/
theorem isValidIntLex_classifyScalarToken (numApi : CharNumApi)
    (hInt : ∀ tok : String, ∀ n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64Chars tok.toList = .ok n)
    (s : String) (n : Int64) (h : isValidIntLex s n = true) :
    classifyScalarChars numApi s.toList = .ok (.int n) ∧
    (s.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
    ∃ c0 cs0, s.toList = c0 :: cs0 ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
  simp only [isValidIntLex, Bool.and_eq_true, Bool.not_eq_true'] at h; rcases h with ⟨⟨⟨hchars, hno_up⟩, hno_exp⟩, hbeq⟩
  have hp_model : NumParse.Model.parseInt64Model s = .ok n := by
    cases hp : NumParse.Model.parseInt64Model s with | error => rw [hp] at hbeq; cases hbeq | ok m => rw [hp] at hbeq; simp only [beq_iff_eq] at hbeq; subst hbeq; rfl
  have hm_chars : ∃ m : Int, NumParse.Model.parseIntModelChars s.toList = .ok m := by
    unfold NumParse.Model.parseInt64Model NumParse.Model.parseIntModel at hp_model
    cases hc : NumParse.Model.parseIntModelChars s.toList with | error => rw [hc] at hp_model; cases hp_model | ok m => exact ⟨m, rfl⟩
  rcases hm_chars with ⟨m, hm⟩
  obtain ⟨⟨c0, rest, hlist, hc0, hc1⟩, hno_cd, _⟩ := parseIntModelChars_props s.toList m hm; obtain ⟨hnd, hnt⟩ := parseIntModelChars_no_datePrefix s.toList m hm
  have hc0_ext : c0 = '+' ∨ c0 = '-' ∨ c0 = 'i' ∨ c0 = 'n' ∨ isAsciiDigit c0 = true :=
    hc0.elim Or.inl fun h => h.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr)
  obtain ⟨hnot_nil, hnot_true, hnot_false, hhead_safe⟩ := unquotedNumHead_props s.toList c0 rest hlist hc0_ext
  have hnot_dt : parseDateTimeChars s.toList = none := by simp [parseDateTimeChars, hnd, hnt, show ¬(':' ∈ s.toList) from fun hc => (hno_cd ':' hc).1 rfl]
  have hnot_spec : (s.toList == ['i', 'n', 'f'] || s.toList == ['+', 'i', 'n', 'f'] || s.toList == ['-', 'i', 'n', 'f'] ||
      s.toList == ['n', 'a', 'n'] || s.toList == ['+', 'n', 'a', 'n'] || s.toList == ['-', 'n', 'a', 'n']) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, hlist]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> intro heq <;> injection heq with h0 hr <;> subst h0
    all_goals first | (rcases hc0 with h1 | h1 | h1 <;> revert h1 <;> decide)
                    | (have hd1 := hc1 _ _ (Or.inl rfl) hr; revert hd1; decide) | (have hd1 := hc1 _ _ (Or.inr rfl) hr; revert hd1; decide)
  have hnot_float_cand : isFloatTokenCandidateChars s.toList = false := by
    unfold isFloatTokenCandidateChars; rw [hnot_spec, Bool.false_or]; split at hno_exp
    · rename_i hhex; rcases String.startsWith_string_iff.mp hhex with ⟨t, ht⟩; rw [show ("0x" : String).toList = ['0', 'x'] from rfl] at ht; simp [← ht]
    · simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true'] at hno_exp
      simp [show ¬('.' ∈ s.toList) from fun hm => (hno_cd '.' hm).2 rfl,
        show ¬('e' ∈ s.toList) by simpa [String.contains_char_eq] using hno_exp.1, show ¬('E' ∈ s.toList) by simpa [String.contains_char_eq] using hno_exp.2]
  have hno_upper : hasUppercaseBasePrefixChars s.toList = false := by
    have hsw (p : String) (hp : s.startsWith p = false) (t : List Char) (ht : s.toList = p.toList ++ t) : true = false := by
      rw [String.startsWith_string_iff.mpr ⟨t, ht.symm⟩] at hp; cases hp
    simp only [Bool.or_eq_false_iff] at hchars; rcases hchars with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
    unfold hasUppercaseBasePrefixChars; split
    all_goals try rfl
    all_goals rename_i _ tail heq
    all_goals first | exact hsw "0X" h1 tail heq | exact hsw "0O" h2 tail heq | exact hsw "0B" h3 tail heq
                    | exact hsw "+0X" h4 tail heq | exact hsw "+0O" h5 tail heq | exact hsw "+0B" h6 tail heq
                    | exact hsw "-0X" h7 tail heq | exact hsw "-0O" h8 tail heq | exact hsw "-0B" h9 tail heq
  have hcls : classifyScalarChars numApi s.toList = .ok (.int n) := by
    unfold classifyScalarChars; split <;> first | exact absurd ‹_› hnot_nil | exact absurd ‹_› hnot_true | exact absurd ‹_› hnot_false | simp [hnot_dt, hnot_float_cand, hno_upper, hInt s n hp_model]
  refine ⟨hcls, List.all_eq_true.mpr fun c hc => ?_, c0, rest, hlist, hhead_safe⟩
  have h1 := List.all_eq_true.mp hno_up c hc; simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h1
  have hne (w : Char) (hw : w.isWhitespace = true) : c ≠ w := fun e => by subst e; simp [hw] at h1
  simp [isUnquotedDelim, isHorizWs, hne ' ' (by decide), hne '\t' (by decide), hne '\n' (by decide), hne '\r' (by decide), h1.1.1.1.1.1.2, h1.1.1.1.1.2, h1.1.1.1.2, h1.1.1.2, h1.2]
/-- Two `Float` values with identical IEEE 754 bit patterns are equal. -/
theorem float_eq_of_toBits_eq {a b : Float} (h : a.toBits = b.toBits) : a = b := by
  cases a with | ofModel am => cases b with | ofModel bm => cases am with | mk _ _ => cases bm with | mk _ _ => cases h; rfl
private theorem float_beq_props (a b : Float) (h : (a == b) = true) : (b == a) = true ∧ a.isNaN = false ∧ b.isNaN = false := by
  have hna : a.isNaN = false := by
    have hbeq : (a.toModel.unpack.compare b.toModel.unpack == some .eq) = true := h; change a.toModel.unpack.isNaN = false
    cases ha : a.toModel.unpack <;> simp [ha, Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] at hbeq ⊢
  have hnb : b.isNaN = false := by
    have hbeq : (a.toModel.unpack.compare b.toModel.unpack == some .eq) = true := h; change b.toModel.unpack.isNaN = false
    cases ha : a.toModel.unpack <;> cases hb : b.toModel.unpack <;> simp [ha, hb, Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] at hbeq ⊢
  exact ⟨(NumParse.Model.floatEquiv_nonNaN_iff_beq (by simp [hnb]) (by simp [hna])).mp (NumParse.Model.floatEquiv_symm (Or.inr h)), hna, hnb⟩
/-- Internal TOML scalar round-trip lemma `canonicalFloat_isValidFloatLex`. -/
theorem canonicalFloat_isValidFloatLex (f : Float) :
    (f.isNaN = true → isValidFloatLex "nan" f = true) ∧ ((f == Float.inf) = true → isValidFloatLex "inf" f = true) ∧
    ((f == -Float.inf) = true → isValidFloatLex "-inf" f = true) ∧ (f.toBits = (0.0 : Float).toBits → isValidFloatLex "0.0" f = true) ∧
    (f.toBits = (-0.0 : Float).toBits → isValidFloatLex "-0.0" f = true) := by
  refine ⟨fun hnan => ?_, fun hinf => ?_, fun hninf => ?_, fun hbits => ?_, fun hbits => ?_⟩
  · simp [isValidFloatLex, (by simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars] : NumParse.Model.parseFloatModel "nan" = .ok Float.nan), hnan, show Float.nan.isNaN = true by decide]; decide
  · simp [isValidFloatLex, (by simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars] : NumParse.Model.parseFloatModel "inf" = .ok Float.inf), (float_beq_props f Float.inf hinf).1]; decide
  · simp [isValidFloatLex, (by simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars] : NumParse.Model.parseFloatModel "-inf" = .ok (-Float.inf)), (float_beq_props f (-Float.inf) hninf).1]; decide
  · obtain rfl := float_eq_of_toBits_eq hbits
    have hp : NumParse.Model.parseFloatModel "0.0" = .ok (0.0 : Float) := by simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars, NumParse.Model.parseFloatIntPart, NumParse.Model.consumeDecFloatDigits, NumParse.Model.isDecDigit, NumParse.Model.evalFloat_zero]
    simp [isValidFloatLex, hp, show ((0.0 : Float) == (0.0 : Float)) = true by decide]; decide
  · obtain rfl := float_eq_of_toBits_eq hbits
    have hp : NumParse.Model.parseFloatModel "-0.0" = .ok (-0.0 : Float) := by simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars, NumParse.Model.parseFloatIntPart, NumParse.Model.consumeDecFloatDigits, NumParse.Model.isDecDigit, NumParse.Model.evalFloat_neg_zero]
    simp [isValidFloatLex, hp, show ((-0.0 : Float) == (-0.0 : Float)) = true by decide]; decide
/-- Any string satisfying `FloatFormatSpec f s` is a valid TOML float lexeme for `f`. -/
theorem floatFormatSpec_isValidFloatLex (f : Float) (s : String) (hs : NumParse.Model.FloatFormatSpec f s) : isValidFloatLex s f = true := by
  simp only [NumParse.Model.FloatFormatSpec] at hs
  if hnan : f.isNaN = true then simp only [hnan, ite_true] at hs; subst hs; exact (canonicalFloat_isValidFloatLex f).1 hnan else
  simp only [hnan] at hs
  if hinf : (f == Float.inf) = true then simp only [hinf, ite_true] at hs; subst hs; exact (canonicalFloat_isValidFloatLex f).2.1 hinf else
  simp only [hinf] at hs
  if hninf : (f == -Float.inf) = true then simp only [hninf, ite_true] at hs; subst hs; exact (canonicalFloat_isValidFloatLex f).2.2.1 hninf else
  simp only [hninf] at hs; rcases hs with ⟨_, hsep, hmatch⟩
  cases hp : NumParse.Model.parseFloatModel s with
  | error => rw [hp] at hmatch; cases hmatch
  | ok y =>
    rw [hp] at hmatch; obtain rfl := float_eq_of_toBits_eq hmatch
    obtain ⟨_, hfmc, _, _, _⟩ := parseFloatModelChars_props s.toList y (by simpa [NumParse.Model.parseFloatModel] using hp)
    have hnoTerm : (s.toList.all fun c => !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c) = true :=
      List.all_eq_true.mpr fun c hc => (isFloatModelChar_props c (hfmc c hc)).2.2.2.1
    have hmark : (s.contains '.' || s.contains 'e' || s.contains 'E' || s == "inf" || s == "+inf" || s == "-inf" || s == "nan" || s == "+nan" || s == "-nan") = true := by
      rcases hsep with h1 | h1 | h1 <;> simp only [String.contains_char_eq, decide_eq_true_eq] at h1 <;> simp [h1]
    simp only [isValidFloatLex]; rw [hmark, hnoTerm, hp]; simp [(NumParse.Model.floatEquiv_nonNaN_iff_beq hnan hnan).mp (NumParse.Model.floatEquiv_refl y)]
/-- Internal TOML scalar round-trip lemma `isValidFloatLex_classifyScalarToken`. -/
theorem isValidFloatLex_classifyScalarToken (numApi : CharNumApi)
    (hFloat : ∀ tok : String, ∀ f, NumParse.Model.parseFloatModel tok = .ok f → ∃ g, numApi.parseFloatChars tok.toList = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (s : String) (f : Float) (h : isValidFloatLex s f = true) :
    ∃ g, classifyScalarChars numApi s.toList = .ok (.float g) ∧ TomlEquiv (.float f) (.float g) ∧
      (s.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
      ∃ c0 cs0, s.toList = c0 :: cs0 ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
  simp only [isValidFloatLex, Bool.and_eq_true] at h; rcases h with ⟨⟨_, _⟩, hmatch⟩
  cases hp : NumParse.Model.parseFloatModel s with
  | error => rw [hp] at hmatch; cases hmatch
  | ok g =>
    rw [hp] at hmatch
    obtain ⟨⟨c0, rest, hlist, hc0⟩, hfmc, hnd, hnt, hcand⟩ := parseFloatModelChars_props s.toList g (by simpa [NumParse.Model.parseFloatModel] using hp)
    obtain ⟨hnot_nil, hnot_true, hnot_false, hhead_safe⟩ := unquotedNumHead_props s.toList c0 rest hlist hc0
    have hnot_dt : parseDateTimeChars s.toList = none := by simp [parseDateTimeChars, hnd, hnt, show ¬(':' ∈ s.toList) from fun hc => by cases hfmc ':' hc]
    obtain ⟨g', hg', hbit⟩ := hFloat s g hp
    have hcls : classifyScalarChars numApi s.toList = .ok (.float g') := by
      unfold classifyScalarChars; split <;> first | exact absurd ‹_› hnot_nil | exact absurd ‹_› hnot_true | exact absurd ‹_› hnot_false | simp [hnot_dt, hcand, hg']
    have heq_f : TomlEquiv (.float f) (.float g') := by
      simp only [TomlEquiv]
      have heq_fg : NumParse.Model.FloatEquiv f g := by
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hmatch; rcases hmatch with ⟨hg_nan, hf_nan⟩ | hgf
        · exact Or.inl ⟨hf_nan, hg_nan⟩
        · obtain ⟨hfg, hna_g, hna_f⟩ := float_beq_props g f hgf
          exact (NumParse.Model.floatEquiv_nonNaN_iff_beq (by simp [hna_f]) (by simp [hna_g])).mpr hfg
      exact NumParse.Model.floatEquiv_trans heq_fg (NumParse.Model.floatEquiv_symm (NumParse.Model.floatBitMatch_implies_floatEquiv hbit))
    exact ⟨g', hcls, heq_f, List.all_eq_true.mpr fun c hc => (isFloatModelChar_props c (hfmc c hc)).2.2.2.2, c0, rest, hlist, hhead_safe⟩

end LeanSwe.Toml.Proofs
