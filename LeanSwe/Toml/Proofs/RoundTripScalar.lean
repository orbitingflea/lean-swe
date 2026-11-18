import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Internal TOML scalar round-trip lemma `normalizeChars_clean`. -/
theorem normalizeChars_clean (cs : List Char)
    (h : cs.all (fun c => !isDisallowedControl c && c != '\r') = true) (line col : Nat) :
    normalizeChars line col cs = .ok cs := by
  induction cs generalizing line col with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    rcases h with ⟨⟨hc_ctrl, hc_cr⟩, hrest⟩
    have hrest' := ih hrest
    by_cases hnl : c = '\n'
    · subst hnl
      simp only [normalizeChars, hrest' (line + 1) 1, bind, Except.bind]
    · unfold normalizeChars
      split <;> rename_i heq
      · simp at heq
      · simp [hc_cr] at heq
      · simp [hc_cr] at heq
      · simp [hnl] at heq
      · cases heq
        simp only [hc_ctrl, Bool.false_eq_true, ↓reduceIte, hrest' line (col + 1), bind, Except.bind]

private theorem isBareKeyChar_lt_128 (c : Char) (h : isBareKeyChar c = true) : c.toNat < 128 := by
  simp only [isBareKeyChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | h1) | h1)
  · have : c.toNat ≤ 'Z'.toNat := h2; have : 'Z'.toNat = 90 := rfl; omega
  · have : c.toNat ≤ 'z'.toNat := h2; have : 'z'.toNat = 122 := rfl; omega
  · have : c.toNat ≤ '9'.toNat := h2; have : '9'.toNat = 57 := rfl; omega
  · simp only [beq_iff_eq] at h1; subst h1; decide
  · simp only [beq_iff_eq] at h1; subst h1; decide

private theorem isBareKeyChar_clean_table :
    (List.range 128).all (fun n =>
      let c := Char.ofNat n
      !isBareKeyChar c ||
        (!isDisallowedControl c && c != '\r' && c != '\n' && !isHorizWs c &&
         c != '.' && c != '"' && c != '\'' && c != '#' && c != ',' && c != ']' && c != '}' && c != '=')) = true := by
  decide

/-- Internal TOML scalar round-trip lemma `isBareKeyChar_clean`. -/
theorem isBareKeyChar_clean (c : Char) (h : isBareKeyChar c = true) :
    (!isDisallowedControl c && c != '\r' && c != '\n' && !isHorizWs c &&
     c != '.' && c != '"' && c != '\'' && c != '#' && c != ',' && c != ']' && c != '}' && c != '=') = true := by
  have hlt := isBareKeyChar_lt_128 c h
  have hmem := List.all_eq_true.mp isBareKeyChar_clean_table c.toNat (List.mem_range.mpr hlt)
  simp only [Char.ofNat_toNat, h, Bool.not_true, Bool.false_or] at hmem
  exact hmem

private theorem isSingleLineClean_implies_clean (s : String) (h : isSingleLineClean s = true) :
    s.toList.all (fun c => !isDisallowedControl c && c != '\r') = true := by
  simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h ⊢
  intro c hc
  have h1 := h c hc
  exact ⟨by simpa [Bool.not_eq_true'] using h1.1.1, h1.2⟩

private theorem isSingleLineClean_no_nl (s : String) (h : isSingleLineClean s = true)
    (c : Char) (hc : c ∈ s.toList) : c ≠ '\n' ∧ c ≠ '\r' ∧ (!isDisallowedControl c) = true := by
  simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h
  have h1 := h c hc
  exact ⟨h1.1.2, h1.2, by simpa [Bool.not_eq_true'] using h1.1.1⟩

private theorem hexDigitUpper_val_table :
    (List.range 16).all (fun n => hexVal? (hexDigitUpper n) == some n) = true := by
  decide

private theorem hexDigitUpper_clean_table :
    (List.range 16).all (fun n =>
      let c := hexDigitUpper n
      !isDisallowedControl c && c != '\r' && c != '\n' && c != '\\' && c != '"') = true := by
  decide

private theorem hexDigitUpper_val (n : Nat) (hn : n < 16) :
    hexVal? (hexDigitUpper n) = some n := by
  have h := List.all_eq_true.mp hexDigitUpper_val_table n (List.mem_range.mpr hn)
  simpa using h

private theorem hexDigitUpper_clean (n : Nat) (hn : n < 16) :
    (!isDisallowedControl (hexDigitUpper n) && hexDigitUpper n != '\r' &&
      hexDigitUpper n != '\n' && hexDigitUpper n != '\\' && hexDigitUpper n != '"') = true := by
  exact List.all_eq_true.mp hexDigitUpper_clean_table n (List.mem_range.mpr hn)

private theorem twoDigits_padNatZero_table :
    (List.range 100).all (fun n =>
      match (padNatZero 2 n).toList with
      | [c1, c2] =>
        !isDisallowedControl c1 && c1 != '\r' && c1 != '\n' && !isUnquotedDelim c1 &&
        !isDisallowedControl c2 && c2 != '\r' && c2 != '\n' && !isUnquotedDelim c2 &&
        twoDigitsNat? c1 c2 == some n
      | _ => false) = true := by
  decide

private theorem twoDigits_padNatZero (n : Nat) (hn : n < 100) :
    ∃ c1 c2, (padNatZero 2 n).toList = [c1, c2] ∧ twoDigitsNat? c1 c2 = some n ∧
      (!isDisallowedControl c1 && c1 != '\r' && c1 != '\n' && !isUnquotedDelim c1) = true ∧
      (!isDisallowedControl c2 && c2 != '\r' && c2 != '\n' && !isUnquotedDelim c2) = true := by
  have h := List.all_eq_true.mp twoDigits_padNatZero_table n (List.mem_range.mpr hn)
  cases hcs : (padNatZero 2 n).toList with
  | nil => simp [hcs] at h
  | cons c1 r1 =>
    cases r1 with
    | nil => simp [hcs] at h
    | cons c2 r2 =>
      cases r2 with
      | nil =>
        simp only [hcs, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
        exact ⟨c1, c2, rfl, h9, by simp [h1, h2, h3, h4], by simp [h5, h6, h7, h8]⟩
      | cons _ _ => simp [hcs] at h

/-- Internal TOML scalar round-trip lemma `toString_lt10_char`. -/
theorem toString_lt10_char (r : Nat) (hr : r < 10) :
    (toString r).toList = [Nat.digitChar r] ∧ isAsciiDigit (Nat.digitChar r) = true ∧
      digitVal (Nat.digitChar r) = r ∧
      (!isDisallowedControl (Nat.digitChar r) && Nat.digitChar r != '\r' &&
        Nat.digitChar r != '\n' && !isUnquotedDelim (Nat.digitChar r)) = true := by
  match r with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
  | r + 10 => omega

private theorem nat_toDigitsCore_acc (fuel n : Nat) (acc : List Char) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => simp [Nat.toDigitsCore]
  | succ f' ih =>
    rw [Nat.toDigitsCore, Nat.toDigitsCore]
    by_cases hdiv : n / 10 = 0
    · simp only [hdiv, ↓reduceIte, List.singleton_append]
    · simp only [hdiv, ↓reduceIte]
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: acc), ih (n / 10) [Nat.digitChar (n % 10)],
        List.append_assoc, List.cons_append, List.nil_append]

private theorem toDigitsCore_fuel_mono (f1 f2 n : Nat) (hf1 : n < f1) (hf2 : n < f2) :
    Nat.toDigitsCore 10 f1 n [] = Nat.toDigitsCore 10 f2 n [] := by
  induction f1 generalizing f2 n with
  | zero => omega
  | succ f1' ih =>
    cases f2 with
    | zero => omega
    | succ f2' =>
      rw [Nat.toDigitsCore, Nat.toDigitsCore]
      by_cases hdiv : n / 10 = 0
      · simp only [hdiv, ↓reduceIte]
      · simp only [hdiv, ↓reduceIte]
        have hlt1 : n / 10 < f1' := by omega
        have hlt2 : n / 10 < f2' := by omega
        rw [nat_toDigitsCore_acc f1' (n / 10) [Nat.digitChar (n % 10)],
          nat_toDigitsCore_acc f2' (n / 10) [Nat.digitChar (n % 10)],
          ih f2' (n / 10) hlt1 hlt2]

/-- Internal TOML scalar round-trip lemma `toString_two_digits_split`. -/
theorem toString_two_digits_split (q r : Nat) (hq : 0 < q) (hr : r < 10) :
    (toString (q * 10 + r)).toList = (toString q).toList ++ [Nat.digitChar r] := by
  change (Nat.repr (q * 10 + r)).toList = (Nat.repr q).toList ++ [Nat.digitChar r]
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits]
  rw [Nat.toDigitsCore]
  have hq0 : q ≠ 0 := by omega
  have hdiv : (q * 10 + r) / 10 = q := by omega
  have hmod : (q * 10 + r) % 10 = r := by omega
  simp only [hdiv, hmod, hq0, ↓reduceIte]
  rw [nat_toDigitsCore_acc _ q [Nat.digitChar r],
    toDigitsCore_fuel_mono (q * 10 + r) (q + 1) q (by omega) (by omega)]

private theorem toString_digits_all_clean (n : Nat) :
    (toString n).toList.all (fun c =>
      isAsciiDigit c && !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
    (toString n).length ≥ 1 := by
  suffices h : ∀ k : Nat, ∀ m : Nat, m ≤ k →
      (toString m).toList.all (fun c =>
        isAsciiDigit c && !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
      (toString m).length ≥ 1 from h n n (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    decide
  | succ k' ih =>
    intro m hm
    by_cases h10 : m < 10
    · obtain ⟨hch, hd, _, hcl⟩ := toString_lt10_char m h10
      constructor
      · simp only [hch, List.all_cons, List.all_nil, Bool.and_true, hd]
        simpa [Bool.and_assoc] using hcl
      · change (toString m).toList.length ≥ 1
        rw [hch]; simp
    · have hq : 0 < m / 10 := by omega
      have hqm : m / 10 ≤ k' := by omega
      have hsplit := toString_two_digits_split (m / 10) (m % 10) hq (Nat.mod_lt m (by decide))
      have heqm : m / 10 * 10 + m % 10 = m := by omega
      rw [heqm] at hsplit
      obtain ⟨ih1, ih2⟩ := ih (m / 10) hqm
      obtain ⟨_, hd, _, hcl⟩ := toString_lt10_char (m % 10) (Nat.mod_lt m (by decide))
      constructor
      · simp only [hsplit, List.all_append, List.all_cons, List.all_nil, Bool.and_true, ih1, Bool.true_and, hd]
        simpa [Bool.and_assoc] using hcl
      · change (toString m).toList.length ≥ 1
        rw [hsplit]; simp

private theorem padNatZero_clean (w n : Nat) :
    (padNatZero w n).toList.all (fun c =>
      isAsciiDigit c && !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  unfold padNatZero
  dsimp only
  by_cases hge : (toString n).length ≥ w
  · simp only [hge, ↓reduceIte, (toString_digits_all_clean n).1]
  · simp only [hge, ↓reduceIte, String.toList_append, String.toList_ofList, List.all_append,
      (toString_digits_all_clean n).1, Bool.and_true, List.all_replicate]
    split <;> decide

private theorem padNatZero_length_of_toString_le (w n : Nat) (h : (toString n).length ≤ w) :
    (padNatZero w n).toList.length = w := by
  unfold padNatZero
  dsimp only
  by_cases hge : (toString n).length ≥ w
  · simp only [hge, ↓reduceIte]
    change (toString n).toList.length = w
    have hlen : (toString n).length = w := by omega
    simpa [String.length] using hlen
  · simp only [hge, ↓reduceIte, String.toList_append, String.toList_ofList, List.length_append,
      List.length_replicate]
    change w - (toString n).length + (toString n).length = w
    omega

private theorem toString_lt_pow10_len4 (y : Nat) (hy : y < 10000) : (toString y).length ≤ 4 := by
  have hlen_eq : (toString y).length = (toString y).toList.length := by
    change (Nat.repr y).length = (Nat.repr y).toList.length
    simp [Nat.repr]
  rw [hlen_eq]
  by_cases h1 : y < 10
  · obtain ⟨hch, _⟩ := toString_lt10_char y h1
    rw [hch]; simp
  · by_cases h2 : y < 100
    · have := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
      have heq : y / 10 * 10 + y % 10 = y := by omega
      rw [heq] at this
      obtain ⟨hch, _⟩ := toString_lt10_char (y / 10) (by omega)
      rw [this, hch]; simp
    · by_cases h3 : y < 1000
      · have hs1 := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
        have heq1 : y / 10 * 10 + y % 10 = y := by omega
        rw [heq1] at hs1
        have hs2 := toString_two_digits_split (y / 100) ((y / 10) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq2 : y / 100 * 10 + (y / 10) % 10 = y / 10 := by omega
        rw [heq2] at hs2
        obtain ⟨hch, _⟩ := toString_lt10_char (y / 100) (by omega)
        rw [hs1, hs2, hch]; simp
      · have hs1 := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
        have heq1 : y / 10 * 10 + y % 10 = y := by omega
        rw [heq1] at hs1
        have hs2 := toString_two_digits_split (y / 100) ((y / 10) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq2 : y / 100 * 10 + (y / 10) % 10 = y / 10 := by omega
        rw [heq2] at hs2
        have hs3 := toString_two_digits_split (y / 1000) ((y / 100) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq3 : y / 1000 * 10 + (y / 100) % 10 = y / 100 := by omega
        rw [heq3] at hs3
        obtain ⟨hch, _⟩ := toString_lt10_char (y / 1000) (by omega)
        rw [hs1, hs2, hs3, hch]; simp

private theorem fourDigitsNat?_of_digits (d1 d2 d3 d4 : Nat)
    (h1 : d1 < 10) (h2 : d2 < 10) (h3 : d3 < 10) (h4 : d4 < 10) :
    fourDigitsNat? (Nat.digitChar d1) (Nat.digitChar d2) (Nat.digitChar d3) (Nat.digitChar d4) =
      some (d1 * 1000 + d2 * 100 + d3 * 10 + d4) := by
  obtain ⟨_, hd1, hv1, _⟩ := toString_lt10_char d1 h1
  obtain ⟨_, hd2, hv2, _⟩ := toString_lt10_char d2 h2
  obtain ⟨_, hd3, hv3, _⟩ := toString_lt10_char d3 h3
  obtain ⟨_, hd4, hv4, _⟩ := toString_lt10_char d4 h4
  simp [fourDigitsNat?, hd1, hd2, hd3, hd4, hv1, hv2, hv3, hv4]
  omega

/-- Internal TOML scalar round-trip lemma `padNatZero_eq_of_toList`. -/
theorem padNatZero_eq_of_toList (w n : Nat) (cs : List Char)
    (hcs : (toString n).toList = cs) (hlen : cs.length ≤ w) :
    (padNatZero w n).toList = List.replicate (w - cs.length) '0' ++ cs := by
  unfold padNatZero
  have hlen_str : (toString n).length = cs.length := by
    have h1 : (toString n).length = (toString n).toList.length := by
      change (Nat.repr n).length = (Nat.repr n).toList.length
      simp [Nat.repr]
    rw [h1, hcs]
  change (if (toString n).length ≥ w then toString n
    else String.ofList (List.replicate (w - (toString n).length) '0') ++ toString n).toList = _
  rw [hlen_str]
  by_cases hge : cs.length ≥ w
  · have hw : cs.length = w := by omega
    simp only [hge, ↓reduceIte]
    rw [hw, Nat.sub_self, List.replicate_zero, List.nil_append, hcs]
  · simp only [hge, ↓reduceIte, String.toList_append, String.toList_ofList, hcs]

private theorem padNatZero_4_digits (y : Nat) (hy : y < 10000) :
    ∃ c1 c2 c3 c4, (padNatZero 4 y).toList = [c1, c2, c3, c4] ∧
      fourDigitsNat? c1 c2 c3 c4 = some y := by
  have h0 : Nat.digitChar 0 = '0' := rfl
  by_cases h1 : y < 10
  · obtain ⟨hc, _⟩ := toString_lt10_char y h1
    refine ⟨Nat.digitChar 0, Nat.digitChar 0, Nat.digitChar 0, Nat.digitChar y, ?_, ?_⟩
    · rw [padNatZero_eq_of_toList 4 y _ hc (by simp), h0]; rfl
    · rw [fourDigitsNat?_of_digits 0 0 0 y (by decide) (by decide) (by decide) h1]
      simp
  · by_cases h2 : y < 100
    · have hstr := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
      have heq : y / 10 * 10 + y % 10 = y := by omega
      rw [heq] at hstr
      obtain ⟨hca, _⟩ := toString_lt10_char (y / 10) (by omega)
      have hlist : (toString y).toList = [Nat.digitChar (y / 10), Nat.digitChar (y % 10)] := by
        rw [hstr, hca]; rfl
      refine ⟨Nat.digitChar 0, Nat.digitChar 0, Nat.digitChar (y / 10), Nat.digitChar (y % 10), ?_, ?_⟩
      · rw [padNatZero_eq_of_toList 4 y _ hlist (by simp), h0]; rfl
      · rw [fourDigitsNat?_of_digits 0 0 (y / 10) (y % 10) (by decide) (by decide) (by omega) (Nat.mod_lt y (by decide))]
        simp [heq]
    · by_cases h3 : y < 1000
      · have hs1 := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
        have heq1 : y / 10 * 10 + y % 10 = y := by omega
        rw [heq1] at hs1
        have hs2 := toString_two_digits_split (y / 100) ((y / 10) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq2 : y / 100 * 10 + (y / 10) % 10 = y / 10 := by omega
        rw [heq2] at hs2
        obtain ⟨hca, _⟩ := toString_lt10_char (y / 100) (by omega)
        have hlist : (toString y).toList =
            [Nat.digitChar (y / 100), Nat.digitChar ((y / 10) % 10), Nat.digitChar (y % 10)] := by
          rw [hs1, hs2, hca]; rfl
        refine ⟨Nat.digitChar 0, Nat.digitChar (y / 100), Nat.digitChar ((y / 10) % 10), Nat.digitChar (y % 10), ?_, ?_⟩
        · rw [padNatZero_eq_of_toList 4 y _ hlist (by simp), h0]; rfl
        · rw [fourDigitsNat?_of_digits 0 (y / 100) ((y / 10) % 10) (y % 10)
            (by decide) (by omega) (Nat.mod_lt _ (by decide)) (Nat.mod_lt y (by decide))]
          apply congrArg some
          calc
            0 * 1000 + y / 100 * 100 + (y / 10) % 10 * 10 + y % 10
              = (y / 100 * 10 + (y / 10) % 10) * 10 + y % 10 := by rw [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc]
            _ = y / 10 * 10 + y % 10 := by rw [heq2]
            _ = y := heq1
      · have hs1 := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
        have heq1 : y / 10 * 10 + y % 10 = y := by omega
        rw [heq1] at hs1
        have hs2 := toString_two_digits_split (y / 100) ((y / 10) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq2 : y / 100 * 10 + (y / 10) % 10 = y / 10 := by omega
        rw [heq2] at hs2
        have hs3 := toString_two_digits_split (y / 1000) ((y / 100) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq3 : y / 1000 * 10 + (y / 100) % 10 = y / 100 := by omega
        rw [heq3] at hs3
        obtain ⟨hca, _⟩ := toString_lt10_char (y / 1000) (by omega)
        have hlist : (toString y).toList =
            [Nat.digitChar (y / 1000), Nat.digitChar ((y / 100) % 10),
             Nat.digitChar ((y / 10) % 10), Nat.digitChar (y % 10)] := by
          rw [hs1, hs2, hs3, hca]; rfl
        refine ⟨Nat.digitChar (y / 1000), Nat.digitChar ((y / 100) % 10),
            Nat.digitChar ((y / 10) % 10), Nat.digitChar (y % 10), ?_, ?_⟩
        · rw [padNatZero_eq_of_toList 4 y _ hlist (by simp)]; rfl
        · rw [fourDigitsNat?_of_digits (y / 1000) ((y / 100) % 10) ((y / 10) % 10) (y % 10)
            (by omega) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt y (by decide))]
          apply congrArg some
          calc
            y / 1000 * 1000 + (y / 100) % 10 * 100 + (y / 10) % 10 * 10 + y % 10
              = ((y / 1000 * 10 + (y / 100) % 10) * 10 + (y / 10) % 10) * 10 + y % 10 := by
                  simp only [Nat.add_mul, Nat.mul_assoc]
            _ = (y / 100 * 10 + (y / 10) % 10) * 10 + y % 10 := by rw [heq3]
            _ = y / 10 * 10 + y % 10 := by rw [heq2]
            _ = y := heq1

private def utf8Sum : List Char → Nat
  | [] => 0
  | c :: cs => c.utf8Size + utf8Sum cs

private theorem utf8Sum_append (a b : List Char) :
    utf8Sum (a ++ b) = utf8Sum a + utf8Sum b := by
  induction a with
  | nil => simp [utf8Sum]
  | cons c cs ih => simp [utf8Sum, ih, Nat.add_assoc]

private theorem utf8ByteSize_ofList (cs : List Char) :
    (String.ofList cs).utf8ByteSize = utf8Sum cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih, utf8Sum]

private theorem utf8ByteSize_eq_utf8Sum (s : String) :
    s.utf8ByteSize = utf8Sum s.toList := by
  have h := utf8ByteSize_ofList s.toList
  simpa [String.ofList_toList] using h

private theorem utf8GetAux_append_add (a b : List Char) (i₀ : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (a ++ b) i₀ ⟨i₀.byteIdx + utf8Sum a⟩ =
      String.Pos.Raw.utf8GetAux b ⟨i₀.byteIdx + utf8Sum a⟩ ⟨i₀.byteIdx + utf8Sum a⟩ := by
  induction a generalizing i₀ with
  | nil => simp [utf8Sum]
  | cons c cs ih =>
    simp only [List.cons_append, utf8Sum]
    rw [String.Pos.Raw.utf8GetAux.eq_def]
    have hpos := Char.utf8Size_pos c
    have hne : i₀ ≠ ⟨i₀.byteIdx + (c.utf8Size + utf8Sum cs)⟩ := by
      intro heq
      have hidx : i₀.byteIdx = i₀.byteIdx + (c.utf8Size + utf8Sum cs) := congrArg String.Pos.Raw.byteIdx heq
      omega
    simp only [hne, ↓reduceIte]
    have hnext : i₀ + c = ⟨i₀.byteIdx + c.utf8Size⟩ := by
      apply String.Pos.Raw.ext
      exact String.Pos.Raw.byteIdx_add_char
    rw [hnext]
    have hadd : i₀.byteIdx + (c.utf8Size + utf8Sum cs) = (i₀.byteIdx + c.utf8Size) + utf8Sum cs := by omega
    rw [hadd]
    exact ih ⟨i₀.byteIdx + c.utf8Size⟩

private theorem get_at_utf8Sum (s : String) (a : List Char) (c : Char) (b : List Char)
    (h : s.toList = a ++ c :: b) :
    String.Pos.Raw.get s ⟨utf8Sum a⟩ = c ∧
    String.Pos.Raw.next s ⟨utf8Sum a⟩ = ⟨utf8Sum a + c.utf8Size⟩ ∧
    String.Pos.Raw.atEnd s ⟨utf8Sum a⟩ = false := by
  have hget : String.Pos.Raw.get s ⟨utf8Sum a⟩ = c := by
    change String.Pos.Raw.utf8GetAux s.toList 0 ⟨utf8Sum a⟩ = c
    rw [h]
    have h0 : (⟨utf8Sum a⟩ : String.Pos.Raw) = ⟨(0 : String.Pos.Raw).byteIdx + utf8Sum a⟩ := by
      simp [String.Pos.Raw.byteIdx_zero]
    rw [h0, utf8GetAux_append_add a (c :: b) 0, String.Pos.Raw.utf8GetAux.eq_def]
    simp
  refine ⟨hget, ?_, ?_⟩
  · apply String.Pos.Raw.ext
    change ((⟨utf8Sum a⟩ : String.Pos.Raw) + String.Pos.Raw.get s ⟨utf8Sum a⟩).byteIdx = utf8Sum a + c.utf8Size
    rw [hget]
    exact String.Pos.Raw.byteIdx_add_char
  · rw [String.Pos.Raw.atEnd.eq_1, decide_eq_false_iff_not]
    have hsz : s.utf8ByteSize = utf8Sum a + (c.utf8Size + utf8Sum b) := by
      rw [utf8ByteSize_eq_utf8Sum, h, utf8Sum_append, utf8Sum]
    have hpos := Char.utf8Size_pos c
    dsimp only
    omega

private theorem splitOnAux_length_ge (s sep : String) (b i j : String.Pos.Raw) (r : List String)
    (hj : j.byteIdx ≤ sep.utf8ByteSize) (hji : j.byteIdx ≤ i.byteIdx) :
    r.length + 1 ≤ (s.splitOnAux sep b i j r).length := by
  induction r_len_fuel :
      (s.utf8ByteSize - (i.unoffsetBy j).byteIdx) * (sep.utf8ByteSize + 2) +
        (sep.utf8ByteSize - j.byteIdx) + 1
      using Nat.strongRecOn generalizing b i j r with
  | ind n ih =>
    rw [String.splitOnAux.eq_def]
    by_cases hati : String.Pos.Raw.atEnd s i = true
    · simp only [hati, ↓reduceIte]
      simp
    · simp only [Bool.not_eq_true] at hati
      simp only [hati, Bool.false_eq_true, ↓reduceIte]
      by_cases hmatch : (String.Pos.Raw.get s i == String.Pos.Raw.get sep j) = true
      · simp only [hmatch, ↓reduceIte]
        have heq_ch : String.Pos.Raw.get s i = String.Pos.Raw.get sep j := by simpa using hmatch
        by_cases hatj : String.Pos.Raw.atEnd sep (String.Pos.Raw.next sep j) = true
        · simp only [hatj, ↓reduceIte]
          have hlt := String.Pos.Raw.byteIdx_lt_byteIdx_next s i
          rw [String.Pos.Raw.atEnd.eq_1] at hati
          simp only [decide_eq_false_iff_not, Nat.not_le] at hati
          have hun_le : (i.unoffsetBy j).byteIdx ≤ i.byteIdx := by
            change i.byteIdx - j.byteIdx ≤ i.byteIdx; omega
          have h0 : ((String.Pos.Raw.next s i).unoffsetBy 0).byteIdx = (String.Pos.Raw.next s i).byteIdx := by
            change (String.Pos.Raw.next s i).byteIdx - 0 = _; omega
          have hstep : (s.utf8ByteSize - ((String.Pos.Raw.next s i).unoffsetBy 0).byteIdx) *
              (sep.utf8ByteSize + 2) + (sep.utf8ByteSize - (0 : String.Pos.Raw).byteIdx) + 1 < n := by
            rw [h0]
            have hdiff : s.utf8ByteSize - (String.Pos.Raw.next s i).byteIdx ≤
                s.utf8ByteSize - (i.unoffsetBy j).byteIdx - 1 := by omega
            have hmul := Nat.mul_le_mul_right (sep.utf8ByteSize + 2) hdiff
            have hge1 : 1 ≤ s.utf8ByteSize - (i.unoffsetBy j).byteIdx := by omega
            have hsub1 : (s.utf8ByteSize - (i.unoffsetBy j).byteIdx - 1) * (sep.utf8ByteSize + 2) +
                (sep.utf8ByteSize + 2) =
                (s.utf8ByteSize - (i.unoffsetBy j).byteIdx) * (sep.utf8ByteSize + 2) := by
              rw [← Nat.succ_mul]; congr 1; omega
            have hz : (0 : String.Pos.Raw).byteIdx = 0 := rfl
            rw [← r_len_fuel, hz]
            omega
          have hrec := ih _ hstep (String.Pos.Raw.next s i) (String.Pos.Raw.next s i) 0
            (String.Pos.Raw.extract s b ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next sep j)) :: r)
            (by change 0 ≤ sep.utf8ByteSize; omega)
            (by change 0 ≤ _; omega)
            rfl
          simp only [List.length_cons] at hrec
          omega
        · simp only [Bool.not_eq_true] at hatj
          simp only [hatj, Bool.false_eq_true, ↓reduceIte]
          have hlt := String.Pos.Raw.byteIdx_lt_byteIdx_next s i
          have hltj := String.Pos.Raw.byteIdx_lt_byteIdx_next sep j
          rw [String.Pos.Raw.atEnd.eq_1] at hati hatj
          simp only [decide_eq_false_iff_not, Nat.not_le] at hati hatj
          have hnext_eq : ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next sep j)).byteIdx =
              (i.unoffsetBy j).byteIdx := by
            change (i + String.Pos.Raw.get s i).byteIdx - (j + String.Pos.Raw.get sep j).byteIdx =
              i.byteIdx - j.byteIdx
            rw [String.Pos.Raw.byteIdx_add_char, String.Pos.Raw.byteIdx_add_char, heq_ch]
            omega
          have hji' : (String.Pos.Raw.next sep j).byteIdx ≤ (String.Pos.Raw.next s i).byteIdx := by
            change (j + String.Pos.Raw.get sep j).byteIdx ≤ (i + String.Pos.Raw.get s i).byteIdx
            rw [String.Pos.Raw.byteIdx_add_char, String.Pos.Raw.byteIdx_add_char, heq_ch]
            omega
          have hj_lt : j.byteIdx < (String.Pos.Raw.next sep j).byteIdx := hltj
          have hstep : (s.utf8ByteSize - ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next sep j)).byteIdx) *
              (sep.utf8ByteSize + 2) + (sep.utf8ByteSize - (String.Pos.Raw.next sep j).byteIdx) + 1 < n := by
            rw [hnext_eq, ← r_len_fuel]
            omega
          exact ih _ hstep b (String.Pos.Raw.next s i) (String.Pos.Raw.next sep j) r (by omega) hji' rfl
      · simp only [Bool.not_eq_true] at hmatch
        simp only [hmatch, Bool.false_eq_true, ↓reduceIte]
        have hlt := String.Pos.Raw.byteIdx_lt_byteIdx_next s (i.unoffsetBy j)
        rw [String.Pos.Raw.atEnd.eq_1] at hati
        simp only [decide_eq_false_iff_not, Nat.not_le] at hati
        have hun_le : (i.unoffsetBy j).byteIdx ≤ i.byteIdx := by
          change i.byteIdx - j.byteIdx ≤ i.byteIdx; omega
        have h0 : ((String.Pos.Raw.next s (i.unoffsetBy j)).unoffsetBy 0).byteIdx =
            (String.Pos.Raw.next s (i.unoffsetBy j)).byteIdx := by
          change (String.Pos.Raw.next s (i.unoffsetBy j)).byteIdx - 0 = _; omega
        have hstep : (s.utf8ByteSize - ((String.Pos.Raw.next s (i.unoffsetBy j)).unoffsetBy 0).byteIdx) *
            (sep.utf8ByteSize + 2) + (sep.utf8ByteSize - (0 : String.Pos.Raw).byteIdx) + 1 < n := by
          rw [h0]
          have hdiff : s.utf8ByteSize - (String.Pos.Raw.next s (i.unoffsetBy j)).byteIdx ≤
              s.utf8ByteSize - (i.unoffsetBy j).byteIdx - 1 := by omega
          have hmul := Nat.mul_le_mul_right (sep.utf8ByteSize + 2) hdiff
          have hge1 : 1 ≤ s.utf8ByteSize - (i.unoffsetBy j).byteIdx := by omega
          have hsub1 : (s.utf8ByteSize - (i.unoffsetBy j).byteIdx - 1) * (sep.utf8ByteSize + 2) +
              (sep.utf8ByteSize + 2) =
              (s.utf8ByteSize - (i.unoffsetBy j).byteIdx) * (sep.utf8ByteSize + 2) := by
            rw [← Nat.succ_mul]; congr 1; omega
          have hz : (0 : String.Pos.Raw).byteIdx = 0 := rfl
          rw [← r_len_fuel, hz]
          omega
        exact ih _ hstep b (String.Pos.Raw.next s (i.unoffsetBy j)) 0 r
          (by change 0 ≤ sep.utf8ByteSize; omega) (by change 0 ≤ _; omega) rfl

private theorem splitOnAux_tripleQuote (s : String) (b i j : String.Pos.Raw) (r : List String)
    (pref suf : List Char)
    (hs : s.toList = pref ++ suf)
    (hj : j.byteIdx < 3)
    (hstate :
      (j.byteIdx = 0 ∧ i = ⟨utf8Sum pref⟩) ∨
      (j.byteIdx = 1 ∧ ∃ suf1, suf = '\'' :: suf1 ∧ i = ⟨utf8Sum pref + 1⟩) ∨
      (j.byteIdx = 2 ∧ ∃ suf2, suf = '\'' :: '\'' :: suf2 ∧ i = ⟨utf8Sum pref + 2⟩))
    (hhas : ∃ a b, suf = a ++ ['\'', '\'', '\''] ++ b) :
    r.length + 2 ≤ (s.splitOnAux "'''" b i j r).length := by
  induction hmeasure : (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - j.byteIdx)
      using Nat.strongRecOn generalizing b i j r pref suf with
  | ind m ih =>
    have hq_sz : ('\'' : Char).utf8Size = 1 := rfl
    have hget_sep : ∀ (p : String.Pos.Raw), p.byteIdx < 3 →
        String.Pos.Raw.get "'''" p = '\'' ∧
        String.Pos.Raw.next "'''" p = ⟨p.byteIdx + 1⟩ ∧
        String.Pos.Raw.atEnd "'''" ⟨p.byteIdx + 1⟩ = decide (p.byteIdx + 1 ≥ 3) := by
      intro p hp
      rcases p with ⟨idx⟩
      dsimp only at hp
      match idx with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | n + 3 => omega
    have hsuf_ne_nil : suf ≠ [] := by
      intro hnil
      rcases hhas with ⟨a, b', hab⟩
      rw [hnil] at hab
      cases a <;> simp at hab
    cases hsuf_eq : suf with
    | nil => exact absurd hsuf_eq hsuf_ne_nil
    | cons c0 suf_tail =>
      have hk_atEnd : String.Pos.Raw.atEnd s ⟨utf8Sum pref⟩ = false := by
        have h' := hs
        rw [hsuf_eq] at h'
        exact (get_at_utf8Sum s pref c0 suf_tail h').2.2
      have hk_lt : utf8Sum pref < s.utf8ByteSize := by
        rw [String.Pos.Raw.atEnd.eq_1, decide_eq_false_iff_not] at hk_atEnd
        dsimp only at hk_atEnd
        omega
      rcases hstate with ⟨hj0, hi⟩ | ⟨hj1, suf1, hsuf1, hi⟩ | ⟨hj2, suf2, hsuf2, hi⟩
      · have hj_eq : j = 0 := String.Pos.Raw.ext hj0
        subst hj_eq
        have hs' : s.toList = pref ++ c0 :: suf_tail := by rw [hs, hsuf_eq]
        obtain ⟨hgetc0, hnextc0, hatc0⟩ := get_at_utf8Sum s pref c0 suf_tail hs'
        have hsep0 : String.Pos.Raw.get "'''" 0 = '\'' := rfl
        have hnextsep0 : String.Pos.Raw.next "'''" 0 = ⟨1⟩ := rfl
        have hatsep0 : String.Pos.Raw.atEnd "'''" ⟨1⟩ = false := rfl
        rw [String.splitOnAux.eq_def, hi, hatc0]
        simp only [Bool.false_eq_true, ↓reduceIte, hgetc0, hsep0, beq_iff_eq]
        by_cases hq : c0 = '\''
        · subst hq
          simp only [↓reduceIte, hnextc0, hnextsep0, hatsep0, hq_sz]
          have hstep : (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 1) < m := by
            change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 0) = m at hmeasure
            omega
          exact ih _ hstep b ⟨utf8Sum pref + 1⟩ ⟨1⟩ r pref suf hs
            (by decide) (Or.inr (Or.inl ⟨rfl, suf_tail, hsuf_eq, rfl⟩)) hhas rfl
        · simp only [hq, ↓reduceIte]
          have hun0 : (⟨utf8Sum pref⟩ : String.Pos.Raw).unoffsetBy 0 = ⟨utf8Sum pref⟩ :=
            String.Pos.Raw.ext (Nat.sub_zero _)
          rw [hun0, hnextc0]
          have hsuf_tail_has : ∃ a b', suf_tail = a ++ ['\'', '\'', '\''] ++ b' := by
            rcases hhas with ⟨a, b', hab⟩
            rw [hsuf_eq] at hab
            cases a with
            | nil => simp at hab; exact absurd hab.1 hq
            | cons _ as =>
              simp only [List.cons_append, List.cons.injEq] at hab
              exact ⟨as, b', hab.2⟩
          have hpos := Char.utf8Size_pos c0
          have hpref' : s.toList = (pref ++ [c0]) ++ suf_tail := by
            rw [hs, hsuf_eq, List.append_assoc]; rfl
          have hsum' : utf8Sum (pref ++ [c0]) = utf8Sum pref + c0.utf8Size := by
            rw [utf8Sum_append, utf8Sum, utf8Sum, Nat.add_zero]
          have hstep : (s.utf8ByteSize - utf8Sum (pref ++ [c0])) * 4 + (3 - 0) < m := by
            change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 0) = m at hmeasure
            omega
          exact ih _ hstep b ⟨utf8Sum pref + c0.utf8Size⟩ 0 r (pref ++ [c0]) suf_tail hpref'
            (by decide) (Or.inl ⟨rfl, by rw [hsum']⟩) hsuf_tail_has rfl
      · have hj_eq : j = ⟨1⟩ := String.Pos.Raw.ext hj1
        subst hj_eq
        have hsuf_eq1 : c0 :: suf_tail = '\'' :: suf1 := by rw [← hsuf_eq, hsuf1]
        injection hsuf_eq1 with hc0 hsuf1_eq
        subst hc0
        have hsuf1_ne : suf1 ≠ [] := by
          intro hnil
          rcases hhas with ⟨a, b', hab⟩
          rw [hsuf1, hnil] at hab
          cases a with
          | nil => simp at hab
          | cons _ a' => cases a' <;> simp at hab
        cases hsuf1_cases : suf1 with
        | nil => exact absurd hsuf1_cases hsuf1_ne
        | cons c1 suf1_tail =>
          have hs' : s.toList = (pref ++ ['\'']) ++ c1 :: suf1_tail := by
            rw [hs, hsuf1, hsuf1_cases, List.append_assoc]; rfl
          have hsum_p1 : utf8Sum (pref ++ ['\'']) = utf8Sum pref + 1 := by
            rw [utf8Sum_append, utf8Sum, utf8Sum, hq_sz]
          obtain ⟨hgetc1, hnextc1, hatc1⟩ := get_at_utf8Sum s (pref ++ ['\'']) c1 suf1_tail hs'
          rw [hsum_p1] at hgetc1 hnextc1 hatc1
          have hsep1 : String.Pos.Raw.get "'''" ⟨1⟩ = '\'' := rfl
          have hnextsep1 : String.Pos.Raw.next "'''" ⟨1⟩ = ⟨2⟩ := rfl
          have hatsep1 : String.Pos.Raw.atEnd "'''" ⟨2⟩ = false := rfl
          rw [String.splitOnAux.eq_def, hi, hatc1]
          simp only [Bool.false_eq_true, ↓reduceIte, hgetc1, hsep1, beq_iff_eq]
          by_cases hq : c1 = '\''
          · subst hq
            simp only [↓reduceIte, hnextc1, hnextsep1, hatsep1, hq_sz]
            have hstep : (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 2) < m := by
              change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 1) = m at hmeasure
              omega
            have hsuf2 : suf = '\'' :: '\'' :: suf1_tail := by rw [hsuf1, hsuf1_cases]
            exact ih _ hstep b ⟨utf8Sum pref + 2⟩ ⟨2⟩ r pref suf hs
              (by decide) (Or.inr (Or.inr ⟨rfl, suf1_tail, hsuf2, rfl⟩)) hhas rfl
          · simp only [hq, ↓reduceIte]
            have hun1 : (⟨utf8Sum pref + 1⟩ : String.Pos.Raw).unoffsetBy ⟨1⟩ = ⟨utf8Sum pref⟩ :=
              String.Pos.Raw.ext (by change utf8Sum pref + 1 - 1 = utf8Sum pref; omega)
            have hs0 : s.toList = pref ++ '\'' :: suf1 := by rw [hs, hsuf1]
            obtain ⟨_, hnext_q0, _⟩ := get_at_utf8Sum s pref '\'' suf1 hs0
            rw [hun1, hnext_q0, hq_sz]
            have hsuf1_has : ∃ a b', suf1 = a ++ ['\'', '\'', '\''] ++ b' := by
              rcases hhas with ⟨a, b', hab⟩
              rw [hsuf1, hsuf1_cases] at hab
              cases a with
              | nil => simp at hab; exact absurd hab.1 hq
              | cons _ as =>
                simp only [List.cons_append, List.cons.injEq] at hab
                exact ⟨as, b', by rw [hsuf1_cases, hab.2]⟩
            have hpref' : s.toList = (pref ++ ['\'']) ++ suf1 := by rw [hs, hsuf1, List.append_assoc]; rfl
            have hstep : (s.utf8ByteSize - utf8Sum (pref ++ ['\''])) * 4 + (3 - 0) < m := by
              change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 1) = m at hmeasure
              omega
            exact ih _ hstep b ⟨utf8Sum pref + 1⟩ 0 r (pref ++ ['\'']) suf1 hpref'
              (by decide) (Or.inl ⟨rfl, by rw [hsum_p1]⟩) hsuf1_has rfl
      · have hj_eq : j = ⟨2⟩ := String.Pos.Raw.ext hj2
        subst hj_eq
        have hsuf_eq2 : c0 :: suf_tail = '\'' :: '\'' :: suf2 := by rw [← hsuf_eq, hsuf2]
        injection hsuf_eq2 with hc0 hsuf2_tail_eq
        subst hc0
        have hsuf2_ne : suf2 ≠ [] := by
          intro hnil
          rcases hhas with ⟨a, b', hab⟩
          rw [hsuf2, hnil] at hab
          cases a with
          | nil => simp at hab
          | cons _ a' =>
            cases a' with
            | nil => simp at hab
            | cons _ a'' => cases a'' <;> simp at hab
        cases hsuf2_cases : suf2 with
        | nil => exact absurd hsuf2_cases hsuf2_ne
        | cons c2 suf2_tail =>
          have hs' : s.toList = (pref ++ ['\'', '\'']) ++ c2 :: suf2_tail := by
            rw [hs, hsuf2, hsuf2_cases, List.append_assoc]; rfl
          have hsum_p2 : utf8Sum (pref ++ ['\'', '\'']) = utf8Sum pref + 2 := by
            rw [utf8Sum_append, utf8Sum, utf8Sum, utf8Sum, hq_sz]
          obtain ⟨hgetc2, hnextc2, hatc2⟩ := get_at_utf8Sum s (pref ++ ['\'', '\'']) c2 suf2_tail hs'
          rw [hsum_p2] at hgetc2 hnextc2 hatc2
          have hsep2 : String.Pos.Raw.get "'''" ⟨2⟩ = '\'' := rfl
          have hnextsep2 : String.Pos.Raw.next "'''" ⟨2⟩ = ⟨3⟩ := rfl
          have hatsep2 : String.Pos.Raw.atEnd "'''" ⟨3⟩ = true := rfl
          rw [String.splitOnAux.eq_def, hi, hatc2]
          simp only [Bool.false_eq_true, ↓reduceIte, hgetc2, hsep2, beq_iff_eq]
          by_cases hq : c2 = '\''
          · subst hq
            simp only [↓reduceIte, hnextc2, hnextsep2, hatsep2]
            have hge := splitOnAux_length_ge s "'''"
              (⟨utf8Sum pref + 2 + '\''.utf8Size⟩)
              (⟨utf8Sum pref + 2 + '\''.utf8Size⟩) 0
              (String.Pos.Raw.extract s b
                ((⟨utf8Sum pref + 2 + '\''.utf8Size⟩ : String.Pos.Raw).unoffsetBy ⟨3⟩) :: r)
              (by decide) (by change 0 ≤ _; omega)
            simp only [List.length_cons] at hge
            omega
          · simp only [hq, ↓reduceIte]
            have hun2 : (⟨utf8Sum pref + 2⟩ : String.Pos.Raw).unoffsetBy ⟨2⟩ = ⟨utf8Sum pref⟩ :=
              String.Pos.Raw.ext (by change utf8Sum pref + 2 - 2 = utf8Sum pref; omega)
            have hs0 : s.toList = pref ++ '\'' :: ('\'' :: suf2) := by rw [hs, hsuf2]
            obtain ⟨_, hnext_q0, _⟩ := get_at_utf8Sum s pref '\'' ('\'' :: suf2) hs0
            rw [hun2, hnext_q0, hq_sz]
            have hsum_p1 : utf8Sum (pref ++ ['\'']) = utf8Sum pref + 1 := by
              rw [utf8Sum_append, utf8Sum, utf8Sum, hq_sz]
            have hsuf2_has : ∃ a b', ('\'' :: suf2) = a ++ ['\'', '\'', '\''] ++ b' := by
              rcases hhas with ⟨a, b', hab⟩
              rw [hsuf2, hsuf2_cases] at hab
              cases a with
              | nil => simp at hab; exact absurd hab.1 hq
              | cons _ as =>
                simp only [List.cons_append, List.cons.injEq] at hab
                exact ⟨as, b', by rw [hsuf2_cases, hab.2]⟩
            have hpref' : s.toList = (pref ++ ['\'']) ++ ('\'' :: suf2) := by
              rw [hs, hsuf2, List.append_assoc]; rfl
            have hstep : (s.utf8ByteSize - utf8Sum (pref ++ ['\''])) * 4 + (3 - 0) < m := by
              change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 2) = m at hmeasure
              omega
            exact ih _ hstep b ⟨utf8Sum pref + 1⟩ 0 r (pref ++ ['\'']) ('\'' :: suf2) hpref'
              (by decide) (Or.inl ⟨rfl, by rw [hsum_p1]⟩) hsuf2_has rfl

private theorem no_triple_quote_of_not_containsSubstr (s : String) (h : containsSubstr s "'''" = false) :
    ∀ a b : List Char, s.toList ≠ a ++ ['\'', '\'', '\''] ++ b := by
  intro a b hab
  simp only [containsSubstr, decide_eq_false_iff_not, Nat.not_lt] at h
  have hne : ("'''" == "") = false := rfl
  have hsplit : s.splitOn "'''" = s.splitOnAux "'''" 0 0 0 [] := by
    simp [String.splitOn, hne]
  rw [hsplit] at h
  have hge := splitOnAux_tripleQuote s 0 0 0 [] [] s.toList (by simp) (by decide)
    (Or.inl ⟨rfl, rfl⟩) ⟨a, b, hab⟩
  simp at hge
  omega

private theorem getLast_ne_quote_of_not_endsWith (s : String) (h : s.endsWith "'" = false) :
    ∀ a : List Char, s.toList ≠ a ++ ['\''] := by
  intro a ha
  rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_eq_false_iff] at h
  apply h
  have hcopy : s.toSlice.copy = s := String.copy_toSlice
  rw [hcopy, ha]
  exact ⟨a, rfl⟩

private theorem not_mem_of_contains_false (s : String) (c : Char) (h : s.contains c = false) :
    c ∉ s.toList := by
  rw [String.contains_char_eq, decide_eq_false_iff_not] at h
  exact h

private theorem takeHexDigits_hexDigitUpper_4 (n : Nat) (hn : n < 256) (rest : List Char) :
    takeHexDigits 4 0 ('0' :: '0' :: hexDigitUpper (n / 16) :: hexDigitUpper (n % 16) :: rest) =
      some (n, rest) := by
  have h0 : hexVal? '0' = some 0 := rfl
  have h1 := hexDigitUpper_val (n / 16) (by omega)
  have h2 := hexDigitUpper_val (n % 16) (Nat.mod_lt n (by decide))
  simp only [takeHexDigits, h0, h1, h2]
  congr 1; congr 1; omega

private theorem parseUnicodeHex_hexDigitUpper_4 (c : Char) (hc : isDisallowedControl c = true) (rest : List Char) :
    parseUnicodeHex 4 ('0' :: '0' :: hexDigitUpper (c.toNat / 16) :: hexDigitUpper (c.toNat % 16) :: rest) =
      .ok (c, rest) := by
  have hlt : c.toNat < 256 := by
    simp only [isDisallowedControl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    omega
  simp only [parseUnicodeHex, takeHexDigits_hexDigitUpper_4 c.toNat hlt rest]
  have hrange : (c.toNat > 0x10FFFF || (0xD800 ≤ c.toNat && c.toNat ≤ 0xDFFF)) = false := by
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨by omega, Or.inl (by omega)⟩
  simp [hrange, Char.ofNat_toNat]

private theorem escapeBasicChar_clean (allowNewline : Bool) (c : Char) :
    ((escapeBasicChar allowNewline c).toList.all fun ch =>
      !isDisallowedControl ch && ch != '\r' && (allowNewline || ch != '\n')) = true := by
  by_cases h1 : c = '\\'
  · subst h1; cases allowNewline <;> decide
  · by_cases h2 : c = '"'
    · subst h2; cases allowNewline <;> decide
    · by_cases h3 : c = '\x08'
      · subst h3; cases allowNewline <;> decide
      · by_cases h4 : c = '\t'
        · subst h4; cases allowNewline <;> decide
        · by_cases h5 : c = '\n'
          · subst h5; cases allowNewline <;> decide
          · by_cases h6 : c = '\x0c'
            · subst h6; cases allowNewline <;> decide
            · by_cases h7 : c = '\r'
              · subst h7; cases allowNewline <;> decide
              · by_cases hc : isDisallowedControl c = true
                · have hdef : escapeBasicChar allowNewline c =
                      "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                    simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                  rw [hdef]
                  have hlt : c.toNat < 256 := by
                    simp only [isDisallowedControl, Bool.or_eq_true, Bool.and_eq_true,
                      decide_eq_true_eq, beq_iff_eq] at hc
                    omega
                  have hd1 := hexDigitUpper_clean (c.toNat / 16) (by omega)
                  have hd2 := hexDigitUpper_clean (c.toNat % 16) (Nat.mod_lt _ (by decide))
                  simp only [String.toList_append, String.toList_ofList, List.all_append,
                    List.all_cons, List.all_nil, Bool.and_true]
                  have hu : (("\\u00" : String).toList.all fun ch =>
                      !isDisallowedControl ch && ch != '\r' && (allowNewline || ch != '\n')) = true := by
                    cases allowNewline <;> decide
                  simp only [Bool.and_eq_true] at hd1 hd2 ⊢
                  refine ⟨hu, ⟨?_, ?_⟩⟩
                  · cases allowNewline <;> simp [hd1]
                  · cases allowNewline <;> simp [hd2]
                · have hdef : escapeBasicChar allowNewline c = String.singleton c := by
                    simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                  rw [hdef]
                  simp only [String.toList_singleton, List.all_cons, List.all_nil, Bool.and_true,
                    Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
                  refine ⟨⟨by simp at hc; exact hc, h7⟩, ?_⟩
                  cases allowNewline <;> simp [h5]

private theorem escapeBasicBody_clean (allowNewline : Bool) (s : String) :
    ((escapeBasicBody allowNewline s).toList.all fun ch =>
      !isDisallowedControl ch && ch != '\r' && (allowNewline || ch != '\n')) = true := by
  simp only [escapeBasicBody, String.toList_join, List.all_flatMap, List.all_map, Function.comp_def]
  rw [List.all_eq_true]
  intro c _
  exact escapeBasicChar_clean allowNewline c

private theorem parseBasicStringBodyFuel_step_bs (f : Nat) (acc rest : List Char) :
    parseBasicStringBodyFuel (f + 1) acc ('\\' :: rest) =
      (parseBasicEscape rest >>= fun (ch, afterEsc) =>
        parseBasicStringBodyFuel f (ch :: acc) afterEsc) := rfl

private theorem parseBasicStringBodyFuel_step_char (f : Nat) (acc : List Char) (c : Char) (rest : List Char)
    (hnl : c ≠ '\n') (hq : c ≠ '"') (hbs : c ≠ '\\') :
    parseBasicStringBodyFuel (f + 1) acc (c :: rest) = parseBasicStringBodyFuel f (c :: acc) rest := by
  conv => lhs; unfold parseBasicStringBodyFuel
  split <;> simp_all

private theorem escapeBasicChar_length_pos (allowNl : Bool) (c : Char) :
    (escapeBasicChar allowNl c).toList.length ≥ 1 := by
  by_cases h1 : c = '\\'
  · subst h1; cases allowNl <;> decide
  · by_cases h2 : c = '"'
    · subst h2; cases allowNl <;> decide
    · by_cases h3 : c = '\x08'
      · subst h3; cases allowNl <;> decide
      · by_cases h4 : c = '\t'
        · subst h4; cases allowNl <;> decide
        · by_cases h5 : c = '\n'
          · subst h5; cases allowNl <;> decide
          · by_cases h6 : c = '\x0c'
            · subst h6; cases allowNl <;> decide
            · by_cases h7 : c = '\r'
              · subst h7; cases allowNl <;> decide
              · by_cases hc : isDisallowedControl c = true
                · have hdef : escapeBasicChar allowNl c =
                      "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                    simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                  rw [hdef]; simp
                · have hdef : escapeBasicChar allowNl c = String.singleton c := by
                    simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                  rw [hdef]; simp

private theorem parseBasicStringBodyFuel_escapeBasicBody_list (cs acc rest : List Char) (fuel : Nat)
    (hfuel : (cs.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 ≤ fuel) :
    parseBasicStringBodyFuel fuel acc (cs.flatMap (fun c => (escapeBasicChar false c).toList) ++ '"' :: rest) =
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
      simp only [List.flatMap_cons, List.append_assoc]
      have hsub : (cs.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 ≤ f := by
        simp only [List.flatMap_cons, List.length_append] at hfuel
        have hlen := escapeBasicChar_length_pos false c
        omega
      by_cases h1 : c = '\\'
      · subst h1
        have hstr : (escapeBasicChar false '\\').toList = ['\\', '\\'] := rfl
        rw [hstr]
        simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
          parseBasicEscape, bind, Except.bind, ih ('\\' :: acc) f hsub]
        simp
      · by_cases h2 : c = '"'
        · subst h2
          have hstr : (escapeBasicChar false '"').toList = ['\\', '"'] := rfl
          rw [hstr]
          simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
            parseBasicEscape, bind, Except.bind, ih ('"' :: acc) f hsub]
          simp
        · by_cases h3 : c = '\x08'
          · subst h3
            have hstr : (escapeBasicChar false '\x08').toList = ['\\', 'b'] := rfl
            rw [hstr]
            simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
              parseBasicEscape, bind, Except.bind, ih ('\x08' :: acc) f hsub]
            simp
          · by_cases h4 : c = '\t'
            · subst h4
              have hstr : (escapeBasicChar false '\t').toList = ['\\', 't'] := rfl
              rw [hstr]
              simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                parseBasicEscape, bind, Except.bind, ih ('\t' :: acc) f hsub]
              simp
            · by_cases h5 : c = '\n'
              · subst h5
                have hstr : (escapeBasicChar false '\n').toList = ['\\', 'n'] := rfl
                rw [hstr]
                simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                  parseBasicEscape, bind, Except.bind, ih ('\n' :: acc) f hsub]
                simp
              · by_cases h6 : c = '\x0c'
                · subst h6
                  have hstr : (escapeBasicChar false '\x0c').toList = ['\\', 'f'] := rfl
                  rw [hstr]
                  simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                    parseBasicEscape, bind, Except.bind, ih ('\x0c' :: acc) f hsub]
                  simp
                · by_cases h7 : c = '\r'
                  · subst h7
                    have hstr : (escapeBasicChar false '\r').toList = ['\\', 'r'] := rfl
                    rw [hstr]
                    simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                      parseBasicEscape, bind, Except.bind, ih ('\r' :: acc) f hsub]
                    simp
                  · by_cases hc : isDisallowedControl c = true
                    · have hstr : (escapeBasicChar false c).toList =
                          ['\\', 'u', '0', '0', hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                        have hdef : escapeBasicChar false c =
                            "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                          simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                        rw [hdef]
                        have hu : ("\\u00" : String).toList = ['\\', 'u', '0', '0'] := rfl
                        simp [hu]
                      rw [hstr]
                      simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                        parseBasicEscape, parseUnicodeHex_hexDigitUpper_4 c hc, bind, Except.bind,
                        ih (c :: acc) f hsub]
                      simp
                    · have hstr : (escapeBasicChar false c).toList = [c] := by
                        have hdef : escapeBasicChar false c = String.singleton c := by
                          simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                        rw [hdef]; simp
                      rw [hstr]
                      simp only [List.cons_append, List.nil_append]
                      rw [parseBasicStringBodyFuel_step_char f acc c _ h5 h2 h1, ih (c :: acc) f hsub]
                      simp

private theorem parseBasicStringBody_escapeBasicBody (s : String) (rest : List Char) :
    parseBasicStringBody ((escapeBasicBody false s).toList ++ '"' :: rest) =
      .ok (s, rest) := by
  unfold parseBasicStringBody
  have heq : (escapeBasicBody false s).toList =
      s.toList.flatMap (fun c => (escapeBasicChar false c).toList) := by
    simp [escapeBasicBody, String.toList_join, List.flatMap_map]
  have hlen : ((escapeBasicBody false s).toList ++ '"' :: rest).length + 1 ≥
      (s.toList.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 := by
    rw [heq]
    simp only [List.length_append, List.length_cons]
    omega
  rw [heq] at hlen ⊢
  rw [parseBasicStringBodyFuel_escapeBasicBody_list s.toList [] rest _ hlen]
  simp [String.ofList_toList]

private theorem parseMultilineBasicBodyFuel_step_bs (f : Nat) (acc rest : List Char) :
    parseMultilineBasicBodyFuel (f + 1) acc ('\\' :: rest) =
      match parseBasicEscape rest with
      | .ok (ch, afterEsc) => parseMultilineBasicBodyFuel f (ch :: acc) afterEsc
      | .error err =>
        match skipHorizWs rest with
        | '\n' :: afterNl => parseMultilineBasicBodyFuel f acc (skipHorizAndNl afterNl)
        | _ =>
          match rest with
          | 'u' :: _ => .error err
          | 'U' :: _ => .error err
          | _ => .error (mkErr .parseError "invalid escape sequence in multiline basic string") := rfl

private theorem parseMultilineBasicBodyFuel_step_char (f : Nat) (acc : List Char) (c : Char) (rest : List Char)
    (hq : c ≠ '"') (hbs : c ≠ '\\') :
    parseMultilineBasicBodyFuel (f + 1) acc (c :: rest) =
      parseMultilineBasicBodyFuel f (c :: acc) rest := by
  conv => lhs; unfold parseMultilineBasicBodyFuel
  split <;> simp_all

private theorem parseMultilineBasicBodyFuel_escapeBasicBody_list (cs acc rest : List Char) (fuel : Nat)
    (hrest : ∀ c r, rest = c :: r → c ≠ '"')
    (hfuel : (cs.flatMap (fun c => (escapeBasicChar true c).toList)).length + 1 ≤ fuel) :
    parseMultilineBasicBodyFuel fuel acc
      (cs.flatMap (fun c => (escapeBasicChar true c).toList) ++ ['"', '"', '"'] ++ rest) =
      .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc fuel with
  | nil =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.flatMap_nil, List.nil_append, List.cons_append]
      cases rest with
      | nil => simp [parseMultilineBasicBodyFuel]
      | cons c r =>
        have hne : c ≠ '"' := hrest c r rfl
        conv => lhs; unfold parseMultilineBasicBodyFuel
        split
        all_goals try (simp_all; done)
        rename_i _ hq1 _ _ heq
        cases heq
        exact absurd rfl (hq1 (c :: r) rfl)
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.flatMap_cons, List.append_assoc]
      have hsub : (cs.flatMap (fun c => (escapeBasicChar true c).toList)).length + 1 ≤ f := by
        simp only [List.flatMap_cons, List.length_append] at hfuel
        have hlen := escapeBasicChar_length_pos true c
        omega
      by_cases h1 : c = '\\'
      · subst h1
        have hstr : (escapeBasicChar true '\\').toList = ['\\', '\\'] := rfl
        rw [hstr]
        simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
          parseBasicEscape]
        have hih := ih ('\\' :: acc) f hsub
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
        rw [hih]; simp
      · by_cases h2 : c = '"'
        · subst h2
          have hstr : (escapeBasicChar true '"').toList = ['\\', '"'] := rfl
          rw [hstr]
          simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
            parseBasicEscape]
          have hih := ih ('"' :: acc) f hsub
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
          rw [hih]; simp
        · by_cases h3 : c = '\x08'
          · subst h3
            have hstr : (escapeBasicChar true '\x08').toList = ['\\', 'b'] := rfl
            rw [hstr]
            simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
              parseBasicEscape]
            have hih := ih ('\x08' :: acc) f hsub
            simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
            rw [hih]; simp
          · by_cases h4 : c = '\t'
            · subst h4
              have hstr : (escapeBasicChar true '\t').toList = ['\\', 't'] := rfl
              rw [hstr]
              simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
                parseBasicEscape]
              have hih := ih ('\t' :: acc) f hsub
              simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
              rw [hih]; simp
            · by_cases h5 : c = '\n'
              · subst h5
                have hstr : (escapeBasicChar true '\n').toList = ['\n'] := rfl
                rw [hstr]
                simp only [List.cons_append, List.nil_append]
                rw [parseMultilineBasicBodyFuel_step_char f acc '\n' _ (by decide) (by decide)]
                have hih := ih ('\n' :: acc) f hsub
                simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                rw [hih]; simp
              · by_cases h6 : c = '\x0c'
                · subst h6
                  have hstr : (escapeBasicChar true '\x0c').toList = ['\\', 'f'] := rfl
                  rw [hstr]
                  simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
                    parseBasicEscape]
                  have hih := ih ('\x0c' :: acc) f hsub
                  simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                  rw [hih]; simp
                · by_cases h7 : c = '\r'
                  · subst h7
                    have hstr : (escapeBasicChar true '\r').toList = ['\\', 'r'] := rfl
                    rw [hstr]
                    simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
                      parseBasicEscape]
                    have hih := ih ('\r' :: acc) f hsub
                    simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                    rw [hih]; simp
                  · by_cases hc : isDisallowedControl c = true
                    · have hstr : (escapeBasicChar true c).toList =
                          ['\\', 'u', '0', '0', hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                        have hdef : escapeBasicChar true c =
                            "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                          simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                        rw [hdef]
                        have hu : ("\\u00" : String).toList = ['\\', 'u', '0', '0'] := rfl
                        simp [hu]
                      rw [hstr]
                      simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
                        parseBasicEscape, parseUnicodeHex_hexDigitUpper_4 c hc]
                      have hih := ih (c :: acc) f hsub
                      simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                      rw [hih]; simp
                    · have hstr : (escapeBasicChar true c).toList = [c] := by
                        have hdef : escapeBasicChar true c = String.singleton c := by
                          simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                        rw [hdef]; simp
                      rw [hstr]
                      simp only [List.cons_append, List.nil_append]
                      rw [parseMultilineBasicBodyFuel_step_char f acc c _ h2 h1]
                      have hih := ih (c :: acc) f hsub
                      simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                      rw [hih]; simp

private theorem parseMultilineBasicString_escapeBasicBody (s : String) (rest : List Char)
    (hrest : ∀ c r, rest = c :: r → c ≠ '"') :
    parseMultilineBasicString ('\n' :: (escapeBasicBody true s).toList ++ ['"', '"', '"'] ++ rest) =
      .ok (s, rest) := by
  unfold parseMultilineBasicString
  have heq : (escapeBasicBody true s).toList =
      s.toList.flatMap (fun c => (escapeBasicChar true c).toList) := by
    simp [escapeBasicBody, String.toList_join, List.flatMap_map]
  rw [heq]
  simp only [List.cons_append]
  have hlen : (s.toList.flatMap (fun c => (escapeBasicChar true c).toList) ++ ['"', '"', '"'] ++ rest).length + 1 ≥
      (s.toList.flatMap (fun c => (escapeBasicChar true c).toList)).length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  rw [parseMultilineBasicBodyFuel_escapeBasicBody_list s.toList [] rest _ hrest hlen]
  simp [String.ofList_toList]

private theorem parseLiteralStringBody_list (cs acc rest : List Char)
    (hnl : '\n' ∉ cs) (hq : '\'' ∉ cs) :
    parseLiteralStringBody acc (cs ++ '\'' :: rest) =
      .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc with
  | nil => simp [parseLiteralStringBody]
  | cons c cs ih =>
    have hc_nl : c ≠ '\n' := fun h => hnl (by simp [h])
    have hc_q : c ≠ '\'' := fun h => hq (by simp [h])
    have hnl' : '\n' ∉ cs := fun h => hnl (by simp [h])
    have hq' : '\'' ∉ cs := fun h => hq (by simp [h])
    simp only [List.cons_append]
    unfold parseLiteralStringBody
    split <;> rename_i heq
    · simp at heq
    · injection heq with hc; exact absurd hc hc_nl
    · injection heq with hc; exact absurd hc hc_q
    · injection heq with hc hr
      subst hc hr
      rw [ih (c :: acc) hnl' hq']
      simp

private theorem parseMultilineLiteralBodyFuel_step (f : Nat) (acc : List Char) (c : Char) (cs : List Char)
    (hnot3 : ¬ (c = '\'' ∧ ∃ t, cs = '\'' :: '\'' :: t)) :
    parseMultilineLiteralBodyFuel (f + 1) acc (c :: cs) =
      parseMultilineLiteralBodyFuel f (c :: acc) cs := by
  conv => lhs; unfold parseMultilineLiteralBodyFuel
  split <;> first | simp_all | (exfalso; apply hnot3; simp_all)

private theorem parseMultilineLiteralBodyFuel_list (cs acc rest : List Char) (fuel : Nat)
    (hno3 : ∀ a b, cs ≠ a ++ ['\'', '\'', '\''] ++ b)
    (hnoend : ∀ a, cs ≠ a ++ ['\''])
    (hrest : ∀ c r, rest = c :: r → c ≠ '\'')
    (hfuel : cs.length + 1 ≤ fuel) :
    parseMultilineLiteralBodyFuel fuel acc (cs ++ ['\'', '\'', '\''] ++ rest) =
      .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc fuel with
  | nil =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.nil_append, List.cons_append]
      cases rest with
      | nil => simp [parseMultilineLiteralBodyFuel]
      | cons c r =>
        have hne : c ≠ '\'' := hrest c r rfl
        conv => lhs; unfold parseMultilineLiteralBodyFuel
        split
        all_goals try (simp_all; done)
        rename_i hq1 _ heq
        cases heq
        exact absurd rfl (hq1 (c :: r) rfl)
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      have hsub : cs.length + 1 ≤ f := by simp at hfuel; omega
      have hno3' : ∀ a b, cs ≠ a ++ ['\'', '\'', '\''] ++ b := by
        intro a b hab
        exact hno3 (c :: a) b (by simp [hab])
      have hnoend' : ∀ a, cs ≠ a ++ ['\''] := by
        intro a ha
        exact hnoend (c :: a) (by simp [ha])
      have hnot3 : ¬ (c = '\'' ∧ ∃ t, cs ++ ['\'', '\'', '\''] ++ rest = '\'' :: '\'' :: t) := by
        intro ⟨hc, t, ht⟩
        subst hc
        cases cs with
        | nil => exact hnoend [] rfl
        | cons c1 cs1 =>
          cases cs1 with
          | nil =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
            exact hnoend ['\''] (by simp [ht.1])
          | cons c2 cs2 =>
            simp only [List.cons_append, List.cons.injEq] at ht
            exact hno3 [] cs2 (by simp [ht.1, ht.2.1])
      change parseMultilineLiteralBodyFuel (f + 1) acc (c :: (cs ++ ['\'', '\'', '\''] ++ rest)) = _
      rw [parseMultilineLiteralBodyFuel_step f acc c _ hnot3,
        ih (c :: acc) f hno3' hnoend' hsub]
      simp

private theorem takeBareKeyChars_append (acc ks rest : List Char)
    (hks : ks.all isBareKeyChar = true)
    (hrest : ∀ c tail, rest = c :: tail → isBareKeyChar c = false) :
    takeBareKeyChars acc (ks ++ rest) = (acc.reverse ++ ks, rest) := by
  induction ks generalizing acc with
  | nil =>
    cases rest with
    | nil => simp [takeBareKeyChars]
    | cons c r =>
      simp only [List.nil_append, takeBareKeyChars, hrest c r rfl, Bool.false_eq_true, ↓reduceIte,
        List.append_nil]
  | cons k ks ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hks
    simp only [List.cons_append, takeBareKeyChars, hks.1, ↓reduceIte]
    rw [ih (k :: acc) hks.2]
    simp

private theorem parseKeySegment_basic (cs : List Char) (hno : ¬ ∃ r, cs = '"' :: '"' :: r) :
    parseKeySegment ('"' :: cs) = parseBasicStringBody cs := by
  unfold parseKeySegment
  split
  · exfalso; apply hno; simp_all
  · simp_all
  · rename_i heq; cases heq; rfl
  · simp_all
  · simp_all

private theorem parseKeySegment_literal (cs : List Char) (hno : ¬ ∃ r, cs = '\'' :: '\'' :: r) :
    parseKeySegment ('\'' :: cs) = parseLiteralStringBody [] cs := by
  unfold parseKeySegment
  split
  · simp_all
  · exfalso; apply hno; simp_all
  · simp_all
  · rename_i heq; cases heq; rfl
  · simp_all

private theorem parseKeySegment_bare (c0 : Char) (cs : List Char) (hq1 : c0 ≠ '"') (hq2 : c0 ≠ '\'') :
    parseKeySegment (c0 :: cs) =
      let (ks, rest) := takeBareKeyChars [] (c0 :: cs)
      if ks.isEmpty then .error (mkErr .parseError "expected key")
      else .ok (String.ofList ks, rest) := by
  unfold parseKeySegment
  split <;> first | simp_all | rfl

/-- Internal TOML scalar round-trip lemma `renderKey_parseKeySegment`. -/
theorem renderKey_parseKeySegment (k : String) (ks : KeyStyle) (rk : String)
    (hr : renderKey k ks = some rk) (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'') :
    parseKeySegment (rk.toList ++ rest) = .ok (k, rest) ∧
    (rk.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  cases ks with
  | bare =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hbare
      injection hr with hrk
      subst hrk
      simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare
      rcases hbare with ⟨hne, hall⟩
      have hne_list : k.toList ≠ [] := by
        intro h
        have hk0 : k = "" := by rw [← String.ofList_toList (s := k), h]
        subst hk0
        simp at hne
      have hrest_bare : ∀ c tail, rest = c :: tail → isBareKeyChar c = false := by
        intro c tail h
        simpa using (hrest c tail h).1
      have htake := takeBareKeyChars_append [] k.toList rest hall hrest_bare
      simp only [List.reverse_nil, List.nil_append] at htake
      have hparse : parseKeySegment (k.toList ++ rest) = .ok (k, rest) := by
        cases hlist : k.toList with
        | nil => exact absurd hlist hne_list
        | cons c0 cs0 =>
          have hc0' : isBareKeyChar c0 = true :=
            List.all_eq_true.mp hall c0 (by rw [hlist]; simp)
          have hcl' := isBareKeyChar_clean c0 hc0'
          simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hcl'
          have hq1 : c0 ≠ '"' := hcl'.1.1.1.1.1.1.2
          have hq2 : c0 ≠ '\'' := hcl'.1.1.1.1.1.2
          simp only [List.cons_append, parseKeySegment_bare c0 (cs0 ++ rest) hq1 hq2]
          rw [← List.cons_append, ← hlist, htake]
          have hne_ks : k.toList.isEmpty = false := by simp [hlist]
          have hk_of : String.ofList k.toList = k := String.ofList_toList
          simp only [hne_ks, Bool.false_eq_true, ↓reduceIte, hk_of]
      refine ⟨hparse, ?_⟩
      rw [List.all_eq_true]
      intro c hc
      have hbc := List.all_eq_true.mp hall c hc
      have hcl := isBareKeyChar_clean c hbc
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hcl ⊢
      exact ⟨⟨hcl.1.1.1.1.1.1.1.1.1.1.1, hcl.1.1.1.1.1.1.1.1.1.1.2⟩, hcl.1.1.1.1.1.1.1.1.1.2⟩
    · simp at hr
  | basic =>
    simp only [renderKey] at hr
    injection hr with hrk
    subst hrk
    have hclean_esc := escapeBasicBody_clean false k
    have hno3 : ¬ ∃ r', ((escapeBasicBody false k).toList ++ '"' :: rest) = '"' :: '"' :: r' := by
      intro ⟨r', hr'⟩
      cases hk : k.toList with
      | nil =>
        have hbody : (escapeBasicBody false k).toList = [] := by
          simp [escapeBasicBody, hk]
        rw [hbody, List.nil_append] at hr'
        cases rest with
        | nil => simp at hr'
        | cons c _ =>
          simp only [List.cons.injEq] at hr'
          exact (hrest c _ rfl).2.1 hr'.2.1
      | cons c0 cs0 =>
        have hbody : (escapeBasicBody false k).toList =
            (escapeBasicChar false c0).toList ++ cs0.flatMap (fun c => (escapeBasicChar false c).toList) := by
          simp [escapeBasicBody, String.toList_join, hk, List.flatMap_map]
        rw [hbody, List.append_assoc] at hr'
        have hne : ((escapeBasicChar false c0).toList).head? ≠ some '"' := by
          by_cases h1 : c0 = '\\'
          · subst h1; decide
          · by_cases h2 : c0 = '"'
            · subst h2; decide
            · by_cases h3 : c0 = '\x08'
              · subst h3; decide
              · by_cases h4 : c0 = '\t'
                · subst h4; decide
                · by_cases h5 : c0 = '\n'
                  · subst h5; decide
                  · by_cases h6 : c0 = '\x0c'
                    · subst h6; decide
                    · by_cases h7 : c0 = '\r'
                      · subst h7; decide
                      · by_cases hc : isDisallowedControl c0 = true
                        · have hdef : escapeBasicChar false c0 =
                              "\\u00" ++ String.ofList [hexDigitUpper (c0.toNat / 16), hexDigitUpper (c0.toNat % 16)] := by
                            simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                          rw [hdef]
                          have hu : ("\\u00" : String).toList = ['\\', 'u', '0', '0'] := rfl
                          simp [hu]
                        · have hdef : escapeBasicChar false c0 = String.singleton c0 := by
                            simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                          rw [hdef]; simp [h2]
        cases h0 : (escapeBasicChar false c0).toList with
        | nil =>
          have hlen := escapeBasicChar_length_pos false c0
          rw [h0] at hlen; simp at hlen
        | cons d0 ds0 =>
          rw [h0] at hr' hne
          injection hr' with hd0
          exact hne (by simp [hd0])
    have hparse : parseKeySegment (("\"" ++ escapeBasicBody false k ++ "\"").toList ++ rest) = .ok (k, rest) := by
      have hstr : ("\"" : String).toList = ['"'] := rfl
      simp only [String.toList_append, hstr, List.cons_append, List.nil_append, List.append_assoc]
      rw [parseKeySegment_basic _ hno3]
      exact parseBasicStringBody_escapeBasicBody k rest
    refine ⟨hparse, ?_⟩
    simp only [String.toList_append]
    have hq_clean : (("\"" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by decide
    simp only [List.all_append, hq_clean, Bool.true_and, Bool.and_true]
    simpa [Bool.and_assoc] using hclean_esc
  | literal =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hcond
      injection hr with hrk
      subst hrk
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      rcases hcond with ⟨hclean, hnoq⟩
      have hnq := not_mem_of_contains_false k '\'' hnoq
      have hnl : '\n' ∉ k.toList := fun h => (isSingleLineClean_no_nl k hclean '\n' h).1 rfl
      have hno3 : ¬ ∃ r', (k.toList ++ '\'' :: rest) = '\'' :: '\'' :: r' := by
        intro ⟨r', hr'⟩
        cases hk : k.toList with
        | nil =>
          rw [hk, List.nil_append] at hr'
          cases rest with
          | nil => simp at hr'
          | cons c _ =>
            simp only [List.cons.injEq] at hr'
            exact (hrest c _ rfl).2.2 hr'.2.1
        | cons c0 _ =>
          rw [hk, List.cons_append] at hr'
          injection hr' with hc0
          exact hnq (by rw [hk, hc0]; simp)
      have hparse : parseKeySegment (("'" ++ k ++ "'").toList ++ rest) = .ok (k, rest) := by
        have hstr : ("'" : String).toList = ['\''] := rfl
        simp only [String.toList_append, hstr, List.cons_append, List.nil_append, List.append_assoc]
        rw [parseKeySegment_literal _ hno3, parseLiteralStringBody_list k.toList [] rest hnl hnq]
        simp [String.ofList_toList]
      refine ⟨hparse, ?_⟩
      simp only [String.toList_append, List.all_append]
      have hq_clean : (("'" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by decide
      simp only [hq_clean, Bool.true_and, Bool.and_true]
      simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hclean ⊢
      intro c hc
      have h1 := hclean c hc
      exact ⟨⟨h1.1.1, h1.2⟩, h1.1.2⟩
    · simp at hr

private theorem renderKey_head_clean (k : String) (ks : KeyStyle) (rk : String)
    (hr : renderKey k ks = some rk) :
    ∃ c cs, rk.toList = c :: cs ∧ isHorizWs c = false ∧ c ≠ '.' := by
  cases ks with
  | bare =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hbare
      injection hr with hrk
      subst hrk
      simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare
      rcases hbare with ⟨hne, hall⟩
      cases hk : k.toList with
      | nil =>
        have hk0 : k = "" := by rw [← String.ofList_toList (s := k), hk]
        subst hk0; simp at hne
      | cons c cs =>
        have hbc := List.all_eq_true.mp hall c (by rw [hk]; simp)
        have hws : isHorizWs c = false := by
          by_cases h1 : c = ' '
          · subst h1; simp [isBareKeyChar] at hbc
          · by_cases h2 : c = '\t'
            · subst h2; simp [isBareKeyChar] at hbc
            · simp [isHorizWs, h1, h2]
        have hndot : c ≠ '.' := by
          intro h; subst h; simp [isBareKeyChar] at hbc
        exact ⟨c, cs, rfl, hws, hndot⟩
    · simp at hr
  | basic =>
    simp only [renderKey] at hr
    injection hr with hrk
    subst hrk
    have hq : ("\"" : String).toList = ['"'] := rfl
    refine ⟨'"', (escapeBasicBody false k ++ "\"").toList, ?_, by decide, by decide⟩
    simp [String.toList_append, hq]
  | literal =>
    simp only [renderKey] at hr
    split at hr
    · injection hr with hrk
      subst hrk
      have hq : ("'" : String).toList = ['\''] := rfl
      refine ⟨'\'', (k ++ "'").toList, ?_, by decide, by decide⟩
      simp [String.toList_append, hq]
    · simp at hr

private theorem skipHorizWs_cons_false (c : Char) (cs : List Char) (hc : isHorizWs c = false) :
    skipHorizWs (c :: cs) = c :: cs := by
  simp [skipHorizWs, hc]

private theorem joinRenderedPath_head_clean (r : String) (rs : List String)
    (hhead : ∃ c cs, r.toList = c :: cs ∧ isHorizWs c = false) :
    ∃ c cs, (joinRenderedPath (r :: rs)).toList = c :: cs ∧ isHorizWs c = false := by
  rcases hhead with ⟨c, cs, hr, hc⟩
  cases rs with
  | nil => exact ⟨c, cs, by simp [joinRenderedPath, hr], hc⟩
  | cons r2 rs2 =>
    refine ⟨c, cs ++ '.' :: (joinRenderedPath (r2 :: rs2)).toList, ?_, hc⟩
    have hd : ("." : String).toList = ['.'] := rfl
    simp [joinRenderedPath, String.toList_append, hr, hd]

private theorem joinRenderedPath_clean (rks : List String)
    (hclean : ∀ r ∈ rks, (r.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) :
    ((joinRenderedPath rks).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  induction rks with
  | nil => simp [joinRenderedPath]
  | cons r rs ih =>
    cases rs with
    | nil => simpa [joinRenderedPath] using hclean r (by simp)
    | cons r2 rs2 =>
      have hr := hclean r (by simp)
      have hrs := ih (fun x hx => hclean x (by simp [hx]))
      have hd : ((".") : String).toList = ['.'] := rfl
      have hdc : (['.'].all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by decide
      simp only [joinRenderedPath, String.toList_append, hd, List.all_append, hr, hdc, hrs, Bool.and_true]

private theorem joinRenderedPath_parseDottedKeyFuel (ks : List (String × KeyStyle)) (rks : List String)
    (hne : ks ≠ []) (hr : ks.mapM (fun p => renderKey p.1 p.2) = some rks)
    (rest : List Char) (fuel : Nat) (hf : ks.length ≤ fuel)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hskip : ∀ c tail, skipHorizWs rest = c :: tail → c ≠ '.') :
    parseDottedKeyFuel fuel ((joinRenderedPath rks).toList ++ rest) =
      .ok (ks.map Prod.fst, skipHorizWs rest) := by
  induction ks generalizing rks fuel with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      simp only [List.mapM_cons, bind, Option.bind] at hr
      cases hrp : renderKey p.1 p.2 with
      | none => simp [hrp] at hr
      | some rk =>
        rw [hrp] at hr
        cases hrps : ps.mapM (fun p => renderKey p.1 p.2) with
        | none => simp [hrps] at hr
        | some rps =>
          rw [hrps] at hr
          injection hr with hrks
          subst hrks
          cases ps with
          | nil =>
            simp only [List.mapM_nil] at hrps
            injection hrps with hrps0
            subst hrps0
            simp only [joinRenderedPath, List.map_cons, List.map_nil]
            have hseg := (renderKey_parseKeySegment p.1 p.2 rk hrp rest hrest).1
            simp only [parseDottedKeyFuel, hseg, bind, Except.bind]
            cases hsw : skipHorizWs rest with
            | nil => simp
            | cons c tail =>
              have hndot : c ≠ '.' := hskip c tail hsw
              simp [hndot]
          | cons q qs =>
            cases rps with
            | nil =>
              simp only [List.mapM_cons, bind, Option.bind] at hrps
              cases hq : renderKey q.1 q.2 with
              | none => simp [hq] at hrps
              | some _ =>
                simp only [hq] at hrps
                cases hqs : qs.mapM (fun p => renderKey p.1 p.2) <;> simp [hqs] at hrps
            | cons rk2 rks2 =>
              have hd : ("." : String).toList = ['.'] := rfl
              have hjoin : (joinRenderedPath (rk :: rk2 :: rks2)).toList ++ rest =
                  rk.toList ++ ('.' :: ((joinRenderedPath (rk2 :: rks2)).toList ++ rest)) := by
                simp [joinRenderedPath, String.toList_append, hd, List.append_assoc]
              have hdot : ∀ c tail, '.' :: ((joinRenderedPath (rk2 :: rks2)).toList ++ rest) = c :: tail →
                  !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'' := by
                intro c tail h; injection h with hc; subst hc; decide
              have hseg := (renderKey_parseKeySegment p.1 p.2 rk hrp
                ('.' :: ((joinRenderedPath (rk2 :: rks2)).toList ++ rest)) hdot).1
              have hq_render : renderKey q.1 q.2 = some rk2 := by
                simp only [List.mapM_cons, bind, Option.bind] at hrps
                cases hq : renderKey q.1 q.2 with
                | none => simp [hq] at hrps
                | some rk2' =>
                  simp only [hq] at hrps
                  cases hqs : qs.mapM (fun p => renderKey p.1 p.2) with
                  | none => simp [hqs] at hrps
                  | some rks2' =>
                    rw [hqs] at hrps
                    injection hrps with heq
                    injection heq with heq2
                    rw [heq2]
              obtain ⟨c2, cs2, hrk2, hws2, _⟩ := renderKey_head_clean q.1 q.2 rk2 hq_render
              obtain ⟨c', cs', hjoin_head, hws'⟩ :=
                joinRenderedPath_head_clean rk2 rks2 ⟨c2, cs2, hrk2, hws2⟩
              have hskip_tail : skipHorizWs ((joinRenderedPath (rk2 :: rks2)).toList ++ rest) =
                  (joinRenderedPath (rk2 :: rks2)).toList ++ rest := by
                rw [hjoin_head, List.cons_append, skipHorizWs_cons_false _ _ hws']
              have hsub : (q :: qs).length ≤ f := by simp at hf; omega
              rw [hjoin]
              simp only [parseDottedKeyFuel, hseg, bind, Except.bind, skipHorizWs,
                show isHorizWs '.' = false from rfl, Bool.false_eq_true, ↓reduceIte, hskip_tail]
              rw [ih (rk2 :: rks2) (by simp) hrps f hsub]
              simp

private theorem joinRenderedPath_parseDottedKey (ks : List (String × KeyStyle)) (rks : List String)
    (hne : ks ≠ []) (hr : ks.mapM (fun p => renderKey p.1 p.2) = some rks)
    (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hskip : ∀ c tail, skipHorizWs rest = c :: tail → c ≠ '.') :
    parseDottedKey ((joinRenderedPath rks).toList ++ rest) =
      .ok (ks.map Prod.fst, skipHorizWs rest) ∧
    ((joinRenderedPath rks).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  have hlen_rks : ∀ (ls : List (String × KeyStyle)) (rs : List String),
      ls.mapM (fun p => renderKey p.1 p.2) = some rs → ls ≠ [] →
      ls.length ≤ (joinRenderedPath rs).toList.length := by
    intro ls
    induction ls with
    | nil => intro _ _ h; exact absurd rfl h
    | cons p ps ih =>
      intro rs hrs _
      simp only [List.mapM_cons, bind, Option.bind] at hrs
      cases hrp : renderKey p.1 p.2 with
      | none => simp [hrp] at hrs
      | some rk =>
        rw [hrp] at hrs
        cases hrps : ps.mapM (fun p => renderKey p.1 p.2) with
        | none => simp [hrps] at hrs
        | some rps =>
          rw [hrps] at hrs
          injection hrs with hrs_eq
          subst hrs_eq
          obtain ⟨c, cs, hrk, _⟩ := renderKey_head_clean p.1 p.2 rk hrp
          cases ps with
          | nil =>
            simp only [List.mapM_nil] at hrps
            injection hrps with hrps0; subst hrps0
            simp [joinRenderedPath, hrk]
          | cons q qs =>
            cases rps with
            | nil =>
              simp only [List.mapM_cons, bind, Option.bind] at hrps
              cases hq : renderKey q.1 q.2 with
              | none => simp [hq] at hrps
              | some _ =>
                simp only [hq] at hrps
                cases hqs : qs.mapM (fun p => renderKey p.1 p.2) <;> simp [hqs] at hrps
            | cons rk2 rks2 =>
              have hsub := ih (rk2 :: rks2) hrps (by simp)
              have hd : ("." : String).toList = ['.'] := rfl
              simp only [joinRenderedPath, String.toList_append, hd, List.length_append, List.length_cons,
                hrk] at hsub ⊢
              omega
  have hf : ks.length ≤ ((joinRenderedPath rks).toList ++ rest).length + 1 := by
    have h1 := hlen_rks ks rks hr hne
    simp only [List.length_append]; omega
  refine ⟨joinRenderedPath_parseDottedKeyFuel ks rks hne hr rest _ hf hrest hskip, ?_⟩
  apply joinRenderedPath_clean
  intro r hr_mem
  have hex : ∃ p ∈ ks, renderKey p.1 p.2 = some r := by
    clear hlen_rks hf hrest hskip hne
    induction ks generalizing rks with
    | nil => simp at hr; subst hr; simp at hr_mem
    | cons p ps ih =>
      simp only [List.mapM_cons, bind, Option.bind] at hr
      cases hrp : renderKey p.1 p.2 with
      | none => simp [hrp] at hr
      | some rk =>
        rw [hrp] at hr
        cases hrps : ps.mapM (fun p => renderKey p.1 p.2) with
        | none => simp [hrps] at hr
        | some rps =>
          rw [hrps] at hr
          injection hr with hrs_eq; subst hrs_eq
          simp only [List.mem_cons] at hr_mem
          rcases hr_mem with rfl | hmem
          · exact ⟨p, by simp, hrp⟩
          · obtain ⟨q, hq_mem, hq_r⟩ := ih rps hrps hmem
            exact ⟨q, by simp [hq_mem], hq_r⟩
  rcases hex with ⟨⟨k, style⟩, _, hkr⟩
  exact (renderKey_parseKeySegment k style r hkr [] (by intro _ _ h; cases h)).2

private theorem parseValueFuel_basic (numApi : NumParseApi) (fuel : Nat) (cs : List Char)
    (hno3 : ¬ ∃ r, cs = '"' :: '"' :: r) :
    parseValueFuel numApi (fuel + 1) ('"' :: cs) =
      (parseBasicStringBody cs >>= fun (s, after) => .ok (.string s, after)) := by
  conv => lhs; unfold parseValueFuel
  split
  · exfalso; apply hno3; simp_all
  · rename_i heq; injection heq with _; subst_vars; rfl
  all_goals simp_all

private theorem parseValueFuel_multilineBasic (numApi : NumParseApi) (fuel : Nat) (cs : List Char) :
    parseValueFuel numApi (fuel + 1) ('"' :: '"' :: '"' :: cs) =
      (parseMultilineBasicString cs >>= fun (s, after) => .ok (.string s, after)) := by
  conv => lhs; unfold parseValueFuel
  rfl

private theorem parseValueFuel_literal (numApi : NumParseApi) (fuel : Nat) (cs : List Char)
    (hno3 : ¬ ∃ r, cs = '\'' :: '\'' :: r) :
    parseValueFuel numApi (fuel + 1) ('\'' :: cs) =
      (parseLiteralStringBody [] cs >>= fun (s, after) => .ok (.string s, after)) := by
  conv => lhs; unfold parseValueFuel
  split
  · simp_all
  · simp_all
  · exfalso; apply hno3; simp_all
  · rename_i heq; injection heq with _; subst_vars; rfl
  all_goals simp_all

private theorem parseValueFuel_multilineLiteral (numApi : NumParseApi) (fuel : Nat) (cs : List Char) :
    parseValueFuel numApi (fuel + 1) ('\'' :: '\'' :: '\'' :: cs) =
      (parseMultilineLiteralString cs >>= fun (s, after) => .ok (.string s, after)) := by
  conv => lhs; unfold parseValueFuel
  rfl

/-- Internal TOML scalar round-trip lemma `renderStringLiteral_parseValueFuel`. -/
theorem renderStringLiteral_parseValueFuel (numApi : NumParseApi) (s : String) (st : StringStyle)
    (rs : String) (hr : renderStringLiteral s st = some rs) (rest : List Char) (fuel : Nat) (hf : fuel ≥ 1)
    (hrest : ∀ c r, rest = c :: r → c ≠ '"' ∧ c ≠ '\'') :
    parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (.string s, rest) ∧
    (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
    ((st = .basic ∨ st = .literal) →
      (rs.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) := by
  cases fuel with
  | zero => omega
  | succ f =>
    cases st with
    | basic =>
      simp only [renderStringLiteral] at hr
      injection hr with hrs; subst hrs
      have hno3 : ¬ ∃ r', ((escapeBasicBody false s).toList ++ '"' :: rest) = '"' :: '"' :: r' := by
        intro ⟨r', hr'⟩
        cases hs : s.toList with
        | nil =>
          have hbody : (escapeBasicBody false s).toList = [] := by simp [escapeBasicBody, hs]
          rw [hbody, List.nil_append] at hr'
          cases rest with
          | nil => simp at hr'
          | cons c t =>
            simp only [List.cons.injEq] at hr'
            exact (hrest c t rfl).1 hr'.2.1
        | cons c0 cs0 =>
          have hbody : (escapeBasicBody false s).toList =
              (escapeBasicChar false c0).toList ++ cs0.flatMap (fun c => (escapeBasicChar false c).toList) := by
            simp [escapeBasicBody, String.toList_join, hs, List.flatMap_map]
          rw [hbody, List.append_assoc] at hr'
          have hne : ((escapeBasicChar false c0).toList).head? ≠ some '"' := by
            by_cases h1 : c0 = '\\'
            · subst h1; decide
            · by_cases h2 : c0 = '"'
              · subst h2; decide
              · by_cases h3 : c0 = '\x08'
                · subst h3; decide
                · by_cases h4 : c0 = '\t'
                  · subst h4; decide
                  · by_cases h5 : c0 = '\n'
                    · subst h5; decide
                    · by_cases h6 : c0 = '\x0c'
                      · subst h6; decide
                      · by_cases h7 : c0 = '\r'
                        · subst h7; decide
                        · by_cases hc : isDisallowedControl c0 = true
                          · have hdef : escapeBasicChar false c0 =
                                "\\u00" ++ String.ofList [hexDigitUpper (c0.toNat / 16), hexDigitUpper (c0.toNat % 16)] := by
                              simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                            rw [hdef]
                            have hu : ("\\u00" : String).toList = ['\\', 'u', '0', '0'] := rfl
                            simp [hu]
                          · have hdef : escapeBasicChar false c0 = String.singleton c0 := by
                              simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                            rw [hdef]; simp [h2]
          cases h0 : (escapeBasicChar false c0).toList with
          | nil =>
            have hlen := escapeBasicChar_length_pos false c0
            rw [h0] at hlen; simp at hlen
          | cons d0 _ =>
            rw [h0] at hr' hne
            injection hr' with hd0
            exact hne (by simp [hd0])
      have hq : ("\"" : String).toList = ['"'] := rfl
      have hparse : parseValueFuel numApi (f + 1) (("\"" ++ escapeBasicBody false s ++ "\"").toList ++ rest) =
          .ok (.string s, rest) := by
        simp only [String.toList_append, hq, List.cons_append, List.nil_append, List.append_assoc]
        rw [parseValueFuel_basic numApi f _ hno3]
        simp [parseBasicStringBody_escapeBasicBody s rest, bind, Except.bind]
      have hcl := escapeBasicBody_clean false s
      have hq_cl : (("\"" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
        decide
      have hcl_inline : (("\"" ++ escapeBasicBody false s ++ "\"").toList.all fun c =>
          !isDisallowedControl c && c != '\r' && c != '\n') = true := by
        simp only [String.toList_append, List.all_append, hq_cl, Bool.true_and, Bool.and_true]
        simpa [Bool.and_assoc] using hcl
      refine ⟨hparse, ?_, fun _ => hcl_inline⟩
      rw [List.all_eq_true]
      intro c hc
      have h1 := List.all_eq_true.mp hcl_inline c hc
      simp only [Bool.and_eq_true] at h1
      exact (Bool.and_eq_true _ _).mpr h1.1
    | multilineBasic =>
      simp only [renderStringLiteral] at hr
      injection hr with hrs; subst hrs
      have ho : ("\"\"\"\n" : String).toList = ['"', '"', '"', '\n'] := rfl
      have hc : ("\"\"\"" : String).toList = ['"', '"', '"'] := rfl
      have hparse : parseValueFuel numApi (f + 1)
          (("\"\"\"\n" ++ escapeBasicBody true s ++ "\"\"\"").toList ++ rest) = .ok (.string s, rest) := by
        simp only [String.toList_append, ho, hc, List.cons_append, List.nil_append, List.append_assoc]
        rw [parseValueFuel_multilineBasic numApi f]
        have hrest_q : ∀ c r, rest = c :: r → c ≠ '"' := fun c r h => (hrest c r h).1
        have hm := parseMultilineBasicString_escapeBasicBody s rest hrest_q
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hm
        simp [hm, bind, Except.bind]
      have hcl := escapeBasicBody_clean true s
      have hoc : (("\"\"\"\n" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by decide
      have hcc : (("\"\"\"" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by decide
      refine ⟨hparse, ?_, fun h => by rcases h with h | h <;> cases h⟩
      simp only [String.toList_append, List.all_append, hoc, hcc, Bool.true_and, Bool.and_true]
      simpa using hcl
    | literal =>
      simp only [renderStringLiteral] at hr
      split at hr
      · rename_i hcond
        injection hr with hrs; subst hrs
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        rcases hcond with ⟨hclean, hnoq⟩
        have hnq := not_mem_of_contains_false s '\'' hnoq
        have hnl : '\n' ∉ s.toList := fun h => (isSingleLineClean_no_nl s hclean '\n' h).1 rfl
        have hno3 : ¬ ∃ r', (s.toList ++ '\'' :: rest) = '\'' :: '\'' :: r' := by
          intro ⟨r', hr'⟩
          cases hs : s.toList with
          | nil =>
            rw [hs, List.nil_append] at hr'
            cases rest with
            | nil => simp at hr'
            | cons c t =>
              simp only [List.cons.injEq] at hr'
              exact (hrest c t rfl).2 hr'.2.1
          | cons c0 _ =>
            rw [hs, List.cons_append] at hr'
            injection hr' with hc0
            exact hnq (by rw [hs, hc0]; simp)
        have hq : ("'" : String).toList = ['\''] := rfl
        have hparse : parseValueFuel numApi (f + 1) (("'" ++ s ++ "'").toList ++ rest) = .ok (.string s, rest) := by
          simp only [String.toList_append, hq, List.cons_append, List.nil_append, List.append_assoc]
          rw [parseValueFuel_literal numApi f _ hno3]
          simp [parseLiteralStringBody_list s.toList [] rest hnl hnq, String.ofList_toList, bind, Except.bind]
        have hq_cl : (("'" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
          decide
        have hcl_inline : (("'" ++ s ++ "'").toList.all fun c =>
            !isDisallowedControl c && c != '\r' && c != '\n') = true := by
          simp only [String.toList_append, List.all_append, hq_cl, Bool.true_and, Bool.and_true]
          simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hclean ⊢
          intro c hc
          have h1 := hclean c hc
          exact ⟨⟨h1.1.1, h1.2⟩, h1.1.2⟩
        refine ⟨hparse, ?_, fun _ => hcl_inline⟩
        rw [List.all_eq_true]
        intro c hc
        have h1 := List.all_eq_true.mp hcl_inline c hc
        simp only [Bool.and_eq_true] at h1
        exact (Bool.and_eq_true _ _).mpr h1.1
      · simp at hr
    | multilineLiteral =>
      simp only [renderStringLiteral] at hr
      split at hr
      · rename_i hcond
        injection hr with hrs; subst hrs
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        rcases hcond with ⟨⟨hclean, hno_sub⟩, hno_end⟩
        have hno3 := no_triple_quote_of_not_containsSubstr s hno_sub
        have hnoend := getLast_ne_quote_of_not_endsWith s hno_end
        have ho : ("'''\n" : String).toList = ['\'', '\'', '\'', '\n'] := rfl
        have hc : ("'''" : String).toList = ['\'', '\'', '\''] := rfl
        have hrest_q : ∀ c r, rest = c :: r → c ≠ '\'' := fun c r h => (hrest c r h).2
        have hparse : parseValueFuel numApi (f + 1) (("'''\n" ++ s ++ "'''").toList ++ rest) =
            .ok (.string s, rest) := by
          simp only [String.toList_append, ho, hc, List.cons_append, List.nil_append, List.append_assoc]
          rw [parseValueFuel_multilineLiteral numApi f]
          unfold parseMultilineLiteralString
          dsimp only
          have hlen : (s.toList ++ ['\'', '\'', '\''] ++ rest).length + 1 ≥ s.toList.length + 1 := by
            simp only [List.length_append]; omega
          have hm := parseMultilineLiteralBodyFuel_list s.toList [] rest _ hno3 hnoend hrest_q hlen
          simp only [List.reverse_nil, List.nil_append, String.ofList_toList, List.append_assoc,
            List.cons_append, List.nil_append, List.length_append, List.length_cons] at hm ⊢
          rw [hm]
          simp [bind, Except.bind]
        have hoc : (("'''\n" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by decide
        have hcc : (("'''" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by decide
        refine ⟨hparse, ?_, fun h => by rcases h with h | h <;> cases h⟩
        simp only [String.toList_append, List.all_append, hoc, hcc, Bool.true_and, Bool.and_true]
        simpa using hclean
      · simp at hr

private theorem twoDigitsNat?_isAscii (c1 c2 : Char) (n : Nat) (h : twoDigitsNat? c1 c2 = some n) :
    isAsciiDigit c1 = true ∧ isAsciiDigit c2 = true := by
  simp only [twoDigitsNat?] at h
  split at h
  · rename_i hc; exact (Bool.and_eq_true _ _).mp hc
  · simp at h

private theorem fourDigitsNat?_isAscii (c1 c2 c3 c4 : Char) (n : Nat)
    (h : fourDigitsNat? c1 c2 c3 c4 = some n) :
    isAsciiDigit c1 = true ∧ isAsciiDigit c2 = true ∧ isAsciiDigit c3 = true ∧ isAsciiDigit c4 = true := by
  simp only [fourDigitsNat?] at h
  split at h
  · rename_i hc; simp only [Bool.and_eq_true] at hc; exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
  · simp at h

private theorem padNatZero_clean_val (w n : Nat) :
    ((padNatZero w n).toList.all fun c =>
      !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  rw [List.all_eq_true]
  intro c hc
  have h1 := List.all_eq_true.mp (padNatZero_clean w n) c hc
  simp only [Bool.and_eq_true] at h1 ⊢
  exact ⟨⟨⟨h1.1.1.1.2, h1.1.1.2⟩, h1.1.2⟩, h1.2⟩

private theorem dite_true {α : Type} {P : Prop} [Decidable P] {f : P → α} {g : ¬ P → α} (h : P) :
    dite P f g = f h := by
  split
  · rfl
  · rename_i hneg; exact absurd h hneg

private theorem renderDate_parseDatePart (d : Std.Time.PlainDate) (ds : String) (rest : List Char)
    (hr : renderDate d = some ds) :
    parseDatePart (ds.toList ++ rest) = .ok (d, rest) ∧
    hasDatePrefix (ds.toList ++ rest) = true ∧
    (ds.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  simp only [renderDate] at hr
  split at hr
  · rename_i hvd
    injection hr with hds
    subst hds
    have hv : (0 : Int) ≤ d.year ∧ d.year ≤ 9999 := by simpa [validTomlDate] using hvd
    have hv_int : (0 : Int) ≤ (d.year : Int) ∧ (d.year : Int) ≤ 9999 := hv
    have h_eq : Int.ofNat (d.year : Int).toNat = (d.year : Int) := Int.toNat_of_nonneg hv_int.1
    have hy_nat : d.year.toNat < 10000 := by
      have hle : Int.ofNat (d.year : Int).toNat ≤ 9999 := by rw [h_eq]; exact hv_int.2
      exact Int.ofNat_lt.mp (by omega)
    have hm_prop := d.month.property
    have hm_nat : d.month.val.toNat < 100 := by omega
    have hd_prop := d.day.property
    have hd_nat : d.day.val.toNat < 100 := by omega
    obtain ⟨y1, y2, y3, y4, hy_list, hy_four⟩ :=
      padNatZero_4_digits d.year.toNat hy_nat
    obtain ⟨m1, m2, hm_list, hm_two, _, _⟩ :=
      twoDigits_padNatZero d.month.val.toNat hm_nat
    obtain ⟨d1, d2, hd_list, hd_two, _, _⟩ :=
      twoDigits_padNatZero d.day.val.toNat hd_nat
    have hdash : ("-" : String).toList = ['-'] := rfl
    have hlist : (padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++
        padNatZero 2 d.day.val.toNat).toList = [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] := by
      simp only [String.toList_append, hy_list, hdash, hm_list, hd_list]
      rfl
    have hy_eq : Std.Time.Year.Offset.ofInt (Int.ofNat d.year.toNat) = d.year :=
      Int.toNat_of_nonneg hv.1
    have hm_ok : d.month.val.toNat ≥ 1 ∧ d.month.val.toNat ≤ 12 := ⟨by omega, by omega⟩
    have hm_eq : Std.Time.Month.Ordinal.ofNat d.month.val.toNat hm_ok = d.month := by
      apply Subtype.ext
      exact Int.toNat_of_nonneg (by omega)
    have hd_ok : d.day.val.toNat ≥ 1 ∧ d.day.val.toNat ≤ 31 := ⟨by omega, by omega⟩
    have hd_eq : Std.Time.Day.Ordinal.ofNat d.day.val.toNat hd_ok = d.day := by
      apply Subtype.ext
      exact Int.toNat_of_nonneg (by omega)
    have hcal : Std.Time.PlainDate.ofYearMonthDay?
        (Std.Time.Year.Offset.ofInt (Int.ofNat d.year.toNat))
        (Std.Time.Month.Ordinal.ofNat d.month.val.toNat hm_ok)
        (Std.Time.Day.Ordinal.ofNat d.day.val.toNat hd_ok) = some d := by
      rw [hy_eq, hm_eq, hd_eq, Std.Time.PlainDate.ofYearMonthDay?]
      exact dite_true d.valid
    have hparse : parseDatePart ((padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++
        padNatZero 2 d.day.val.toNat).toList ++ rest) = .ok (d, rest) := by
      rw [hlist]
      simp only [List.cons_append, List.nil_append, parseDatePart, hy_four, hm_two, hd_two]
      rw [dite_true hm_ok, dite_true hd_ok, hcal]
      simp [hvd]
    have hpref : hasDatePrefix ((padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++
        padNatZero 2 d.day.val.toNat).toList ++ rest) = true := by
      rw [hlist]
      obtain ⟨ay1, ay2, ay3, ay4⟩ := fourDigitsNat?_isAscii y1 y2 y3 y4 d.year.toNat hy_four
      obtain ⟨am1, am2⟩ := twoDigitsNat?_isAscii m1 m2 d.month.val.toNat hm_two
      obtain ⟨ad1, ad2⟩ := twoDigitsNat?_isAscii d1 d2 d.day.val.toNat hd_two
      simp [hasDatePrefix, ay1, ay2, ay3, ay4, am1, am2, ad1, ad2]
    refine ⟨hparse, hpref, ?_⟩
    have hdash_cl : ("-".toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
      decide
    simp only [String.toList_append, List.all_append, padNatZero_clean_val, hdash_cl, Bool.and_self]
  · simp at hr

/-- Internal TOML scalar round-trip lemma `pow10Nat_pos`. -/
theorem pow10Nat_pos (k : Nat) : 0 < pow10Nat k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [pow10Nat]; omega

/-- Internal TOML scalar round-trip lemma `pow10Nat_add`. -/
theorem pow10Nat_add (a b : Nat) : pow10Nat (a + b) = pow10Nat a * pow10Nat b := by
  induction a with
  | zero => simp [pow10Nat]
  | succ a ih =>
    rw [Nat.succ_add, pow10Nat, ih, pow10Nat, Nat.mul_assoc]

/-- Internal TOML scalar round-trip lemma `pow10Nat_9`. -/
theorem pow10Nat_9 : pow10Nat 9 = 1000000000 := rfl

/-- Internal TOML scalar round-trip lemma `toString_length_le_pow10`. -/
theorem toString_length_le_pow10 (w n : Nat) (hw : 1 ≤ w) (hn : n < pow10Nat w) :
    (toString n).length ≤ w := by
  induction w generalizing n with
  | zero => omega
  | succ w ih =>
    by_cases h10 : n < 10
    · obtain ⟨hch, _⟩ := toString_lt10_char n h10
      have hlen : (toString n).length = (toString n).toList.length := by
        change (Nat.repr n).length = (Nat.repr n).toList.length; simp [Nat.repr]
      rw [hlen, hch]; simp
    · have hw1 : 1 ≤ w := by
        cases w with
        | zero => simp [pow10Nat] at hn; omega
        | succ _ => omega
      have hdiv_lt : n / 10 < pow10Nat w := by
        simp only [pow10Nat] at hn
        omega
      have hsub := ih (n / 10) hw1 hdiv_lt
      have hsplit := toString_two_digits_split (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      have heq : n / 10 * 10 + n % 10 = n := by omega
      rw [heq] at hsplit
      have hlen : ∀ m : Nat, (toString m).length = (toString m).toList.length := by
        intro m; change (Nat.repr m).length = (Nat.repr m).toList.length; simp [Nat.repr]
      rw [hlen n, hlen (n / 10)] at *
      rw [hsplit, List.length_append, List.length_singleton]
      omega

private theorem foldl_digits_add (ds : List Char) (init : Nat)
    (hds : ds.all isAsciiDigit = true) :
    ds.foldl (fun a c => a * 10 + digitVal c) init =
      init * pow10Nat ds.length + ds.foldl (fun a c => a * 10 + digitVal c) 0 := by
  induction ds generalizing init with
  | nil => simp [pow10Nat]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (init * 10 + digitVal c) hds.2, ih (digitVal c) hds.2, pow10Nat]
    calc
      (init * 10 + digitVal c) * pow10Nat cs.length + List.foldl (fun a c => a * 10 + digitVal c) 0 cs
        = init * (10 * pow10Nat cs.length) +
            (digitVal c * pow10Nat cs.length + List.foldl (fun a c => a * 10 + digitVal c) 0 cs) := by
          rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem toString_foldl_digits (n : Nat) :
    (toString n).toList.foldl (fun a c => a * 10 + digitVal c) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h10 : n < 10
    · obtain ⟨hch, _, hdv, _⟩ := toString_lt10_char n h10
      rw [hch]
      simp [hdv]
    · have hsplit := toString_two_digits_split (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      have heq : n / 10 * 10 + n % 10 = n := by omega
      rw [heq] at hsplit
      obtain ⟨_, _, hdv, _⟩ := toString_lt10_char (n % 10) (Nat.mod_lt n (by decide))
      rw [hsplit, List.foldl_append, List.foldl_cons, List.foldl_nil, hdv, ih (n / 10) (by omega)]
      omega

private theorem padNatZero_foldl_digits (w n : Nat) :
    (padNatZero w n).toList.foldl (fun a c => a * 10 + digitVal c) 0 = n := by
  unfold padNatZero
  dsimp only
  by_cases hge : (toString n).length ≥ w
  · simp only [hge, ↓reduceIte, toString_foldl_digits]
  · simp only [hge, ↓reduceIte, String.toList_append, String.toList_ofList, List.foldl_append]
    have hzeros : ∀ k, (List.replicate k '0').foldl (fun a c => a * 10 + digitVal c) 0 = 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [List.replicate_succ, List.foldl_cons]
        have hd0 : digitVal '0' = 0 := rfl
        rw [Nat.zero_mul, Nat.zero_add, hd0]
        exact ih
    rw [hzeros, toString_foldl_digits]

private theorem takeDigits_append (acc ds rest : List Char)
    (hds : ds.all isAsciiDigit = true)
    (hrest : ∀ c r, rest = c :: r → isAsciiDigit c = false) :
    takeDigits acc (ds ++ rest) = (acc.reverse ++ ds, rest) := by
  induction ds generalizing acc with
  | nil =>
    cases rest with
    | nil => simp [takeDigits]
    | cons c r => simp [takeDigits, hrest c r rfl]
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    simp only [List.cons_append, takeDigits, hds.1, ↓reduceIte]
    rw [ih (d :: acc) hds.2]
    simp

private theorem fracDigitsToNanosAux_append (k acc : Nat) (ds1 ds2 : List Char)
    (hlen : ds1.length ≤ k) (hds1 : ds1.all isAsciiDigit = true) :
    fracDigitsToNanosAux k acc (ds1 ++ ds2) =
      fracDigitsToNanosAux (k - ds1.length)
        (acc * pow10Nat ds1.length + ds1.foldl (fun a c => a * 10 + digitVal c) 0) ds2 := by
  induction ds1 generalizing k acc with
  | nil => simp [pow10Nat]
  | cons d ds ih =>
    cases k with
    | zero => simp at hlen
    | succ k' =>
      simp only [List.length_cons, List.all_cons, Bool.and_eq_true] at hlen hds1
      simp only [List.cons_append, fracDigitsToNanosAux]
      rw [ih k' (acc * 10 + digitVal d) (by omega) hds1.2]
      have hfold : (d :: ds).foldl (fun a c => a * 10 + digitVal c) 0 =
          digitVal d * pow10Nat ds.length + ds.foldl (fun a c => a * 10 + digitVal c) 0 := by
        simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add]
        exact foldl_digits_add ds (digitVal d) hds1.2
      rw [hfold]
      simp only [List.length_cons, pow10Nat]
      congr 1
      · omega
      · rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem fracDigitsToNanosAux_nil (k acc : Nat) :
    fracDigitsToNanosAux k acc [] = acc * pow10Nat k := by
  induction k generalizing acc with
  | zero => simp [fracDigitsToNanosAux, pow10Nat]
  | succ k ih =>
    simp only [fracDigitsToNanosAux, pow10Nat, ih (acc * 10)]
    rw [Nat.mul_assoc, Nat.mul_comm 10 (pow10Nat k)]

private theorem parseTimePart_digits_nofrac (h1 h2 m1 m2 s1 s2 : Char) (hh mm ss : Nat)
    (hh_two : twoDigitsNat? h1 h2 = some hh)
    (hm_two : twoDigitsNat? m1 m2 = some mm)
    (hs_two : twoDigitsNat? s1 s2 = some ss)
    (hh_ok : hh ≤ 23) (mm_ok : mm ≤ 59) (ss_ok : ss ≤ 59)
    (rest : List Char) (hndot : ∀ r, rest ≠ '.' :: r) :
    parseTimePart ([h1, h2, ':', m1, m2, ':', s1, s2] ++ rest) =
      .ok (Std.Time.PlainTime.mk
        (Std.Time.Hour.Ordinal.ofNat hh hh_ok)
        (Std.Time.Minute.Ordinal.ofNat mm mm_ok)
        (Std.Time.Second.Ordinal.ofNat ss (Nat.le_trans ss_ok (by decide)))
        0, rest) := by
  simp only [List.cons_append, List.nil_append, parseTimePart, hh_two, hm_two, hs_two,
    hh_ok, mm_ok, ss_ok, ↓reduceDIte]

private theorem parseTimePart_digits_frac (h1 h2 m1 m2 s1 s2 : Char) (hh mm ss : Nat)
    (hh_two : twoDigitsNat? h1 h2 = some hh)
    (hm_two : twoDigitsNat? m1 m2 = some mm)
    (hs_two : twoDigitsNat? s1 s2 = some ss)
    (hh_ok : hh ≤ 23) (mm_ok : mm ≤ 59) (ss_ok : ss ≤ 59)
    (fracDs rest : List Char)
    (htake : takeDigits [] (fracDs ++ rest) = (fracDs, rest))
    (hne : fracDs.isEmpty = false) :
    parseTimePart ([h1, h2, ':', m1, m2, ':', s1, s2] ++ '.' :: (fracDs ++ rest)) =
      .ok (Std.Time.PlainTime.mk
        (Std.Time.Hour.Ordinal.ofNat hh hh_ok)
        (Std.Time.Minute.Ordinal.ofNat mm mm_ok)
        (Std.Time.Second.Ordinal.ofNat ss (Nat.le_trans ss_ok (by decide)))
        (Std.Time.Nanosecond.Ordinal.ofNat (fracDigitsToNanos fracDs) (Nat.min_le_left _ _)),
        rest) := by
  simp only [List.cons_append, List.nil_append, parseTimePart, hh_two, hm_two, hs_two,
    hh_ok, mm_ok, ss_ok, ↓reduceDIte, htake, hne, Bool.false_eq_true, ↓reduceIte]

private theorem renderTime_parseTimePart (t : Std.Time.PlainTime) (fd : Nat) (ts : String)
    (rest : List Char)
    (hr : renderTime t fd = some ts)
    (hrest : ∀ c r, rest = c :: r → isAsciiDigit c = false ∧ (fd = 0 → c ≠ '.')) :
    parseTimePart (ts.toList ++ rest) = .ok (t, rest) ∧
    hasTimePrefix (ts.toList ++ rest) = true ∧
    (ts.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  simp only [renderTime] at hr
  split at hr
  · simp at hr
  · rename_i hvt
    simp only [Bool.not_eq_true] at hvt
    have hvt_sec : t.second.val ≤ 59 := by simpa [validTomlTime] using hvt
    cases hfrac : formatNanosExact t.nanosecond.val.toNat fd with
    | none => simp [hfrac] at hr
    | some frac =>
      rw [hfrac] at hr
      injection hr with hts
      subst hts
      have hh_prop := t.hour.property
      have hm_prop := t.minute.property
      have hs_prop := t.second.property
      have hn_prop := t.nanosecond.property
      have hh_nat : t.hour.val.toNat < 100 := by omega
      have hm_nat : t.minute.val.toNat < 100 := by omega
      have hs_nat : t.second.val.toNat < 100 := by omega
      obtain ⟨h1, h2, hh_list, hh_two, _, _⟩ := twoDigits_padNatZero t.hour.val.toNat hh_nat
      obtain ⟨m1, m2, hm_list, hm_two, _, _⟩ := twoDigits_padNatZero t.minute.val.toNat hm_nat
      obtain ⟨s1, s2, hs_list, hs_two, _, _⟩ := twoDigits_padNatZero t.second.val.toNat hs_nat
      have hh_ok : t.hour.val.toNat ≤ 23 := by omega
      have mm_ok : t.minute.val.toNat ≤ 59 := by omega
      have ss_ok : t.second.val.toNat ≤ 59 := by omega
      have hh_eq : Std.Time.Hour.Ordinal.ofNat t.hour.val.toNat hh_ok = t.hour := by
        apply Subtype.ext; exact Int.toNat_of_nonneg (by omega)
      have mm_eq : Std.Time.Minute.Ordinal.ofNat t.minute.val.toNat mm_ok = t.minute := by
        apply Subtype.ext; exact Int.toNat_of_nonneg (by omega)
      have ss_eq : Std.Time.Second.Ordinal.ofNat t.second.val.toNat (Nat.le_trans ss_ok (by decide)) =
          t.second := by
        apply Subtype.ext; exact Int.toNat_of_nonneg (by omega)
      have hcol : (":" : String).toList = [':'] := rfl
      have hbase : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
          padNatZero 2 t.second.val.toNat).toList = [h1, h2, ':', m1, m2, ':', s1, s2] := by
        simp only [String.toList_append, hh_list, hcol, hm_list, hs_list]; rfl
      have hcol_cl : (":".toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
        decide
      have hpref : hasTimePrefix ((padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
          padNatZero 2 t.second.val.toNat ++ frac).toList ++ rest) = true := by
        rw [String.toList_append, List.append_assoc, hbase]
        obtain ⟨ah1, ah2⟩ := twoDigitsNat?_isAscii h1 h2 t.hour.val.toNat hh_two
        obtain ⟨am1, am2⟩ := twoDigitsNat?_isAscii m1 m2 t.minute.val.toNat hm_two
        obtain ⟨as1, as2⟩ := twoDigitsNat?_isAscii s1 s2 t.second.val.toNat hs_two
        simp [hasTimePrefix, ah1, ah2, am1, am2, as1, as2]
      simp only [formatNanosExact] at hfrac
      by_cases hgt9 : fd > 9
      · simp [hgt9] at hfrac
      · simp only [hgt9, ↓reduceIte] at hfrac
        by_cases hfd0 : fd = 0
        · subst hfd0
          simp only [beq_self_eq_true, ↓reduceIte] at hfrac
          by_cases hn0 : t.nanosecond.val.toNat = 0
          · simp only [hn0, beq_self_eq_true, ↓reduceIte] at hfrac
            injection hfrac with hfr; subst hfr
            have hn_eq : (0 : Std.Time.Nanosecond.Ordinal) = t.nanosecond := by
              apply Subtype.ext
              change (0 : Int) = t.nanosecond.val
              omega
            have htm : Std.Time.PlainTime.mk
                (Std.Time.Hour.Ordinal.ofNat t.hour.val.toNat hh_ok)
                (Std.Time.Minute.Ordinal.ofNat t.minute.val.toNat mm_ok)
                (Std.Time.Second.Ordinal.ofNat t.second.val.toNat (Nat.le_trans ss_ok (by decide)))
                0 = t := by
              apply Std.Time.PlainTime.ext
              · exact hh_eq
              · exact mm_eq
              · exact ss_eq
              · exact hn_eq
            have hparse : parseTimePart ((padNatZero 2 t.hour.val.toNat ++ ":" ++
                padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat ++ "").toList ++ rest) =
                .ok (t, rest) := by
              rw [String.append_empty, hbase]
              have hndot : ∀ r, rest ≠ '.' :: r := by
                intro r hr'
                exact (hrest '.' r hr').2 rfl rfl
              rw [parseTimePart_digits_nofrac h1 h2 m1 m2 s1 s2 _ _ _ hh_two hm_two hs_two hh_ok mm_ok ss_ok rest hndot, htm]
            refine ⟨hparse, hpref, ?_⟩
            simp only [String.append_empty, String.toList_append, List.all_append, padNatZero_clean_val,
              hcol_cl, Bool.and_self]
          · simp [hn0] at hfrac
        · have hfd_ne : (fd == 0) = false := beq_false_of_ne hfd0
          simp only [hfd_ne, Bool.false_eq_true, ↓reduceIte] at hfrac
          by_cases hmod : t.nanosecond.val.toNat % pow10Nat (9 - fd) = 0
          · simp only [hmod, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hfrac
            injection hfrac with hfr; subst hfr
            have hn_lt9 : t.nanosecond.val.toNat < pow10Nat 9 := by
              rw [pow10Nat_9]; omega
            have hfd_pos : 1 ≤ fd := by omega
            have hfd_le9 : fd ≤ 9 := by omega
            have hdiv_lt : t.nanosecond.val.toNat / pow10Nat (9 - fd) < pow10Nat fd := by
              have h9 : fd + (9 - fd) = 9 := by omega
              have hsplit_p : pow10Nat fd * pow10Nat (9 - fd) = pow10Nat 9 := by
                rw [← pow10Nat_add, h9]
              exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, hsplit_p]; exact hn_lt9)
            have hlen_str := toString_length_le_pow10 fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))
              hfd_pos hdiv_lt
            have hlen_pad := padNatZero_length_of_toString_le fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))
              hlen_str
            have hpad_digits : ((padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList).all
                isAsciiDigit = true := by
              rw [List.all_eq_true]
              intro c hc
              have h1 := List.all_eq_true.mp (padNatZero_clean fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))) c hc
              simp only [Bool.and_eq_true] at h1
              exact h1.1.1.1.1
            have htake := takeDigits_append []
              (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList rest
              hpad_digits (fun c r h => (hrest c r h).1)
            simp only [List.reverse_nil, List.nil_append] at htake
            have hne_empty : ((padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList).isEmpty = false := by
              cases hpl : (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList with
              | nil => rw [hpl] at hlen_pad; simp at hlen_pad; omega
              | cons _ _ => rfl
            have hnano_eq : fracDigitsToNanos
                (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList = t.nanosecond.val.toNat := by
              simp only [fracDigitsToNanos]
              rw [← List.append_nil (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList]
              rw [fracDigitsToNanosAux_append 9 0 _ [] (by rw [hlen_pad]; omega) hpad_digits]
              rw [Nat.zero_mul, Nat.zero_add, padNatZero_foldl_digits, fracDigitsToNanosAux_nil, hlen_pad]
              have hmul : (t.nanosecond.val.toNat / pow10Nat (9 - fd)) * pow10Nat (9 - fd) =
                  t.nanosecond.val.toNat := by
                have hd := Nat.div_add_mod t.nanosecond.val.toNat (pow10Nat (9 - fd))
                rw [hmod, Nat.add_zero, Nat.mul_comm] at hd
                exact hd
              rw [hmul]
              exact Nat.min_eq_right (by omega)
            have hn_eq : Std.Time.Nanosecond.Ordinal.ofNat
                (fracDigitsToNanos (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList)
                (Nat.min_le_left _ _) = t.nanosecond := by
              apply Subtype.ext
              change (Int.ofNat (fracDigitsToNanos (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList)) =
                t.nanosecond.val
              rw [hnano_eq]
              exact Int.toNat_of_nonneg (by omega)
            have htm : Std.Time.PlainTime.mk
                (Std.Time.Hour.Ordinal.ofNat t.hour.val.toNat hh_ok)
                (Std.Time.Minute.Ordinal.ofNat t.minute.val.toNat mm_ok)
                (Std.Time.Second.Ordinal.ofNat t.second.val.toNat (Nat.le_trans ss_ok (by decide)))
                (Std.Time.Nanosecond.Ordinal.ofNat
                  (fracDigitsToNanos (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList)
                  (Nat.min_le_left _ _)) = t := by
              apply Std.Time.PlainTime.ext
              · exact hh_eq
              · exact mm_eq
              · exact ss_eq
              · exact hn_eq
            have hdot : ("." : String).toList = ['.'] := rfl
            have hparse : parseTimePart ((padNatZero 2 t.hour.val.toNat ++ ":" ++
                padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat ++
                ("." ++ padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd)))).toList ++ rest) =
                .ok (t, rest) := by
              rw [String.toList_append, List.append_assoc, hbase, String.toList_append, hdot]
              have hfrac_call := parseTimePart_digits_frac h1 h2 m1 m2 s1 s2 _ _ _ hh_two hm_two hs_two
                hh_ok mm_ok ss_ok
                (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList rest htake hne_empty
              simp only [List.cons_append, List.nil_append] at hfrac_call ⊢
              rw [hfrac_call, htm]
            refine ⟨hparse, hpref, ?_⟩
            have hdot_cl : (".".toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
              decide
            simp only [String.toList_append, List.all_append, padNatZero_clean_val, hcol_cl, hdot_cl, Bool.and_self]
          · simp [hmod] at hfrac

/-- Internal TOML scalar round-trip lemma `renderOffset_parseOffsetPart`. -/
theorem renderOffset_parseOffsetPart (o : Std.Time.TimeZone.Offset) (style : OffsetStyle) (os : String)
    (hr : renderOffset o style = some os) :
    parseOffsetPart os.toList = .ok o ∧
    (os.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  simp only [renderOffset] at hr
  split at hr
  · simp at hr
  · rename_i hvo
    simp only [Bool.not_eq_true] at hvo
    have hvo' : o.second.val % 60 = 0 ∧ -86340 ≤ o.second.val ∧ o.second.val ≤ 86340 := by
      simpa [validTomlOffset] using hvo
    by_cases hz : o.second.val = 0
    · have ho_eq : Std.Time.TimeZone.Offset.ofSeconds 0 = o := by
        apply Std.Time.TimeZone.Offset.ext
        apply Std.Time.Internal.UnitVal.ext
        exact hz.symm
      simp only [hz, beq_self_eq_true, ↓reduceIte] at hr
      cases style with
      | upperZ =>
        injection hr with hos; subst hos
        refine ⟨?_, by decide⟩
        have hlist : ("Z" : String).toList = ['Z'] := rfl
        rw [hlist, parseOffsetPart, ho_eq]
      | lowerZ =>
        injection hr with hos; subst hos
        refine ⟨?_, by decide⟩
        have hlist : ("z" : String).toList = ['z'] := rfl
        rw [hlist, parseOffsetPart, ho_eq]
      | numeric =>
        injection hr with hos; subst hos
        refine ⟨?_, by decide⟩
        have hlist : ("+00:00" : String).toList = ['+', '0', '0', ':', '0', '0'] := rfl
        have h00 : twoDigitsNat? '0' '0' = some 0 := rfl
        have hstep : parseOffsetPart ['+', '0', '0', ':', '0', '0'] =
            .ok (Std.Time.TimeZone.Offset.ofSeconds 0) := by
          simp [parseOffsetPart, h00, validTomlOffset]
          rfl
        rw [hlist, hstep, ho_eq]
    · have hne : (o.second.val == 0) = false := beq_false_of_ne hz
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hr
      injection hr with hos; subst hos
      have habs_lt : o.second.val.natAbs / 60 ≤ 1439 := by omega
      have hdiv_lt : o.second.val.natAbs / 60 / 60 ≤ 23 := by omega
      have hmod_lt : (o.second.val.natAbs / 60) % 60 ≤ 59 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
      obtain ⟨h1, h2, hh_list, hh_two, _, _⟩ :=
        twoDigits_padNatZero (o.second.val.natAbs / 60 / 60) (by omega)
      obtain ⟨m1, m2, hm_list, hm_two, _, _⟩ :=
        twoDigits_padNatZero ((o.second.val.natAbs / 60) % 60) (by omega)
      have hdiv60 : (o.second.val.natAbs / 60) * 60 = o.second.val.natAbs := by
        have hm0 : o.second.val.natAbs % 60 = 0 := by omega
        have hd := Nat.div_add_mod o.second.val.natAbs 60
        rw [hm0, Nat.add_zero, Nat.mul_comm] at hd
        exact hd
      have htotal_nat : (o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60 =
          o.second.val.natAbs := by
        have hsub : (o.second.val.natAbs / 60 / 60) * 60 + (o.second.val.natAbs / 60) % 60 =
            o.second.val.natAbs / 60 := by
          omega
        calc
          (o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60
            = ((o.second.val.natAbs / 60 / 60) * 60 + (o.second.val.natAbs / 60) % 60) * 60 := by
              rw [Nat.add_mul, Nat.mul_assoc]
          _ = (o.second.val.natAbs / 60) * 60 := by rw [hsub]
          _ = o.second.val.natAbs := hdiv60
      have htotal_pos : 0 < o.second.val.natAbs := Int.natAbs_pos.mpr hz
      have hsec_eq : (if Int.ofNat ((o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60) == 0 then (0 : Int)
          else if (if o.second.val < 0 then '-' else '+') == '-' then
            -Int.ofNat ((o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60)
          else Int.ofNat ((o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60)) =
          o.second.val := by
        rw [htotal_nat]
        have hnz : (Int.ofNat o.second.val.natAbs == 0) = false :=
          beq_false_of_ne (by change (o.second.val.natAbs : Int) ≠ 0; omega)
        simp only [hnz, Bool.false_eq_true, ↓reduceIte]
        by_cases hneg : o.second.val < 0
        · simp only [hneg, ↓reduceIte, beq_self_eq_true]
          change -(o.second.val.natAbs : Int) = o.second.val
          omega
        · simp only [hneg, ↓reduceIte]
          have hne_sign : ('+' == '-') = false := rfl
          simp only [hne_sign, Bool.false_eq_true, ↓reduceIte]
          change (o.second.val.natAbs : Int) = o.second.val
          omega
      have ho_eq : Std.Time.TimeZone.Offset.ofSeconds (Std.Time.Second.Offset.ofInt o.second.val) = o := by
        apply Std.Time.TimeZone.Offset.ext
        apply Std.Time.Internal.UnitVal.ext
        rfl
      have hcol : (":" : String).toList = [':'] := rfl
      have hsign_char : (if o.second.val < 0 then "-" else "+").toList = [if o.second.val < 0 then '-' else '+'] := by
        split <;> rfl
      have hlist : ((if o.second.val < 0 then "-" else "+") ++
          padNatZero 2 (o.second.val.natAbs / 60 / 60) ++ ":" ++
          padNatZero 2 ((o.second.val.natAbs / 60) % 60)).toList =
          [if o.second.val < 0 then '-' else '+', h1, h2, ':', m1, m2] := by
        simp only [String.toList_append, hsign_char, hh_list, hcol, hm_list]
        rfl
      have hparse : parseOffsetPart (((if o.second.val < 0 then "-" else "+") ++
          padNatZero 2 (o.second.val.natAbs / 60 / 60) ++ ":" ++
          padNatZero 2 ((o.second.val.natAbs / 60) % 60)).toList) = .ok o := by
        rw [hlist]
        simp only [parseOffsetPart, hh_two, hm_two]
        have hsign_ok : ((if o.second.val < 0 then '-' else '+') == '+' ||
            (if o.second.val < 0 then '-' else '+') == '-') = true := by
          split <;> decide
        have hbound_ok : (decide (o.second.val.natAbs / 60 / 60 ≤ 23) &&
            decide ((o.second.val.natAbs / 60) % 60 ≤ 59)) = true := by
          simp [hdiv_lt, hmod_lt]
        have hvo_t : validTomlOffset o = true := by simpa using hvo
        simp only [hsign_ok, ↓reduceIte, hbound_ok]
        rw [hsec_eq, ho_eq, hvo_t]
        simp only [↓reduceIte]
      refine ⟨hparse, ?_⟩
      have hsign_cl : ((if o.second.val < 0 then "-" else "+").toList.all fun c =>
          !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
        split <;> decide
      have hcol_cl : (":".toList.all fun c =>
          !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
        decide
      simp only [String.toList_append, List.all_append, hsign_cl, padNatZero_clean_val, hcol_cl, Bool.and_self]

private theorem isUnquotedDelim_asciiDigit (c : Char) (h : isAsciiDigit c = true) :
    isUnquotedDelim c = false := by
  have h1 : '0' ≤ c ∧ c ≤ '9' := by
    simpa [isAsciiDigit] using h
  have hne : c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '#' ∧ c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;>
      exact absurd h1 (by decide)
  simp [isUnquotedDelim, isHorizWs, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1,
    hne.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2]

private theorem not_unquotedDelim_of_not_ws (c : Char)
    (hws : c.isWhitespace = false) (hn : c != '#') (hc : c != ',')
    (hb : c != ']') (hrb : c != '}') : isUnquotedDelim c = false := by
  have hsp : c ≠ ' ' := by
    intro h; subst h; exact absurd (by decide : (' ').isWhitespace = true) (by simp [hws])
  have htb : c ≠ '\t' := by
    intro h; subst h; exact absurd (by decide : ('\t').isWhitespace = true) (by simp [hws])
  have hnl : c ≠ '\n' := by
    intro h; subst h; exact absurd (by decide : ('\n').isWhitespace = true) (by simp [hws])
  simp only [bne_iff_ne, ne_eq] at hn hc hb hrb
  simp [isUnquotedDelim, isHorizWs, hsp, htb, hnl, hn, hc, hb, hrb]

private theorem takeNonDelim_append (acc tok rest : List Char)
    (htok : tok.all (fun c => !isUnquotedDelim c) = true)
    (hrest : ∀ c r, rest = c :: r → isUnquotedDelim c = true) :
    takeNonDelim acc (tok ++ rest) = (acc.reverse ++ tok, rest) := by
  induction tok generalizing acc with
  | nil =>
    cases rest with
    | nil => simp [takeNonDelim]
    | cons c r => simp [takeNonDelim, hrest c r rfl]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at htok
    simp only [List.cons_append, takeNonDelim, htok.1, Bool.false_eq_true, ↓reduceIte]
    rw [ih (c :: acc) htok.2]
    simp

private theorem list_append_split_cases {α : Type} (l1 l2 a b : List α) (x : α)
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

/-- Internal TOML scalar round-trip lemma `takeUnquotedToken_noSpace`. -/
theorem takeUnquotedToken_noSpace (tok rest : List Char)
    (htok : tok.all (fun c => !isUnquotedDelim c) = true)
    (hrest : ∀ c r, rest = c :: r →
      isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) :
    takeUnquotedToken (tok ++ rest) = (String.ofList tok, rest) := by
  unfold takeUnquotedToken
  split
  · rename_i y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 rest' heq
    by_cases hcond : (isAsciiDigit y1 && isAsciiDigit y2 && isAsciiDigit y3 && isAsciiDigit y4 &&
        isAsciiDigit m1 && isAsciiDigit m2 && isAsciiDigit d1 && isAsciiDigit d2 &&
        isAsciiDigit h1 && isAsciiDigit h2 && isAsciiDigit min1 && isAsciiDigit min2 &&
        isAsciiDigit s1 && isAsciiDigit s2) = true
    · exfalso
      simp only [Bool.and_eq_true] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩, hm1⟩, hm2⟩, hd1⟩, hd2⟩, hh1⟩, _⟩, _⟩, _⟩, _⟩, _⟩
      have hheq' : tok ++ rest =
          [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] ++
            ' ' :: [h1, h2, ':', min1, min2, ':', s1, s2] ++ rest' := heq
      rw [List.append_assoc] at hheq'
      have hsp := list_append_split_cases tok rest [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2]
        ([h1, h2, ':', min1, min2, ':', s1, s2] ++ rest') ' ' hheq'
      rcases hsp with ⟨c, hc, r, hr⟩ | ⟨_, hrest_eq⟩ | hmem_sp
      · have hdelim_t : isUnquotedDelim c = true := (hrest c r hr).1
        have hnot_delim : isUnquotedDelim c = false := by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hy1
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hy2
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hy3
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hy4
          rcases List.mem_cons.mp hc with rfl | hc
          · rfl
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hm1
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hm2
          rcases List.mem_cons.mp hc with rfl | hc
          · rfl
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hd1
          rcases List.mem_singleton.mp hc with rfl
          exact isUnquotedDelim_asciiDigit _ hd2
        rw [hdelim_t] at hnot_delim
        contradiction
      · have hnd := (hrest ' ' _ hrest_eq).2 rfl h1 _ rfl
        rw [hh1] at hnd
        contradiction
      · have h1 := List.all_eq_true.mp htok ' ' hmem_sp
        have hsp_delim : isUnquotedDelim ' ' = true := rfl
        simp [hsp_delim] at h1
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      rw [takeNonDelim_append [] tok rest htok (fun c r h => (hrest c r h).1)]
      simp
  · rw [takeNonDelim_append [] tok rest htok (fun c r h => (hrest c r h).1)]
    simp

private theorem takeUnquotedToken_spaceDateTime
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
  rw [takeNonDelim_append [] tail rest htail hrest]
  simp

private theorem padNatZero_all_digit (w n : Nat) :
    (padNatZero w n).toList.all isAsciiDigit = true := by
  rw [List.all_eq_true]
  intro c hc
  have h := List.all_eq_true.mp (padNatZero_clean w n) c hc
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1

private theorem renderDate_head_digit (d : Std.Time.PlainDate) (ds : String) (hr : renderDate d = some ds) :
    ∀ c r, ds.toList = c :: r → isAsciiDigit c = true := by
  simp only [renderDate] at hr
  split at hr
  · injection hr with hds; subst hds
    have h4 : (padNatZero 4 d.year.toNat).toList.all isAsciiDigit = true := padNatZero_all_digit 4 d.year.toNat
    cases hpl : (padNatZero 4 d.year.toNat).toList with
    | nil =>
      have hlen : (padNatZero 4 d.year.toNat).toList.length ≥ 4 := by
        have hlen_eq : (toString (Int.toNat d.year)).toList.length =
            (toString (Int.toNat d.year)).length := by
          change (Nat.repr (Int.toNat d.year)).toList.length =
            (Nat.repr (Int.toNat d.year)).length
          simp [Nat.repr]
        simp only [padNatZero]
        split
        · rename_i hge
          change 4 ≤ (toString (Int.toNat d.year)).toList.length
          rw [hlen_eq]; exact hge
        · simp only [String.toList_append, String.toList_ofList,
            List.length_append, List.length_replicate]
          change 4 ≤ (4 - (toString (Int.toNat d.year)).length) +
            (toString (Int.toNat d.year)).toList.length
          rw [hlen_eq]; omega
      rw [hpl] at hlen; simp at hlen
    | cons y1 ys =>
      simp only [hpl, List.all_cons, Bool.and_eq_true] at h4
      intro c r hcr
      simp only [String.toList_append, hpl, List.cons_append] at hcr
      injection hcr with hc _; subst hc
      exact h4.1
  · simp at hr

private theorem renderTime_head_digit (t : Std.Time.PlainTime) (fd : Nat) (ts : String)
    (hr : renderTime t fd = some ts) :
    ∀ c r, ts.toList = c :: r → isAsciiDigit c = true := by
  simp only [renderTime] at hr
  split at hr
  · simp at hr
  · cases hfr : formatNanosExact t.nanosecond.val.toNat fd with
    | none => simp [hfr] at hr
    | some frac =>
      rw [hfr] at hr
      injection hr with hts; subst hts
      have hh_prop := t.hour.property
      have hh_nat : t.hour.val.toNat < 100 := by omega
      obtain ⟨h1, h2, hh_list, hh_two, _, _⟩ := twoDigits_padNatZero t.hour.val.toNat hh_nat
      obtain ⟨ah1, _⟩ := twoDigitsNat?_isAscii h1 h2 t.hour.val.toNat hh_two
      intro c r hcr
      simp only [String.toList_append, hh_list, List.cons_append] at hcr
      injection hcr with hc _; subst hc
      exact ah1

/-- Internal TOML scalar round-trip lemma `renderDate_localDate`. -/
theorem renderDate_localDate (d : Std.Time.PlainDate) (ds : String)
    (hr : renderDate d = some ds) :
    parseDateTimeToken ds = some (.ok (.localDate d)) ∧
    (ds.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
    (∀ c r, ds.toList = c :: r → isAsciiDigit c = true) := by
  obtain ⟨hp, hpref, hcl⟩ := renderDate_parseDatePart d ds [] hr
  simp only [List.append_nil] at hp hpref
  refine ⟨?_, hcl, renderDate_head_digit d ds hr⟩
  simp [parseDateTimeToken, hpref, hp]

/-- Internal TOML scalar round-trip lemma `renderTime_localTime`. -/
theorem renderTime_localTime (t : Std.Time.PlainTime) (fd : Nat) (ts : String)
    (hr : renderTime t fd = some ts) :
    parseDateTimeToken ts = some (.ok (.localTime t)) ∧
    (ts.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
    (∀ c r, ts.toList = c :: r → isAsciiDigit c = true) := by
  obtain ⟨hp, hpref, hcl⟩ := renderTime_parseTimePart t fd ts [] hr (fun _ _ h => by cases h)
  simp only [List.append_nil] at hp hpref
  have hno_date : hasDatePrefix ts.toList = false := by
    simp only [renderTime] at hr
    split at hr
    · simp at hr
    · cases hfr : formatNanosExact t.nanosecond.val.toNat fd with
      | none => simp [hfr] at hr
      | some frac =>
        rw [hfr] at hr
        injection hr with hts; subst hts
        have hh_prop := t.hour.property
        have hh_nat : t.hour.val.toNat < 100 := by omega
        obtain ⟨h1, h2, hh_list, _, _, _⟩ := twoDigits_padNatZero t.hour.val.toNat hh_nat
        have hm_prop := t.minute.property
        have hm_nat : t.minute.val.toNat < 100 := by omega
        obtain ⟨m1, m2, hm_list, _, _, _⟩ := twoDigits_padNatZero t.minute.val.toNat hm_nat
        have hs_prop := t.second.property
        have hs_le : t.second.val ≤ 60 := by simpa using hs_prop.2
        have hs_nat : t.second.val.toNat < 100 := by omega
        obtain ⟨s1, s2, hs_list, _, _, _⟩ := twoDigits_padNatZero t.second.val.toNat hs_nat
        have hcol : (":" : String).toList = [':'] := rfl
        simp only [String.toList_append, hh_list, hm_list, hs_list, hcol, List.cons_append, List.nil_append]
        simp only [hasDatePrefix]
        split
        · rename_i heq
          have h3 : ':' = _ := (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).1
          rw [← h3]
          simp [show isAsciiDigit ':' = false from rfl]
        · rfl
  refine ⟨?_, hcl, renderTime_head_digit t fd ts hr⟩
  simp [parseDateTimeToken, hno_date, hpref, hp]

private theorem renderDateTime_localDateTime_char (dt : Std.Time.PlainDateTime)
    (sepStr : String) (sepChar : Char) (hsep_list : sepStr.toList = [sepChar])
    (hsep_ok : (sepChar == 'T' || sepChar == 't' || sepChar == ' ') = true)
    (fd : Nat) (ds ts : String)
    (hdr : renderDate dt.date = some ds) (htr : renderTime dt.time fd = some ts) :
    parseDateTimeToken (ds ++ sepStr ++ ts) = some (.ok (.localDateTime dt)) := by
  obtain ⟨hdp, hdpref, _⟩ := renderDate_parseDatePart dt.date ds (sepStr ++ ts).toList hdr
  obtain ⟨htp, _, _⟩ := renderTime_parseTimePart dt.time fd ts [] htr (fun _ _ h => by cases h)
  simp only [List.append_nil] at htp
  have hdpref' : hasDatePrefix (ds ++ sepStr ++ ts).toList = true := by
    simpa [String.toList_append, hsep_list] using hdpref
  have hdp' : parseDatePart (ds ++ sepStr ++ ts).toList = .ok (dt.date, sepChar :: ts.toList) := by
    simpa [String.toList_append, hsep_list] using hdp
  have htm_eq : Std.Time.PlainDateTime.mk dt.date dt.time = dt := by
    cases dt; rfl
  simp only [parseDateTimeToken, hdpref', ↓reduceIte, hdp', hsep_ok, htp, htm_eq]

/-- Internal TOML scalar round-trip lemma `renderDateTime_localDateTime`. -/
theorem renderDateTime_localDateTime (dt : Std.Time.PlainDateTime) (sep : DateTimeSep) (fd : Nat)
    (ds ts : String) (hdr : renderDate dt.date = some ds) (htr : renderTime dt.time fd = some ts) :
    parseDateTimeToken (ds ++ renderDateTimeSep sep ++ ts) = some (.ok (.localDateTime dt)) := by
  cases sep
  · exact renderDateTime_localDateTime_char dt "T" 'T' rfl rfl fd ds ts hdr htr
  · exact renderDateTime_localDateTime_char dt "t" 't' rfl rfl fd ds ts hdr htr
  · exact renderDateTime_localDateTime_char dt " " ' ' rfl rfl fd ds ts hdr htr

private theorem renderOffset_head_char (o : Std.Time.TimeZone.Offset) (style : OffsetStyle) (os : String)
    (hr : renderOffset o style = some os) :
    ∀ c r, os.toList = c :: r → isAsciiDigit c = false ∧ c ≠ '.' := by
  simp only [renderOffset] at hr
  split at hr
  · simp at hr
  · by_cases hz : o.second.val = 0
    · simp only [hz, beq_self_eq_true, ↓reduceIte] at hr
      cases style with
      | upperZ =>
        injection hr with hos; subst hos
        intro c r hcr
        have h : ("Z" : String).toList = ['Z'] := rfl
        rw [h] at hcr; injection hcr with hc _; subst hc; exact ⟨rfl, by decide⟩
      | lowerZ =>
        injection hr with hos; subst hos
        intro c r hcr
        have h : ("z" : String).toList = ['z'] := rfl
        rw [h] at hcr; injection hcr with hc _; subst hc; exact ⟨rfl, by decide⟩
      | numeric =>
        injection hr with hos; subst hos
        intro c r hcr
        have h : ("+00:00" : String).toList = ['+', '0', '0', ':', '0', '0'] := rfl
        rw [h] at hcr; injection hcr with hc _; subst hc; exact ⟨rfl, by decide⟩
    · have hne : (o.second.val == 0) = false := beq_false_of_ne hz
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hr
      injection hr with hos; subst hos
      intro c r hcr
      have hsign : (if o.second.val < 0 then "-" else "+").toList =
          [if o.second.val < 0 then '-' else '+'] := by
        split <;> rfl
      simp only [String.toList_append, hsign, List.cons_append] at hcr
      injection hcr with hc _; subst hc
      split <;> exact ⟨rfl, by decide⟩

private theorem renderOffsetDateTime_offsetDateTime_char (odt : TomlOffsetDateTime)
    (sepStr : String) (sepChar : Char) (hsep_list : sepStr.toList = [sepChar])
    (hsep_ok : (sepChar == 'T' || sepChar == 't' || sepChar == ' ') = true)
    (oStyle : OffsetStyle) (fd : Nat) (ds ts os : String)
    (hdr : renderDate odt.dateTime.date = some ds)
    (htr : renderTime odt.dateTime.time fd = some ts)
    (hor : renderOffset odt.offset oStyle = some os) :
    parseDateTimeToken (ds ++ sepStr ++ ts ++ os) = some (.ok (.offsetDateTime odt)) := by
  obtain ⟨hdp, hdpref, _⟩ := renderDate_parseDatePart odt.dateTime.date ds
    ((sepStr ++ ts ++ os).toList) hdr
  obtain ⟨htp, _, _⟩ := renderTime_parseTimePart odt.dateTime.time fd ts os.toList htr
    (fun c r h => let h1 := renderOffset_head_char odt.offset oStyle os hor c r h; ⟨h1.1, fun _ => h1.2⟩)
  obtain ⟨hop, _⟩ := renderOffset_parseOffsetPart odt.offset oStyle os hor
  have hdpref' : hasDatePrefix (ds ++ sepStr ++ ts ++ os).toList = true := by
    simpa [String.toList_append, hsep_list, List.append_assoc] using hdpref
  have hdp' : parseDatePart (ds ++ sepStr ++ ts ++ os).toList =
      .ok (odt.dateTime.date, sepChar :: (ts.toList ++ os.toList)) := by
    simpa [String.toList_append, hsep_list, List.append_assoc] using hdp
  have hodt_eq : TomlOffsetDateTime.mk (Std.Time.PlainDateTime.mk odt.dateTime.date odt.dateTime.time) odt.offset = odt := by
    rcases odt with ⟨⟨dd, tt⟩, oo⟩; rfl
  cases hos : os.toList with
  | nil => rw [hos] at hop; cases hop
  | cons o0 os' =>
    have htp' : parseTimePart (ts.toList ++ o0 :: os') = Except.ok (odt.dateTime.time, o0 :: os') := by
      simpa [hos] using htp
    have hop' : parseOffsetPart (o0 :: os') = Except.ok odt.offset := by
      simpa [hos] using hop
    simp only [parseDateTimeToken, hdpref', ↓reduceIte, hdp', hsep_ok, hos, htp', hop', hodt_eq]

/-- Internal TOML scalar round-trip lemma `renderOffsetDateTime_offsetDateTime`. -/
theorem renderOffsetDateTime_offsetDateTime (odt : TomlOffsetDateTime)
    (sep : DateTimeSep) (oStyle : OffsetStyle) (fd : Nat) (ds ts os : String)
    (hdr : renderDate odt.dateTime.date = some ds)
    (htr : renderTime odt.dateTime.time fd = some ts)
    (hor : renderOffset odt.offset oStyle = some os) :
    parseDateTimeToken (ds ++ renderDateTimeSep sep ++ ts ++ os) = some (.ok (.offsetDateTime odt)) := by
  cases sep
  · exact renderOffsetDateTime_offsetDateTime_char odt "T" 'T' rfl rfl oStyle fd ds ts os hdr htr hor
  · exact renderOffsetDateTime_offsetDateTime_char odt "t" 't' rfl rfl oStyle fd ds ts os hdr htr hor
  · exact renderOffsetDateTime_offsetDateTime_char odt " " ' ' rfl rfl oStyle fd ds ts os hdr htr hor

/-- Internal TOML scalar round-trip lemma `clean_all_not_unquotedDelim`. -/
theorem clean_all_not_unquotedDelim (cs : List Char)
    (h : (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true) :
    cs.all (fun c => !isUnquotedDelim c) = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have h1 := h c hc
  simp only [Bool.and_eq_true] at h1
  exact h1.2

/-- Internal TOML scalar round-trip lemma `dateTime_space_takeUnquotedToken`. -/
theorem dateTime_space_takeUnquotedToken
    (d : Std.Time.PlainDate) (t : Std.Time.PlainTime) (fd : Nat)
    (ds ts suffix : String)
    (hdr : renderDate d = some ds)
    (htr : renderTime t fd = some ts)
    (hsuf : suffix.toList.all (fun c => !isUnquotedDelim c) = true)
    (rest : List Char)
    (hrest : ∀ c r, rest = c :: r → isUnquotedDelim c = true) :
    takeUnquotedToken ((ds ++ " " ++ ts ++ suffix).toList ++ rest) =
      (ds ++ " " ++ ts ++ suffix, rest) := by
  have hd_eq : ∃ y1 y2 y3 y4 m1 m2 d1 d2,
      ds.toList = [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] ∧
      isAsciiDigit y1 = true ∧ isAsciiDigit y2 = true ∧ isAsciiDigit y3 = true ∧ isAsciiDigit y4 = true ∧
      isAsciiDigit m1 = true ∧ isAsciiDigit m2 = true ∧ isAsciiDigit d1 = true ∧ isAsciiDigit d2 = true := by
    simp only [renderDate] at hdr
    split at hdr
    · rename_i hvd
      injection hdr with hds; subst hds
      have hv : (0 : Int) ≤ d.year ∧ d.year ≤ 9999 := by simpa [validTomlDate] using hvd
      have h_eq : Int.ofNat (d.year : Int).toNat = (d.year : Int) := Int.toNat_of_nonneg hv.1
      have hy_nat : d.year.toNat < 10000 := by
        have hle : Int.ofNat (d.year : Int).toNat ≤ 9999 := by rw [h_eq]; exact hv.2
        exact Int.ofNat_lt.mp (by omega)
      have hm_prop := d.month.property
      have hd_prop := d.day.property
      obtain ⟨y1, y2, y3, y4, hy_list, hy_four⟩ := padNatZero_4_digits d.year.toNat hy_nat
      obtain ⟨m1, m2, hm_list, hm_two, _, _⟩ := twoDigits_padNatZero d.month.val.toNat (by omega)
      obtain ⟨d1, d2, hd_list, hd_two, _, _⟩ := twoDigits_padNatZero d.day.val.toNat (by omega)
      obtain ⟨ay1, ay2, ay3, ay4⟩ := fourDigitsNat?_isAscii _ _ _ _ _ hy_four
      obtain ⟨am1, am2⟩ := twoDigitsNat?_isAscii _ _ _ hm_two
      obtain ⟨ad1, ad2⟩ := twoDigitsNat?_isAscii _ _ _ hd_two
      have hdash : ("-" : String).toList = ['-'] := rfl
      refine ⟨y1, y2, y3, y4, m1, m2, d1, d2, ?_, ay1, ay2, ay3, ay4, am1, am2, ad1, ad2⟩
      simp only [String.toList_append, hy_list, hdash, hm_list, hd_list]
      rfl
    · simp at hdr
  have ht_eq : ∃ h1 h2 min1 min2 s1 s2 ttail,
      ts.toList = [h1, h2, ':', min1, min2, ':', s1, s2] ++ ttail ∧
      isAsciiDigit h1 = true ∧ isAsciiDigit h2 = true ∧
      isAsciiDigit min1 = true ∧ isAsciiDigit min2 = true ∧
      isAsciiDigit s1 = true ∧ isAsciiDigit s2 = true ∧
      ttail.all (fun c => !isUnquotedDelim c) = true := by
    obtain ⟨_, _, hts_cl⟩ := renderTime_parseTimePart t fd ts [] htr (fun _ _ h => by cases h)
    simp only [renderTime] at htr
    split at htr
    · simp at htr
    · cases hfr : formatNanosExact t.nanosecond.val.toNat fd with
      | none => simp [hfr] at htr
      | some frac =>
        rw [hfr] at htr
        injection htr with hts; subst hts
        have hh_prop := t.hour.property
        have hm_prop := t.minute.property
        have hs_prop := t.second.property
        have hs_le : t.second.val ≤ 60 := by simpa using hs_prop.2
        obtain ⟨h1, h2, hh_list, hh_two, _, _⟩ := twoDigits_padNatZero t.hour.val.toNat (by omega)
        obtain ⟨min1, min2, hmin_list, hmin_two, _, _⟩ := twoDigits_padNatZero t.minute.val.toNat (by omega)
        obtain ⟨s1, s2, hs_list, hs_two, _, _⟩ := twoDigits_padNatZero t.second.val.toNat (by omega)
        obtain ⟨ah1, ah2⟩ := twoDigitsNat?_isAscii _ _ _ hh_two
        obtain ⟨amin1, amin2⟩ := twoDigitsNat?_isAscii _ _ _ hmin_two
        obtain ⟨as1, as2⟩ := twoDigitsNat?_isAscii _ _ _ hs_two
        have hcol : (":" : String).toList = [':'] := rfl
        have hfull : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
            padNatZero 2 t.second.val.toNat ++ frac).toList =
            [h1, h2, ':', min1, min2, ':', s1, s2] ++ frac.toList := by
          simp only [String.toList_append, hh_list, hcol, hmin_list, hs_list]
          rfl
        have hfrac_cl : frac.toList.all (fun c => !isUnquotedDelim c) = true := by
          have h1 := clean_all_not_unquotedDelim _ hts_cl
          rw [hfull, List.all_append, Bool.and_eq_true] at h1
          exact h1.2
        exact ⟨h1, h2, min1, min2, s1, s2, frac.toList, hfull, ah1, ah2, amin1, amin2, as1, as2, hfrac_cl⟩
  rcases hd_eq with ⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, hy1, hy2, hy3, hy4, hm1, hm2, hd1, hd2⟩
  rcases ht_eq with ⟨h1, h2, min1, min2, s1, s2, ttail, hts, hh1, hh2, hmin1, hmin2, hs1, hs2, httail⟩
  have hsp : (" " : String).toList = [' '] := rfl
  have hfull : (ds ++ " " ++ ts ++ suffix).toList =
      [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++
        (ttail ++ suffix.toList) := by
    simp only [String.toList_append, hds, hsp, hts, List.cons_append, List.nil_append]
  rw [hfull]
  have htail_all : (ttail ++ suffix.toList).all (fun c => !isUnquotedDelim c) = true := by
    simp [List.all_append, httail, hsuf]
  rw [takeUnquotedToken_spaceDateTime y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2
    (ttail ++ suffix.toList) rest hy1 hy2 hy3 hy4 hm1 hm2 hd1 hd2 hh1 hh2 hmin1 hmin2 hs1 hs2
    htail_all hrest]
  have hstr : String.ofList
      ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++
        (ttail ++ suffix.toList)) = ds ++ " " ++ ts ++ suffix := by
    rw [← hfull, String.ofList_toList]
  rw [hstr]

private theorem consumeIntDigits_props (b : NumBase) (acc : Nat) (cs : List Char) (n : Nat)
    (h : NumParse.Model.consumeIntDigits b acc cs = .ok n) :
    ∀ c ∈ cs, c ≠ ':' ∧ (b ≠ .hex → c ≠ 'e' ∧ c ≠ 'E') := by
  induction hlen : cs.length using Nat.strongRecOn generalizing cs acc with
  | ind len ih =>
    intro c hc
    cases cs with
    | nil => cases hc
    | cons c0 cs0 =>
      by_cases hu : c0 = '_'
      · subst hu
        cases cs0 with
        | nil => simp [NumParse.Model.consumeIntDigits] at h
        | cons c1 cs1 =>
          simp only [NumParse.Model.consumeIntDigits] at h
          cases hc with
          | head => exact ⟨by decide, fun _ => ⟨by decide, by decide⟩⟩
          | tail _ hc' =>
            cases hdv : NumParse.Model.digitVal? b c1 with
            | none => rw [hdv] at h; cases h
            | some d =>
              rw [hdv] at h
              dsimp only at h
              have hc1 : c1 ≠ ':' ∧ (b ≠ .hex → c1 ≠ 'e' ∧ c1 ≠ 'E') := by
                constructor
                · intro heq1; subst heq1; cases b <;> simp [NumParse.Model.digitVal?] at hdv
                · intro hb
                  constructor <;> intro heq1 <;> subst heq1 <;> cases b <;>
                    simp [NumParse.Model.digitVal?] at hdv <;> exact absurd rfl hb
              rcases List.mem_cons.mp hc' with rfl | hc''
              · exact hc1
              · exact ih cs1.length (by simp [← hlen]; omega) (acc * b.radix + d) cs1 h rfl c hc''
      · unfold NumParse.Model.consumeIntDigits at h
        split at h
        · rename_i heq; cases heq
        · rename_i _ _ heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i c0' cs0' _ _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at h
          cases hdv : NumParse.Model.digitVal? b c0 with
          | none => rw [hdv] at h; cases h
          | some d =>
            rw [hdv] at h
            dsimp only at h
            rcases List.mem_cons.mp hc with rfl | hc'
            · constructor
              · intro heq1; subst heq1; cases b <;> simp [NumParse.Model.digitVal?] at hdv
              · intro hb
                constructor <;> intro heq1 <;> subst heq1 <;> cases b <;>
                  simp [NumParse.Model.digitVal?] at hdv <;> exact absurd rfl hb
            · exact ih cs0.length (by simp [← hlen]) (acc * b.radix + d) cs0 h rfl c hc'

private theorem parseDecAfterSign_props (neg : Bool) (cs : List Char) (m : Int)
    (h : NumParse.Model.parseDecAfterSign neg cs = .ok m) :
    (∃ c0 rest, cs = c0 :: rest ∧ isAsciiDigit c0 = true) ∧
    (∀ c ∈ cs, c ≠ ':' ∧ c ≠ 'e' ∧ c ≠ 'E') := by
  cases cs with
  | nil => simp [NumParse.Model.parseDecAfterSign] at h
  | cons c0 rest =>
    cases h0 : c0 == '_' with
    | true =>
      have hc0 : c0 = '_' := beq_iff_eq.mp h0
      subst hc0
      simp [NumParse.Model.parseDecAfterSign] at h
    | false =>
      cases hzero : c0 == '0' with
      | true =>
        have hc0 : c0 = '0' := beq_iff_eq.mp hzero
        subst hc0
        cases rest with
        | nil =>
          refine ⟨⟨'0', [], rfl, rfl⟩, fun c hc => ?_⟩
          rcases List.mem_singleton.mp hc with rfl
          exact ⟨by decide, by decide, by decide⟩
        | cons c1 r1 =>
          by_cases hd1 : NumParse.Model.isDecDigit c1 = true
          · simp [NumParse.Model.parseDecAfterSign, hd1] at h
          · by_cases hu1 : c1 = '_'
            · subst hu1
              cases r1 with
              | nil => simp [NumParse.Model.parseDecAfterSign, hd1] at h
              | cons c2 tail =>
                by_cases hd2 : NumParse.Model.isDecDigit c2 = true <;>
                  simp [NumParse.Model.parseDecAfterSign, hd1, hd2] at h
            · simp [NumParse.Model.parseDecAfterSign, hd1, hu1] at h
      | false =>
        have hne0 : c0 ≠ '0' := fun he => by rw [he] at hzero; contradiction
        have hne_u : c0 ≠ '_' := fun he => by rw [he] at h0; contradiction
        unfold NumParse.Model.parseDecAfterSign at h
        split at h
        · contradiction
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_u
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne0
        · rename_i c0' rest' _ _ _ heq
          injection heq with h1 h2; subst h1; subst h2
          cases hdv : NumParse.Model.digitVal? .dec c0 with
          | none => rw [hdv] at h; cases h
          | some d =>
            rw [hdv] at h
            dsimp only at h
            cases hn : NumParse.Model.consumeIntDigits .dec d rest with
            | error => rw [hn] at h; cases h
            | ok n =>
              have hd_c : isAsciiDigit c0 = true := by
                simp only [NumParse.Model.digitVal?] at hdv
                split at hdv
                · rename_i hc; simpa [isAsciiDigit, Bool.and_eq_true] using hc
                · cases hdv
              refine ⟨⟨c0, rest, rfl, hd_c⟩, fun c hc => ?_⟩
              rcases List.mem_cons.mp hc with rfl | hc'
              · refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hd_c <;> decide
              · have hp := consumeIntDigits_props .dec d rest n hn c hc'
                exact ⟨hp.1, hp.2 (by decide)⟩

/-- Internal TOML scalar round-trip lemma `parseIntModelChars_props`. -/
theorem parseIntModelChars_props (cs : List Char) (m : Int)
    (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    (∃ c0 rest, cs = c0 :: rest ∧ (c0 = '+' ∨ c0 = '-' ∨ isAsciiDigit c0 = true) ∧
      (∀ c1 r1, (c0 = '+' ∨ c0 = '-') → rest = c1 :: r1 → isAsciiDigit c1 = true)) ∧
    (∀ c ∈ cs, c ≠ ':') := by
  unfold NumParse.Model.parseIntModelChars at h
  split at h
  · cases h
  · rename_i _ b rest
    split at h
    · cases h
    · rcases parseDecAfterSign_props false ('0' :: b :: rest) m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
      injection hdr with hc1 _; subst hc1
      refine ⟨⟨'+', '0' :: b :: rest, rfl, Or.inl rfl, fun c1 r1 _ h1 => ?_⟩, fun c hc => ?_⟩
      · injection h1 with hc1 _; subst hc1; exact hd_dig
      · rcases List.mem_cons.mp hc with rfl | hc'
        · decide
        · exact (hchars c hc').1
  · rename_i _ b rest
    split at h
    · cases h
    · rcases parseDecAfterSign_props true ('0' :: b :: rest) m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
      injection hdr with hc1 _; subst hc1
      refine ⟨⟨'-', '0' :: b :: rest, rfl, Or.inr (Or.inl rfl), fun c1 r1 _ h1 => ?_⟩, fun c hc => ?_⟩
      · injection h1 with hc1 _; subst hc1; exact hd_dig
      · rcases List.mem_cons.mp hc with rfl | hc'
        · decide
        · exact (hchars c hc').1
  · rename_i _ rest _
    rcases parseDecAfterSign_props false rest m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
    refine ⟨⟨'+', rest, rfl, Or.inl rfl, fun c1 r1 _ h1 => ?_⟩, fun c hc => ?_⟩
    · rw [h1] at hdr; injection hdr with hc1 _; subst hc1; exact hd_dig
    · rcases List.mem_cons.mp hc with rfl | hc'
      · decide
      · exact (hchars c hc').1
  · rename_i _ rest _
    rcases parseDecAfterSign_props true rest m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
    refine ⟨⟨'-', rest, rfl, Or.inr (Or.inl rfl), fun c1 r1 _ h1 => ?_⟩, fun c hc => ?_⟩
    · rw [h1] at hdr; injection hdr with hc1 _; subst hc1; exact hd_dig
    · rcases List.mem_cons.mp hc with rfl | hc'
      · decide
      · exact (hchars c hc').1
  · rename_i _ b rest
    cases hbp : NumParse.Model.basePrefix? b with
    | none =>
      rw [hbp] at h
      dsimp only at h
      have hd := parseDecAfterSign_props false ('0' :: b :: rest) m h
      refine ⟨⟨'0', b :: rest, rfl, Or.inr (Or.inr rfl), fun _ _ hs => by rcases hs with h1 | h1 <;> cases h1⟩,
        fun c hc => (hd.2 c hc).1⟩
    | some base =>
      rw [hbp] at h
      dsimp only at h
      cases rest with
      | nil => cases h
      | cons c1 cs1 =>
        by_cases hu : c1 = '_'
        · subst hu; cases h
        · split at h
          · cases h
          · cases h
          · rename_i c1' cs1' _ _ heq
            injection heq with h1 h2; subst h1; subst h2
            cases hdv : NumParse.Model.digitVal? base c1 with
            | none => rw [hdv] at h; cases h
            | some d =>
              rw [hdv] at h
              dsimp only at h
              cases hn : NumParse.Model.consumeIntDigits base d cs1 with
              | error => rw [hn] at h; cases h
              | ok n =>
                refine ⟨⟨'0', b :: c1 :: cs1, rfl, Or.inr (Or.inr rfl),
                  fun _ _ hs => by rcases hs with h1 | h1 <;> cases h1⟩, fun c hc => ?_⟩
                rcases List.mem_cons.mp hc with rfl | hc
                · decide
                rcases List.mem_cons.mp hc with rfl | hc
                · intro heq; subst heq; cases hbp
                rcases List.mem_cons.mp hc with rfl | hc
                · cases base <;> simp [NumParse.Model.digitVal?] at hdv <;>
                    intro heq <;> subst heq <;> simp at hdv
                · exact (consumeIntDigits_props base d cs1 n hn c hc).1
  · rcases parseDecAfterSign_props false cs m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
    have hne_sign : d0 ≠ '+' ∧ d0 ≠ '-' := ⟨fun he => by subst he; revert hd_dig; decide, fun he => by subst he; revert hd_dig; decide⟩
    refine ⟨⟨d0, dr, hdr, Or.inr (Or.inr hd_dig), fun _ _ hs _ => by rcases hs with h1 | h1; exact absurd h1 hne_sign.1; exact absurd h1 hne_sign.2⟩,
      fun c hc => (hchars c hc).1⟩

private theorem toString_nat_head_nonzero (n : Nat) (hn : 0 < n) :
    ∃ d0 ds, (toString n).toList = d0 :: ds ∧ isAsciiDigit d0 = true ∧ d0 ≠ '0' ∧
      (d0 :: ds).all isAsciiDigit = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h10 : n < 10
    · obtain ⟨hch, had, _, _⟩ := toString_lt10_char n h10
      have hne0 : (n : Nat).digitChar ≠ '0' := by
        intro heq
        have hdv : digitVal n.digitChar = digitVal '0' := congrArg digitVal heq
        obtain ⟨_, _, hdv', _⟩ := toString_lt10_char n h10
        have hd0 : digitVal '0' = 0 := rfl
        omega
      refine ⟨n.digitChar, [], hch, had, hne0, ?_⟩
      simp [had]
    · have hdiv_pos : 0 < n / 10 := by omega
      have hdiv_lt : n / 10 < n := by omega
      obtain ⟨d0, ds, hd_list, hd_dig, hd_ne0, hd_all⟩ := ih (n / 10) hdiv_lt hdiv_pos
      have hsplit := toString_two_digits_split (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      have heq : n / 10 * 10 + n % 10 = n := by omega
      rw [heq] at hsplit
      obtain ⟨_, had_m, _, _⟩ := toString_lt10_char (n % 10) (Nat.mod_lt n (by decide))
      refine ⟨d0, ds ++ [(n % 10).digitChar], ?_, hd_dig, hd_ne0, ?_⟩
      · rw [hsplit, hd_list]; rfl
      · simp only [List.all_cons, Bool.and_eq_true] at hd_all
        simp [List.all_append, hd_all.1, hd_all.2, had_m]

private theorem consumeIntDigits_dec_foldl (acc : Nat) (ds : List Char)
    (hds : ds.all isAsciiDigit = true) :
    NumParse.Model.consumeIntDigits .dec acc ds =
      .ok (ds.foldl (fun a c => a * 10 + digitVal c) acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    have hnot_u : c ≠ '_' := by intro heq; subst heq; exact absurd hds.1 (by decide)
    have hdig_val : NumParse.Model.digitVal? .dec c = some (digitVal c) := by
      have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigit] using hds.1
      simp [NumParse.Model.digitVal?, h1.1, h1.2, digitVal]
    unfold NumParse.Model.consumeIntDigits
    split
    · rename_i heq; cases heq
    · rename_i heq; injection heq with h1 _; exact absurd h1 hnot_u
    · rename_i heq; injection heq with h1 _; exact absurd h1 hnot_u
    · rename_i c1 cs1 _ _ heq
      injection heq with h1 h2
      rw [← h1, ← h2]
      simp only [hdig_val, NumParse.Model.NumBase.radix, List.foldl_cons]
      exact ih (acc * 10 + digitVal c) hds.2

private theorem parseDecAfterSign_toString_nat (neg : Bool) (n : Nat) :
    NumParse.Model.parseDecAfterSign neg (toString n).toList =
      .ok (if neg then -Int.ofNat n else Int.ofNat n) := by
  by_cases hn : n = 0
  · subst hn
    have h0 : (toString (0 : Nat)).toList = ['0'] := rfl
    rw [h0]
    simp [NumParse.Model.parseDecAfterSign]
  · obtain ⟨d0, ds, hlist, hd0, hne0, hall⟩ := toString_nat_head_nonzero n (by omega)
    rw [hlist]
    have hnot_u : d0 ≠ '_' := by intro heq; subst heq; revert hd0; decide
    have hdig_val : NumParse.Model.digitVal? .dec d0 = some (digitVal d0) := by
      have h1 : '0' ≤ d0 ∧ d0 ≤ '9' := by simpa [isAsciiDigit] using hd0
      simp [NumParse.Model.digitVal?, h1.1, h1.2, digitVal]
    have hall_ds : ds.all isAsciiDigit = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hall; exact hall.2
    have hfold : (d0 :: ds).foldl (fun a c => a * 10 + digitVal c) 0 = n := by
      rw [← hlist]; exact toString_foldl_digits n
    unfold NumParse.Model.parseDecAfterSign
    split
    · contradiction
    · rename_i heq; injection heq with h1 _; exact absurd h1 hnot_u
    · rename_i heq; injection heq with h1 _; exact absurd h1 hne0
    · rename_i c1 rest1 _ _ heq
      injection heq with h1 h2; subst h1; subst h2
      simp only [hdig_val, consumeIntDigits_dec_foldl (digitVal d0) ds hall_ds]
      have hfold' : List.foldl (fun a c => a * 10 + digitVal c) (digitVal d0) ds = n := by
        simpa [List.foldl_cons, Nat.zero_mul, Nat.zero_add] using hfold
      rw [hfold']

/-- Internal TOML scalar round-trip lemma `formatInt64Canonical_isValidIntLex`. -/
theorem formatInt64Canonical_isValidIntLex (n : Int64) :
    isValidIntLex (formatInt64Canonical n) n = true := by
  have hparse_int : NumParse.Model.parseIntModel (formatInt64Canonical n) = .ok n.toInt := by
    simp only [formatInt64Canonical, NumParse.Model.parseIntModel]
    cases hni : n.toInt with
    | ofNat m =>
      have hstr : toString (Int.ofNat m) = toString m := rfl
      rw [hstr]
      cases hm : m with
      | zero =>
        have h0 : (toString (0 : Nat)).toList = ['0'] := rfl
        rw [h0]; rfl
      | succ k =>
        obtain ⟨d0, ds, hlist, hd0, hne0, hall⟩ := toString_nat_head_nonzero (k + 1) (by omega)
        have hd := parseDecAfterSign_toString_nat false (k + 1)
        rw [hlist] at hd ⊢
        simp only [Bool.false_eq_true, ↓reduceIte] at hd
        have hne_plus : d0 ≠ '+' := fun he => by subst he; revert hd0; decide
        have hne_minus : d0 ≠ '-' := fun he => by subst he; revert hd0; decide
        unfold NumParse.Model.parseIntModelChars
        split
        · contradiction
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_plus
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_minus
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_plus
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_minus
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne0
        · exact hd
    | negSucc k =>
      have hstr : (toString (Int.negSucc k)).toList = '-' :: (toString (k + 1)).toList := by
        change (("-" ++ (k + 1).repr) : String).toList = '-' :: (toString (k + 1)).toList
        simp [String.toList_append, toString]
      rw [hstr]
      obtain ⟨d0, ds, hlist, hd0, hne0, _⟩ := toString_nat_head_nonzero (k + 1) (by omega)
      have hd := parseDecAfterSign_toString_nat true (k + 1)
      rw [hlist] at hd ⊢
      simp only [↓reduceIte] at hd
      have hres : NumParse.Model.parseIntModelChars ('-' :: d0 :: ds) =
          .ok (-Int.ofNat (k + 1)) := by
        unfold NumParse.Model.parseIntModelChars
        split
        · contradiction
        · rename_i heq; cases heq
        · rename_i heq; injection heq with _ h2; injection h2 with h3 _; exact absurd h3 hne0
        · rename_i heq; cases heq
        · rename_i rest _ _ heq; injection heq with _ h2; subst h2; exact hd
        · rename_i heq; cases heq
        · rename_i _ _ _ _ hne _; exact False.elim (hne (d0 :: ds) rfl)
      rw [hres]
      rfl
  have hbounds : NumParse.Model.inInt64Range n.toInt = true := by
    have h1 : (-2 ^ 63 : Int) ≤ n.toInt := Int64.le_toInt n
    have h2 : n.toInt ≤ Int64.maxValue.toInt := Int64.toInt_le n
    have hmax : Int64.maxValue.toInt = 9223372036854775807 := by decide
    rw [NumParse.Model.inInt64Range, decide_eq_true_eq]
    simp only [NumParse.Model.int64MinInt, NumParse.Model.int64MaxInt]
    omega
  have hof : Int64.ofInt n.toInt = n := Int64.ofInt_toInt n
  have hp64 : NumParse.Model.parseInt64Model (formatInt64Canonical n) = .ok n := by
    simp [NumParse.Model.parseInt64Model, hparse_int, hbounds, hof]
  have honly_dec_or_minus : ∀ c ∈ (formatInt64Canonical n).toList, c = '-' ∨ isAsciiDigit c = true := by
    intro c hc
    simp only [formatInt64Canonical] at hc
    cases hni : n.toInt with
    | ofNat m =>
      rw [hni] at hc
      have hstr : toString (Int.ofNat m) = toString m := rfl
      rw [hstr] at hc
      have hd := List.all_eq_true.mp (toString_digits_all_clean m).1 c hc
      simp only [Bool.and_eq_true] at hd
      exact Or.inr hd.1.1.1.1
    | negSucc k =>
      rw [hni] at hc
      have hstr : (toString (Int.negSucc k)).toList = '-' :: (toString (k + 1)).toList := by
        change (("-" ++ (k + 1).repr) : String).toList = '-' :: (toString (k + 1)).toList
        simp [String.toList_append, toString]
      rw [hstr] at hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact Or.inl rfl
      · have hd := List.all_eq_true.mp (toString_digits_all_clean (k + 1)).1 c hc'
        simp only [Bool.and_eq_true] at hd
        exact Or.inr hd.1.1.1.1
  have hclean_all : (formatInt64Canonical n).toList.all (fun c =>
      !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' &&
      c != '.' && !isDisallowedControl c) = true := by
    rw [List.all_eq_true]
    intro c hc
    rcases honly_dec_or_minus c hc with rfl | hcd
    · decide
    · have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigit] using hcd
      have hws : c.isWhitespace = false := by
        simp only [Char.isWhitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro heq <;> subst heq <;> exact absurd h1 (by decide)
      have hneq : c ≠ '#' ∧ c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ '.' := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> exact absurd h1 (by decide)
      have hctrl : isDisallowedControl c = false := by
        have h1' : (48 : Nat) ≤ c.toNat ∧ c.toNat ≤ 57 :=
          ⟨UInt32.le_iff_toNat_le.mp h1.1, UInt32.le_iff_toNat_le.mp h1.2⟩
        simp [isDisallowedControl]
        omega
      simp [hws, hneq.1, hneq.2.1, hneq.2.2.1, hneq.2.2.2.1, hneq.2.2.2.2, hctrl]
  have hno_upper : hasUppercaseBasePrefix (formatInt64Canonical n) = false := by
    have hnot_sw : ∀ p : String, ∀ c : Char, c ∈ p.toList → (c = 'X' ∨ c = 'O' ∨ c = 'B') →
        (formatInt64Canonical n).startsWith p = false := by
      intro p c hc_mem hc_up
      rw [Bool.eq_false_iff]
      intro hsw
      rw [String.startsWith_string_iff] at hsw
      rcases hsw with ⟨t, ht⟩
      have hmem : c ∈ (formatInt64Canonical n).toList := by
        rw [← ht]
        exact List.mem_append_left t hc_mem
      rcases honly_dec_or_minus c hmem with rfl | hdig
      · rcases hc_up with h | h | h <;> contradiction
      · rcases hc_up with rfl | rfl | rfl <;> revert hdig <;> decide
    simp only [hasUppercaseBasePrefix, Bool.or_eq_false_iff]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨hnot_sw "0X" 'X' (by decide) (by decide),
      hnot_sw "0O" 'O' (by decide) (by decide)⟩,
      hnot_sw "0B" 'B' (by decide) (by decide)⟩,
      hnot_sw "+0X" 'X' (by decide) (by decide)⟩,
      hnot_sw "+0O" 'O' (by decide) (by decide)⟩,
      hnot_sw "+0B" 'B' (by decide) (by decide)⟩,
      hnot_sw "-0X" 'X' (by decide) (by decide)⟩,
      hnot_sw "-0O" 'O' (by decide) (by decide)⟩,
      hnot_sw "-0B" 'B' (by decide) (by decide)⟩
  have hno_exp : (!(formatInt64Canonical n).contains 'e' && !(formatInt64Canonical n).contains 'E') = true := by
    have hnot_e : 'e' ∉ (formatInt64Canonical n).toList := by
      intro hmem
      rcases honly_dec_or_minus 'e' hmem with h1 | h2
      · cases h1
      · revert h2; decide
    have hnot_E : 'E' ∉ (formatInt64Canonical n).toList := by
      intro hmem
      rcases honly_dec_or_minus 'E' hmem with h1 | h2
      · cases h1
      · revert h2; decide
    have he1 : (formatInt64Canonical n).contains 'e' = false := by simp [String.contains, hnot_e]
    have he2 : (formatInt64Canonical n).contains 'E' = false := by simp [String.contains, hnot_E]
    simp [he1, he2]
  simp only [isValidIntLex, hp64, hclean_all, beq_self_eq_true, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · simpa [hasUppercaseBasePrefix] using hno_upper
  · split
    · trivial
    · simpa [Bool.not_or] using hno_exp

private theorem asciiDigit_clean (c : Char) (hc : isAsciiDigit c = true) :
    !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' &&
      c != '.' && c != '\r' && c != '\n' && !isDisallowedControl c && !isUnquotedDelim c = true := by
  have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigit] using hc
  have h1' : (48 : Nat) ≤ c.toNat ∧ c.toNat ≤ 57 :=
    ⟨UInt32.le_iff_toNat_le.mp h1.1, UInt32.le_iff_toNat_le.mp h1.2⟩
  have hws : c.isWhitespace = false := by
    simp only [Char.isWhitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro heq <;> subst heq <;> exact absurd h1 (by decide)
  have hneq : c ≠ '#' ∧ c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ '.' ∧ c ≠ '\r' ∧ c ≠ '\n' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> exact absurd h1 (by decide)
  have hctrl : isDisallowedControl c = false := by
    simp [isDisallowedControl]
    omega
  have hud : isUnquotedDelim c = false := isUnquotedDelim_asciiDigit c hc
  simp [hws, hneq.1, hneq.2.1, hneq.2.2.1, hneq.2.2.2.1, hneq.2.2.2.2.1,
    hneq.2.2.2.2.2.1, hneq.2.2.2.2.2.2, hctrl, hud]

private def isFloatModelChar (c : Char) : Bool :=
  c == '+' || c == '-' || c == '.' || c == 'e' || c == 'E' || c == '_' ||
    c == 'i' || c == 'n' || c == 'f' || c == 'a' || isAsciiDigit c

private theorem isFloatModelChar_props (c : Char) (h : isFloatModelChar c = true) :
    c ≠ ':' ∧ c ≠ 'x' ∧ c ≠ 'X' ∧
      (!c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c) = true ∧
      (!isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  simp only [isFloatModelChar, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | hc)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · have hcl := asciiDigit_clean c hc
    simp only [Bool.and_eq_true] at hcl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro heq; subst heq; revert hc; decide
    · intro heq; subst heq; revert hc; decide
    · intro heq; subst heq; revert hc; decide
    · simp [hcl.1.1.1.1.1.1.1.1.1, hcl.1.1.1.1.1.1.1.1.2, hcl.1.1.1.1.1.1.1.2,
        hcl.1.1.1.1.1.1.2, hcl.1.1.1.1.1.2, hcl.1.2]
    · have hud : isUnquotedDelim c = false := by simpa using hcl.2
      simp [hcl.1.2, hcl.1.1.1.2, hcl.1.1.2, hud]

private theorem consumeDecFloatDigits_props (acc cnt : Nat) (cs : List Char)
    (m c : Nat) (rest : List Char)
    (h : NumParse.Model.consumeDecFloatDigits acc cnt cs = .ok (m, c, rest)) :
    ∃ pfx, cs = pfx ++ rest ∧
      (∀ ch ∈ pfx, ch = '_' ∨ isAsciiDigit ch = true) ∧
      (∀ c0 r0, rest = c0 :: r0 → c0 ≠ '_' ∧ isAsciiDigit c0 = false) := by
  induction hlen : cs.length using Nat.strongRecOn generalizing cs acc cnt with
  | ind len ih =>
    cases cs with
    | nil =>
      simp only [NumParse.Model.consumeDecFloatDigits] at h
      injection h with h1
      have hrest : rest = [] := (Prod.mk.inj (Prod.mk.inj h1).2).2.symm
      exact ⟨[], by simp [hrest], by simp, fun _ _ hr => by rw [hrest] at hr; cases hr⟩
    | cons c0 cs0 =>
      by_cases hu : c0 = '_'
      · subst hu
        cases cs0 with
        | nil => simp [NumParse.Model.consumeDecFloatDigits] at h
        | cons c1 cs1 =>
          simp only [NumParse.Model.consumeDecFloatDigits] at h
          by_cases hd1 : NumParse.Model.isDecDigit c1 = true
          · simp only [hd1, ↓reduceIte] at h
            obtain ⟨pfx, hcs, hpfx, hrest⟩ :=
              ih cs1.length (by simp [← hlen]; omega) _ _ cs1 h rfl
            have had1 : isAsciiDigit c1 = true := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd1
            refine ⟨'_' :: c1 :: pfx, by simp [hcs], fun ch hc => ?_, hrest⟩
            rcases List.mem_cons.mp hc with rfl | hc
            · exact Or.inl rfl
            rcases List.mem_cons.mp hc with rfl | hc
            · exact Or.inr had1
            · exact hpfx ch hc
          · simp [hd1] at h
      · unfold NumParse.Model.consumeDecFloatDigits at h
        split at h
        · rename_i heq; cases heq
        · rename_i _ _ heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i c0' cs0' _ _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at h
          by_cases hd0 : NumParse.Model.isDecDigit c0 = true
          · simp only [hd0] at h
            obtain ⟨pfx, hcs, hpfx, hrest⟩ :=
              ih cs0.length (by simp [← hlen]) _ _ cs0 h rfl
            have had0 : isAsciiDigit c0 = true := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd0
            refine ⟨c0 :: pfx, by simp [hcs], fun ch hc => ?_, hrest⟩
            rcases List.mem_cons.mp hc with rfl | hc
            · exact Or.inr had0
            · exact hpfx ch hc
          · simp only [hd0] at h
            injection h with h1
            have hrest : rest = c0 :: cs0 := (Prod.mk.inj (Prod.mk.inj h1).2).2.symm
            have had0 : isAsciiDigit c0 = false := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd0
            refine ⟨[], by simp [hrest], by simp, fun x r hxr => ?_⟩
            rw [hrest] at hxr
            injection hxr with hx _
            subst hx
            exact ⟨hu, had0⟩

private theorem parseFloatIntPart_props (cs : List Char) (m : Nat) (rest : List Char)
    (h : NumParse.Model.parseFloatIntPart cs = .ok (m, rest)) :
    ∃ pfx d0 ptail, cs = pfx ++ rest ∧ pfx = d0 :: ptail ∧ isAsciiDigit d0 = true ∧
      (∀ ch ∈ pfx, ch = '_' ∨ isAsciiDigit ch = true) ∧
      (∀ c0 r0, rest = c0 :: r0 → c0 ≠ '_' ∧ isAsciiDigit c0 = false) := by
  cases cs with
  | nil => simp [NumParse.Model.parseFloatIntPart] at h
  | cons c0 cs0 =>
    by_cases hu : c0 = '_'
    · subst hu; simp [NumParse.Model.parseFloatIntPart] at h
    · by_cases hz : c0 = '0'
      · subst hz
        cases cs0 with
        | nil =>
          simp only [NumParse.Model.parseFloatIntPart] at h
          injection h with h1
          have hrest : rest = [] := (Prod.mk.inj h1).2.symm
          refine ⟨['0'], '0', [], by simp [hrest], rfl, rfl, fun ch hc => ?_, fun _ _ hr => by rw [hrest] at hr; cases hr⟩
          rcases List.mem_singleton.mp hc with rfl; exact Or.inr rfl
        | cons c1 r1 =>
          simp only [NumParse.Model.parseFloatIntPart] at h
          by_cases hd1 : NumParse.Model.isDecDigit c1 = true
          · simp [hd1] at h
          · by_cases hc1u : c1 = '_'
            · subst hc1u
              cases r1 with
              | nil => simp [hd1] at h
              | cons c2 t2 =>
                by_cases hd2 : NumParse.Model.isDecDigit c2 = true <;> simp [hd1, hd2] at h
            · have hbeq : (c1 == '_') = false := beq_false_of_ne hc1u
              simp only [hd1, Bool.false_eq_true, ↓reduceIte, hbeq] at h
              injection h with h1
              have hrest : rest = c1 :: r1 := (Prod.mk.inj h1).2.symm
              have had1 : isAsciiDigit c1 = false := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd1
              refine ⟨['0'], '0', [], by simp [hrest], rfl, rfl, fun ch hc => ?_, fun x r hxr => ?_⟩
              · rcases List.mem_singleton.mp hc with rfl; exact Or.inr rfl
              · rw [hrest] at hxr; injection hxr with hx _; subst hx; exact ⟨hc1u, had1⟩
      · unfold NumParse.Model.parseFloatIntPart at h
        split at h
        · rename_i heq; cases heq
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i heq; injection heq with h1 _; exact absurd h1 hz
        · rename_i c0' cs0' _ _ _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at h
          by_cases hd0 : NumParse.Model.isDecDigit c0 = true
          · simp only [hd0] at h
            cases hc : NumParse.Model.consumeDecFloatDigits (c0.toNat - '0'.toNat) 1 cs0 with
            | error => rw [hc] at h; cases h
            | ok res =>
              rcases res with ⟨mv, fst, rem⟩
              rw [hc] at h
              injection h with h1
              have hrem : rem = rest := (Prod.mk.inj h1).2
              subst hrem
              obtain ⟨pfx, hcs0, hpfx, hrest⟩ := consumeDecFloatDigits_props _ _ _ _ _ _ hc
              have had0 : isAsciiDigit c0 = true := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd0
              refine ⟨c0 :: pfx, c0, pfx, by simp [hcs0], rfl, had0, fun ch hm => ?_, hrest⟩
              rcases List.mem_cons.mp hm with rfl | hm'
              · exact Or.inr had0
              · exact hpfx ch hm'
          · simp [hd0] at h

private theorem parseFloatExpPart_props (cs : List Char) (e : Int)
    (h : NumParse.Model.parseFloatExpPart cs = .ok (e, [])) :
    ∀ c ∈ cs, c = '+' ∨ c = '-' ∨ c = '_' ∨ isAsciiDigit c = true := by
  unfold NumParse.Model.parseFloatExpPart at h
  have hbody : ∀ (expNeg : Bool) (body : List Char),
      (match body with
        | [] => Except.error NumParseErrorKind.invalidSyntax
        | '_' :: tail => Except.error NumParseErrorKind.invalidUnderscore
        | c :: rest =>
          if NumParse.Model.isDecDigit c = true then
            match NumParse.Model.consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest with
            | .ok (eMag, _, rem) =>
              .ok (if expNeg = true then -Int.ofNat eMag else Int.ofNat eMag, rem)
            | .error k => .error k
          else .error .invalidSyntax) = .ok (e, []) →
      ∀ c ∈ body, c = '_' ∨ isAsciiDigit c = true := by
    intro expNeg body hb c hc
    cases body with
    | nil => cases hb
    | cons c0 r0 =>
      by_cases hu : c0 = '_'
      · subst hu; cases hb
      · split at hb
        · rename_i heq; cases heq
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i c0' r0' _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at hb
          by_cases hd0 : NumParse.Model.isDecDigit c0 = true
          · simp only [hd0, ↓reduceIte] at hb
            cases hc2 : NumParse.Model.consumeDecFloatDigits (c0.toNat - '0'.toNat) 1 r0 with
            | error => rw [hc2] at hb; cases hb
            | ok res =>
              rcases res with ⟨em, fst, rem⟩
              rw [hc2] at hb
              injection hb with h1
              have hrem : rem = [] := (Prod.mk.inj h1).2
              subst hrem
              obtain ⟨pfx, hr0, hpfx, _⟩ := consumeDecFloatDigits_props _ _ _ _ _ _ hc2
              simp only [List.append_nil] at hr0
              subst hr0
              rcases List.mem_cons.mp hc with rfl | hc'
              · exact Or.inr (by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd0)
              · exact hpfx c hc'
          · simp [hd0] at hb
  cases cs with
  | nil => simp at h
  | cons c0 r0 =>
    by_cases hp : c0 = '+'
    · subst hp
      dsimp only at h
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact Or.inl rfl
      · rcases hbody false r0 h c hc' with h1 | h2
        · exact Or.inr (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inr (Or.inr h2))
    · by_cases hm : c0 = '-'
      · subst hm
        dsimp only at h
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact Or.inr (Or.inl rfl)
        · rcases hbody true r0 h c hc' with h1 | h2
          · exact Or.inr (Or.inr (Or.inl h1))
          · exact Or.inr (Or.inr (Or.inr h2))
      · dsimp only at h
        split at h
        · cases h
        · cases h
        · rename_i c0' r0' _ heq
          split at heq
          · rename_i _ heq_c0
            injection heq_c0 with h1 _
            exact absurd h1 hp
          · rename_i _ heq_c0
            injection heq_c0 with h1 _
            exact absurd h1 hm
          · dsimp only at heq
            have hfst : (match c0 :: r0 with
                | '+' :: rest => (false, rest)
                | '-' :: rest => (true, rest)
                | _ => (false, c0 :: r0)).fst = false := by
              split
              · rename_i _ heq_c0
                injection heq_c0 with h1 _
                exact absurd h1 hp
              · rename_i _ heq_c0
                injection heq_c0 with h1 _
                exact absurd h1 hm
              · rfl
            erw [hfst] at h
            intro c hc
            have hc' : c ∈ c0' :: r0' := by rw [← heq]; exact hc
            have hcall := hbody false (c0' :: r0') (by
              split
              · rename_i h_nil
                cases h_nil
              · rename_i _ h_us
                injection h_us with h_us' _
                exact absurd h_us' ‹c0' = '_' → False›
              · rename_i heq_cr
                injection heq_cr with hc1 hr1
                rw [← hc1, ← hr1]
                exact h) c hc'
            rcases hcall with h1 | h2
            · exact Or.inr (Or.inr (Or.inl h1))
            · exact Or.inr (Or.inr (Or.inr h2))

private theorem hasDatePrefix_false_of_digit_or_us_before_sep
    (pfx : List Char) (sep : Char) (tail : List Char)
    (hpfx : ∀ c ∈ pfx, c = '_' ∨ isAsciiDigit c = true)
    (hsep : sep = '.' ∨ sep = 'e' ∨ sep = 'E') :
    hasDatePrefix (pfx ++ sep :: tail) = false := by
  have hsep_not_dig : isAsciiDigit sep = false := by
    rcases hsep with rfl | rfl | rfl <;> rfl
  have hsep_not_dash : sep ≠ '-' := by
    rcases hsep with rfl | rfl | rfl <;> decide
  rcases pfx with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
  · simp only [List.nil_append, hasDatePrefix]
    split
    · rename_i heq; injection heq with h1 _; subst h1; simp [hsep_not_dig]
    · rfl
  · simp only [List.cons_append, List.nil_append, hasDatePrefix]
    split
    · rename_i heq; have h2 := (List.cons.inj heq).2; injection h2 with h1 _; subst h1; simp [hsep_not_dig]
    · rfl
  · simp only [List.cons_append, List.nil_append, hasDatePrefix]
    split
    · rename_i heq; have h2 := (List.cons.inj (List.cons.inj heq).2).2; injection h2 with h1 _; subst h1; simp [hsep_not_dig]
    · rfl
  · simp only [List.cons_append, List.nil_append, hasDatePrefix]
    split
    · rename_i heq; have h2 := (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2; injection h2 with h1 _; subst h1; simp [hsep_not_dig]
    · rfl
  · simp only [List.cons_append, List.nil_append, hasDatePrefix]
    split
    · rename_i heq
      have hdash : sep = '-' := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2).1
      exact absurd hdash hsep_not_dash
    · rfl
  · have he := hpfx e (by simp)
    have hne : e ≠ '-' := by
      rcases he with rfl | hd
      · decide
      · intro h1; subst h1; revert hd; decide
    simp only [List.cons_append, hasDatePrefix]
    split
    · rename_i heq
      have hdash : e = '-' := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2).1
      exact absurd hdash hne
    · rfl

private theorem parseFloatExpSuffix_props (afterE : List Char) (g : Int → Float) (f : Float)
    (h : (match NumParse.Model.parseFloatExpPart afterE with
      | Except.error k => Except.error k
      | Except.ok (expVal, afterExp) =>
        if afterExp.isEmpty = true then Except.ok (g expVal) else Except.error NumParseErrorKind.trailingChars) = Except.ok f) :
    ∀ c ∈ afterE, isFloatModelChar c = true := by
  cases hexp : NumParse.Model.parseFloatExpPart afterE with
  | error => rw [hexp] at h; cases h
  | ok res =>
    rcases res with ⟨expVal, afterExp⟩
    rw [hexp] at h
    dsimp only at h
    cases hrem : afterExp.isEmpty with
    | false => simp [hrem] at h
    | true =>
      have hae : afterExp = [] := by cases afterExp <;> simp_all
      subst hae
      intro c hc
      rcases parseFloatExpPart_props afterE expVal hexp c hc with rfl | rfl | rfl | hd
      · rfl
      · rfl
      · rfl
      · simp [isFloatModelChar, hd]

private theorem parseFloatAfterFrac_props (afterFrac : List Char) (neg : Bool) (mant fracCount : Nat) (f : Float)
    (h : (match afterFrac with
      | 'e' :: afterE =>
        match NumParse.Model.parseFloatExpPart afterE with
        | Except.error k => Except.error k
        | Except.ok (expVal, afterExp) =>
          if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg mant (expVal - Int.ofNat fracCount))
          else Except.error NumParseErrorKind.trailingChars
      | 'E' :: afterE =>
        match NumParse.Model.parseFloatExpPart afterE with
        | Except.error k => Except.error k
        | Except.ok (expVal, afterExp) =>
          if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg mant (expVal - Int.ofNat fracCount))
          else Except.error NumParseErrorKind.trailingChars
      | [] => Except.ok (NumParse.Model.evalFloat neg mant (-Int.ofNat fracCount))
      | _ :: _ => Except.error NumParseErrorKind.trailingChars) = Except.ok f) :
    ∀ c ∈ afterFrac, isFloatModelChar c = true := by
  split at h
  · rename_i afterE
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · rfl
    · exact parseFloatExpSuffix_props afterE _ f h c hc'
  · rename_i afterE
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · rfl
    · exact parseFloatExpSuffix_props afterE _ f h c hc'
  · simp
  · simp at h

/-- Internal TOML scalar round-trip lemma `parseFloatModelChars_props`. -/
theorem parseFloatModelChars_props (cs : List Char) (f : Float)
    (h : NumParse.Model.parseFloatModelChars cs = .ok f) :
    (∃ c0 rest, cs = c0 :: rest ∧
      (c0 = '+' ∨ c0 = '-' ∨ c0 = 'i' ∨ c0 = 'n' ∨ isAsciiDigit c0 = true)) ∧
    (∀ c ∈ cs, isFloatModelChar c = true) ∧
    hasDatePrefix cs = false ∧
    hasTimePrefix cs = false ∧
    isFloatTokenCandidate (String.ofList cs) = true := by
  have hnot_time : ∀ l : List Char, (∀ c ∈ l, isFloatModelChar c = true) → hasTimePrefix l = false := by
    intro l hl
    unfold hasTimePrefix
    split
    · exact absurd rfl (isFloatModelChar_props ':' (hl ':' (by simp))).1
    · rfl
  have hcand_of_sep : ∀ l : List Char, (∀ c ∈ l, isFloatModelChar c = true) →
      (l.contains '.' || l.contains 'e' || l.contains 'E') = true →
      isFloatTokenCandidate (String.ofList l) = true := by
    intro l hl hsep
    have hno_x : ∀ p : String, ∀ c ∈ p.toList, c = 'x' ∨ c = 'X' →
        (String.ofList l).startsWith p = false := by
      intro p c hcm hcx
      rw [Bool.eq_false_iff]
      intro hsw
      rw [String.startsWith_string_iff] at hsw
      rcases hsw with ⟨t, ht⟩
      have hmem : c ∈ l := by
        have h1 : c ∈ (String.ofList l).toList := by rw [← ht]; exact List.mem_append_left t hcm
        simpa [String.toList_ofList] using h1
      have hnx := (isFloatModelChar_props c (hl c hmem)).2
      rcases hcx with rfl | rfl
      · exact absurd rfl hnx.1
      · exact absurd rfl hnx.2.1
    simp only [isFloatTokenCandidate, String.toList_ofList, hsep, Bool.and_true]
    rw [hno_x "0x" 'x' (by decide) (Or.inl rfl),
      hno_x "0X" 'X' (by decide) (Or.inr rfl),
      hno_x "+0x" 'x' (by decide) (Or.inl rfl),
      hno_x "-0x" 'x' (by decide) (Or.inl rfl),
      hno_x "+0X" 'X' (by decide) (Or.inr rfl),
      hno_x "-0X" 'X' (by decide) (Or.inr rfl)]
    simp
  have hbody : ∀ body : List Char, ∀ neg : Bool,
      (match body with
        | 'i' :: 'n' :: 'f' :: rest =>
          match rest with | [] => Except.ok (if neg = true then -Float.inf else Float.inf) | _ :: _ => Except.error NumParseErrorKind.trailingChars
        | 'n' :: 'a' :: 'n' :: rest =>
          match rest with | [] => Except.ok Float.nan | _ :: _ => Except.error NumParseErrorKind.trailingChars
        | _ =>
          match NumParse.Model.parseFloatIntPart body with
          | Except.error k => Except.error k
          | Except.ok (intVal, afterInt) =>
            match afterInt with
            | '.' :: afterDot =>
              match afterDot with
              | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
              | c :: rest =>
                if NumParse.Model.isDecDigit c = true then
                  match NumParse.Model.consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest with
                  | Except.error k => Except.error k
                  | Except.ok (mantissa, fracCount, afterFrac) =>
                    match afterFrac with
                    | 'e' :: afterE =>
                      match NumParse.Model.parseFloatExpPart afterE with
                      | Except.error k => Except.error k
                      | Except.ok (expVal, afterExp) =>
                        if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                        else Except.error NumParseErrorKind.trailingChars
                    | 'E' :: afterE =>
                      match NumParse.Model.parseFloatExpPart afterE with
                      | Except.error k => Except.error k
                      | Except.ok (expVal, afterExp) =>
                        if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                        else Except.error NumParseErrorKind.trailingChars
                    | [] => Except.ok (NumParse.Model.evalFloat neg mantissa (-Int.ofNat fracCount))
                    | _ :: _ => Except.error NumParseErrorKind.trailingChars
                else Except.error NumParseErrorKind.invalidSyntax
              | [] => Except.error NumParseErrorKind.invalidSyntax
            | 'e' :: afterE =>
              match NumParse.Model.parseFloatExpPart afterE with
              | Except.error k => Except.error k
              | Except.ok (expVal, afterExp) =>
                if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg intVal expVal)
                else Except.error NumParseErrorKind.trailingChars
            | 'E' :: afterE =>
              match NumParse.Model.parseFloatExpPart afterE with
              | Except.error k => Except.error k
              | Except.ok (expVal, afterExp) =>
                if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg intVal expVal)
                else Except.error NumParseErrorKind.trailingChars
            | _ => Except.error NumParseErrorKind.invalidSyntax) = Except.ok f →
      (∃ b0 br, body = b0 :: br ∧ (b0 = 'i' ∨ b0 = 'n' ∨ isAsciiDigit b0 = true)) ∧
      (∀ c ∈ body, isFloatModelChar c = true) ∧
      hasDatePrefix body = false ∧
      (body = ['i', 'n', 'f'] ∨ body = ['n', 'a', 'n'] ∨
        (body.contains '.' || body.contains 'e' || body.contains 'E') = true) := by
    intro body neg hb
    split at hb
    · rename_i rest
      cases rest with
      | nil =>
        refine ⟨⟨'i', ['n', 'f'], rfl, Or.inl rfl⟩, fun c hc => ?_, ?_, Or.inl rfl⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl <;> rfl
        · decide
      | cons _ _ => simp at hb
    · rename_i rest
      cases rest with
      | nil =>
        refine ⟨⟨'n', ['a', 'n'], rfl, Or.inr (Or.inl rfl)⟩, fun c hc => ?_, ?_, Or.inr (Or.inl rfl)⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl <;> rfl
        · decide
      | cons _ _ => simp at hb
    · cases hip : NumParse.Model.parseFloatIntPart body with
      | error => rw [hip] at hb; cases hb
      | ok res =>
        rcases res with ⟨intVal, afterInt⟩
        rw [hip] at hb
        dsimp only at hb
        obtain ⟨pfx, d0, ptail, hbody_eq, hpfx_eq, hd0, hpfx_ch, _h_after⟩ := parseFloatIntPart_props body intVal afterInt hip
        have hpfx_fmc : ∀ c ∈ pfx, isFloatModelChar c = true := by
          intro c hc
          rcases hpfx_ch c hc with rfl | hd
          · rfl
          · simp [isFloatModelChar, hd]
        have hhead : ∃ b0 br, body = b0 :: br ∧ (b0 = 'i' ∨ b0 = 'n' ∨ isAsciiDigit b0 = true) := by
          refine ⟨d0, ptail ++ afterInt, ?_, Or.inr (Or.inr hd0)⟩
          rw [hbody_eq, hpfx_eq, List.cons_append]
        split at hb
        · rename_i afterDot
          refine ⟨hhead, fun ch hc => ?_, ?_, Or.inr (Or.inr ?_)⟩
          · rw [hbody_eq] at hc
            rcases List.mem_append.mp hc with hc1 | hc2
            · exact hpfx_fmc ch hc1
            · rcases List.mem_cons.mp hc2 with rfl | hc3
              · rfl
              · cases afterDot with
                | nil => cases hb
                | cons c1 r1 =>
                  by_cases h_us : c1 = '_'
                  · subst h_us; cases hb
                  · split at hb
                    · cases hb
                    · rename_i c1' r1' hne heq_ad
                      injection heq_ad with hc_eq hr_eq
                      subst hc_eq; subst hr_eq
                      by_cases hd1 : NumParse.Model.isDecDigit c1 = true
                      · simp only [hd1, ↓reduceIte] at hb
                        cases hcf : NumParse.Model.consumeDecFloatDigits (intVal * 10 + (c1.toNat - '0'.toNat)) 1 r1 with
                        | error => rw [hcf] at hb; cases hb
                        | ok res2 =>
                          rcases res2 with ⟨mantissa, fracCount, afterFrac⟩
                          rw [hcf] at hb
                          dsimp only at hb
                          obtain ⟨fpfx, hr1, hfpfx, _⟩ := consumeDecFloatDigits_props _ _ _ _ _ _ hcf
                          rcases List.mem_cons.mp hc3 with rfl | hc4
                          · have : isAsciiDigit ch = true := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd1
                            simp [isFloatModelChar, this]
                          · rw [hr1] at hc4
                            rcases List.mem_append.mp hc4 with hfp | haf
                            · rcases hfpfx ch hfp with rfl | hd'
                              · rfl
                              · simp [isFloatModelChar, hd']
                            · exact parseFloatAfterFrac_props afterFrac neg mantissa fracCount f hb ch haf
                      · simp [hd1] at hb
                    · cases hb
          · rw [hbody_eq]
            exact hasDatePrefix_false_of_digit_or_us_before_sep pfx '.' afterDot hpfx_ch (Or.inl rfl)
          · have hmem_dot : '.' ∈ body := by rw [hbody_eq]; simp
            simp only [List.contains_iff_mem, Bool.or_eq_true]
            exact Or.inl (Or.inl hmem_dot)
        · rename_i afterE
          refine ⟨hhead, fun c hc => ?_, ?_, Or.inr (Or.inr ?_)⟩
          · rw [hbody_eq] at hc
            rcases List.mem_append.mp hc with hc1 | hc2
            · exact hpfx_fmc c hc1
            · rcases List.mem_cons.mp hc2 with rfl | hc3
              · rfl
              · exact parseFloatExpSuffix_props afterE _ f hb c hc3
          · rw [hbody_eq]
            exact hasDatePrefix_false_of_digit_or_us_before_sep pfx 'e' afterE hpfx_ch (Or.inr (Or.inl rfl))
          · have hmem_e : 'e' ∈ body := by rw [hbody_eq]; simp
            simp only [List.contains_iff_mem, Bool.or_eq_true]
            exact Or.inl (Or.inr hmem_e)
        · rename_i afterE
          refine ⟨hhead, fun c hc => ?_, ?_, Or.inr (Or.inr ?_)⟩
          · rw [hbody_eq] at hc
            rcases List.mem_append.mp hc with hc1 | hc2
            · exact hpfx_fmc c hc1
            · rcases List.mem_cons.mp hc2 with rfl | hc3
              · rfl
              · exact parseFloatExpSuffix_props afterE _ f hb c hc3
          · rw [hbody_eq]
            exact hasDatePrefix_false_of_digit_or_us_before_sep pfx 'E' afterE hpfx_ch (Or.inr (Or.inr rfl))
          · have hmem_E : 'E' ∈ body := by rw [hbody_eq]; simp
            simp only [List.contains_iff_mem, Bool.or_eq_true]
            exact Or.inr hmem_E
        · cases hb
  cases cs with
  | nil => simp [NumParse.Model.parseFloatModelChars] at h
  | cons c0 r0 =>
    by_cases hp : c0 = '+'
    · subst hp
      simp only [NumParse.Model.parseFloatModelChars] at h
      obtain ⟨⟨b0, br, hr0, hb0⟩, hfmc, _, hkind⟩ := hbody r0 false h
      have hfmc_all : ∀ c ∈ '+' :: r0, isFloatModelChar c = true := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · rfl
        · exact hfmc c hc'
      have hnd : hasDatePrefix ('+' :: r0) = false := by
        unfold hasDatePrefix
        split
        · rename_i heq; injection heq with h1 _; subst h1; rfl
        · rfl
      refine ⟨⟨'+', r0, rfl, Or.inl rfl⟩, hfmc_all, hnd, hnot_time _ hfmc_all, ?_⟩
      rcases hkind with rfl | rfl | hsep
      · decide
      · decide
      · apply hcand_of_sep _ hfmc_all
        simp only [List.contains_iff_mem, Bool.or_eq_true] at hsep ⊢
        rcases hsep with (h1 | h2) | h3
        · exact Or.inl (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inl (Or.inr (List.mem_cons_of_mem _ h2))
        · exact Or.inr (List.mem_cons_of_mem _ h3)
    · by_cases hm : c0 = '-'
      · subst hm
        simp only [NumParse.Model.parseFloatModelChars] at h
        obtain ⟨⟨b0, br, hr0, hb0⟩, hfmc, _, hkind⟩ := hbody r0 true h
        have hfmc_all : ∀ c ∈ '-' :: r0, isFloatModelChar c = true := by
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc'
          · rfl
          · exact hfmc c hc'
        have hnd : hasDatePrefix ('-' :: r0) = false := by
          unfold hasDatePrefix
          split
          · rename_i heq; injection heq with h1 _; subst h1; rfl
          · rfl
        refine ⟨⟨'-', r0, rfl, Or.inr (Or.inl rfl)⟩, hfmc_all, hnd, hnot_time _ hfmc_all, ?_⟩
        rcases hkind with rfl | rfl | hsep
        · decide
        · decide
        · apply hcand_of_sep _ hfmc_all
          simp only [List.contains_iff_mem, Bool.or_eq_true] at hsep ⊢
          rcases hsep with (h1 | h2) | h3
          · exact Or.inl (Or.inl (List.mem_cons_of_mem _ h1))
          · exact Or.inl (Or.inr (List.mem_cons_of_mem _ h2))
          · exact Or.inr (List.mem_cons_of_mem _ h3)
      · unfold NumParse.Model.parseFloatModelChars at h
        dsimp only at h
        have hfst : (match c0 :: r0 with
            | '+' :: rest => (false, rest)
            | '-' :: rest => (true, rest)
            | _ => (false, c0 :: r0)).fst = false := by
          split
          · rename_i _ heq_c0; injection heq_c0 with h1 _; exact absurd h1 hp
          · rename_i _ heq_c0; injection heq_c0 with h1 _; exact absurd h1 hm
          · rfl
        have hsnd : (match c0 :: r0 with
            | '+' :: rest => (false, rest)
            | '-' :: rest => (true, rest)
            | _ => (false, c0 :: r0)).snd = c0 :: r0 := by
          split
          · rename_i _ heq_c0; injection heq_c0 with h1 _; exact absurd h1 hp
          · rename_i _ heq_c0; injection heq_c0 with h1 _; exact absurd h1 hm
          · rfl
        erw [hfst, hsnd] at h
        obtain ⟨⟨b0, br, hr0, hb0⟩, hfmc, hnd, hkind⟩ := hbody (c0 :: r0) false h
        have hhead : c0 = '+' ∨ c0 = '-' ∨ c0 = 'i' ∨ c0 = 'n' ∨ isAsciiDigit c0 = true := by
          injection hr0 with h1 _; subst h1
          rcases hb0 with rfl | rfl | hd
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hd)))
        refine ⟨⟨c0, r0, rfl, hhead⟩, hfmc, hnd, hnot_time _ hfmc, ?_⟩
        rcases hkind with h1 | h2 | hsep
        · rw [h1]; decide
        · rw [h2]; decide
        · exact hcand_of_sep _ hfmc hsep

private theorem consumeIntDigits_extra (b : NumParse.Model.NumBase) (acc : Nat)
    (cs : List Char) (n : Nat) (h : NumParse.Model.consumeIntDigits b acc cs = .ok n) :
    ∀ c ∈ cs, c ≠ '.' ∧ c ≠ '-' := by
  induction n0 : cs.length using Nat.strongRecOn generalizing cs acc with
  | ind len ih =>
    intro c hc
    cases cs with
    | nil => cases hc
    | cons c0 rest =>
      by_cases hu : c0 = '_'
      · subst hu
        cases rest with
        | nil => simp [NumParse.Model.consumeIntDigits] at h
        | cons c1 cs1 =>
          simp only [NumParse.Model.consumeIntDigits] at h
          cases hc with
          | head => exact ⟨by decide, by decide⟩
          | tail _ hc' =>
            cases hdv : NumParse.Model.digitVal? b c1 with
            | none => rw [hdv] at h; cases h
            | some d =>
              rw [hdv] at h
              dsimp only at h
              have hc1 : c1 ≠ '.' ∧ c1 ≠ '-' := by
                cases b <;> simp [NumParse.Model.digitVal?] at hdv <;>
                  constructor <;> intro heq <;> subst heq <;> simp at hdv
              rcases List.mem_cons.mp hc' with rfl | hc''
              · exact hc1
              · exact ih cs1.length (by simp [← n0]; omega) (acc * b.radix + d) cs1 h rfl c hc''
      · unfold NumParse.Model.consumeIntDigits at h
        split at h
        · rename_i heq; cases heq
        · rename_i _ _ heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i c0' rest' _ _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at h
          cases hdv : NumParse.Model.digitVal? b c0 with
          | none => rw [hdv] at h; cases h
          | some d =>
            rw [hdv] at h
            dsimp only at h
            rcases List.mem_cons.mp hc with rfl | hc'
            · cases b <;> simp [NumParse.Model.digitVal?] at hdv <;>
                constructor <;> intro heq <;> subst heq <;> simp at hdv
            · exact ih rest.length (by simp [← n0]) (acc * b.radix + d) rest h rfl c hc'

private theorem parseDecAfterSign_extra (neg : Bool) (cs : List Char) (m : Int)
    (h : NumParse.Model.parseDecAfterSign neg cs = .ok m) :
    ∀ c ∈ cs, c ≠ '.' ∧ c ≠ '-' := by
  cases cs with
  | nil => simp [NumParse.Model.parseDecAfterSign] at h
  | cons c0 rest =>
    cases h0 : c0 == '_' with
    | true =>
      have hc0 : c0 = '_' := beq_iff_eq.mp h0
      subst hc0; simp [NumParse.Model.parseDecAfterSign] at h
    | false =>
      cases hzero : c0 == '0' with
      | true =>
        have hc0 : c0 = '0' := beq_iff_eq.mp hzero
        subst hc0
        cases rest with
        | nil =>
          intro c hc
          rcases List.mem_singleton.mp hc with rfl
          exact ⟨by decide, by decide⟩
        | cons c1 r1 =>
          by_cases hd1 : NumParse.Model.isDecDigit c1 = true
          · simp [NumParse.Model.parseDecAfterSign, hd1] at h
          · by_cases hu1 : c1 = '_'
            · subst hu1
              cases r1 with
              | nil => simp [NumParse.Model.parseDecAfterSign, hd1] at h
              | cons c2 tail =>
                by_cases hd2 : NumParse.Model.isDecDigit c2 = true <;>
                  simp [NumParse.Model.parseDecAfterSign, hd1, hd2] at h
            · simp [NumParse.Model.parseDecAfterSign, hd1, hu1] at h
      | false =>
        have hne0 : c0 ≠ '0' := fun he => by rw [he] at hzero; contradiction
        have hne_u : c0 ≠ '_' := fun he => by rw [he] at h0; contradiction
        unfold NumParse.Model.parseDecAfterSign at h
        split at h
        · contradiction
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_u
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne0
        · rename_i c0' rest' _ _ _ heq
          injection heq with h1 h2; subst h1; subst h2
          cases hdv : NumParse.Model.digitVal? .dec c0 with
          | none => rw [hdv] at h; cases h
          | some d =>
            rw [hdv] at h
            dsimp only at h
            cases hn : NumParse.Model.consumeIntDigits .dec d rest with
            | error => rw [hn] at h; cases h
            | ok n =>
              intro c hc
              rcases List.mem_cons.mp hc with rfl | hc'
              · simp [NumParse.Model.digitVal?] at hdv
                constructor <;> intro heq <;> subst heq <;> simp at hdv
              · exact consumeIntDigits_extra .dec d rest n hn c hc'

private theorem parseIntModelChars_extra (cs : List Char) (m : Int)
    (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    (∀ c ∈ cs, c ≠ '.') ∧ (∀ c0 r0, cs = c0 :: r0 → ∀ c ∈ r0, c ≠ '-') := by
  unfold NumParse.Model.parseIntModelChars at h
  split at h
  · cases h
  · rename_i _ b rest
    split at h
    · cases h
    · have hd := parseDecAfterSign_extra false ('0' :: b :: rest) m h
      refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
      · rcases List.mem_cons.mp hc with rfl | hc'
        · decide
        · exact (hd c hc').1
      · injection hcr with _ hr; subst hr
        exact (hd c hc).2
  · rename_i _ b rest
    split at h
    · cases h
    · have hd := parseDecAfterSign_extra true ('0' :: b :: rest) m h
      refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
      · rcases List.mem_cons.mp hc with rfl | hc'
        · decide
        · exact (hd c hc').1
      · injection hcr with _ hr; subst hr
        exact (hd c hc).2
  · rename_i _ rest _
    have hd := parseDecAfterSign_extra false rest m h
    refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
    · rcases List.mem_cons.mp hc with rfl | hc'
      · decide
      · exact (hd c hc').1
    · injection hcr with _ hr; subst hr
      exact (hd c hc).2
  · rename_i _ rest _
    have hd := parseDecAfterSign_extra true rest m h
    refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
    · rcases List.mem_cons.mp hc with rfl | hc'
      · decide
      · exact (hd c hc').1
    · injection hcr with _ hr; subst hr
      exact (hd c hc).2
  · rename_i _ b rest
    cases hbp : NumParse.Model.basePrefix? b with
    | none =>
      rw [hbp] at h
      dsimp only at h
      have hd := parseDecAfterSign_extra false ('0' :: b :: rest) m h
      refine ⟨fun c hc => (hd c hc).1, fun c0 r0 hcr c hc => ?_⟩
      injection hcr with _ hr; subst hr
      exact (hd c (List.mem_cons_of_mem _ hc)).2
    | some base =>
      rw [hbp] at h
      dsimp only at h
      cases rest with
      | nil => cases h
      | cons c1 cs1 =>
        by_cases hu : c1 = '_'
        · subst hu; cases h
        · split at h
          · cases h
          · cases h
          · rename_i c1' cs1' _ _ heq
            injection heq with h1 h2; subst h1; subst h2
            cases hdv : NumParse.Model.digitVal? base c1 with
            | none => rw [hdv] at h; cases h
            | some d =>
              rw [hdv] at h
              dsimp only at h
              cases hn : NumParse.Model.consumeIntDigits base d cs1 with
              | error => rw [hn] at h; cases h
              | ok n =>
                have hex := consumeIntDigits_extra base d cs1 n hn
                have hc1_ne : c1 ≠ '.' ∧ c1 ≠ '-' := by
                  cases base <;> simp [NumParse.Model.digitVal?] at hdv <;>
                    constructor <;> intro heq <;> subst heq <;> simp at hdv
                have hb_ne : b ≠ '.' ∧ b ≠ '-' := by
                  constructor <;> intro heq <;> subst heq <;> cases hbp
                refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
                · rcases List.mem_cons.mp hc with rfl | hc
                  · decide
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact hb_ne.1
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact hc1_ne.1
                  · exact (hex c hc).1
                · injection hcr with _ hr; subst hr
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact hb_ne.2
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact hc1_ne.2
                  · exact (hex c hc).2
  · have hd := parseDecAfterSign_extra false cs m h
    refine ⟨fun c hc => (hd c hc).1, fun c0 r0 hcr c hc => ?_⟩
    rw [hcr] at hd
    exact (hd c (List.mem_cons_of_mem _ hc)).2

private theorem hasDatePrefix_imp (cs : List Char) (h : hasDatePrefix cs = true) :
    ∃ y1 y2 y3 y4 m1 m2 d1 d2 rest,
      cs = y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: rest := by
  unfold hasDatePrefix at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

private theorem hasTimePrefix_imp (cs : List Char) (h : hasTimePrefix cs = true) :
    ':' ∈ cs := by
  unfold hasTimePrefix at h
  split at h
  · simp
  · cases h

private theorem parseIntModelChars_no_datePrefix (cs : List Char) (m : Int)
    (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    hasDatePrefix cs = false ∧ hasTimePrefix cs = false := by
  obtain ⟨⟨c0, rest, hcs, _, _⟩, hno_col⟩ := parseIntModelChars_props cs m h
  obtain ⟨_, hno_dash⟩ := parseIntModelChars_extra cs m h
  refine ⟨?_, ?_⟩
  · cases hdp : hasDatePrefix cs
    · rfl
    · obtain ⟨y1, y2, y3, y4, m1, m2, d1, d2, rest', heq⟩ := hasDatePrefix_imp cs hdp
      have hcs' : c0 :: rest = y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: rest' := by
        rw [← hcs, heq]
      injection hcs' with _ hrest
      have hdash : '-' ∈ rest := by rw [hrest]; simp
      exact absurd rfl (hno_dash c0 rest hcs '-' hdash)
  · cases htp : hasTimePrefix cs
    · rfl
    · exact absurd rfl (hno_col ':' (hasTimePrefix_imp cs htp))

/-- Internal TOML scalar round-trip lemma `isValidIntLex_classifyScalarToken`. -/
theorem isValidIntLex_classifyScalarToken (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (s : String) (n : Int64) (h : isValidIntLex s n = true) :
    classifyScalarToken numApi s = .ok (.int n) ∧
    (s.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
    ∃ c0 cs0, s.toList = c0 :: cs0 ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
  simp only [isValidIntLex, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨hchars, hno_up⟩, hno_exp⟩, hbeq⟩
  have hn_eq : (match NumParse.Model.parseInt64Model s with | .ok m => m == n | .error _ => false) = true :=
    hbeq
  have hp_model : NumParse.Model.parseInt64Model s = .ok n := by
    cases hp : NumParse.Model.parseInt64Model s with
    | error => rw [hp] at hn_eq; cases hn_eq
    | ok m =>
      rw [hp] at hn_eq
      have hmn : m = n := by simpa using hn_eq
      subst hmn; rfl
  have hm_chars : ∃ m : Int, NumParse.Model.parseIntModelChars s.toList = .ok m := by
    unfold NumParse.Model.parseInt64Model NumParse.Model.parseIntModel at hp_model
    cases hc : NumParse.Model.parseIntModelChars s.toList with
    | error => rw [hc] at hp_model; cases hp_model
    | ok m => exact ⟨m, rfl⟩
  rcases hm_chars with ⟨m, hm⟩
  obtain ⟨⟨c0, rest, hlist, hc0, hc1⟩, hno_col⟩ := parseIntModelChars_props s.toList m hm
  obtain ⟨hno_dot, _⟩ := parseIntModelChars_extra s.toList m hm
  obtain ⟨hnd, hnt⟩ := parseIntModelChars_no_datePrefix s.toList m hm
  have hnot_empty : s.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    have hnil : s.toList = [] := by
      have : s = "" := by simpa using he
      subst this; rfl
    rw [hnil] at hlist; cases hlist
  have hnot_true : s ≠ "true" := by
    intro heq; subst heq
    rcases hc0 with rfl | rfl | hdig
    · cases hlist
    · cases hlist
    · injection hlist with h0 _; subst h0; revert hdig; decide
  have hnot_false : s ≠ "false" := by
    intro heq; subst heq
    rcases hc0 with rfl | rfl | hdig
    · cases hlist
    · cases hlist
    · injection hlist with h0 _; subst h0; revert hdig; decide
  have hnot_colon : ¬(':' ∈ s.toList) := fun hc => hno_col ':' hc rfl
  have hnot_dt : parseDateTimeToken s = none := by
    simp [parseDateTimeToken, hnd, hnt, hnot_colon]
  have hnot_spec : (s == "inf" || s == "+inf" || s == "-inf" || s == "nan" || s == "+nan" || s == "-nan") = false := by
    have hs_list : ∀ t : String, s = t → s.toList = t.toList := fun t ht => by subst ht; rfl
    have hc_head : ∀ (t : String) (d : Char) (td : List Char), t.toList = d :: td →
        (d ≠ '+' ∧ d ≠ '-' ∧ isAsciiDigit d = false) → s ≠ t := by
      intro t d td ht hd hs_eq
      have h' := hs_list t hs_eq
      rw [hlist, ht] at h'
      injection h' with hd0 _
      subst hd0
      rcases hc0 with rfl | rfl | hdig
      · exact hd.1 rfl
      · exact hd.2.1 rfl
      · rw [hdig] at hd; cases hd.2.2
    have hc_snd : ∀ (t : String) (s0 s1 : Char) (td : List Char), t.toList = s0 :: s1 :: td →
        (s0 = '+' ∨ s0 = '-') → isAsciiDigit s1 = false → s ≠ t := by
      intro t s0 s1 td ht hs0 hs1 hs_eq
      have h' := hs_list t hs_eq
      rw [hlist, ht] at h'
      injection h' with hc0_eq hr_eq
      rcases hc0 with rfl | rfl | hdig
      · have hd1 := hc1 s1 td (Or.inl rfl) hr_eq
        rw [hd1] at hs1; cases hs1
      · have hd1 := hc1 s1 td (Or.inr rfl) hr_eq
        rw [hd1] at hs1; cases hs1
      · rw [hc0_eq] at hdig
        rcases hs0 with rfl | rfl <;> cases hdig
    have hni : s ≠ "inf" := hc_head "inf" 'i' ['n', 'f'] rfl (by decide)
    have hnn : s ≠ "nan" := hc_head "nan" 'n' ['a', 'n'] rfl (by decide)
    have hnpi : s ≠ "+inf" := hc_snd "+inf" '+' 'i' ['n', 'f'] rfl (Or.inl rfl) (by decide)
    have hnmi : s ≠ "-inf" := hc_snd "-inf" '-' 'i' ['n', 'f'] rfl (Or.inr rfl) (by decide)
    have hnpn : s ≠ "+nan" := hc_snd "+nan" '+' 'n' ['a', 'n'] rfl (Or.inl rfl) (by decide)
    have hnmn : s ≠ "-nan" := hc_snd "-nan" '-' 'n' ['a', 'n'] rfl (Or.inr rfl) (by decide)
    simp [hni, hnpi, hnmi, hnn, hnpn, hnmn]
  have hndot : ¬('.' ∈ s.toList) := fun hmem => hno_dot '.' hmem rfl
  have hnot_float_cand : isFloatTokenCandidate s = false := by
    unfold isFloatTokenCandidate
    rw [hnot_spec, Bool.false_or]
    split at hno_exp
    · rename_i hhex
      simp [hhex]
    · simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true'] at hno_exp
      have hne1 : ¬('e' ∈ s.toList) := by
        have h1 : s.contains 'e' = false := hno_exp.1
        simpa [String.contains_char_eq] using h1
      have hne2 : ¬('E' ∈ s.toList) := by
        have h2 : s.contains 'E' = false := hno_exp.2
        simpa [String.contains_char_eq] using h2
      simp [hndot, hne1, hne2]
  have hcls : classifyScalarToken numApi s = .ok (.int n) := by
    simp [classifyScalarToken, hasUppercaseBasePrefix, hnot_empty, hnot_true, hnot_false, hnot_dt,
      hnot_float_cand, hchars]
    rw [hInt s n hp_model]
  refine ⟨hcls, ?_, c0, rest, hlist, ?_⟩
  · rw [List.all_eq_true] at hno_up ⊢
    intro c hc
    have h1 := hno_up c hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h1
    have hws : c.isWhitespace = false := h1.1.1.1.1.1.1
    have hnl : c ≠ '\n' := by
      intro heq; subst heq
      exact absurd (by decide : ('\n').isWhitespace = true) (by simp [hws])
    have hcr : c ≠ '\r' := by
      intro heq; subst heq
      exact absurd (by decide : ('\r').isWhitespace = true) (by simp [hws])
    have hud : isUnquotedDelim c = false :=
      not_unquotedDelim_of_not_ws c hws
        (bne_iff_ne.mpr h1.1.1.1.1.1.2)
        (bne_iff_ne.mpr h1.1.1.1.1.2)
        (bne_iff_ne.mpr h1.1.1.1.2)
        (bne_iff_ne.mpr h1.1.1.2)
    simp [h1.2, hcr, hnl, hud]
  · rcases hc0 with rfl | rfl | hdig
    · decide
    · decide
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide

/-- Two `Float` values with identical IEEE 754 bit patterns are equal. -/
theorem float_eq_of_toBits_eq {a b : Float} (h : a.toBits = b.toBits) : a = b := by
  cases a with | ofModel am =>
  cases b with | ofModel bm =>
  cases am with | mk ab _ =>
  cases bm with | mk bb _ =>
  cases h
  rfl

private theorem float_beq_props (a b : Float) (h : (a == b) = true) :
    (b == a) = true ∧ a.isNaN = false ∧ b.isNaN = false := by
  have hbeq : (a.toModel.unpack.compare b.toModel.unpack == some .eq) = true := h
  change (b.toModel.unpack.compare a.toModel.unpack == some .eq) = true ∧
    a.toModel.unpack.isNaN = false ∧ b.toModel.unpack.isNaN = false
  cases hu1 : a.toModel.unpack with
  | notANumber => simp [hu1, Float.Model.UnpackedFloat.compare] at hbeq
  | infinity s1 =>
    cases s1 <;> cases hu2 : b.toModel.unpack with
    | notANumber => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | infinity s2 => cases s2 <;> simp_all [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN]
    | zero _ => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | finite _ _ _ _ => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
  | zero s1 =>
    cases hu2 : b.toModel.unpack with
    | notANumber => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | infinity s2 => cases s2 <;> simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | zero _ => simp [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN]
    | finite s2 _ _ _ => cases s2 <;> simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
  | finite s1 m1 e1 p1 =>
    cases s1 <;> cases hu2 : b.toModel.unpack with
    | notANumber => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | infinity s2 => cases s2 <;> simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | zero _ => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | finite s2 m2 e2 p2 =>
      cases s2 <;> simp_all [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] <;>
        exact ⟨by omega, by omega⟩

private theorem float_beq_refl_of_nonNaN (a : Float) (h : a.isNaN = false) : (a == a) = true := by
  exact (NumParse.Model.floatEquiv_nonNaN_iff_beq (by simp [h]) (by simp [h])).mp (NumParse.Model.floatEquiv_refl a)

/-- Any string satisfying `FloatFormatSpec f s` is a valid TOML float lexeme for `f`. -/
theorem floatFormatSpec_isValidFloatLex (f : Float) (s : String)
    (hs : NumParse.Model.FloatFormatSpec f s) :
    isValidFloatLex s f = true := by
  simp only [NumParse.Model.FloatFormatSpec] at hs
  by_cases hnan : f.isNaN = true
  · simp only [hnan, ite_true] at hs
    subst hs
    have hp : NumParse.Model.parseFloatModel "nan" = .ok Float.nan := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    have hnan_lit : Float.nan.isNaN = true := by decide
    simp [isValidFloatLex, hp, hnan, hnan_lit]
    decide
  · have hnan_f : f.isNaN = false := Bool.eq_false_iff.mpr hnan
    simp only [hnan] at hs
    by_cases hinf : (f == Float.inf) = true
    · simp only [hinf, ite_true] at hs
      subst hs
      have hp : NumParse.Model.parseFloatModel "inf" = .ok Float.inf := by
        simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
      have hsym : (Float.inf == f) = true := (float_beq_props f Float.inf hinf).1
      simp [isValidFloatLex, hp, hsym]
      decide
    · simp only [hinf] at hs
      by_cases hninf : (f == -Float.inf) = true
      · simp only [hninf, ite_true] at hs
        subst hs
        have hp : NumParse.Model.parseFloatModel "-inf" = .ok (-Float.inf) := by
          simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
        have hsym : (-Float.inf == f) = true := (float_beq_props f (-Float.inf) hninf).1
        simp [isValidFloatLex, hp, hsym]
        decide
      · simp only [hninf] at hs
        rcases hs with ⟨_, hsep, hmatch⟩
        cases hp : NumParse.Model.parseFloatModel s with
        | error => rw [hp] at hmatch; cases hmatch
        | ok y =>
          rw [hp] at hmatch
          have hy_eq : y = f := float_eq_of_toBits_eq hmatch
          subst hy_eq
          have hp_chars : NumParse.Model.parseFloatModelChars s.toList = .ok y := by
            simpa [NumParse.Model.parseFloatModel] using hp
          obtain ⟨_, hfmc, _, _, _⟩ := parseFloatModelChars_props s.toList y hp_chars
          have hnoTerm : (s.toList.all fun c => !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c) = true := by
            rw [List.all_eq_true]
            intro c hc
            exact (isFloatModelChar_props c (hfmc c hc)).2.2.2.1
          have hmark : (s.contains '.' || s.contains 'e' || s.contains 'E' ||
              s == "inf" || s == "+inf" || s == "-inf" || s == "nan" || s == "+nan" || s == "-nan") = true := by
            rcases hsep with h1 | h1 | h1 <;>
              simp only [String.contains_char_eq, decide_eq_true_eq] at h1 <;>
              simp [h1]
          have hbeq : (y == y) = true := float_beq_refl_of_nonNaN y hnan_f
          simp only [isValidFloatLex]
          rw [hmark, hnoTerm, hp]
          simp [hbeq]

/-- Internal TOML scalar round-trip lemma `isValidFloatLex_classifyScalarToken`. -/
theorem isValidFloatLex_classifyScalarToken (numApi : NumParseApi)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (s : String) (f : Float) (h : isValidFloatLex s f = true) :
    ∃ g, classifyScalarToken numApi s = .ok (.float g) ∧
      TomlEquiv (.float f) (.float g) ∧
      (s.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
      ∃ c0 cs0, s.toList = c0 :: cs0 ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
  simp only [isValidFloatLex, Bool.and_eq_true] at h
  rcases h with ⟨⟨_, _⟩, hmatch⟩
  cases hp : NumParse.Model.parseFloatModel s with
  | error => rw [hp] at hmatch; cases hmatch
  | ok g =>
    rw [hp] at hmatch
    have hp_chars : NumParse.Model.parseFloatModelChars s.toList = .ok g := by
      simpa [NumParse.Model.parseFloatModel] using hp
    obtain ⟨⟨c0, rest, hlist, hc0⟩, hfmc, hnd, hnt, hcand⟩ :=
      parseFloatModelChars_props s.toList g hp_chars
    have hnot_empty : s.isEmpty = false := by
      rw [Bool.eq_false_iff]
      intro he
      have hnil : s.toList = [] := by
        have : s = "" := by simpa using he
        subst this; rfl
      rw [hnil] at hlist; cases hlist
    have hnot_true : s ≠ "true" := by
      intro heq; subst heq
      rcases hc0 with rfl | rfl | rfl | rfl | hdig
      · cases hlist
      · cases hlist
      · cases hlist
      · cases hlist
      · injection hlist with h0 _; subst h0; revert hdig; decide
    have hnot_false : s ≠ "false" := by
      intro heq; subst heq
      rcases hc0 with rfl | rfl | rfl | rfl | hdig
      · cases hlist
      · cases hlist
      · cases hlist
      · cases hlist
      · injection hlist with h0 _; subst h0; revert hdig; decide
    have hnot_colon : ¬(':' ∈ s.toList) := by
      intro hc
      have := hfmc ':' hc
      cases this
    have hnot_dt : parseDateTimeToken s = none := by
      simp [parseDateTimeToken, hnd, hnt, hnot_colon]
    obtain ⟨g', hg', hbit⟩ := hFloat s g hp
    have hcls : classifyScalarToken numApi s = .ok (.float g') := by
      rw [String.ofList_toList] at hcand
      simp [classifyScalarToken, hnot_empty, hnot_true, hnot_false, hnot_dt, hcand, hg']
    have heq_f : TomlEquiv (.float f) (.float g') := by
      simp only [TomlEquiv]
      have heq_fg : NumParse.Model.FloatEquiv f g := by
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hmatch
        rcases hmatch with ⟨hg_nan, hf_nan⟩ | hgf
        · exact Or.inl ⟨hf_nan, hg_nan⟩
        · obtain ⟨hfg, hna_g, hna_f⟩ := float_beq_props g f hgf
          exact (NumParse.Model.floatEquiv_nonNaN_iff_beq (by simp [hna_f]) (by simp [hna_g])).mpr hfg
      exact NumParse.Model.floatEquiv_trans heq_fg
        (NumParse.Model.floatEquiv_symm (NumParse.Model.floatBitMatch_implies_floatEquiv hbit))
    refine ⟨g', hcls, heq_f, ?_, c0, rest, hlist, ?_⟩
    · rw [List.all_eq_true]
      intro c hc
      exact (isFloatModelChar_props c (hfmc c hc)).2.2.2.2
    · rcases hc0 with rfl | rfl | rfl | rfl | hdig
      · decide
      · decide
      · decide
      · decide
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide

/-- Internal TOML scalar round-trip lemma `canonicalFloat_isValidFloatLex`. -/
theorem canonicalFloat_isValidFloatLex (f : Float) :
    (f.isNaN = true → isValidFloatLex "nan" f = true) ∧
    ((f == Float.inf) = true → isValidFloatLex "inf" f = true) ∧
    ((f == -Float.inf) = true → isValidFloatLex "-inf" f = true) ∧
    (f.toBits = (0.0 : Float).toBits → isValidFloatLex "0.0" f = true) ∧
    (f.toBits = (-0.0 : Float).toBits → isValidFloatLex "-0.0" f = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnan
    have hp : NumParse.Model.parseFloatModel "nan" = .ok Float.nan := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    have hnan_lit : Float.nan.isNaN = true := by decide
    simp [isValidFloatLex, hp, hnan, hnan_lit]
    decide
  · intro hinf
    have hp : NumParse.Model.parseFloatModel "inf" = .ok Float.inf := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    have hsym := (float_beq_props f Float.inf hinf).1
    simp [isValidFloatLex, hp, hsym]
    decide
  · intro hninf
    have hp : NumParse.Model.parseFloatModel "-inf" = .ok (-Float.inf) := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    have hsym := (float_beq_props f (-Float.inf) hninf).1
    simp [isValidFloatLex, hp, hsym]
    decide
  · intro hbits
    have hfeq : f = (0.0 : Float) := float_eq_of_toBits_eq hbits
    subst hfeq
    have hp : NumParse.Model.parseFloatModel "0.0" = .ok (0.0 : Float) := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars,
        NumParse.Model.parseFloatIntPart, NumParse.Model.consumeDecFloatDigits,
        NumParse.Model.isDecDigit, NumParse.Model.evalFloat_zero]
    have h0_eq : ((0.0 : Float) == (0.0 : Float)) = true := by decide
    simp [isValidFloatLex, hp, h0_eq]
    decide
  · intro hbits
    have hfeq : f = (-0.0 : Float) := float_eq_of_toBits_eq hbits
    subst hfeq
    have hp : NumParse.Model.parseFloatModel "-0.0" = .ok (-0.0 : Float) := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars,
        NumParse.Model.parseFloatIntPart, NumParse.Model.consumeDecFloatDigits,
        NumParse.Model.isDecDigit, NumParse.Model.evalFloat_neg_zero]
    have h0_eq : ((-0.0 : Float) == (-0.0 : Float)) = true := by decide
    simp [isValidFloatLex, hp, h0_eq]
    decide


end LeanSwe.Toml.Proofs
