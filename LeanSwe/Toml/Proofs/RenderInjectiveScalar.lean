import LeanSwe.Toml.Proofs.RenderInjectiveLex

/-!
# Unquoted Scalar Token & Value Injectivity for `Toml.Model.render`

Proves `Impl`-independent token splitting (`splitModelUnquoted`) and value equivalence
(`TomlEquiv`) for booleans, integers, IEEE-754 floats, and RFC 3339 datetimes.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Check whether `c` terminates an unquoted TOML scalar token in `Model`. -/
def isModelDelim (c : Char) : Bool :=
  isModelHorizWs c || c == '\n' || c == '#' || c == ',' || c == ']' || c == '}'

/-- Suffix condition satisfied after every TOML value in statements, arrays, and inline tables. -/
def ModelDelimTail (rem : List Char) : Prop :=
  ∀ c r, rem = c :: r →
    isModelDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigitModel c2 = false)

/-- Consume non-delimiter characters at the head of `cs`. -/
def takeModelNonDelim : List Char → List Char × List Char
  | c :: cs =>
    if isModelDelim c then ([], c :: cs)
    else let (t, r) := takeModelNonDelim cs; (c :: t, r)
  | [] => ([], [])

theorem takeModelNonDelim_append :
    ∀ (tok rem : List Char), (tok.all fun c => !isModelDelim c) = true →
      (∀ c r, rem = c :: r → isModelDelim c = true) →
      takeModelNonDelim (tok ++ rem) = (tok, rem)
  | [], [], _, _ => rfl
  | [], c :: r, _, hrem => by simp [takeModelNonDelim, hrem c r rfl]
  | c :: cs, rem, htok, hrem => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at htok
    simp [takeModelNonDelim, htok.1, takeModelNonDelim_append cs rem htok.2 hrem]

/-- Pure left-inverse splitter for unquoted TOML scalar tokens (handling `YYYY-MM-DD HH:MM:SS`). -/
def splitModelUnquoted : List Char → List Char × List Char
  | y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: ' ' ::
      h1 :: h2 :: ':' :: min1 :: min2 :: ':' :: s1 :: s2 :: rest =>
    if [y1, y2, y3, y4, m1, m2, d1, d2, h1, h2, min1, min2, s1, s2].all isAsciiDigitModel then
      let (tail, after) := takeModelNonDelim rest
      ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++ tail, after)
    else
      takeModelNonDelim (y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: ' ' ::
        h1 :: h2 :: ':' :: min1 :: min2 :: ':' :: s1 :: s2 :: rest)
  | cs => takeModelNonDelim cs

theorem splitModelUnquoted_noSpace {tok rem : List Char}
    (htok : (tok.all fun c => !isModelDelim c) = true) (hrem : ModelDelimTail rem) :
    splitModelUnquoted (tok ++ rem) = (tok, rem) := by
  have hnd := takeModelNonDelim_append tok rem htok (fun c r h => (hrem c r h).1)
  unfold splitModelUnquoted
  split
  · rename_i y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 rest heq
    split
    · rename_i hdig
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hdig
      have h10 : tok.length ≤ 10 → False := by
        intro hle
        have hsp_idx : (tok ++ rem)[10]? = some ' ' := by rw [heq]; rfl
        have hh1_idx : (tok ++ rem)[11]? = some h1 := by rw [heq]; rfl
        by_cases hlt10 : 10 < tok.length
        · omega
        · have heq10 : tok.length = 10 ∨ tok.length < 10 := by omega
          rcases heq10 with hlen10 | hlt
          · rw [List.getElem?_append_right (by omega), hlen10, Nat.sub_self] at hsp_idx
            rw [List.getElem?_append_right (by omega), hlen10] at hh1_idx
            cases rem with
            | nil => simp at hsp_idx
            | cons cr rr =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hsp_idx
              cases rr with
              | nil => simp at hh1_idx
              | cons c2 r2 =>
                simp only [show 11 - 10 = 1 from rfl, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hh1_idx
                have hndig := (hrem ' ' (h1 :: r2) (by rw [hsp_idx, hh1_idx])).2 rfl h1 r2 rfl
                rw [hdig.2.2.2.2.2.2.2.2.1] at hndig; cases hndig
          · have hdash_or_dig : (tok ++ rem)[10]? = some ' ' → False := by
              have hrem0 : (tok ++ rem)[tok.length]? = rem[0]? := by
                rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
              have htok_lt : tok.length < 10 := hlt
              have hc_at : ∃ ch, (tok ++ rem)[tok.length]? = some ch ∧ (isAsciiDigitModel ch = true ∨ ch = '-') := by
                have hidx := htok_lt
                rw [heq]
                match hm : tok.length with
                | 0 => exact ⟨y1, rfl, Or.inl hdig.1⟩
                | 1 => exact ⟨y2, rfl, Or.inl hdig.2.1⟩
                | 2 => exact ⟨y3, rfl, Or.inl hdig.2.2.1⟩
                | 3 => exact ⟨y4, rfl, Or.inl hdig.2.2.2.1⟩
                | 4 => exact ⟨'-', rfl, Or.inr rfl⟩
                | 5 => exact ⟨m1, rfl, Or.inl hdig.2.2.2.2.1⟩
                | 6 => exact ⟨m2, rfl, Or.inl hdig.2.2.2.2.2.1⟩
                | 7 => exact ⟨'-', rfl, Or.inr rfl⟩
                | 8 => exact ⟨d1, rfl, Or.inl hdig.2.2.2.2.2.2.1⟩
                | 9 => exact ⟨d2, rfl, Or.inl hdig.2.2.2.2.2.2.2.1⟩
                | _ + 10 => omega
              obtain ⟨ch, hch, hkind⟩ := hc_at
              rw [hrem0] at hch
              cases rem with
              | nil => simp at hch
              | cons r0 rs =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hch
                have hdel := (hrem ch rs (by rw [hch])).1
                rcases hkind with hd | rfl
                · simp only [isModelDelim, isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hdel
                  rcases hdel with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) <;> exact absurd hd (by decide)
                · exact absurd hdel (by decide)
            exact hdash_or_dig hsp_idx
      exfalso; apply h10
      by_cases hgt : 10 < tok.length
      · have hmem : ' ' ∈ tok := by
          have hget : (tok ++ rem)[10]? = some ' ' := by rw [heq]; rfl
          rw [List.getElem?_append_left hgt] at hget
          exact List.mem_of_getElem? hget
        have hsp_nd := List.all_eq_true.mp htok ' ' hmem
        exact absurd hsp_nd (by decide)
      · omega
    · rw [← heq]; exact hnd
  · rename_i cs _
    exact hnd

private theorem toString_lt10_info (r : Nat) (hr : r < 10) :
    (toString r).toList = [Nat.digitChar r] ∧ isAsciiDigitModel (Nat.digitChar r) = true ∧
      (Nat.digitChar r).toNat - '0'.toNat = r := by
  match r with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | _ + 10 => omega

private theorem nat_toDigitsCore_accM (fuel n : Nat) (acc : List Char) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => simp [Nat.toDigitsCore]
  | succ _ ih =>
    rw [Nat.toDigitsCore, Nat.toDigitsCore]; split
    · simp
    · rw [ih (n / 10) (_ :: acc), ih (n / 10) [_]]; simp [List.append_assoc]

private theorem toDigitsCore_fuel_monoM (f1 f2 n : Nat) (hf1 : n < f1) (hf2 : n < f2) :
    Nat.toDigitsCore 10 f1 n [] = Nat.toDigitsCore 10 f2 n [] := by
  induction f1 generalizing f2 n with
  | zero => omega
  | succ f1' ih =>
    cases f2 with
    | zero => omega
    | succ f2' =>
      rw [Nat.toDigitsCore, Nat.toDigitsCore]
      if hdiv : n / 10 = 0 then simp [hdiv] else
        simp only [hdiv, ↓reduceIte]
        rw [nat_toDigitsCore_accM f1' (n / 10) [_], nat_toDigitsCore_accM f2' (n / 10) [_],
          ih f2' (n / 10) (by omega) (by omega)]

private theorem toString_div_mod10 (q r : Nat) (hq : 0 < q) (hr : r < 10) :
    (toString (q * 10 + r)).toList = (toString q).toList ++ [Nat.digitChar r] := by
  change (Nat.repr (q * 10 + r)).toList = (Nat.repr q).toList ++ [Nat.digitChar r]
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits]; rw [Nat.toDigitsCore]
  simp only [show (q * 10 + r) / 10 = q by omega, show (q * 10 + r) % 10 = r by omega, show q ≠ 0 by omega, ↓reduceIte]
  rw [nat_toDigitsCore_accM _ q [Nat.digitChar r], toDigitsCore_fuel_monoM (q * 10 + r) (q + 1) q (by omega) (by omega)]

private theorem toString_nat_digits_and_eval (n : Nat) :
    (toString n).toList ≠ [] ∧
    (toString n).toList.all isAsciiDigitModel = true ∧
    (toString n).toList.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    if h10 : n < 10 then
      obtain ⟨hch, hd, hdv⟩ := toString_lt10_info n h10
      rw [hch]
      exact ⟨by simp, by simp [hd], by rw [List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]; exact hdv⟩
    else
      have hsp := toString_div_mod10 (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      rw [show (n / 10) * 10 + n % 10 = n by omega] at hsp
      obtain ⟨_, ihd, ihf⟩ := ih (n / 10) (by omega)
      obtain ⟨_, hd, hdv⟩ := toString_lt10_info (n % 10) (Nat.mod_lt n (by decide))
      rw [hsp]
      refine ⟨by simp, by rw [List.all_append, ihd, List.all_cons, hd, List.all_nil]; rfl, ?_⟩
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ihf, hdv]; omega

private theorem pow10Nat_posM (k : Nat) : 0 < pow10Nat k := by
  induction k with | zero => decide | succ _ ih => simp only [pow10Nat]; omega

private theorem toString_len_le_pow10M (w n : Nat) (hw : 1 ≤ w) (hn : n < pow10Nat w) :
    (toString n).toList.length ≤ w := by
  induction w generalizing n with
  | zero => omega
  | succ w ih =>
    if h10 : n < 10 then
      obtain ⟨hch, _⟩ := toString_lt10_info n h10; rw [hch]; simp
    else
      have hw1 : 1 ≤ w := by cases w with | zero => simp [pow10Nat] at hn; omega | succ _ => omega
      have hsub := ih (n / 10) hw1 (by simp only [pow10Nat] at hn; omega)
      have hsp := toString_div_mod10 (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      rw [show (n / 10) * 10 + n % 10 = n by omega] at hsp
      rw [hsp, List.length_append, List.length_singleton]; omega

theorem padNatZero_props (w n : Nat) :
    (padNatZero w n).toList.all isAsciiDigitModel = true ∧
    (padNatZero w n).toList.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0 = n ∧
    (1 ≤ w → n < pow10Nat w → (padNatZero w n).toList.length = w) := by
  obtain ⟨_, hd, hf⟩ := toString_nat_digits_and_eval n
  have hlen_eq : (toString n).length = (toString n).toList.length := by
    change (Nat.repr n).length = (Nat.repr n).toList.length; simp [Nat.repr]
  have hz : ∀ k, (List.replicate k '0').foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0 = 0 := fun k => by
    induction k with | zero => rfl | succ _ ih => rw [List.replicate_succ, List.foldl_cons]; exact ih
  refine ⟨?_, ?_, fun hw hn => ?_⟩
  · unfold padNatZero; dsimp only; split
    · exact hd
    · simp only [String.toList_append, String.toList_ofList, List.all_append, hd, Bool.and_true, List.all_replicate]
      split <;> decide
  · unfold padNatZero; dsimp only; split
    · exact hf
    · simp only [String.toList_append, String.toList_ofList, List.foldl_append, hz, hf]
  · have hle := toString_len_le_pow10M w n hw hn
    unfold padNatZero; dsimp only
    rw [hlen_eq]
    split
    · omega
    · simp only [String.toList_append, String.toList_ofList, List.length_append, List.length_replicate]; omega

theorem padNatZero_inj {w n1 n2 : Nat} (h : padNatZero w n1 = padNatZero w n2) : n1 = n2 := by
  have h1 := (padNatZero_props w n1).2.1
  have h2 := (padNatZero_props w n2).2.1
  rw [h] at h1; exact h1.symm.trans h2

theorem isAsciiDigitModel_clean {c : Char} (h : isAsciiDigitModel c = true) :
    (!isModelDelim c && c != '\r' && c != '"' && c != '\'' && c != '[' && c != '{') = true := by
  have hlt : c.toNat < 128 := by
    have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigitModel] using h
    have := UInt32.le_iff_toNat_le.mp h1.2
    have : '9'.val.toNat = 57 := rfl; have : c.toNat = c.val.toNat := rfl; omega
  have hall : (List.range 128).all (fun n =>
      let x := Char.ofNat n
      !isAsciiDigitModel x || (!isModelDelim x && x != '\r' && x != '"' && x != '\'' && x != '[' && x != '{')) = true := by
    decide
  simpa [Char.ofNat_toNat, h] using List.all_eq_true.mp hall c.toNat (List.mem_range.mpr hlt)

theorem renderDate_info {d : Std.Time.PlainDate} {ds : String} (hr : renderDate d = some ds) :
    (∃ y1 y2 y3 y4 m1 m2 d1 d2, ds.toList = [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] ∧
      [y1, y2, y3, y4, m1, m2, d1, d2].all isAsciiDigitModel = true) ∧
    (ds.toList.all fun c => !isModelDelim c) = true ∧ NoCrStr ds := by
  simp only [renderDate] at hr; split at hr
  · rename_i hvd; injection hr with hds; subst hds
    have hv_lo : @LE.le Int _ 0 d.year := (decide_eq_true_eq.mp hvd).1
    have hv_hi : @LE.le Int _ d.year 9999 := (decide_eq_true_eq.mp hvd).2
    have hy_nat : d.year.toNat < pow10Nat 4 := by
      have : Int.ofNat d.year.toNat = (d.year : Int) := Int.toNat_of_nonneg hv_lo
      change Int.toNat d.year < 10000; omega
    have hm_prop := d.month.property; have hd_prop := d.day.property
    obtain ⟨hdy, _, hly⟩ := padNatZero_props 4 d.year.toNat
    obtain ⟨hdm, _, hlm⟩ := padNatZero_props 2 d.month.val.toNat
    obtain ⟨hdd, _, hld⟩ := padNatZero_props 2 d.day.val.toNat
    have hly' := hly (by decide) hy_nat
    have hlm' := hlm (by decide) (by change d.month.val.toNat < 100; omega)
    have hld' := hld (by decide) (by change d.day.val.toNat < 100; omega)
    rcases hyl : (padNatZero 4 d.year.toNat).toList with _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, _ | _⟩⟩⟩⟩ <;>
      rw [hyl] at hly' <;> try (simp at hly')
    rcases hml : (padNatZero 2 d.month.val.toNat).toList with _ | ⟨m1, _ | ⟨m2, _ | _⟩⟩ <;>
      rw [hml] at hlm' <;> try (simp at hlm')
    rcases hdl : (padNatZero 2 d.day.val.toNat).toList with _ | ⟨d1, _ | ⟨d2, _ | _⟩⟩ <;>
      rw [hdl] at hld' <;> try (simp at hld')
    rw [hyl] at hdy; rw [hml] at hdm; rw [hdd] at *; simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hdy hdm
    have hdd' := (padNatZero_props 2 d.day.val.toNat).1; rw [hdl] at hdd'
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hdd'
    have hfull : (padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++ padNatZero 2 d.day.val.toNat).toList =
        [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] := by
      simp only [String.toList_append, hyl, hml, hdl, show ("-" : String).toList = ['-'] from rfl]; rfl
    refine ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hfull, by simp [hdy, hdm, hdd']⟩, ?_, ?_⟩
    · rw [hfull]; simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      have cl (c) (hc : isAsciiDigitModel c = true) : (!isModelDelim c) = true := by
        have := isAsciiDigitModel_clean hc; simp only [Bool.and_eq_true] at this; exact this.1.1.1.1.1
      exact ⟨cl _ hdy.1, cl _ hdy.2.1, cl _ hdy.2.2.1, cl _ hdy.2.2.2, by decide,
        cl _ hdm.1, cl _ hdm.2, by decide, cl _ hdd'.1, cl _ hdd'.2⟩
    · unfold NoCrStr; rw [hfull]
      have nr (c) (hc : isAsciiDigitModel c = true) : c ≠ '\r' := by
        have := isAsciiDigitModel_clean hc; simp only [Bool.and_eq_true, bne_iff_ne] at this; exact this.1.1.1.1.2
      simp [(nr _ hdy.1).symm, (nr _ hdy.2.1).symm, (nr _ hdy.2.2.1).symm, (nr _ hdy.2.2.2).symm,
        (nr _ hdm.1).symm, (nr _ hdm.2).symm, (nr _ hdd'.1).symm, (nr _ hdd'.2).symm]
  · cases hr

theorem renderDate_inj {d1 d2 : Std.Time.PlainDate} {ds : String}
    (h1 : renderDate d1 = some ds) (h2 : renderDate d2 = some ds) : d1 = d2 := by
  unfold renderDate at h1 h2
  cases hvd1 : validTomlDate d1 <;> rw [hvd1] at h1
  · cases h1
  · cases hvd2 : validTomlDate d2 <;> rw [hvd2] at h2
    · cases h2
    · simp only [↓reduceIte, Option.some.injEq] at h1 h2
      have hv1_lo : @LE.le Int _ 0 d1.year := (decide_eq_true_eq.mp hvd1).1
      have hv1_hi : @LE.le Int _ d1.year 9999 := (decide_eq_true_eq.mp hvd1).2
      have hv2_lo : @LE.le Int _ 0 d2.year := (decide_eq_true_eq.mp hvd2).1
      have hv2_hi : @LE.le Int _ d2.year 9999 := (decide_eq_true_eq.mp hvd2).2
      have hn1_eq : Int.ofNat d1.year.toNat = (d1.year : Int) := Int.toNat_of_nonneg hv1_lo
      have hn2_eq : Int.ofNat d2.year.toNat = (d2.year : Int) := Int.toNat_of_nonneg hv2_lo
      have heq := congrArg String.toList (h1.trans h2.symm)
      simp only [String.toList_append, show ("-" : String).toList = ['-'] from rfl, List.append_assoc, List.singleton_append] at heq
      have ly1 := (padNatZero_props 4 d1.year.toNat).2.2 (by decide) (by change d1.year.toNat < 10000; omega)
      have ly2 := (padNatZero_props 4 d2.year.toNat).2.2 (by decide) (by change d2.year.toNat < 10000; omega)
      have lm1 := (padNatZero_props 2 d1.month.val.toNat).2.2 (by decide) (by have := d1.month.property; change d1.month.val.toNat < 100; omega)
      have lm2 := (padNatZero_props 2 d2.month.val.toNat).2.2 (by decide) (by have := d2.month.property; change d2.month.val.toNat < 100; omega)
      obtain ⟨hy_l, hrest1⟩ := List.append_inj heq (ly1.trans ly2.symm)
      have hrest2 := (List.cons.inj hrest1).2
      obtain ⟨hm_l, hrest3⟩ := List.append_inj hrest2 (lm1.trans lm2.symm)
      have hd_l := (List.cons.inj hrest3).2
      have hy : d1.year.toNat = d2.year.toNat := padNatZero_inj (String.ext_iff.mpr hy_l)
      have hm := padNatZero_inj (String.ext_iff.mpr hm_l)
      have hd := padNatZero_inj (String.ext_iff.mpr hd_l)
      have hyear : d1.year = d2.year := show @Eq Int d1.year d2.year by omega
      have hmonth : d1.month = d2.month := Subtype.ext (by
        have := d1.month.property; have := d2.month.property
        have := Int.toNat_of_nonneg (show (0 : Int) ≤ d1.month.val by omega)
        have := Int.toNat_of_nonneg (show (0 : Int) ≤ d2.month.val by omega); omega)
      have hday : d1.day = d2.day := Subtype.ext (by
        have := d1.day.property; have := d2.day.property
        have := Int.toNat_of_nonneg (show (0 : Int) ≤ d1.day.val by omega)
        have := Int.toNat_of_nonneg (show (0 : Int) ≤ d2.day.val by omega); omega)
      cases d1; cases d2; simp only at hyear hmonth hday; subst hyear hmonth hday; rfl

end LeanSwe.Toml.Proofs
