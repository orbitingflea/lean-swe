import Core.NondetTest
import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.Toml.SpecTests
import LeanSwe.Toml.Proofs.Core
import LeanSwe.Toml.Proofs.RoundTripScalar
import LeanSwe.Toml.Proofs.RoundTripDoc
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model

/-!
# Format & Round-Trip Bridge Proofs

Proves `Impl.formatWithNum` refines `Model.render` via explicit tape/plan witnesses and lifts
both `render` and `format` round-trip theorems to `AllPass` and `CanReach` under `ValidNumApi`.
-/

set_option Elab.async false
namespace LeanSwe.Toml.Proofs
open Core LeanSwe.Toml LeanSwe.Toml.Model LeanSwe.Toml.Impl LeanSwe.NumParse LeanSwe.NumParse.Model

private def ValidFmt (numApi : NumParseApi) : Prop :=
  (∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true) ∧
  (∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)

private theorem validNumApi_parseInt64 (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (tok : String) (n : Int64) (h : parseInt64Model tok = .ok n) : numApi.parseInt64 tok = .ok n := by
  have hspec := (hnum.parseInt64 tok).1
  cases ha : numApi.parseInt64 tok with
  | error _ => simp [Except.mapError, ha, h] at hspec
  | ok m => simp [Except.mapError, ha, h] at hspec; exact congrArg Except.ok hspec

private theorem validNumApi_parseFloat (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (tok : String) (f : Float) (h : parseFloatModel tok = .ok f) :
    ∃ g, numApi.parseFloat tok = .ok g ∧ FloatBitMatch f g := by
  have hspec := hnum.parseFloat tok
  rw [h] at hspec; cases ha : numApi.parseFloat tok <;> rw [ha] at hspec
  · exact False.elim hspec
  · exact ⟨_, rfl, hspec⟩

private theorem decOrMinus_clean {c : Char} (h : (isAsciiDigit c || c == '-') = true) :
    (!c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && c != '.' && !isDisallowedControl c) = true := by
  rcases Bool.or_eq_true_iff.mp h with hd | hm
  · have hctrl : isDisallowedControl c = false := by
      have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigit] using hd
      have := UInt32.le_iff_toNat_le.mp h1.1; have := UInt32.le_iff_toNat_le.mp h1.2
      have : '0'.val.toNat = 48 := rfl; have : '9'.val.toNat = 57 := rfl; have : c.toNat = c.val.toNat := rfl
      simp [isDisallowedControl]; omega
    simp only [Char.isWhitespace, hctrl, Bool.not_false, Bool.and_true, Bool.and_eq_true,
      Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, bne_iff_ne]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> (rintro rfl; revert hd; decide)
  · rw [beq_iff_eq.mp hm]; decide

private theorem no_char_of_decOrMinus {s : String} (hs : (s.toList.all fun c => isAsciiDigit c || c == '-') = true)
    (c : Char) (hc : (isAsciiDigit c || c == '-') = false := by decide) : c ∉ s.toList :=
  fun hm => by rw [List.all_eq_true.mp hs c hm] at hc; cases hc

private theorem not_startsWith_of_not_mem {s p : String} {c : Char}
    (h : c ∉ s.toList) (hp : c ∈ p.toList := by decide) : s.startsWith p = false :=
  Bool.eq_false_iff.mpr fun hsw => let ⟨t, ht⟩ := String.startsWith_string_iff.mp hsw; h (ht ▸ List.mem_append_left t hp)

private theorem validNumApi_validFmt (numApi : NumParseApi) (hnum : ValidNumApi numApi) : ValidFmt numApi := by
  refine ⟨fun n => ?_, fun f => ?_⟩
  · have hbounds : inInt64Range n.toInt = true := by
      have := Int64.le_toInt n; have := Int64.toInt_le n
      have : Int64.maxValue.toInt = 9223372036854775807 := by decide
      rw [inInt64Range, decide_eq_true_eq]; simp only [int64MinInt, int64MaxInt]; omega
    have hfmt := hnum.formatInt n.toInt
    simp only [hbounds, ↓reduceIte, Int64.ofInt_toInt] at hfmt
    have hchars := hnum.formatIntChars n.toInt
    have hspec := (hnum.parseInt64 (numApi.formatInt n.toInt)).1
    generalize numApi.formatInt n.toInt = s at hfmt hchars hspec ⊢
    rw [hfmt.2.2.2] at hspec
    have hp64 : parseInt64Model s = .ok n := by simpa [Except.mapError] using hspec.symm
    have hclean := List.all_eq_true.mpr fun c hc => decOrMinus_clean (List.all_eq_true.mp hchars c hc)
    have hX := no_char_of_decOrMinus hchars 'X'; have hO := no_char_of_decOrMinus hchars 'O'; have hB := no_char_of_decOrMinus hchars 'B'
    have hno_upper : (s.startsWith "0X" || s.startsWith "0O" || s.startsWith "0B" || s.startsWith "+0X" ||
        s.startsWith "+0O" || s.startsWith "+0B" || s.startsWith "-0X" || s.startsWith "-0O" || s.startsWith "-0B") = false := by
      simp only [Bool.or_eq_false_iff]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨not_startsWith_of_not_mem hX, not_startsWith_of_not_mem hO⟩, not_startsWith_of_not_mem hB⟩,
        not_startsWith_of_not_mem hX⟩, not_startsWith_of_not_mem hO⟩, not_startsWith_of_not_mem hB⟩,
        not_startsWith_of_not_mem hX⟩, not_startsWith_of_not_mem hO⟩, not_startsWith_of_not_mem hB⟩
    simp only [isValidIntLex, hp64, hclean, hno_upper, beq_self_eq_true, Bool.not_false, Bool.true_and, Bool.and_true]
    split <;> simp [String.contains, no_char_of_decOrMinus hchars 'e', no_char_of_decOrMinus hchars 'E']
  · exact floatFormatSpec_isValidFloatLex f (numApi.formatFloat f) (hnum.formatFloat f).1

private theorem joinRenderedPath_eq_intercalate : (xs : List String) → joinRenderedPath xs = String.intercalate "." xs
  | [] => by simp [joinRenderedPath, String.intercalate_nil]
  | [k] => by simp [joinRenderedPath, String.intercalate_singleton]
  | k :: a :: rest => by simp [joinRenderedPath, joinRenderedPath_eq_intercalate (a :: rest), String.intercalate_cons_cons]

private theorem toString_mul_pow10 (q k : Nat) (hq : 0 < q) :
    (toString (q * pow10Nat k)).toList = (toString q).toList ++ List.replicate k '0' := by
  induction k with
  | zero => simp [pow10Nat]
  | succ k' ih =>
    have hmul : q * pow10Nat (k' + 1) = (q * pow10Nat k') * 10 + 0 := by
      change q * (10 * pow10Nat k') = q * pow10Nat k' * 10 + 0; rw [Nat.add_zero, Nat.mul_left_comm, Nat.mul_comm 10]
    rw [hmul, toString_two_digits_split (q * pow10Nat k') 0 (Nat.mul_pos hq (pow10Nat_pos k')) (by decide),
      ih, (by decide : Nat.digitChar 0 = '0'), List.append_assoc, ← List.replicate_succ']

private theorem digitChar_ne_zero (d : Nat) (hd0 : d ≠ 0) (hd10 : d < 10) : Nat.digitChar d ≠ '0' := by
  match d with | 0 => exact absurd rfl hd0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide | _ + 10 => omega

private theorem padNatZero_last_ne_zero (w q : Nat) (hq : 0 < q) (hmod : q % 10 ≠ 0) (hw : (toString q).toList.length ≤ w) :
    ∃ pref c, (padNatZero w q).toList = pref ++ [c] ∧ c ≠ '0' := by
  have ⟨pref, c, hq_eq, hne⟩ : ∃ pref c, (toString q).toList = pref ++ [c] ∧ c ≠ '0' := by
    by_cases h10 : q < 10
    · exact ⟨[], Nat.digitChar q, (toString_lt10_char q h10).1, digitChar_ne_zero q (by omega) h10⟩
    · have hsp := toString_two_digits_split (q / 10) (q % 10) (by omega) (Nat.mod_lt q (by decide))
      rw [show (q / 10) * 10 + q % 10 = q by omega] at hsp
      exact ⟨_, _, hsp, digitChar_ne_zero (q % 10) hmod (Nat.mod_lt q (by decide))⟩
  rw [padNatZero_eq_of_toList w q (toString q).toList rfl hw]
  exact ⟨List.replicate (w - (toString q).toList.length) '0' ++ pref, c, by rw [hq_eq, List.append_assoc], hne⟩

private theorem dropWhile_replicate_zero_cons (k : Nat) (c : Char) (tl : List Char) (hc : c ≠ '0') :
    (List.replicate k '0' ++ c :: tl).dropWhile (· == '0') = c :: tl := by
  induction k with | zero => simp [beq_false_of_ne hc] | succ _ ih => simp [List.replicate_succ, ih]

private def stripTrailingZerosNat (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 0) else if n % 10 = 0 then let p := stripTrailingZerosNat (n / 10); (p.1 + 1, p.2) else (0, n)
termination_by n

private theorem stripTrailingZerosNat_spec (n : Nat) (hn : 0 < n) :
    let p := stripTrailingZerosNat n; n = p.2 * pow10Nat p.1 ∧ 0 < p.2 ∧ p.2 % 10 ≠ 0 := by
  unfold stripTrailingZerosNat; simp only [show n ≠ 0 by omega, ↓reduceIte]
  by_cases hmod : n % 10 = 0
  · simp only [hmod, ↓reduceIte]; obtain ⟨heq, hq_pos, hq_mod⟩ := stripTrailingZerosNat_spec (n / 10) (by omega)
    refine ⟨?_, hq_pos, hq_mod⟩
    calc n = (n / 10) * 10 := by omega
      _ = ((stripTrailingZerosNat (n / 10)).2 * pow10Nat (stripTrailingZerosNat (n / 10)).1) * 10 := by rw [← heq]
      _ = _ := by change _ = _ * (10 * pow10Nat _); rw [Nat.mul_assoc, Nat.mul_comm (pow10Nat _) 10]
  · simp [hmod, pow10Nat, hn]
termination_by n

private theorem pow10Nat_mono {a b : Nat} (hab : a ≤ b) : pow10Nat a ≤ pow10Nat b := by
  induction hab with | refl => exact Nat.le_refl _ | step _ ih => simp only [pow10Nat]; omega
private def chooseFracDigits (nano : Nat) : Nat := if nano = 0 then 0 else 9 - (stripTrailingZerosNat nano).1

private theorem formatNanosExact_chooseFracDigits (nano : Nat) (hn : nano < pow10Nat 9) :
    formatNanosExact nano (chooseFracDigits nano) = some (formatNanosTrimmed nano) := by
  by_cases hn0 : nano = 0
  · subst hn0; simp [chooseFracDigits, formatNanosExact, formatNanosTrimmed]
  · simp only [chooseFracDigits, hn0, ↓reduceIte]
    obtain ⟨heq, hq_pos, hq_mod⟩ := stripTrailingZerosNat_spec nano (by omega)
    let k := (stripTrailingZerosNat nano).1; let q := (stripTrailingZerosNat nano).2; let fd := 9 - k
    change nano = q * pow10Nat k at heq
    have hk_lt9 : k < 9 := by
      by_cases hk : k < 9; · exact hk
      have : pow10Nat 9 ≤ nano := by rw [heq]; exact Nat.le_trans (pow10Nat_mono (by omega)) (Nat.le_mul_of_pos_left _ hq_pos)
      omega
    have hq_lt : q < pow10Nat fd := by
      by_cases hlt : q < pow10Nat fd; · exact hlt
      have hmul : pow10Nat fd * pow10Nat k = pow10Nat 9 := by rw [← pow10Nat_add]; congr 1; omega
      have h2 := Nat.mul_le_mul_right (pow10Nat k) (show pow10Nat fd ≤ q by omega); rw [hmul, ← heq] at h2; omega
    have hq_len : (toString q).toList.length ≤ fd := by simpa [String.length] using toString_length_le_pow10 fd q (by omega) hq_lt
    have hn_len : (toString nano).toList.length ≤ 9 := by simpa [String.length] using toString_length_le_pow10 9 nano (by omega) hn
    have hnano_list := heq ▸ toString_mul_pow10 q k hq_pos
    have hpad9 : (padNatZero 9 nano).toList = (padNatZero fd q).toList ++ List.replicate k '0' := by
      rw [padNatZero_eq_of_toList 9 nano _ hnano_list (hnano_list ▸ hn_len),
        padNatZero_eq_of_toList fd q (toString q).toList rfl hq_len, List.length_append, List.length_replicate,
        show 9 - ((toString q).toList.length + k) = fd - (toString q).toList.length by omega, List.append_assoc]
    obtain ⟨pref, c, hpad_fd, hc_ne⟩ := padNatZero_last_ne_zero fd q hq_pos hq_mod hq_len
    have htrim : ((padNatZero 9 nano).toList.reverse.dropWhile (· == '0')).reverse = (padNatZero fd q).toList := by
      rw [hpad9, hpad_fd, List.reverse_append, List.reverse_replicate, List.reverse_append]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      rw [dropWhile_replicate_zero_cons k c pref.reverse hc_ne, List.reverse_cons, List.reverse_reverse]
    have hfmt : formatNanosTrimmed nano = "." ++ padNatZero fd q := by
      simp only [formatNanosTrimmed, beq_false_of_ne hn0, Bool.false_eq_true, ↓reduceIte]; rw [htrim, String.ofList_toList]
    change formatNanosExact nano fd = some (formatNanosTrimmed nano)
    simp only [formatNanosExact, show ¬(fd > 9) by omega, ↓reduceIte, beq_false_of_ne (show fd ≠ 0 by omega),
      Bool.false_eq_true, show 9 - fd = k by omega, show nano % pow10Nat k = 0 by rw [heq]; exact Nat.mul_mod_left q _,
      bne_self_eq_false, show nano / pow10Nat k = q by rw [heq]; exact Nat.mul_div_cancel q (pow10Nat_pos k), hfmt]

private def chooseKeyStyle (k : String) : KeyStyle := if isValidBareKey k then .bare else .basic
private theorem renderKey_chooseKeyStyle (k : String) : renderKey k (chooseKeyStyle k) = some (formatKey k) := by
  by_cases hk : isValidBareKey k = true <;> simp [chooseKeyStyle, renderKey, formatKey, hk]
private theorem renderDate_formatDate (d : Std.Time.PlainDate) (h : validTomlDate d = true) :
    renderDate d = some (formatDate d) := by simp [renderDate, formatDate, h]
private theorem renderTime_formatTime (t : Std.Time.PlainTime) (h : validTomlTime t = true) :
    renderTime t (chooseFracDigits t.nanosecond.val.toNat) = some (formatTime t) := by
  have := t.nanosecond.property
  simp [renderTime, formatTime, h, formatNanosExact_chooseFracDigits t.nanosecond.val.toNat (by rw [pow10Nat_9]; omega)]
private theorem renderOffset_formatOffset (o : Std.Time.TimeZone.Offset) (h : validTomlOffset o = true) :
    renderOffset o .upperZ = some (formatOffset o) := by
  simp only [renderOffset, formatOffset, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; split <;> rfl

private theorem lookupKeyList_mem_of_noDupKeys (entries : List (String × TomlValue))
    (hnd : noDupKeysBool entries = true) : ∀ k v, (k, v) ∈ entries → lookupKeyList k entries = some v := by
  induction entries with
  | nil => intro _ _ hm; nomatch hm
  | cons hd tl ih =>
    rcases hd with ⟨k', _⟩; simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    intro k v hm; rcases List.mem_cons.mp hm with hhead | htail
    · cases hhead; simp [lookupKeyList]
    · have hne : k ≠ k' := fun heq => by
        subst heq; rw [(hasKeyList_eq_true_iff k tl).mpr (List.mem_map.mpr ⟨(k, v), htail, rfl⟩)] at hnd; nomatch hnd.1
      simp [lookupKeyList, beq_false_of_ne hne, ih hnd.2 k v htail]

private theorem filter_ne_head_of_not_hasKey (k : String) (entries : List (String × TomlValue))
    (hnot : hasKeyList k entries = false) : entries.filter (fun p => p.1 != k) = entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', _⟩; simp only [hasKeyList, Bool.or_eq_false_iff] at hnot
    simp [bne_iff_ne.mpr (fun h => by subst h; simp at hnot : k' ≠ k), ih hnot.2]

private theorem noDupStringsBool_map_fst (entries : List (String × TomlValue)) :
    noDupStringsBool (entries.map Prod.fst) = noDupKeysBool entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, _⟩; simp only [List.map_cons, noDupStringsBool, noDupKeysBool, ih]
    congr 2; apply Bool.eq_iff_iff.mpr; rw [List.contains_iff_mem, hasKeyList_eq_true_iff]

mutual
  private def chooseValueTape (numApi : NumParseApi) : TomlValue → ValueTape
    | .string _ => .string .basic | .int n => .int (some (numApi.formatInt n.toInt))
    | .float f => .float (some (numApi.formatFloat f)) | .bool _ => .bool
    | .offsetDateTime odt => .offsetDateTime .upperT .upperZ (chooseFracDigits odt.dateTime.time.nanosecond.val.toNat)
    | .localDateTime dt => .localDateTime .upperT (chooseFracDigits dt.time.nanosecond.val.toNat)
    | .localDate _ => .localDate | .localTime t => .localTime (chooseFracDigits t.nanosecond.val.toNat)
    | .array xs => .array (chooseArrayTapes numApi xs.toList) | .table t => .inlineTable (chooseInlineTapes numApi t.toList)
  termination_by v => sizeOf v
  decreasing_by all_goals exact Nat.lt_trans (sizeOf_toList_lt_array _) (by simp +arith)
  private def chooseArrayTapes (numApi : NumParseApi) : List TomlValue → List ValueTape
    | [] => [] | x :: xs => chooseValueTape numApi x :: chooseArrayTapes numApi xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp +arith
  private def chooseInlineTapes (numApi : NumParseApi) : List (String × TomlValue) → List (String × KeyStyle × ValueTape)
    | [] => [] | (k, v) :: rest => (k, chooseKeyStyle k, chooseValueTape numApi v) :: chooseInlineTapes numApi rest
  termination_by entries => sizeOf entries
  decreasing_by all_goals simp +arith
end

mutual
  private theorem renderValueInline_formatValueInline_aux (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (v : TomlValue) (hwf : WellFormedValue v) :
      renderValueInline v (chooseValueTape numApi v) = some (formatValueInline numApi v) := by
    match v with
    | .string _ | .bool _ => simp [chooseValueTape, renderValueInline, renderStringLiteral, formatValueInline]
    | .int n => simp [chooseValueTape, renderValueInline, hfmt.1 n, formatValueInline]
    | .float f => simp [chooseValueTape, renderValueInline, hfmt.2 f, formatValueInline]
    | .offsetDateTime odt =>
      have hvd : validTomlOffsetDateTime odt = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
      simp only [validTomlOffsetDateTime, validTomlDateTime, Bool.and_eq_true] at hvd
      simp [chooseValueTape, renderValueInline, formatValueInline, renderDateTimeSep,
        renderDate_formatDate _ hvd.1.1, renderTime_formatTime _ hvd.1.2, renderOffset_formatOffset _ hvd.2]
    | .localDateTime dt =>
      have hvd : validTomlDateTime dt = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
      simp only [validTomlDateTime, Bool.and_eq_true] at hvd
      simp [chooseValueTape, renderValueInline, formatValueInline, renderDateTimeSep, renderDate_formatDate _ hvd.1, renderTime_formatTime _ hvd.2]
    | .localDate d => simp [chooseValueTape, renderValueInline, formatValueInline, renderDate_formatDate d hwf]
    | .localTime t => simp [chooseValueTape, renderValueInline, formatValueInline, renderTime_formatTime t hwf]
    | .array xs => simp [chooseValueTape, renderValueInline, formatValueInline, renderArrayElems_chooseArrayTapes numApi hfmt xs.toList hwf]
    | .table t =>
      have hwf_t : noDupKeysBool t.toList = true ∧ wellFormedValueBool.wellFormedTableListBool t.toList = true := by
        simpa [WellFormedValue, wellFormedValueBool, Bool.and_eq_true] using hwf
      simp [chooseValueTape, renderValueInline, formatValueInline, hwf_t.1, renderInlineEntries_chooseInlineTapes numApi hfmt t.toList hwf_t.1 hwf_t.2]
  termination_by sizeOf v
  decreasing_by all_goals exact Nat.lt_trans (sizeOf_toList_lt_array _) (by simp +arith)
  private theorem renderArrayElems_chooseArrayTapes (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (xs : List TomlValue) (hwf : wellFormedValueBool.wellFormedListBool xs = true) :
      renderValueInline.renderArrayElems xs (chooseArrayTapes numApi xs) = some (formatArrayElems numApi xs) := by
    match xs with
    | [] => simp [chooseArrayTapes, renderValueInline.renderArrayElems, formatArrayElems]
    | x :: rest =>
      simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at hwf
      simp [chooseArrayTapes, renderValueInline.renderArrayElems, formatArrayElems,
        renderValueInline_formatValueInline_aux numApi hfmt x hwf.1, renderArrayElems_chooseArrayTapes numApi hfmt rest hwf.2]
  termination_by sizeOf xs
  decreasing_by all_goals simp +arith
  private theorem renderInlineEntries_chooseInlineTapes (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (entries : List (String × TomlValue)) (hnd : noDupKeysBool entries = true)
      (hwf : wellFormedValueBool.wellFormedTableListBool entries = true) :
      renderValueInline.renderInlineTableEntries entries (chooseInlineTapes numApi entries) = some (formatInlineEntries numApi entries) := by
    match entries with
    | [] => simp [chooseInlineTapes, renderValueInline.renderInlineTableEntries, formatInlineEntries]
    | (k, v) :: rest =>
      simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
      simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
      have hfilt : ((k, v) :: rest).filter (fun p => p.1 != k) = rest := by
        simp only [List.filter_cons, bne_self_eq_false]; exact filter_ne_head_of_not_hasKey k rest hnd.1
      simp [chooseInlineTapes, renderValueInline.renderInlineTableEntries, lookupKeyList, renderKey_chooseKeyStyle k,
        renderValueInline_formatValueInline_aux numApi hfmt v hwf.1, hfilt,
        renderInlineEntries_chooseInlineTapes numApi hfmt rest hnd.2 hwf.2, formatInlineEntries]
  termination_by sizeOf entries
  decreasing_by all_goals simp +arith
end

mutual
  private def choosePlan (numApi : NumParseApi) : List (String × TomlValue) → List (String × EntryPlacement)
    | [] => []
    | (k, v) :: rest =>
      let ep := match v with
        | .table sub => .tableSection (chooseKeyStyle k) false (choosePlan numApi sub.toList) none
        | .array xs =>
          if isNonEmptyTableArray xs then .aotSection (chooseKeyStyle k) (chooseAotPlans numApi xs.toList) none
          else .direct (chooseKeyStyle k) (chooseValueTape numApi (.array xs)) none
        | other => .direct (chooseKeyStyle k) (chooseValueTape numApi other) none
      (k, ep) :: choosePlan numApi rest
  termination_by entries => sizeOf entries
  decreasing_by all_goals first | (simp +arith; done) | (cases sub; simp +arith) | (cases xs; simp +arith)
  private def chooseAotPlans (numApi : NumParseApi) : List TomlValue → List (List (String × EntryPlacement))
    | [] => [] | .table elem :: rest => choosePlan numApi elem.toList :: chooseAotPlans numApi rest | _ :: rest => chooseAotPlans numApi rest
  termination_by xs => sizeOf xs
  decreasing_by all_goals first | (simp +arith; done) | (cases elem; simp +arith)
end

private theorem isPlanPermutation_choosePlan (numApi : NumParseApi)
    (entries : List (String × TomlValue)) (hnd : noDupKeysBool entries = true) :
    isPlanPermutation entries (choosePlan numApi entries) = true := by
  have hmap : ∀ es, (choosePlan numApi es).map Prod.fst = es.map Prod.fst := fun es => by
    induction es with | nil => simp [choosePlan] | cons hd tl ih => rcases hd with ⟨k, v⟩; cases v <;> simp [choosePlan, ih]
  simp only [isPlanPermutation, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨hnd, by rw [hmap entries, noDupStringsBool_map_fst, hnd]⟩, by simpa using congrArg List.length (hmap entries)⟩, fun p hp => ?_⟩
  exact (hasKeyList_eq_true_iff p.1 entries).mpr (hmap entries ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)

private theorem renderEntries_direct_step (numApi : NumParseApi) (hfmt : ValidFmt numApi)
    {fullEntries tl : List (String × TomlValue)} {revPref : List String} {k : String} {v : TomlValue}
    (hwf : WellFormedValue v) (hlu : lookupKeyList k fullEntries = some v)
    (ih_inl : renderInlineEntries revPref fullEntries (choosePlan numApi tl) = some (formatTableInlinePart numApi tl))
    (ih_sec : renderSectionEntries revPref fullEntries (choosePlan numApi tl) = some (formatTableSectionPart numApi revPref tl))
    (hcp : choosePlan numApi ((k, v) :: tl) = (k, .direct (chooseKeyStyle k) (chooseValueTape numApi v) none) :: choosePlan numApi tl)
    (hfi : formatTableInlinePart numApi ((k, v) :: tl) = (formatKey k ++ " = " ++ formatValueInline numApi v) :: formatTableInlinePart numApi tl)
    (hfs : formatTableSectionPart numApi revPref ((k, v) :: tl) = formatTableSectionPart numApi revPref tl) :
    renderInlineEntries revPref fullEntries (choosePlan numApi ((k, v) :: tl)) = some (formatTableInlinePart numApi ((k, v) :: tl)) ∧
    renderSectionEntries revPref fullEntries (choosePlan numApi ((k, v) :: tl)) = some (formatTableSectionPart numApi revPref ((k, v) :: tl)) := by
  have hrv := renderValueInline_formatValueInline_aux numApi hfmt v hwf
  refine ⟨?_, by rw [hcp, hfs]; simp [renderSectionEntries, EntryPlacement.isInlineScope, ih_sec]⟩
  rw [hcp, hfi]; simp only [renderInlineEntries, EntryPlacement.isInlineScope, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, hlu, renderKey_chooseKeyStyle k, hrv, renderCommentSuffix, ih_inl, bind, Option.bind, String.append_empty]; rfl

mutual
  private theorem choosePlan_exists_aux (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (entries : List (String × TomlValue)) (hnd : noDupKeysBool entries = true)
      (hwf : wellFormedValueBool.wellFormedTableListBool entries = true) (revPref : List String) :
      renderTablePlan revPref entries (choosePlan numApi entries) =
        some (formatTableInlinePart numApi entries ++ formatTableSectionPart numApi revPref entries) := by
    obtain ⟨hinl, hsec⟩ := renderEntries_choosePlan numApi hfmt entries entries
      (fun p hp => lookupKeyList_mem_of_noDupKeys entries hnd p.1 p.2 hp) hwf revPref
    simp [renderTablePlan, isPlanPermutation_choosePlan numApi entries hnd, hinl, hsec]
  termination_by sizeOf entries * 2 + 1
  decreasing_by simp +arith
  private theorem renderEntries_choosePlan (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (fullEntries subEntries : List (String × TomlValue))
      (hsub : ∀ p ∈ subEntries, lookupKeyList p.1 fullEntries = some p.2)
      (hwf : wellFormedValueBool.wellFormedTableListBool subEntries = true) (revPref : List String) :
      renderInlineEntries revPref fullEntries (choosePlan numApi subEntries) = some (formatTableInlinePart numApi subEntries) ∧
      renderSectionEntries revPref fullEntries (choosePlan numApi subEntries) = some (formatTableSectionPart numApi revPref subEntries) := by
    match subEntries with
    | [] => exact ⟨by simp [choosePlan, renderInlineEntries, formatTableInlinePart], by simp [choosePlan, renderSectionEntries, formatTableSectionPart]⟩
    | (k, v) :: tl =>
      simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
      have hlu := hsub (k, v) List.mem_cons_self
      obtain ⟨ih_inl, ih_sec⟩ := renderEntries_choosePlan numApi hfmt fullEntries tl (fun p hp => hsub p (List.mem_cons_of_mem _ hp)) hwf.2 revPref
      match hv : v with
      | .table ⟨subList⟩ =>
        have hwf_sub : noDupKeysBool subList = true ∧ wellFormedValueBool.wellFormedTableListBool subList = true := by
          simpa [WellFormedValue, wellFormedValueBool, Bool.and_eq_true] using hwf.1
        have htp := choosePlan_exists_aux numApi hfmt subList hwf_sub.1 hwf_sub.2 (formatKey k :: revPref)
        refine ⟨by simp [choosePlan, renderInlineEntries, EntryPlacement.isInlineScope, ih_inl, formatTableInlinePart], ?_⟩
        simp only [choosePlan, renderSectionEntries, EntryPlacement.isInlineScope, Bool.false_eq_true, ↓reduceIte,
          hlu, renderKey_chooseKeyStyle k, renderCommentSuffix, htp, ih_sec, formatTableSectionPart,
          bind, Option.bind, joinRenderedPath_eq_intercalate, String.append_empty, List.cons_append, List.append_assoc]
      | .array ⟨xsList⟩ =>
        by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
        · have hall_xs := (Bool.and_eq_true_iff.mp haot).2
          have hne : (⟨xsList⟩ : Array TomlValue).isEmpty = false := by cases h : (⟨xsList⟩ : Array TomlValue).isEmpty <;> simp_all [isNonEmptyTableArray]
          have ha := renderAotElems_chooseAotPlans numApi hfmt xsList hwf.1 hall_xs (formatKey k :: revPref)
          refine ⟨by simp [choosePlan, haot, renderInlineEntries, EntryPlacement.isInlineScope, ih_inl, formatTableInlinePart], ?_⟩
          simp [choosePlan, haot, renderSectionEntries, EntryPlacement.isInlineScope, hlu, hne,
            renderKey_chooseKeyStyle k, renderCommentSuffix, ha, ih_sec, formatTableSectionPart]
        · have haf := Bool.eq_false_iff.mpr haot
          exact renderEntries_direct_step numApi hfmt hwf.1 hlu ih_inl ih_sec
            (by simp [choosePlan, haf]) (by simp [formatTableInlinePart, haf]) (by simp [formatTableSectionPart, haf])
      | .string _ | .int _ | .float _ | .bool _ | .offsetDateTime _ | .localDateTime _ | .localDate _ | .localTime _ =>
        exact renderEntries_direct_step numApi hfmt hwf.1 hlu ih_inl ih_sec
          (by simp [choosePlan]) (by simp [formatTableInlinePart]) (by simp [formatTableSectionPart])
  termination_by sizeOf subEntries * 2
  decreasing_by all_goals subst_vars; simp +arith
  private theorem renderAotElems_chooseAotPlans (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (xs : List TomlValue) (hwf : wellFormedValueBool.wellFormedListBool xs = true)
      (hall : (xs.all fun v => match v with | .table _ => true | _ => false) = true) (revTarget : List String) :
      renderAotElems revTarget "" xs (chooseAotPlans numApi xs) =
        some (formatAotElemList numApi revTarget ("[[" ++ String.intercalate "." revTarget.reverse ++ "]]") xs) := by
    match xs with
    | [] => simp [chooseAotPlans, renderAotElems, formatAotElemList]
    | x :: rest =>
      simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at hwf
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have htail := renderAotElems_chooseAotPlans numApi hfmt rest hwf.2 hall.2 revTarget
      match hx : x with
      | .table ⟨elemList⟩ =>
        have hwf_e : noDupKeysBool elemList = true ∧ wellFormedValueBool.wellFormedTableListBool elemList = true := by
          simpa [WellFormedValue, wellFormedValueBool, Bool.and_eq_true] using hwf.1
        have hep := choosePlan_exists_aux numApi hfmt elemList hwf_e.1 hwf_e.2 revTarget
        simp only [chooseAotPlans, renderAotElems, joinRenderedPath_eq_intercalate, String.append_empty,
          hep, htail, formatAotElemList, bind, Option.bind, List.cons_append, List.append_assoc]
      | .string _ | .int _ | .float _ | .bool _ | .offsetDateTime _ | .localDateTime _ | .localDate _ | .localTime _ | .array _ =>
        nomatch hall.1
  termination_by sizeOf xs * 2
  decreasing_by all_goals subst_vars; simp +arith
end

private theorem formatSectionLines_nil_eq_nil (numApi : NumParseApi) (revPref : List String)
    (doc : TomlTable) (h : formatSectionLines numApi revPref doc = []) : doc.toList = [] := by
  cases hlist : doc.toList with
  | nil => rfl
  | cons hd _ =>
    rcases hd with ⟨_, v⟩; simp only [formatSectionLines, hlist, List.append_eq_nil_iff] at h
    cases v with
    | table sub => cases sub; simp [formatTableSectionPart] at h
    | array xs =>
      cases xs with
      | mk xsList =>
        by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
        · simp only [formatTableSectionPart, haot, ↓reduceIte] at h
          cases xsList with
          | nil => simp [isNonEmptyTableArray] at haot
          | cons x0 _ =>
            simp only [isNonEmptyTableArray, List.all_cons, Bool.and_eq_true] at haot
            cases x0 with | table elem => cases elem; simp [formatAotElemList] at h | _ => cases haot.2.1
        · simp [formatTableInlinePart, Bool.eq_false_iff.mpr haot] at h
    | _ => simp [formatTableInlinePart] at h

private theorem formatWithNum_roundTrip_model (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (doc : TomlTable) (hwf : WellFormedTable doc) :
    ∃ parsed, parseWithNum numApi (formatWithNum numApi doc) = .ok parsed ∧ TomlTableEquiv doc parsed := by
  unfold formatWithNum; cases hlines : formatSectionLines numApi [] doc with
  | nil =>
    refine ⟨#[], ?_, by simp [TomlTableEquiv, formatSectionLines_nil_eq_nil numApi [] doc hlines, TomlTableEquivList, lookupKeyList]⟩
    simp [parseWithNum, parseCharsWithNum, normalizeChars, normalizeCharsAux, parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux, entriesToTomlList, bind, Except.bind]
  | cons hd tl =>
    have hwf_b : wellFormedTableBool doc = true := hwf
    have hwf_p : noDupKeysBool doc.toList = true ∧ wellFormedValueBool.wellFormedTableListBool doc.toList = true := by
      simpa [wellFormedTableBool, Bool.and_eq_true] using hwf_b
    have hbp : renderTablePlan [] doc.toList (choosePlan numApi doc.toList) = some (hd :: tl) := by
      have hp := choosePlan_exists_aux numApi (validNumApi_validFmt numApi hnum) doc.toList hwf_p.1 hwf_p.2 []
      unfold formatSectionLines at hlines; rwa [hlines] at hp
    exact render_parse_roundTrip_model numApi (validNumApi_parseInt64 numApi hnum) (validNumApi_parseFloat numApi hnum)
      doc ⟨choosePlan numApi doc.toList, none⟩ (String.intercalate "\n" (hd :: tl) ++ "\n") (by simp [render, hwf_b, hbp, bind, Option.bind])

section
attribute [local irreducible] parseWithNum
/-- Prove `test_toml_render_parse_roundTrip` for `makeTomlApi numApi`. -/
theorem allPass_render_parse_roundTrip (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.AllPass (test_toml_render_parse_roundTrip (makeTomlApi numApi)) := by
  rintro ⟨doc, tape⟩
  dsimp only [test_toml_render_parse_roundTrip, makeTomlApi, Core.NondetTest.assume, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  cases hr : render doc tape with
  | none => exact fun _ => trivial
  | some out =>
    obtain ⟨_, hp, heq⟩ := render_parse_roundTrip_model numApi
      (validNumApi_parseInt64 numApi hnum) (validNumApi_parseFloat numApi hnum) doc tape out hr
    dsimp only; rw [hp]; exact ⟨heq, trivial⟩

/-- Witness `CanReach` for `test_toml_render_parse_roundTrip`. -/
theorem canReach_render_parse_roundTrip (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.CanReach (test_toml_render_parse_roundTrip (makeTomlApi numApi)) := by
  have hr : render #[] ⟨[], none⟩ = some "\n" := by
    simp [render, wellFormedTableBool, wellFormedValueBool.wellFormedTableListBool, noDupKeysBool,
      renderTablePlan, isPlanPermutation, noDupStringsBool, renderInlineEntries, renderSectionEntries]
  obtain ⟨_, hp, heq⟩ := render_parse_roundTrip_model numApi
    (validNumApi_parseInt64 numApi hnum) (validNumApi_parseFloat numApi hnum) #[] ⟨[], none⟩ "\n" hr
  refine ⟨(#[], ⟨[], none⟩), ?_⟩
  dsimp only [test_toml_render_parse_roundTrip, makeTomlApi, Core.NondetTest.assume, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  rw [hr]; dsimp only; rw [hp]; exact ⟨heq, trivial⟩

/-- Prove `test_toml_format_validAndRoundTrip` for `makeTomlApi numApi`. -/
theorem allPass_format_validAndRoundTrip (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.AllPass (test_toml_format_validAndRoundTrip (makeTomlApi numApi)) := by
  intro doc hwf
  dsimp only [test_toml_format_validAndRoundTrip, makeTomlApi, Core.NondetTest.assume, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  obtain ⟨_, hp, heq⟩ := formatWithNum_roundTrip_model numApi hnum doc hwf
  rw [hp]; exact ⟨heq, trivial⟩

/-- Witness `CanReach` for `test_toml_format_validAndRoundTrip`. -/
theorem canReach_format_validAndRoundTrip (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.CanReach (test_toml_format_validAndRoundTrip (makeTomlApi numApi)) := by
  have hwf : WellFormedTable #[] := rfl
  obtain ⟨_, hp, heq⟩ := formatWithNum_roundTrip_model numApi hnum #[] hwf
  refine ⟨#[], hwf, ?_⟩
  dsimp only [test_toml_format_validAndRoundTrip, makeTomlApi, Core.NondetTest.assume, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  rw [hp]; exact ⟨heq, trivial⟩
end

private theorem isPrefixOf_append_self : ∀ (sub suf : List Char), sub.isPrefixOf (sub ++ suf) = true
  | [], _ => rfl
  | _ :: cs, suf => by simp [isPrefixOf_append_self cs suf]

private theorem hasCharSublist_mid (sub : List Char) :
    ∀ (pre suf : List Char), hasCharSublist sub (pre ++ sub ++ suf) = true
  | [], suf => by
    cases sub with
    | nil => cases suf <;> simp [hasCharSublist]
    | cons c cs => simp [hasCharSublist, isPrefixOf_append_self cs suf]
  | c :: pre, suf => by
    simp only [List.cons_append, hasCharSublist, Bool.or_eq_true]
    exact Or.inr (hasCharSublist_mid sub pre suf)

private theorem intercalate_nl_decomp :
    ∀ (hd : String) (tl : List String),
      (String.intercalate "\n" (hd :: tl)).toList =
        hd.toList ++ tl.flatMap (fun s => '\n' :: s.toList)
  | hd, [] => by simp [String.intercalate_singleton]
  | hd, x :: xs => by
    rw [String.intercalate_cons_cons, String.toList_append, String.toList_append,
      intercalate_nl_decomp x xs]
    simp [List.flatMap_cons, List.append_assoc]

private theorem intercalate_mem_sublist {ln : String} {lines : List String} (hmem : ln ∈ lines)
    {sub : List Char} (hsub : ∃ p s, ln.toList = p ++ sub ++ s) :
    hasCharSublist sub (String.intercalate "\n" lines ++ "\n").toList = true := by
  rcases hsub with ⟨p, s, hln⟩
  cases lines with
  | nil => nomatch hmem
  | cons hd tl =>
    rw [String.toList_append, intercalate_nl_decomp hd tl]
    rcases List.mem_cons.mp hmem with rfl | htl
    · rw [hln]
      have hassoc : p ++ sub ++ s ++ tl.flatMap (fun x => '\n' :: x.toList) ++ "\n".toList =
          p ++ sub ++ (s ++ tl.flatMap (fun x => '\n' :: x.toList) ++ "\n".toList) := by
        simp [List.append_assoc]
      rw [hassoc]
      exact hasCharSublist_mid sub p _
    · rcases List.mem_iff_append.mp htl with ⟨before, after, hsplit⟩
      rw [hsplit, List.flatMap_append, List.flatMap_cons, hln]
      have hassoc :
          hd.toList ++ (before.flatMap (fun x => '\n' :: x.toList) ++
            ('\n' :: (p ++ sub ++ s) ++ after.flatMap (fun x => '\n' :: x.toList))) ++ "\n".toList =
          (hd.toList ++ before.flatMap (fun x => '\n' :: x.toList) ++ ('\n' :: p)) ++
            sub ++ (s ++ after.flatMap (fun x => '\n' :: x.toList) ++ "\n".toList) := by
        simp [List.append_assoc]
      rw [hassoc]
      exact hasCharSublist_mid sub _ _

private theorem entry_emits_rendered_key (numApi : NumParseApi) (kvs : List (String × TomlValue))
    {k : String} {v : TomlValue} (hm : (k, v) ∈ kvs) :
    ∃ ln ∈ formatTableInlinePart numApi kvs ++ formatTableSectionPart numApi [] kvs,
      ∃ p s, ln.toList = p ++ (formatKey k).toList ++ s := by
  induction kvs with
  | nil => nomatch hm
  | cons kv rest ih =>
    rcases kv with ⟨k0, v0⟩
    rcases List.mem_cons.mp hm with hhead | htail
    · injection hhead with hk hv
      subst hk hv
      cases v with
      | table sub =>
        cases sub with
        | mk subList =>
          refine ⟨"[" ++ formatKey k ++ "]", ?_, ['['], [']'], ?_⟩
          · simp [formatTableInlinePart, formatTableSectionPart, String.intercalate_singleton]
          · simp [String.toList_append]
      | array xs =>
        cases xs with
        | mk xsList =>
          by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
          · have haot0 := haot
            cases xsList with
            | nil => simp [isNonEmptyTableArray] at haot
            | cons x0 xsTail =>
              simp only [isNonEmptyTableArray, List.all_cons, Bool.and_eq_true] at haot
              cases x0 with
              | table elem =>
                cases elem with
                | mk elemList =>
                  refine ⟨"[[" ++ formatKey k ++ "]]", ?_, ['[', '['], [']', ']'], ?_⟩
                  · simp [formatTableInlinePart, formatTableSectionPart, haot0,
                      formatAotElemList, String.intercalate_singleton]
                  · simp [String.toList_append]
              | _ => nomatch haot.2.1
          · have haotF : isNonEmptyTableArray ⟨xsList⟩ = false := Bool.eq_false_iff.mpr haot
            refine ⟨formatKey k ++ " = " ++ formatValueInline numApi (.array ⟨xsList⟩), ?_,
              [], (" = " ++ formatValueInline numApi (.array ⟨xsList⟩)).toList, ?_⟩
            · simp [formatTableInlinePart, haotF]
            · simp [String.toList_append]
      | string s =>
        refine ⟨formatKey k ++ " = " ++ formatValueInline numApi (.string s), by simp [formatTableInlinePart],
          [], (" = " ++ formatValueInline numApi (.string s)).toList, by simp [String.toList_append]⟩
      | int n =>
        refine ⟨formatKey k ++ " = " ++ formatValueInline numApi (.int n), by simp [formatTableInlinePart],
          [], (" = " ++ formatValueInline numApi (.int n)).toList, by simp [String.toList_append]⟩
      | float f =>
        refine ⟨formatKey k ++ " = " ++ formatValueInline numApi (.float f), by simp [formatTableInlinePart],
          [], (" = " ++ formatValueInline numApi (.float f)).toList, by simp [String.toList_append]⟩
      | bool b =>
        refine ⟨formatKey k ++ " = " ++ formatValueInline numApi (.bool b), by simp [formatTableInlinePart],
          [], (" = " ++ formatValueInline numApi (.bool b)).toList, by simp [String.toList_append]⟩
      | offsetDateTime d =>
        refine ⟨formatKey k ++ " = " ++ formatValueInline numApi (.offsetDateTime d), by simp [formatTableInlinePart],
          [], (" = " ++ formatValueInline numApi (.offsetDateTime d)).toList, by simp [String.toList_append]⟩
      | localDateTime d =>
        refine ⟨formatKey k ++ " = " ++ formatValueInline numApi (.localDateTime d), by simp [formatTableInlinePart],
          [], (" = " ++ formatValueInline numApi (.localDateTime d)).toList, by simp [String.toList_append]⟩
      | localDate d =>
        refine ⟨formatKey k ++ " = " ++ formatValueInline numApi (.localDate d), by simp [formatTableInlinePart],
          [], (" = " ++ formatValueInline numApi (.localDate d)).toList, by simp [String.toList_append]⟩
      | localTime t =>
        refine ⟨formatKey k ++ " = " ++ formatValueInline numApi (.localTime t), by simp [formatTableInlinePart],
          [], (" = " ++ formatValueInline numApi (.localTime t)).toList, by simp [String.toList_append]⟩
    · obtain ⟨ln, hlnMem, hsub⟩ := ih htail
      refine ⟨ln, ?_, hsub⟩
      rcases List.mem_append.mp hlnMem with hinl | hsec
      · apply List.mem_append_left
        cases v0 with
        | table _ => simp [formatTableInlinePart, hinl]
        | array xs =>
          by_cases haot : isNonEmptyTableArray xs = true
          · simp [formatTableInlinePart, haot, hinl]
          · simp [formatTableInlinePart, Bool.eq_false_iff.mpr haot, hinl]
        | _ => simp [formatTableInlinePart, hinl]
      · apply List.mem_append_right
        cases v0 with
        | table sub =>
          cases sub with
          | mk subList => simp [formatTableSectionPart, hsec]
        | array xs =>
          cases xs with
          | mk xsList =>
            by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
            · simp [formatTableSectionPart, haot, hsec]
            · simp [formatTableSectionPart, Bool.eq_false_iff.mpr haot, hsec]
        | _ => simp [formatTableSectionPart, hsec]

/-- `formatWithNum` satisfies `Model.allowedFormat` for any `ValidNumApi`. -/
theorem formatWithNum_allowedFormat (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (doc : TomlTable) : allowedFormat doc (formatWithNum numApi doc) := by
  unfold allowedFormat
  cases hdoc : doc.toList with
  | nil =>
    have hempty : doc = #[] := Array.ext' hdoc
    subst hempty
    simp [formatWithNum, formatSectionLines, formatTableInlinePart, formatTableSectionPart]
  | cons kv rest =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    by_cases hwf : wellFormedTableBool doc = true
    · simp only [hwf, ↓reduceIte]
      unfold formatWithNum
      cases hlines : formatSectionLines numApi [] doc with
      | nil =>
        have hnil := formatSectionLines_nil_eq_nil numApi [] doc hlines
        rw [hdoc] at hnil; nomatch hnil
      | cons hd tl =>
        have hwf_p : noDupKeysBool doc.toList = true ∧ wellFormedValueBool.wellFormedTableListBool doc.toList = true := by
          simpa [wellFormedTableBool, Bool.and_eq_true] using hwf
        have hbp : renderTablePlan [] doc.toList (choosePlan numApi doc.toList) = some (hd :: tl) := by
          have hp := choosePlan_exists_aux numApi (validNumApi_validFmt numApi hnum) doc.toList hwf_p.1 hwf_p.2 []
          unfold formatSectionLines at hlines; rwa [hlines] at hp
        exact ⟨⟨choosePlan numApi doc.toList, none⟩, rfl, by simp [render, hwf, hbp, bind, Option.bind]⟩
    · simp only [hwf, Bool.false_eq_true, ↓reduceIte]
      unfold formatWithNum
      cases hlines : formatSectionLines numApi [] doc with
      | nil =>
        have hnil := formatSectionLines_nil_eq_nil numApi [] doc hlines
        rw [hdoc] at hnil; nomatch hnil
      | cons hd tl =>
        refine ⟨?_, ?_⟩
        · simp [String.toList_append, List.reverse_append]
        · intro k v hmem
          rw [← hdoc] at hmem
          obtain ⟨ln, hlnMem, hsub⟩ := entry_emits_rendered_key numApi doc.toList hmem
          unfold formatSectionLines at hlines
          rw [hlines] at hlnMem
          exact ⟨formatKey k, renderKey_chooseKeyStyle k, intercalate_mem_sublist hlnMem hsub⟩

end LeanSwe.Toml.Proofs
