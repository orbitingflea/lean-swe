import LeanSwe.Toml.Proofs.RoundTripDoc

/-!
# Scalar & Inline Value Formatter Bridge (`FormatBridgeVal`)

Constructs canonical `ValueTape` witnesses for `Impl.formatValueInline` under `ValidNumApi`
and proves reusable `SkeletonNode` association-list and `skelMatchesEntries` lemmas.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Check that `numApi` emits valid TOML integer and float lexemes. -/
def ValidFmt (numApi : NumParseApi) : Prop :=
  (∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true) ∧
  (∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)

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

/-- Every `ValidNumApi` satisfies `ValidFmt`. -/
theorem validNumApi_validFmt (numApi : NumParseApi) (hnum : ValidNumApi numApi) : ValidFmt numApi := by
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

/-- Canonical `KeyStyle` used by `Impl.formatKey`. -/
def chooseKeyStyle (k : String) : KeyStyle :=
  if isValidBareKey k then .bare else .basic

/-- `Model.renderKey` on `chooseKeyStyle` produces `Impl.formatKey`. -/
theorem renderKey_chooseKeyStyle (k : String) : renderKey k (chooseKeyStyle k) = some (formatKey k) := by
  by_cases hk : isValidBareKey k = true <;> simp [chooseKeyStyle, renderKey, formatKey, hk]

/-- `chooseKeyStyle` always satisfies `Model.isCleanKeyStyle`. -/
theorem isCleanKeyStyle_chooseKeyStyle (k : String) : isCleanKeyStyle k (chooseKeyStyle k) = true := by
  by_cases hk : isValidBareKey k = true <;> simp [isCleanKeyStyle, chooseKeyStyle, hk]

private theorem dropWhile_zero_decomp :
    ∀ r : List Char, ∃ k, r = List.replicate k '0' ++ r.dropWhile (· == '0')
  | [] => ⟨0, rfl⟩
  | c :: rs => by
    by_cases hc : (c == '0') = true
    · obtain ⟨k, hk⟩ := dropWhile_zero_decomp rs
      exact ⟨k + 1, by simp [List.dropWhile, List.replicate_succ, eq_of_beq hc, ← hk]⟩
    · exact ⟨0, by simp [List.dropWhile, hc]⟩

private theorem foldl_replicate_zero :
    ∀ k : Nat, (List.replicate k '0').foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = 0
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ', List.foldl_append, foldl_replicate_zero k]
    rfl

private theorem fracAux_replicate_zero :
    ∀ (m acc : Nat), fracDigitsToNanosAuxModel m acc (List.replicate m '0') = fracDigitsToNanosAuxModel m acc []
  | 0, _ => rfl
  | m + 1, acc => by simpa [List.replicate_succ, fracDigitsToNanosAuxModel] using fracAux_replicate_zero m (acc * 10)

private theorem fracAux_append :
    ∀ (ds : List Char) (m acc : Nat) (tl : List Char),
      ds.length ≤ m →
      fracDigitsToNanosAuxModel m acc (ds ++ tl) =
        fracDigitsToNanosAuxModel (m - ds.length)
          (ds.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) acc) tl
  | [], m, acc, tl, _ => by simp
  | c :: rest, 0, _, _, hlen => by simp at hlen
  | c :: rest, m + 1, acc, tl, hlen => by
    simpa [fracDigitsToNanosAuxModel, List.foldl_cons, Nat.succ_sub_succ_eq_sub] using
      fracAux_append rest m (acc * 10 + (c.toNat - '0'.toNat)) tl (by simp at hlen; omega)

private def chooseFracLex (nano : Nat) : Option String :=
  if nano == 0 then none
  else some (String.ofList ((padNatZero 9 nano).toList.reverse.dropWhile (· == '0')).reverse)

private theorem renderDate_formatDate (d : Std.Time.PlainDate) (h : validTomlDate d = true) :
    renderDate d = some (formatDate d) := by
  simp [renderDate, formatDate, h]

private theorem renderTime_formatTime (t : Std.Time.PlainTime) (h : validTomlTime t = true) :
    renderTime t (chooseFracLex t.nanosecond.val.toNat) = some (formatTime t) := by
  have hn_p := t.nanosecond.property
  let nano := t.nanosecond.val.toNat
  have hnano_lt : nano < 1000000000 := by dsimp [nano]; omega
  have hval_eq : t.nanosecond.val = Int.ofNat nano := (Int.toNat_of_nonneg hn_p.1).symm
  by_cases hn0 : nano = 0
  · have hv0 : t.nanosecond.val = 0 := by omega
    change renderTime t (chooseFracLex nano) =
      some (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
        padNatZero 2 t.second.val.toNat ++ formatNanosTrimmed nano)
    simp [renderTime, formatNanosTrimmed, chooseFracLex, h, hn0, hv0]
  · obtain ⟨hpad_dig, hpad_fold, hpad_len_fn⟩ := padNatZero_props 9 nano
    have hpad_len : (padNatZero 9 nano).toList.length = 9 :=
      hpad_len_fn (by decide) (by change nano < 1000000000; exact hnano_lt)
    let trimmed := ((padNatZero 9 nano).toList.reverse.dropWhile (· == '0')).reverse
    obtain ⟨k, hk_rev⟩ := dropWhile_zero_decomp (padNatZero 9 nano).toList.reverse
    have hpad_eq : (padNatZero 9 nano).toList = trimmed ++ List.replicate k '0' := by
      have hrev := congrArg List.reverse hk_rev
      simpa [List.reverse_append, List.reverse_replicate, trimmed] using hrev
    have hlen_sum : trimmed.length + k = 9 := by
      have := congrArg List.length hpad_eq; simp at this; omega
    have htrim_dig : trimmed.all isAsciiDigitModel = true := by
      rw [hpad_eq, List.all_append, Bool.and_eq_true] at hpad_dig; exact hpad_dig.1
    have htrim_ne : (!(String.ofList trimmed).isEmpty) = true := by
      cases htl : trimmed with
      | nil =>
        exfalso; apply hn0
        rw [htl, List.nil_append] at hpad_eq
        rw [← hpad_fold, hpad_eq, foldl_replicate_zero]
      | cons _ _ => simp [String.ext_iff]
    have hfrac_eq : fracDigitsToNanosModel trimmed = nano := by
      have h1 := fracAux_append trimmed 9 0 (List.replicate k '0') (by omega)
      have h2 := fracAux_append trimmed 9 0 [] (by omega)
      have h3 := fracAux_append (padNatZero 9 nano).toList 9 0 [] (by omega)
      rw [show 9 - trimmed.length = k by omega, fracAux_replicate_zero] at h1
      rw [show 9 - trimmed.length = k by omega, List.append_nil] at h2
      rw [hpad_len, Nat.sub_self, List.append_nil, fracDigitsToNanosAuxModel, hpad_fold] at h3
      rw [hpad_eq] at h3
      have haux : fracDigitsToNanosAuxModel 9 0 trimmed = nano := h2.trans (h1.symm.trans h3)
      simp [fracDigitsToNanosModel, haux, Nat.min_eq_right (show nano ≤ 999999999 by omega)]
    have hcf : chooseFracLex nano = some (String.ofList trimmed) := by
      simp [chooseFracLex, hn0, trimmed]
    have hfn : formatNanosTrimmed nano = "." ++ String.ofList trimmed := by
      simp [formatNanosTrimmed, hn0, trimmed]
    change renderTime t (chooseFracLex nano) =
      some (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
        padNatZero 2 t.second.val.toNat ++ formatNanosTrimmed nano)
    rw [hcf, hfn]
    simp only [renderTime, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      htrim_ne, String.toList_ofList, htrim_dig, hfrac_eq, Bool.true_and, beq_iff_eq, nano]
    simp [String.append_assoc]

private theorem renderOffset_formatOffset (o : Std.Time.TimeZone.Offset) (h : validTomlOffset o = true) :
    renderOffset o .upperZ = some (formatOffset o) := by
  simp only [renderOffset, formatOffset, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split <;> rfl

/-- In a `noDupKeysBool` entry list, every `(k, v) ∈ entries` is returned by `lookupKeyList k entries`. -/
theorem lookupKeyList_mem_of_noDupKeys (entries : List (String × TomlValue))
    (hnd : noDupKeysBool entries = true) :
    ∀ k v, (k, v) ∈ entries → lookupKeyList k entries = some v := by
  induction entries with
  | nil => intro _ _ hm; nomatch hm
  | cons hd tl ih =>
    rcases hd with ⟨k', _⟩; simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    intro k v hm; rcases List.mem_cons.mp hm with hhead | htail
    · cases hhead; simp [lookupKeyList]
    · have hne : k ≠ k' := fun heq => by
        subst heq; rw [(hasKeyList_eq_true_iff k tl).mpr (List.mem_map.mpr ⟨(k, v), htail, rfl⟩)] at hnd; nomatch hnd.1
      simp [lookupKeyList, beq_false_of_ne hne, ih hnd.2 k v htail]

/-- Look up a key just set in `assocSetSkel`. -/
theorem assocLookupSkel_set_self (k : String) (v : SkeletonNode) :
    ∀ sk : List (String × SkeletonNode), assocLookupSkel k (assocSetSkel k v sk) = some v
  | [] => by simp [assocSetSkel, assocLookupSkel]
  | (k', old) :: rest => by
    by_cases hk : (k == k') = true <;> simp [assocSetSkel, assocLookupSkel, hk, assocLookupSkel_set_self k v rest]

/-- Look up a distinct key across `assocSetSkel`. -/
theorem assocLookupSkel_set_ne {k1 k2 : String} (hne : k1 ≠ k2) (v : SkeletonNode) :
    ∀ sk : List (String × SkeletonNode), assocLookupSkel k1 (assocSetSkel k2 v sk) = assocLookupSkel k1 sk
  | [] => by simp [assocSetSkel, assocLookupSkel, beq_false_of_ne hne]
  | (k', old) :: rest => by
    by_cases h2 : k2 = k'
    · subst h2; simp [assocSetSkel, assocLookupSkel, beq_false_of_ne hne]
    · simp [assocSetSkel, assocLookupSkel, beq_false_of_ne h2, assocLookupSkel_set_ne hne v rest]

/-- Setting the same key twice in `assocSetSkel` collapses to the second write. -/
theorem assocSetSkel_idem (k : String) (v1 v2 : SkeletonNode) :
    ∀ sk : List (String × SkeletonNode), assocSetSkel k v2 (assocSetSkel k v1 sk) = assocSetSkel k v2 sk
  | [] => by simp [assocSetSkel]
  | (k', old) :: rest => by
    by_cases hk : (k == k') = true <;> simp [assocSetSkel, hk, assocSetSkel_idem k v1 v2 rest]

/-- Setting an absent key in `assocSetSkel` appends `(k, v)`. -/
theorem assocSetSkel_eq_append_of_none {k : String} (v : SkeletonNode) :
    ∀ sk : List (String × SkeletonNode), assocLookupSkel k sk = none → assocSetSkel k v sk = sk ++ [(k, v)]
  | [], _ => rfl
  | (k', old) :: rest, hnone => by
    by_cases hk : (k == k') = true
    · simp [assocLookupSkel, hk] at hnone
    · simp only [assocLookupSkel, hk, Bool.false_eq_true, ↓reduceIte] at hnone
      simp [assocSetSkel, hk, assocSetSkel_eq_append_of_none v rest hnone]

/-- Membership of `(k, sn)` in `sk` implies `(assocLookupSkel k sk).isSome = true`. -/
theorem assocLookupSkel_isSome_of_mem {k : String} {sn : SkeletonNode} :
    ∀ {sk : List (String × SkeletonNode)}, (k, sn) ∈ sk → (assocLookupSkel k sk).isSome = true
  | (k', old) :: rest, hm => by
    rcases List.mem_cons.mp hm with hhd | htl
    · obtain ⟨rfl, _⟩ := Prod.mk.inj hhd; simp [assocLookupSkel]
    · by_cases hk : (k == k') = true
      · simp [assocLookupSkel, hk]
      · simp [assocLookupSkel, hk, assocLookupSkel_isSome_of_mem htl]

/-- Sufficient coverage and node-match criteria for `skelMatchesEntries sk entries = true`. -/
theorem skelMatchesEntries_of_props (sk : List (String × SkeletonNode))
    (entries : List (String × TomlValue))
    (hcov : ∀ p ∈ entries, (assocLookupSkel p.1 sk).isSome = true)
    (hall : ∀ k sn, (k, sn) ∈ sk → ∃ v, lookupKeyList k entries = some v ∧ skelNodeMatchesValue sn v = true) :
    skelMatchesEntries sk entries = true := by
  have hall_b : ∀ sk0,
      (∀ k sn, (k, sn) ∈ sk0 → ∃ v, lookupKeyList k entries = some v ∧ skelNodeMatchesValue sn v = true) →
      skelMatchesEntriesAll sk0 entries = true := by
    intro sk0; induction sk0 with
    | nil => intro _; simp [skelMatchesEntriesAll]
    | cons hd rest ih =>
      rcases hd with ⟨k, sn⟩; intro hall0
      obtain ⟨v, hlu, hm⟩ := hall0 k sn List.mem_cons_self
      simp [skelMatchesEntriesAll, hlu, hm, ih (fun k' s' h => hall0 k' s' (List.mem_cons_of_mem _ h))]
  simp [skelMatchesEntries, List.all_eq_true.mpr hcov, hall_b sk hall]

private theorem intercalate_space_aux :
    ∀ (b : String) (bs : List String),
      String.intercalate "," ((" " ++ b) :: bs.map (" " ++ ·)) = " " ++ String.intercalate ", " (b :: bs)
  | b, [] => by simp [String.intercalate_singleton]
  | b, c :: cs => by
    rw [List.map_cons, String.intercalate_cons_cons, intercalate_space_aux c cs, String.intercalate_cons_cons (s := ", ")]
    rw [String.ext_iff]
    simp only [String.toList_append,
      show (" " : String).toList = [' '] from rfl, show ("," : String).toList = [','] from rfl,
      show (", " : String).toList = [',', ' '] from rfl, List.cons_append, List.nil_append, List.append_assoc]

private theorem intercalate_comma_space (hd : String) :
    ∀ tl : List String, String.intercalate "," (hd :: tl.map (" " ++ ·)) = String.intercalate ", " (hd :: tl)
  | [] => by simp [String.intercalate_singleton]
  | b :: bs => by
    rw [List.map_cons, String.intercalate_cons_cons, intercalate_space_aux b bs, String.intercalate_cons_cons (s := ", ")]
    rw [String.ext_iff]
    simp only [String.toList_append,
      show (" " : String).toList = [' '] from rfl, show ("," : String).toList = [','] from rfl,
      show (", " : String).toList = [',', ' '] from rfl, List.cons_append, List.nil_append, List.append_assoc]

private def inlineNodeOf : TomlValue → SkeletonNode
  | .table _ => .inlineTable
  | _ => .leaf

mutual
  /-- Canonical `ValueTape` witnessing `Impl.formatValueInline`. -/
  def chooseValueTape (numApi : NumParseApi) : TomlValue → ValueTape
    | .string _ => .string .basic
    | .int n => .int (some (numApi.formatInt n.toInt))
    | .float f => .float (some (numApi.formatFloat f))
    | .bool _ => .bool
    | .offsetDateTime odt => .offsetDateTime .upperT .upperZ (chooseFracLex odt.dateTime.time.nanosecond.val.toNat)
    | .localDateTime dt => .localDateTime .upperT (chooseFracLex dt.time.nanosecond.val.toNat)
    | .localDate _ => .localDate
    | .localTime t => .localTime (chooseFracLex t.nanosecond.val.toNat)
    | .array xs => .array (chooseArrayElemTapes numApi true xs.toList) none
    | .table t => .inlineTable (chooseInlineAssigns numApi true t.toList) ""
  termination_by v => sizeOf v
  decreasing_by all_goals exact Nat.lt_trans (sizeOf_toList_lt_array _) (by simp +arith)

  /-- Canonical element tapes for `Impl.formatArrayElems`. -/
  def chooseArrayElemTapes (numApi : NumParseApi) (first : Bool) :
      List TomlValue → List (String × ValueTape × String)
    | [] => []
    | x :: xs => (if first then "" else " ", chooseValueTape numApi x, "") :: chooseArrayElemTapes numApi false xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp +arith

  /-- Canonical inline-table assignment tapes for `Impl.formatInlineEntries`. -/
  def chooseInlineAssigns (numApi : NumParseApi) (first : Bool) :
      List (String × TomlValue) → List (String × DottedKeyTape × String × String × ValueTape × String)
    | [] => []
    | (k, v) :: rest =>
      (if first then "" else " ", { firstKey := k, firstStyle := chooseKeyStyle k },
        " ", " ", chooseValueTape numApi v, "") :: chooseInlineAssigns numApi false rest
  termination_by entries => sizeOf entries
  decreasing_by all_goals simp +arith
end

mutual
  /-- `chooseValueTape` always emits a clean `ValueTape`. -/
  theorem chooseValueTape_clean (numApi : NumParseApi) (v : TomlValue) :
      isCleanValueTape (chooseValueTape numApi v) = true := by
    match v with
    | .string _ | .int _ | .float _ | .bool _ | .offsetDateTime _ | .localDateTime _
    | .localDate _ | .localTime _ => simp [chooseValueTape, isCleanValueTape]
    | .array ⟨xsList⟩ =>
      simp [chooseValueTape, isCleanValueTape, chooseArrayElemTapes_clean numApi true xsList]
    | .table ⟨entries⟩ =>
      simp [chooseValueTape, isCleanValueTape, chooseInlineAssigns_clean numApi true entries]
  termination_by sizeOf v
  decreasing_by all_goals simp +arith

  /-- `chooseArrayElemTapes` always emits clean array element tapes. -/
  theorem chooseArrayElemTapes_clean (numApi : NumParseApi) (first : Bool)
      (xs : List TomlValue) :
      isCleanArrayElems first (chooseArrayElemTapes numApi first xs) = true := by
    match xs with
    | [] => simp [chooseArrayElemTapes, isCleanArrayElems]
    | x :: rest =>
      cases first <;>
        simp [chooseArrayElemTapes, isCleanArrayElems,
          chooseValueTape_clean numApi x, chooseArrayElemTapes_clean numApi false rest]
  termination_by sizeOf xs
  decreasing_by all_goals simp +arith

  /-- `chooseInlineAssigns` always emits clean inline-table assignment tapes. -/
  theorem chooseInlineAssigns_clean (numApi : NumParseApi) (first : Bool)
      (entries : List (String × TomlValue)) :
      isCleanInlineAssigns first (chooseInlineAssigns numApi first entries) = true := by
    match entries with
    | [] => simp [chooseInlineAssigns, isCleanInlineAssigns]
    | (k, v) :: rest =>
      cases first <;>
        simp [chooseInlineAssigns, isCleanInlineAssigns, isCleanDottedKey,
          isCleanKeyStyle_chooseKeyStyle k, chooseValueTape_clean numApi v,
          chooseInlineAssigns_clean numApi false rest]
  termination_by sizeOf entries
  decreasing_by all_goals simp +arith
end

mutual
  /-- `Model.renderValueInline` on `chooseValueTape` produces `Impl.formatValueInline`. -/
  theorem renderValueInline_formatValueInline (numApi : NumParseApi) (hfmt : ValidFmt numApi)
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
      simp [chooseValueTape, renderValueInline, formatValueInline, renderDateTimeSep,
        renderDate_formatDate _ hvd.1, renderTime_formatTime _ hvd.2]
    | .localDate d => simp [chooseValueTape, renderValueInline, formatValueInline, renderDate_formatDate d hwf]
    | .localTime t => simp [chooseValueTape, renderValueInline, formatValueInline, renderTime_formatTime t hwf]
    | .array ⟨[]⟩ =>
      rw [chooseValueTape]; unfold renderValueInline
      simp [chooseArrayElemTapes, formatValueInline,
        formatArrayElems, String.intercalate_nil, show isClosedTrivia "" = true by decide]
    | .array ⟨x0 :: xr⟩ =>
      have hwf_l : wellFormedValueBool x0 = true ∧ wellFormedValueBool.wellFormedListBool xr = true := by
        simpa [WellFormedValue, wellFormedValueBool, wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] using hwf
      have hr0 := renderValueInline_formatValueInline numApi hfmt x0 hwf_l.1
      have hrr := renderArrayElems_choose numApi hfmt xr hwf_l.2
      rw [chooseValueTape]; unfold renderValueInline
      simp [chooseArrayElemTapes, renderArrayElems,
        hr0, hrr, formatValueInline, formatArrayElems, intercalate_comma_space,
        show isClosedTrivia "" = true by decide]
    | .table ⟨[]⟩ =>
      rw [chooseValueTape]; unfold renderValueInline
      simp [chooseInlineAssigns, show (#[] : TomlTable).isEmpty = true from rfl,
        formatValueInline, formatInlineEntries, String.intercalate_nil,
        show isHorizWsStr "" = true by decide, noDupKeysBool]
    | .table ⟨(k0, v0) :: rest⟩ =>
      have hwf_t : noDupKeysBool ((k0, v0) :: rest) = true ∧
          wellFormedValueBool.wellFormedTableListBool ((k0, v0) :: rest) = true := by
        simpa [WellFormedValue, wellFormedValueBool, Bool.and_eq_true] using hwf
      have hwf_c : wellFormedValueBool v0 = true ∧ wellFormedValueBool.wellFormedTableListBool rest = true := by
        simpa [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] using hwf_t.2
      have hnd_sp : hasKeyList k0 rest = false ∧ noDupKeysBool rest = true := by
        simpa [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] using hwf_t.1
      have hr0 := renderValueInline_formatValueInline numApi hfmt v0 hwf_c.1
      have hrk0 : renderDottedKey { firstKey := k0, firstStyle := chooseKeyStyle k0 } = some (formatKey k0) := by
        simp [renderDottedKey, renderDottedKeyCont, renderKey_chooseKeyStyle]
      have hins0 : insertDottedAndLookup ((k0, v0) :: rest) [] [k0] = some ([(k0, inlineNodeOf v0)], v0) := by
        cases v0 <;> simp [insertDottedAndLookup, assocLookupSkel, lookupKeyList, assocSetSkel, inlineNodeOf]
      have hdisj0 : ∀ p ∈ rest, assocLookupSkel p.1 [(k0, inlineNodeOf v0)] = none := by
        intro p hp
        have hne : p.1 ≠ k0 := fun he => by
          subst he; rw [(hasKeyList_eq_true_iff p.1 rest).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)] at hnd_sp
          nomatch hnd_sp.1
        simp [assocLookupSkel, beq_false_of_ne hne]
      have hrest := renderInlineAssigns_choose numApi hfmt ((k0, v0) :: rest) rest
        [(k0, inlineNodeOf v0)]
        (fun p hp => lookupKeyList_mem_of_noDupKeys _ hwf_t.1 p.1 p.2 (List.mem_cons_of_mem _ hp))
        hdisj0 hnd_sp.2 hwf_c.2
      let fullSk := (((k0, v0) :: rest).map fun (k, v) => (k, inlineNodeOf v))
      have hsk_eq : [(k0, inlineNodeOf v0)] ++ (rest.map fun (k, v) => (k, inlineNodeOf v)) = fullSk := rfl
      have hmatch : skelMatchesEntries fullSk ((k0, v0) :: rest) = true := by
        refine skelMatchesEntries_of_props fullSk ((k0, v0) :: rest) (fun p hp => ?_) (fun k sn hm => ?_)
        · rcases p with ⟨kp, vp⟩
          exact assocLookupSkel_isSome_of_mem (sn := inlineNodeOf vp)
            (List.mem_map.mpr ⟨(kp, vp), hp, rfl⟩)
        · rcases List.mem_map.mp hm with ⟨⟨k', v'⟩, hmem, heq⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          exact ⟨v', lookupKeyList_mem_of_noDupKeys _ hwf_t.1 k' v' hmem,
            by cases v' <;> simp [inlineNodeOf, skelNodeMatchesValue]⟩
      rw [hsk_eq] at hrest
      rw [chooseValueTape]; unfold renderValueInline
      simp only [chooseInlineAssigns, hwf_t.1,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
      unfold renderInlineAssigns
      simp only [show isHorizWsStr "" = true by decide, show isHorizWsStr " " = true by decide,
        Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        hrk0, DottedKeyTape.path, List.map_nil, hins0, hr0, hrest,
        Option.bind_eq_bind, Option.bind, hmatch]
      simp [formatValueInline, formatInlineEntries, intercalate_comma_space, String.append_assoc]
  termination_by sizeOf v
  decreasing_by all_goals simp +arith

  private theorem renderArrayElems_choose (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (xs : List TomlValue) (hwf : wellFormedValueBool.wellFormedListBool xs = true) :
      renderArrayElems xs (chooseArrayElemTapes numApi false xs) =
        some ((formatArrayElems numApi xs).map (" " ++ ·)) := by
    match xs with
    | [] => simp [chooseArrayElemTapes, renderArrayElems, formatArrayElems]
    | x :: rest =>
      simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at hwf
      simp [chooseArrayElemTapes, renderArrayElems, formatArrayElems,
        renderValueInline_formatValueInline numApi hfmt x hwf.1,
        renderArrayElems_choose numApi hfmt rest hwf.2,
        show isClosedTrivia " " = true by decide, show isClosedTrivia "" = true by decide]
  termination_by sizeOf xs
  decreasing_by all_goals simp +arith

  private theorem renderInlineAssigns_choose (numApi : NumParseApi) (hfmt : ValidFmt numApi)
      (fullEntries subEntries : List (String × TomlValue))
      (sk : List (String × SkeletonNode))
      (hlu : ∀ p ∈ subEntries, lookupKeyList p.1 fullEntries = some p.2)
      (hdisj : ∀ p ∈ subEntries, assocLookupSkel p.1 sk = none)
      (hnd : noDupKeysBool subEntries = true)
      (hwf : wellFormedValueBool.wellFormedTableListBool subEntries = true) :
      renderInlineAssigns fullEntries sk (chooseInlineAssigns numApi false subEntries) =
        some (sk ++ subEntries.map (fun (k, v) => (k, inlineNodeOf v)),
          (formatInlineEntries numApi subEntries).map (" " ++ ·)) := by
    match subEntries with
    | [] => simp [chooseInlineAssigns, renderInlineAssigns, formatInlineEntries]
    | (k, v) :: rest =>
      simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
      simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
      have hk_none := hdisj (k, v) List.mem_cons_self
      have hk_lu := hlu (k, v) List.mem_cons_self
      have hins : insertDottedAndLookup fullEntries sk [k] = some (sk ++ [(k, inlineNodeOf v)], v) := by
        rw [← assocSetSkel_eq_append_of_none (inlineNodeOf v) sk hk_none]
        cases v <;> simp [insertDottedAndLookup, hk_none, hk_lu, inlineNodeOf]
      have hdisj_next : ∀ p ∈ rest, assocLookupSkel p.1 (sk ++ [(k, inlineNodeOf v)]) = none := by
        intro p hp
        have hne : p.1 ≠ k := fun he => by
          subst he; rw [(hasKeyList_eq_true_iff p.1 rest).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)] at hnd
          nomatch hnd.1
        rw [← assocSetSkel_eq_append_of_none (inlineNodeOf v) sk hk_none,
            assocLookupSkel_set_ne hne, hdisj p (List.mem_cons_of_mem _ hp)]
      have hrec := renderInlineAssigns_choose numApi hfmt fullEntries rest
        (sk ++ [(k, inlineNodeOf v)])
        (fun p hp => hlu p (List.mem_cons_of_mem _ hp)) hdisj_next hnd.2 hwf.2
      have hrk : renderDottedKey { firstKey := k, firstStyle := chooseKeyStyle k } = some (formatKey k) := by
        simp [renderDottedKey, renderDottedKeyCont, renderKey_chooseKeyStyle]
      have hrv := renderValueInline_formatValueInline numApi hfmt v hwf.1
      simp only [chooseInlineAssigns, renderInlineAssigns, Bool.false_eq_true, ↓reduceIte,
        show isHorizWsStr " " = true by decide, show isHorizWsStr "" = true by decide,
        Bool.not_true, Bool.or_self, hrk, DottedKeyTape.path, List.map_nil, hins, hrv, hrec,
        Option.bind_eq_bind, Option.bind, formatInlineEntries, List.map_cons, List.append_assoc,
        List.cons_append, List.nil_append, String.append_assoc]
      congr 3
      rw [String.ext_iff]
      simp only [String.toList_append,
        show (" " : String).toList = [' '] from rfl, show ("=" : String).toList = ['='] from rfl,
        show (" = " : String).toList = [' ', '=', ' '] from rfl, show ("" : String).toList = [] from rfl,
        List.cons_append, List.nil_append, List.append_nil]
  termination_by sizeOf subEntries
  decreasing_by all_goals simp +arith
end

end LeanSwe.Toml.Proofs
