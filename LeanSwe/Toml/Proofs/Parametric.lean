import Core.NondetTest
import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.Toml.SpecTests
import LeanSwe.Toml.Proofs.ModelCheckKeysStrings
import LeanSwe.Toml.Proofs.ModelCheckInlineAot
import LeanSwe.Toml.Proofs.ModelCheckNumDtErrFloat
import LeanSwe.Toml.Proofs.ModelCheckNumDt
import LeanSwe.Toml.Proofs.RoundTrip
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests

namespace LeanSwe.Toml.Proofs

open Core
open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Bundle of `NumParse` specification proofs assumed for a parametric `numApi : NumParseApi`. -/
structure ValidNumApi (numApi : NumParseApi) : Prop where
  /-- Errors returned by `numApi` carry non-empty diagnostic messages. -/
  onError : Core.AllPass (test_numparse_onError_returnsNonEmptyMessage numApi)
  /-- `parseInt64` refines `parseInt64Model`. -/
  parseInt64 : Core.AllPass (test_numparse_parseInt64_matchesModel numApi)
  /-- `parseFloat` refines `parseFloatModel`. -/
  parseFloat : Core.AllPass (test_numparse_parseFloat_matchesModel numApi)
  /-- `formatInt` round-trips through `parseInt` and `parseIntModel`. -/
  formatInt : Core.AllPass (test_numparse_formatInt_roundTrip numApi)
  /-- `formatFloat` satisfies `FloatFormatSpec` and round-trips through `parseFloat`. -/
  formatFloat : Core.AllPass (test_numparse_formatFloat_specAndRoundTrip numApi)
  /-- `formatInt` emits canonical signed decimal characters (`'-'` or `'0'..'9'`) with no delimiters or base prefixes. -/
  formatIntChars : ∀ n : Int, (numApi.formatInt n).toList.all (fun c => isAsciiDigit c || c == '-') = true

/-- `nonEmptyMsg` always returns a non-empty string. -/
theorem nonEmptyMsg_nonEmpty (msg : String) : (!(nonEmptyMsg msg).isEmpty) = true := by
  unfold nonEmptyMsg
  split
  · decide
  · rename_i h
    simp [h]

/-- Errors built by `mkErr` always have non-empty messages. -/
theorem mkErr_nonEmpty (kind : TomlErrorKind) (msg : String)
    (line : Option Nat := none) (col : Option Nat := none) (path : Option String := none) :
    (!(mkErr kind msg line col path).message.isEmpty) = true :=
  nonEmptyMsg_nonEmpty msg

/-- Implicit-argument helper for `mkErr` message non-emptiness. -/
theorem mkErr_nonEmpty' {kind : TomlErrorKind} {msg : String}
    {line : Option Nat} {col : Option Nat} {path : Option String} :
    (!(mkErr kind msg line col path).message.isEmpty) = true :=
  nonEmptyMsg_nonEmpty msg

/-- `tomlTableListBeq` lookup consistency helper. -/
theorem lookupKeyList_of_tomlTableListBeq_none (e1 e2 : List (String × TomlValue))
    (h : tomlValueBeq.tomlTableListBeq e1 e2 = true) (k : String)
    (hk : lookupKeyList k e1 = none) : lookupKeyList k e2 = none := by
  induction e1 generalizing e2 with
  | nil =>
    cases e2 with
    | nil => rfl
    | cons _ _ => simp [tomlValueBeq.tomlTableListBeq] at h
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨k1, v1⟩
    cases e2 with
    | nil => simp [tomlValueBeq.tomlTableListBeq] at h
    | cons hd2 tl2 =>
      rcases hd2 with ⟨k2, v2⟩
      simp only [tomlValueBeq.tomlTableListBeq, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨hk12, _⟩, htl⟩
      subst hk12
      simp only [lookupKeyList] at hk ⊢
      by_cases heqk : (k == k1) = true
      · simp [heqk] at hk
      · simp only [heqk] at hk ⊢
        exact ih tl2 htl hk

/-- `tomlTableListBeq` lookup correspondence helper. -/
theorem lookupKeyList_of_tomlTableListBeq_some (e1 e2 : List (String × TomlValue))
    (h : tomlValueBeq.tomlTableListBeq e1 e2 = true) (k : String) (v1 : TomlValue)
    (hk : lookupKeyList k e1 = some v1) :
    ∃ v2, lookupKeyList k e2 = some v2 ∧ tomlValueBeq v1 v2 = true := by
  induction e1 generalizing e2 with
  | nil => simp [lookupKeyList] at hk
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨k1, v1'⟩
    cases e2 with
    | nil => simp [tomlValueBeq.tomlTableListBeq] at h
    | cons hd2 tl2 =>
      rcases hd2 with ⟨k2, v2'⟩
      simp only [tomlValueBeq.tomlTableListBeq, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨hk12, hv12⟩, htl⟩
      subst hk12
      simp only [lookupKeyList] at hk ⊢
      by_cases heqk : (k == k1) = true
      · simp only [heqk, ↓reduceIte, Option.some.injEq] at hk ⊢
        subst hk
        exact ⟨v2', rfl, hv12⟩
      · simp only [heqk, Bool.false_eq_true, ↓reduceIte] at hk ⊢
        exact ih tl2 htl hk

/-- `TomlOffsetDateTime` boolean equality reflects Leibniz equality. -/
theorem tomlOffsetDateTime_eq_of_beq {a b : TomlOffsetDateTime} (h : (a == b) = true) : a = b := by
  cases a with | mk ad ao =>
  cases b with | mk bd bo =>
  have h1 : (ad == bd && ao == bo) = true := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  rcases h1 with ⟨hd, ho⟩
  subst hd ho
  rfl

/-- `tomlValueBeq` returning `true` implies `TomlEquiv`. -/
theorem tomlValueBeq_implies_equiv (a b : TomlValue) (h : tomlValueBeq a b = true) :
    TomlEquiv a b := by
  suffices hmain : ∀ n : Nat, ∀ x y : TomlValue, sizeOf x ≤ n → tomlValueBeq x y = true → TomlEquiv x y from
    hmain (sizeOf a) a b (Nat.le_refl _) h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x y hx hxy
    cases x with
    | string s1 =>
      cases y <;> simp [tomlValueBeq, TomlEquiv] at hxy ⊢
      exact hxy
    | int n1 =>
      cases y <;> simp [tomlValueBeq, TomlEquiv] at hxy ⊢
      exact hxy
    | float f1 =>
      cases y with
      | float f2 =>
        simp only [tomlValueBeq] at hxy
        simp only [TomlEquiv, FloatEquiv]
        exact Or.inr hxy
      | _ => simp [tomlValueBeq] at hxy
    | bool b1 =>
      cases y <;> simp [tomlValueBeq, TomlEquiv] at hxy ⊢
      exact hxy
    | offsetDateTime d1 =>
      cases y <;> simp [tomlValueBeq, TomlEquiv] at hxy ⊢
      exact tomlOffsetDateTime_eq_of_beq hxy
    | localDateTime d1 =>
      cases y <;> simp [tomlValueBeq, TomlEquiv] at hxy ⊢
      exact hxy
    | localDate d1 =>
      cases y <;> simp [tomlValueBeq, TomlEquiv] at hxy ⊢
      exact hxy
    | localTime t1 =>
      cases y <;> simp [tomlValueBeq, TomlEquiv] at hxy ⊢
      exact hxy
    | array xs =>
      cases y with
      | array ys =>
        simp only [tomlValueBeq] at hxy
        simp only [TomlEquiv]
        have hlist : ∀ l1 l2 : List TomlValue,
            sizeOf l1 < sizeOf (TomlValue.array xs) →
            tomlValueBeq.tomlArrayBeq l1 l2 = true → TomlListEquiv l1 l2 := by
          intro l1 l2 hl1 h12
          induction l1 generalizing l2 with
          | nil =>
            cases l2 with
            | nil => simp [TomlListEquiv]
            | cons _ _ => simp [tomlValueBeq.tomlArrayBeq] at h12
          | cons hd1 tl1 ihl =>
            cases l2 with
            | nil => simp [tomlValueBeq.tomlArrayBeq] at h12
            | cons hd2 tl2 =>
              simp only [tomlValueBeq.tomlArrayBeq, Bool.and_eq_true] at h12
              simp only [TomlListEquiv]
              have hhd : sizeOf hd1 < sizeOf (hd1 :: tl1) := by simp +arith
              have htl : sizeOf tl1 < sizeOf (hd1 :: tl1) := by simp +arith
              have hn : sizeOf hd1 < n := Nat.lt_of_lt_of_le (Nat.lt_trans hhd hl1) hx
              exact ⟨ih (sizeOf hd1) hn hd1 hd2 (Nat.le_refl _) h12.1,
                ihl tl2 (Nat.lt_trans htl hl1) h12.2⟩
        exact hlist xs.toList ys.toList (Nat.lt_trans (sizeOf_toList_lt_array xs) (by simp +arith)) hxy
      | _ => simp [tomlValueBeq] at hxy
    | table t1 =>
      cases y with
      | table t2 =>
        simp only [tomlValueBeq] at hxy
        simp only [TomlEquiv, TomlTableEquivList]
        constructor
        · exact lookupKeyList_of_tomlTableListBeq_none t1.toList t2.toList hxy
        · intro k v1 hk1
          obtain ⟨v2, hk2, hv12⟩ :=
            lookupKeyList_of_tomlTableListBeq_some t1.toList t2.toList hxy k v1 hk1
          have hv : sizeOf v1 < sizeOf t1.toList := lookupKeyList_sizeOf hk1
          have ht : sizeOf t1.toList < sizeOf (TomlValue.table t1) :=
            Nat.lt_trans (sizeOf_toList_lt_array t1) (by simp +arith)
          exact ⟨v2, hk2, ih (sizeOf v1) (by omega) v1 v2 (Nat.le_refl _) hv12⟩
      | _ => simp [tomlValueBeq] at hxy

/-- Structural boolean table equality implies `TomlTableEquiv`. -/
theorem tomlTableBeq_implies_equiv {t1 t2 : TomlTable} (h : (t1 == t2) = true) :
    TomlTableEquiv t1 t2 := by
  have hval : tomlValueBeq (.table t1) (.table t2) = true := by
    change tomlValueBeq.tomlTableListBeq t1.toList t2.toList = true
    have hlist : (t1.toList == t2.toList) = true := by
      cases t1; cases t2
      simpa using h
    clear h
    match t1, t2 with
    | ⟨l1⟩, ⟨l2⟩ =>
      induction l1 generalizing l2 with
      | nil =>
        cases l2 with
        | nil => rfl
        | cons _ _ => simp at hlist
      | cons a l1' ih =>
        cases l2 with
        | nil => simp at hlist
        | cons b l2' =>
          rcases a with ⟨k1, v1⟩
          rcases b with ⟨k2, v2⟩
          change ((k1 == k2 && tomlValueBeq v1 v2) && (l1' == l2')) = true at hlist
          simp only [Bool.and_eq_true] at hlist
          simp only [tomlValueBeq.tomlTableListBeq, Bool.and_eq_true]
          exact ⟨hlist.1, ih l2' hlist.2⟩
  simpa [TomlEquiv, TomlTableEquiv] using tomlValueBeq_implies_equiv (.table t1) (.table t2) hval

/-- Deconstruct an `Except.bind` returning `.error`. -/
theorem except_bind_err {α β ε : Type} {m : Except ε α} {f : α → Except ε β} {e : ε}
    (h : (m >>= f) = .error e) : (m = .error e) ∨ (∃ a, m = .ok a ∧ f a = .error e) := by
  cases m with
  | error e' =>
    simp only [bind, Except.bind, Except.error.injEq] at h
    exact Or.inl (congrArg Except.error h)
  | ok a =>
    simp only [bind, Except.bind] at h
    exact Or.inr ⟨a, rfl, h⟩

/-- Errors from `normalizeChars` have non-empty messages. -/
theorem normalizeChars_err_nonEmpty (line col : Nat) (cs : List Char) (e : TomlError)
    (herr : normalizeChars line col cs = .error e) : (!e.message.isEmpty) = true := by
  unfold normalizeChars at herr
  split at herr
  · simp at herr
  · rcases except_bind_err herr with h | ⟨_, _, h⟩
    · exact normalizeChars_err_nonEmpty (line + 1) 1 _ e h
    · simp at h
  · cases herr; exact mkErr_nonEmpty _ _ _ _
  · rcases except_bind_err herr with h | ⟨_, _, h⟩
    · exact normalizeChars_err_nonEmpty (line + 1) 1 _ e h
    · simp at h
  · split at herr
    · cases herr; exact mkErr_nonEmpty _ _ _ _
    · rcases except_bind_err herr with h | ⟨_, _, h⟩
      · exact normalizeChars_err_nonEmpty line (col + 1) _ e h
      · simp at h
termination_by cs.length

/-- Errors from `parseUnicodeHex` have non-empty messages. -/
theorem parseUnicodeHex_err_nonEmpty (count : Nat) (cs : List Char) (e : TomlError)
    (herr : parseUnicodeHex count cs = .error e) : (!e.message.isEmpty) = true := by
  unfold parseUnicodeHex at herr
  split at herr
  · cases herr; exact mkErr_nonEmpty _ _ _ _
  · split at herr
    · cases herr; exact mkErr_nonEmpty _ _ _ _
    · cases herr

/-- Errors from `parseBasicEscape` have non-empty messages. -/
theorem parseBasicEscape_err_nonEmpty (cs : List Char) (e : TomlError)
    (herr : parseBasicEscape cs = .error e) : (!e.message.isEmpty) = true := by
  unfold parseBasicEscape at herr
  split at herr <;>
    first
    | contradiction
    | (cases herr; exact mkErr_nonEmpty _ _ _ _)
    | exact parseUnicodeHex_err_nonEmpty _ _ e herr

/-- Errors from `parseBasicStringBodyFuel` have non-empty messages. -/
theorem parseBasicStringBodyFuel_err_nonEmpty (fuel : Nat) (acc cs : List Char) (e : TomlError)
    (herr : parseBasicStringBodyFuel fuel acc cs = .error e) : (!e.message.isEmpty) = true := by
  induction fuel generalizing acc cs with
  | zero =>
    simp only [parseBasicStringBodyFuel] at herr
    cases herr; exact mkErr_nonEmpty'
  | succ fuel ih =>
    unfold parseBasicStringBodyFuel at herr
    split at herr
    · cases herr; exact mkErr_nonEmpty'
    · cases herr; exact mkErr_nonEmpty'
    · cases herr; exact mkErr_nonEmpty'
    · contradiction
    · rename_i heq
      cases Nat.succ.inj heq
      rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
      · exact parseBasicEscape_err_nonEmpty _ e h
      · exact ih _ _ h
    · rename_i heq
      cases Nat.succ.inj heq
      exact ih _ _ herr

/-- Errors from `parseLiteralStringBody` have non-empty messages. -/
theorem parseLiteralStringBody_err_nonEmpty (acc cs : List Char) (e : TomlError)
    (herr : parseLiteralStringBody acc cs = .error e) : (!e.message.isEmpty) = true := by
  induction cs generalizing acc with
  | nil =>
    simp only [parseLiteralStringBody] at herr
    cases herr; exact mkErr_nonEmpty'
  | cons c rest ih =>
    unfold parseLiteralStringBody at herr
    split at herr
    · cases herr; exact mkErr_nonEmpty'
    · cases herr; exact mkErr_nonEmpty'
    · contradiction
    · rename_i c' rest' _ _ heq
      obtain ⟨_, rfl⟩ := List.cons.inj heq
      exact ih _ herr

/-- Errors from `parseMultilineBasicBodyFuel` have non-empty messages. -/
theorem parseMultilineBasicBodyFuel_err_nonEmpty (fuel : Nat) (acc cs : List Char) (e : TomlError)
    (herr : parseMultilineBasicBodyFuel fuel acc cs = .error e) : (!e.message.isEmpty) = true := by
  induction fuel generalizing acc cs with
  | zero =>
    simp only [parseMultilineBasicBodyFuel] at herr
    cases herr; exact mkErr_nonEmpty'
  | succ fuel ih =>
    unfold parseMultilineBasicBodyFuel at herr
    split at herr
    · cases herr; exact mkErr_nonEmpty'
    · cases herr; exact mkErr_nonEmpty'
    · cases herr; exact mkErr_nonEmpty'
    · contradiction
    · contradiction
    · contradiction
    · rename_i heq
      cases Nat.succ.inj heq
      split at herr
      · exact ih _ _ herr
      · split at herr
        · exact ih _ _ herr
        · split at herr
          · cases herr; exact parseBasicEscape_err_nonEmpty _ e ‹_›
          · cases herr; exact parseBasicEscape_err_nonEmpty _ e ‹_›
          · cases herr; exact mkErr_nonEmpty'
    · rename_i heq
      cases Nat.succ.inj heq
      exact ih _ _ herr

/-- Errors from `parseMultilineLiteralBodyFuel` have non-empty messages. -/
theorem parseMultilineLiteralBodyFuel_err_nonEmpty (fuel : Nat) (acc cs : List Char) (e : TomlError)
    (herr : parseMultilineLiteralBodyFuel fuel acc cs = .error e) : (!e.message.isEmpty) = true := by
  induction fuel generalizing acc cs with
  | zero =>
    simp only [parseMultilineLiteralBodyFuel] at herr
    cases herr; exact mkErr_nonEmpty'
  | succ fuel ih =>
    unfold parseMultilineLiteralBodyFuel at herr
    split at herr
    · cases herr; exact mkErr_nonEmpty'
    · cases herr; exact mkErr_nonEmpty'
    · cases herr; exact mkErr_nonEmpty'
    · contradiction
    · contradiction
    · contradiction
    · rename_i heq
      cases Nat.succ.inj heq
      exact ih _ _ herr

/-- Errors from `parseKeySegment` have non-empty messages. -/
theorem parseKeySegment_err_nonEmpty (cs : List Char) (e : TomlError)
    (herr : parseKeySegment cs = .error e) : (!e.message.isEmpty) = true := by
  unfold parseKeySegment at herr
  split at herr
  · cases herr; exact mkErr_nonEmpty'
  · cases herr; exact mkErr_nonEmpty'
  · exact parseBasicStringBodyFuel_err_nonEmpty _ _ _ e herr
  · exact parseLiteralStringBody_err_nonEmpty _ _ e herr
  · dsimp only at herr
    split at herr
    · cases herr; exact mkErr_nonEmpty'
    · contradiction

/-- Errors from `parseDottedKeyFuel` have non-empty messages. -/
theorem parseDottedKeyFuel_err_nonEmpty (fuel : Nat) (cs : List Char) (e : TomlError)
    (herr : parseDottedKeyFuel fuel cs = .error e) : (!e.message.isEmpty) = true := by
  induction fuel generalizing cs with
  | zero =>
    simp only [parseDottedKeyFuel] at herr
    cases herr; exact mkErr_nonEmpty'
  | succ fuel ih =>
    unfold parseDottedKeyFuel at herr
    rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
    · exact parseKeySegment_err_nonEmpty _ e h
    · dsimp only at h
      split at h
      · rcases except_bind_err h with h2 | ⟨⟨_, _⟩, _, h2⟩
        · exact ih _ h2
        · contradiction
      · contradiction

/-- Errors from `parseDatePart` have non-empty messages. -/
theorem parseDatePart_err_nonEmpty (cs : List Char) (e : TomlError)
    (herr : parseDatePart cs = .error e) : (!e.message.isEmpty) = true := by
  unfold parseDatePart at herr
  repeat' (first | contradiction | (split at herr <;> try (cases herr; exact mkErr_nonEmpty')) | (cases herr; exact mkErr_nonEmpty'))

/-- Errors from `parseTimePart` have non-empty messages. -/
theorem parseTimePart_err_nonEmpty (cs : List Char) (e : TomlError)
    (herr : parseTimePart cs = .error e) : (!e.message.isEmpty) = true := by
  unfold parseTimePart at herr
  repeat' (first | contradiction | (split at herr <;> try (cases herr; exact mkErr_nonEmpty')) | (cases herr; exact mkErr_nonEmpty'))

/-- Errors from `parseOffsetPart` have non-empty messages. -/
theorem parseOffsetPart_err_nonEmpty (cs : List Char) (e : TomlError)
    (herr : parseOffsetPart cs = .error e) : (!e.message.isEmpty) = true := by
  unfold parseOffsetPart at herr
  dsimp only at herr
  repeat' (first | contradiction | (split at herr <;> try (cases herr; exact mkErr_nonEmpty')) | (cases herr; exact mkErr_nonEmpty'))

/-- Errors from `parseDateTimeToken` have non-empty messages. -/
theorem parseDateTimeToken_err_nonEmpty (tok : String) (e : TomlError)
    (herr : parseDateTimeToken tok = some (.error e)) : (!e.message.isEmpty) = true := by
  unfold parseDateTimeToken at herr
  dsimp only at herr
  split at herr
  · split at herr
    · cases herr; exact parseDatePart_err_nonEmpty _ e ‹_›
    · cases herr
    · split at herr
      · split at herr
        · cases herr; exact parseTimePart_err_nonEmpty _ e ‹_›
        · cases herr
        · split at herr
          · cases herr; exact parseOffsetPart_err_nonEmpty _ e ‹_›
          · cases herr
      · cases herr; exact mkErr_nonEmpty'
  · split at herr
    · split at herr
      · cases herr; exact parseTimePart_err_nonEmpty _ e ‹_›
      · cases herr
      · cases herr; exact mkErr_nonEmpty'
    · split at herr
      · cases herr; exact mkErr_nonEmpty'
      · cases herr

/-- Errors from `classifyScalarToken` have non-empty messages. -/
theorem classifyScalarToken_err_nonEmpty (numApi : NumParseApi) (tok : String) (e : TomlError)
    (herr : classifyScalarToken numApi tok = .error e) : (!e.message.isEmpty) = true := by
  unfold classifyScalarToken at herr
  split at herr
  · cases herr; exact mkErr_nonEmpty'
  · split at herr
    · contradiction
    · split at herr
      · contradiction
      · split at herr
        · rename_i res hres
          rw [herr] at hres
          exact parseDateTimeToken_err_nonEmpty tok e hres
        · split at herr
          · split at herr
            · contradiction
            · cases herr; exact mkErr_nonEmpty'
          · split at herr
            · cases herr; exact mkErr_nonEmpty'
            · split at herr
              · contradiction
              · cases herr; exact mkErr_nonEmpty'

/-- Errors from `insertDottedEntries` have non-empty messages. -/
theorem insertDottedEntries_err_nonEmpty (fullPath : List String)
    (entries : List (String × Node)) (relPath : List String) (newNode : Node) (e : TomlError)
    (herr : insertDottedEntries fullPath entries relPath newNode = .error e) :
    (!e.message.isEmpty) = true := by
  induction relPath generalizing entries with
  | nil =>
    simp only [insertDottedEntries] at herr
    cases herr; exact mkErr_nonEmpty'
  | cons k rest ih =>
    cases rest with
    | nil =>
      unfold insertDottedEntries at herr
      split at herr
      · contradiction
      · cases herr; exact mkErr_nonEmpty'
      · cases herr; exact mkErr_nonEmpty'
    | cons k2 rest2 =>
      unfold insertDottedEntries at herr
      split at herr
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact ih [] h
        · contradiction
      · cases herr; exact mkErr_nonEmpty'
      · cases herr; exact mkErr_nonEmpty'
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact ih _ h
        · contradiction
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact ih _ h
        · contradiction
      · cases herr; exact mkErr_nonEmpty'
      · cases herr; exact mkErr_nonEmpty'
      · cases herr; exact mkErr_nonEmpty'

/-- Errors from `parseValueFuel`, `parseArrayFuel`, and `parseInlineTableFuel` have non-empty messages. -/
theorem parseValArrInline_err_nonEmpty (numApi : NumParseApi) (fuel : Nat) :
    (∀ cs e, parseValueFuel numApi fuel cs = .error e → (!e.message.isEmpty) = true) ∧
    (∀ cs acc e, parseArrayFuel numApi fuel cs acc = .error e → (!e.message.isEmpty) = true) ∧
    (∀ cs entries e, parseInlineTableFuel numApi fuel cs entries = .error e → (!e.message.isEmpty) = true) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intro cs <;> intros <;> cases ‹_› <;> exact mkErr_nonEmpty'
  | succ fuel ih =>
    rcases ih with ⟨ihVal, ihArr, ihInl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro cs e herr
      unfold parseValueFuel at herr
      split at herr
      · rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
        · exact parseMultilineBasicBodyFuel_err_nonEmpty _ _ _ e h
        · contradiction
      · rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
        · exact parseBasicStringBodyFuel_err_nonEmpty _ _ _ e h
        · contradiction
      · rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
        · exact parseMultilineLiteralBodyFuel_err_nonEmpty _ _ _ e h
        · contradiction
      · rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
        · exact parseLiteralStringBody_err_nonEmpty _ _ e h
        · contradiction
      · exact ihArr _ _ e herr
      · split at herr
        · contradiction
        · exact ihInl _ _ e herr
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact classifyScalarToken_err_nonEmpty numApi _ e h
        · cases h
    · intro cs acc e herr
      unfold parseArrayFuel at herr
      split at herr
      · contradiction
      · cases herr; exact mkErr_nonEmpty'
      · rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
        · exact ihVal _ e h
        · dsimp only at h
          split at h
          · exact ihArr _ _ e h
          · cases h
          · cases h; exact mkErr_nonEmpty'
    · intro cs entries e herr
      unfold parseInlineTableFuel at herr
      rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
      · exact parseDottedKeyFuel_err_nonEmpty _ _ e h
      · dsimp only at h
        split at h
        · rcases except_bind_err h with h2 | ⟨⟨_, _⟩, _, h2⟩
          · exact ihVal _ e h2
          · rcases except_bind_err h2 with h3 | ⟨_, _, h3⟩
            · exact insertDottedEntries_err_nonEmpty _ _ _ _ e h3
            · dsimp only at h3
              split at h3
              · split at h3
                · cases h3; exact mkErr_nonEmpty'
                · exact ihInl _ _ e h3
              · cases h3
              · cases h3; exact mkErr_nonEmpty'
        · cases h; exact mkErr_nonEmpty'

/-- Errors from `mapLastAot` have non-empty messages. -/
theorem mapLastAot_err_nonEmpty (f : List (String × Node) → Except TomlError (List (String × Node)))
    (hf : ∀ x e, f x = .error e → (!e.message.isEmpty) = true)
    (elems : List (List (String × Node))) (e : TomlError)
    (herr : mapLastAot f elems = .error e) : (!e.message.isEmpty) = true := by
  induction elems with
  | nil =>
    simp only [mapLastAot] at herr
    cases herr; exact mkErr_nonEmpty'
  | cons hd tl ih =>
    cases tl with
    | nil =>
      unfold mapLastAot at herr
      rcases except_bind_err herr with h | ⟨_, _, h⟩
      · exact hf hd e h
      · contradiction
    | cons hd2 tl2 =>
      unfold mapLastAot at herr
      rcases except_bind_err herr with h | ⟨_, _, h⟩
      · exact ih h
      · contradiction

/-- Errors from `applyTableHeader` have non-empty messages. -/
theorem applyTableHeader_err_nonEmpty (fullPath : List String)
    (entries : List (String × Node)) (path : List String) (e : TomlError)
    (herr : applyTableHeader fullPath entries path = .error e) : (!e.message.isEmpty) = true := by
  induction path generalizing entries e with
  | nil =>
    simp only [applyTableHeader] at herr
    cases herr; exact mkErr_nonEmpty'
  | cons k rest ih =>
    cases rest with
    | nil =>
      unfold applyTableHeader at herr
      split at herr <;> first | contradiction | (cases herr; exact mkErr_nonEmpty')
    | cons k2 rest2 =>
      unfold applyTableHeader at herr
      split at herr
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact ih [] e h
        · contradiction
      · cases herr; exact mkErr_nonEmpty'
      · cases herr; exact mkErr_nonEmpty'
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact ih _ e h
        · contradiction
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact mapLastAot_err_nonEmpty _ (fun _ e' hsub => ih _ e' hsub) _ e h
        · contradiction
      · cases herr; exact mkErr_nonEmpty'

/-- Errors from `applyAotHeader` have non-empty messages. -/
theorem applyAotHeader_err_nonEmpty (fullPath : List String)
    (entries : List (String × Node)) (path : List String) (e : TomlError)
    (herr : applyAotHeader fullPath entries path = .error e) : (!e.message.isEmpty) = true := by
  induction path generalizing entries e with
  | nil =>
    simp only [applyAotHeader] at herr
    cases herr; exact mkErr_nonEmpty'
  | cons k rest ih =>
    cases rest with
    | nil =>
      unfold applyAotHeader at herr
      split at herr <;> first | contradiction | (cases herr; exact mkErr_nonEmpty')
    | cons k2 rest2 =>
      unfold applyAotHeader at herr
      split at herr
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact ih [] e h
        · contradiction
      · cases herr; exact mkErr_nonEmpty'
      · cases herr; exact mkErr_nonEmpty'
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact ih _ e h
        · contradiction
      · rcases except_bind_err herr with h | ⟨_, _, h⟩
        · exact mapLastAot_err_nonEmpty _ (fun _ e' hsub => ih _ e' hsub) _ e h
        · contradiction
      · cases herr; exact mkErr_nonEmpty'

/-- Errors from `insertAtActivePath` have non-empty messages. -/
theorem insertAtActivePath_err_nonEmpty (fullPath : List String)
    (entries : List (String × Node)) (activePath relPath : List String) (valNode : Node) (e : TomlError)
    (herr : insertAtActivePath fullPath entries activePath relPath valNode = .error e) :
    (!e.message.isEmpty) = true := by
  induction activePath generalizing entries e with
  | nil =>
    simp only [insertAtActivePath] at herr
    exact insertDottedEntries_err_nonEmpty fullPath entries relPath valNode e herr
  | cons k rest ih =>
    unfold insertAtActivePath at herr
    split at herr
    · rcases except_bind_err herr with h | ⟨_, _, h⟩
      · exact ih _ e h
      · contradiction
    · rcases except_bind_err herr with h | ⟨_, _, h⟩
      · exact mapLastAot_err_nonEmpty _ (fun _ e' hsub => ih _ e' hsub) _ e h
      · contradiction
    · cases herr; exact mkErr_nonEmpty'

/-- Errors from `consumeStatementEnd` have non-empty messages. -/
theorem consumeStatementEnd_err_nonEmpty (cs : List Char) (e : TomlError)
    (herr : consumeStatementEnd cs = .error e) : (!e.message.isEmpty) = true := by
  unfold consumeStatementEnd at herr
  split at herr <;> try cases herr
  exact mkErr_nonEmpty _ _ _ _

/-- Errors from `parseDocumentFuel` have non-empty messages. -/
theorem parseDocumentFuel_err_nonEmpty (numApi : NumParseApi)
    (fuel : Nat) (cs : List Char) (activePath : List String) (root : List (String × Node)) (e : TomlError)
    (herr : parseDocumentFuel numApi fuel cs activePath root = .error e) :
    (!e.message.isEmpty) = true := by
  induction fuel generalizing cs activePath root with
  | zero =>
    unfold parseDocumentFuel at herr
    split at herr
    · cases herr
    · cases herr; exact mkErr_nonEmpty _ _ _ _
  | succ fuel ih =>
    unfold parseDocumentFuel at herr
    split at herr
    · cases herr
    · rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
      · exact parseDottedKeyFuel_err_nonEmpty _ _ e h
      · dsimp only at h
        split at h
        · rcases except_bind_err h with h2 | ⟨_, _, h2⟩
          · exact consumeStatementEnd_err_nonEmpty _ e h2
          · rcases except_bind_err h2 with h3 | ⟨_, _, h3⟩
            · exact applyAotHeader_err_nonEmpty _ _ _ e h3
            · exact ih _ _ _ h3
        · cases h; exact mkErr_nonEmpty _ _ _ _
    · rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
      · exact parseDottedKeyFuel_err_nonEmpty _ _ e h
      · dsimp only at h
        split at h
        · rcases except_bind_err h with h2 | ⟨_, _, h2⟩
          · exact consumeStatementEnd_err_nonEmpty _ e h2
          · rcases except_bind_err h2 with h3 | ⟨_, _, h3⟩
            · exact applyTableHeader_err_nonEmpty _ _ _ e h3
            · exact ih _ _ _ h3
        · cases h; exact mkErr_nonEmpty _ _ _ _
    · rcases except_bind_err herr with h | ⟨⟨_, _⟩, _, h⟩
      · exact parseDottedKeyFuel_err_nonEmpty _ _ e h
      · dsimp only at h
        split at h
        · rcases except_bind_err h with h2 | ⟨⟨_, _⟩, _, h2⟩
          · exact (parseValArrInline_err_nonEmpty numApi _).1 _ e h2
          · rcases except_bind_err h2 with h3 | ⟨_, _, h3⟩
            · exact consumeStatementEnd_err_nonEmpty _ e h3
            · rcases except_bind_err h3 with h4 | ⟨_, _, h4⟩
              · exact insertAtActivePath_err_nonEmpty _ _ _ _ _ e h4
              · exact ih _ _ _ h4
        · cases h; exact mkErr_nonEmpty _ _ _ _

/-- Any error returned by `parseWithNum` carries a non-empty diagnostic message. -/
theorem parseWithNum_error_nonEmpty (numApi : NumParseApi) (s : String) (e : TomlError)
    (herr : parseWithNum numApi s = .error e) : (!e.message.isEmpty) = true := by
  unfold parseWithNum at herr
  rcases except_bind_err herr with h | ⟨_, _, h⟩
  · exact normalizeChars_err_nonEmpty 1 1 s.toList e h
  · rcases except_bind_err h with h2 | ⟨_, _, h2⟩
    · exact parseDocumentFuel_err_nonEmpty numApi _ _ [] [] e h2
    · cases h2

/-- Prove `test_toml_onError_returnsNonEmptyMessage` for `makeTomlApi numApi`. -/
theorem allPass_onError (numApi : NumParseApi) :
    Core.AllPass (test_toml_onError_returnsNonEmptyMessage (makeTomlApi numApi)) := by
  dsimp only [Core.AllPass, test_toml_onError_returnsNonEmptyMessage, Core.NondetTest.nondet,
    NondetTest.assert, bind, pure]
  intro s
  simp only [makeTomlApi]
  cases h : parseWithNum numApi s with
  | ok _ => trivial
  | error e =>
    refine ⟨?_, trivial⟩
    simpa using parseWithNum_error_nonEmpty numApi s e h

/-- Convert `(!s.isEmpty) = true` to `(!decide (s.isEmpty = true)) = true`. -/
theorem not_decide_isEmpty_eq_true {s : String} (h : (!s.isEmpty) = true) :
    (!decide (s.isEmpty = true)) = true := by
  simpa using h

/-- Prove `test_toml_accessorError_returnsNonEmptyMessage` for `makeTomlApi numApi`. -/
theorem allPass_accessorError (numApi : NumParseApi) :
    Core.AllPass (test_toml_accessorError_returnsNonEmptyMessage (makeTomlApi numApi)) := by
  dsimp only [Core.AllPass, test_toml_accessorError_returnsNonEmptyMessage, Core.NondetTest.nondet,
    NondetTest.assert, bind, pure]
  intro v t k path
  simp only [makeTomlApi]
  have htab : ∀ e, tomlGetTable v = .error e → (!decide (e.message.isEmpty = true)) = true := by
    intro e he
    cases v <;> simp [tomlGetTable] at he <;> subst he <;> exact not_decide_isEmpty_eq_true mkErr_nonEmpty'
  have harr : ∀ e, tomlGetArray v = .error e → (!decide (e.message.isEmpty = true)) = true := by
    intro e he
    cases v <;> simp [tomlGetArray] at he <;> subst he <;> exact not_decide_isEmpty_eq_true mkErr_nonEmpty'
  have hfld : ∀ e, tomlGetField (α := TomlValue) t k = .error e →
      (!decide (e.message.isEmpty = true)) = true := by
    intro e he
    simp only [tomlGetField] at he
    cases hl : lookupKey k t with
    | none => simp [hl] at he; subst he; exact not_decide_isEmpty_eq_true mkErr_nonEmpty'
    | some val => simp [hl, FromToml.fromToml] at he
  have hopt : ∀ e, tomlGetOptField (α := String) t k = .error e →
      (!decide (e.message.isEmpty = true)) = true := by
    intro e he
    simp only [tomlGetOptField] at he
    cases hl : lookupKey k t with
    | none => simp [hl] at he
    | some val =>
      simp only [hl] at he
      cases val <;> simp [FromToml.fromToml] at he <;>
        subst he <;> exact not_decide_isEmpty_eq_true (nonEmptyMsg_nonEmpty _)
  have hpathAux : ∀ (p acc : List String) (tbl : TomlTable) (e : TomlError),
      tomlGetPathAux (α := TomlValue) acc tbl p = .error e →
      (!decide (e.message.isEmpty = true)) = true := by
    intro p
    induction p with
    | nil =>
      intro acc tbl e he
      simp [tomlGetPathAux, FromToml.fromToml] at he
    | cons seg rest ih =>
      intro acc tbl e he
      cases rest with
      | nil =>
        simp only [tomlGetPathAux] at he
        cases hl : lookupKey seg tbl with
        | none => simp [hl] at he; subst he; exact not_decide_isEmpty_eq_true mkErr_nonEmpty'
        | some val => simp [hl, FromToml.fromToml] at he
      | cons seg2 rest2 =>
        simp only [tomlGetPathAux] at he
        cases hl : lookupKey seg tbl with
        | none => simp [hl] at he; subst he; exact not_decide_isEmpty_eq_true mkErr_nonEmpty'
        | some val =>
          simp only [hl] at he
          cases val with
          | table sub => exact ih (seg :: acc) sub e he
          | _ => dsimp only at he; cases he; exact not_decide_isEmpty_eq_true mkErr_nonEmpty'
  have hpath : ∀ e, tomlGetPath (α := TomlValue) t path = .error e →
      (!decide (e.message.isEmpty = true)) = true :=
    fun e he => hpathAux path [] t e he
  cases h1 : tomlGetTable v <;> (try refine ⟨htab _ h1, ?_⟩) <;> dsimp only
  all_goals (cases h2 : tomlGetArray v <;> (try refine ⟨harr _ h2, ?_⟩) <;> dsimp only)
  all_goals (cases h3 : tomlGetField (α := TomlValue) t k <;> (try refine ⟨hfld _ h3, ?_⟩) <;> dsimp only)
  all_goals (cases h4 : tomlGetOptField (α := String) t k <;> (try refine ⟨hopt _ h4, ?_⟩) <;> dsimp only)
  all_goals (cases h5 : tomlGetPath (α := TomlValue) t path <;> (try exact ⟨hpath _ h5, trivial⟩) <;> trivial)

/-- Deconstruct an `Except.bind` returning `.ok`. -/
theorem except_bind_ok {α β ε : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => simp only [bind, Except.bind] at h; cases h
  | ok a => simp only [bind, Except.bind] at h; exact ⟨a, rfl, h⟩

/-- Check whether key `k` appears in builder association list `entries`. -/
def assocHasKey (k : String) : List (String × Node) → Bool
  | [] => false
  | (k', _) :: rest => k == k' || assocHasKey k rest

/-- Check that builder association list `entries` has pairwise distinct keys. -/
def entriesNoDup : List (String × Node) → Bool
  | [] => true
  | (k, _) :: rest => !assocHasKey k rest && entriesNoDup rest

mutual
  /-- Computable well-formedness check for a builder `Node`. -/
  def wellFormedNodeBool : Node → Bool
    | .leaf v => wellFormedValueBool v
    | .table _ entries => entriesNoDup entries && wellFormedNodeListBool entries
    | .aot elems => wellFormedAotBool elems

  /-- Computable well-formedness check for a list of `(String × Node)` entries. -/
  def wellFormedNodeListBool : List (String × Node) → Bool
    | [] => true
    | (_, n) :: rest => wellFormedNodeBool n && wellFormedNodeListBool rest

  /-- Computable well-formedness check for `[[aot]]` table element builders. -/
  def wellFormedAotBool : List (List (String × Node)) → Bool
    | [] => true
    | e :: rest => (entriesNoDup e && wellFormedNodeListBool e) && wellFormedAotBool rest
end

/-- Combined well-formedness invariant on a builder entry list (`entriesNoDup` and well-formed children). -/
def EntriesWF (entries : List (String × Node)) : Prop :=
  entriesNoDup entries = true ∧ wellFormedNodeListBool entries = true

/-- `assocHasKey` agrees with `hasKeyList` after `entriesToTomlList`. -/
theorem assocHasKey_eq_hasKeyList (k : String) (entries : List (String × Node)) :
    hasKeyList k (entriesToTomlList entries) = assocHasKey k entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', n⟩
    simp [entriesToTomlList, hasKeyList, assocHasKey, ih]

/-- `entriesNoDup entries = true` implies `noDupKeysBool (entriesToTomlList entries) = true`. -/
theorem entriesNoDup_implies_noDupKeys (entries : List (String × Node))
    (h : entriesNoDup entries = true) : noDupKeysBool (entriesToTomlList entries) = true := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, n⟩
    simp only [entriesNoDup, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [entriesToTomlList, noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true',
      assocHasKey_eq_hasKeyList]
    exact ⟨h.1, ih h.2⟩

/-- Mutual translation of `wellFormedNodeBool` / `wellFormedNodeListBool` / `wellFormedAotBool` into `Model.wellFormedValueBool`. -/
theorem wellFormedNode_implies_value_aux :
    (∀ n, wellFormedNodeBool n = true → wellFormedValueBool (nodeToTomlValue n) = true) ∧
    (∀ entries, wellFormedNodeListBool entries = true →
      wellFormedValueBool.wellFormedTableListBool (entriesToTomlList entries) = true) ∧
    (∀ elems, wellFormedAotBool elems = true →
      wellFormedValueBool.wellFormedListBool (aotElemsToToml elems) = true) := by
  have hbound : ∀ m : Nat,
      (∀ n, sizeOf n ≤ m → wellFormedNodeBool n = true →
        wellFormedValueBool (nodeToTomlValue n) = true) ∧
      (∀ entries, sizeOf entries ≤ m → wellFormedNodeListBool entries = true →
        wellFormedValueBool.wellFormedTableListBool (entriesToTomlList entries) = true) ∧
      (∀ elems, sizeOf elems ≤ m → wellFormedAotBool elems = true →
        wellFormedValueBool.wellFormedListBool (aotElemsToToml elems) = true) := by
    intro m0
    refine Nat.strongRecOn (motive := fun m =>
      (∀ n, sizeOf n ≤ m → wellFormedNodeBool n = true →
        wellFormedValueBool (nodeToTomlValue n) = true) ∧
      (∀ entries, sizeOf entries ≤ m → wellFormedNodeListBool entries = true →
        wellFormedValueBool.wellFormedTableListBool (entriesToTomlList entries) = true) ∧
      (∀ elems, sizeOf elems ≤ m → wellFormedAotBool elems = true →
        wellFormedValueBool.wellFormedListBool (aotElemsToToml elems) = true)) m0 fun m ih => ?_
    refine ⟨?_, ?_, ?_⟩
    · intro n hm hn
      cases n with
      | leaf v =>
        simpa [wellFormedNodeBool, nodeToTomlValue] using hn
      | table kind entries =>
        simp only [wellFormedNodeBool, Bool.and_eq_true] at hn
        simp only [nodeToTomlValue, wellFormedValueBool, Bool.and_eq_true]
        have hsub : sizeOf entries < m := by
          have : sizeOf entries < sizeOf (Node.table kind entries) := by simp; omega
          omega
        exact ⟨entriesNoDup_implies_noDupKeys entries hn.1,
          (ih (sizeOf entries) hsub).2.1 entries (Nat.le_refl _) hn.2⟩
      | aot elems =>
        simp only [wellFormedNodeBool] at hn
        simp only [nodeToTomlValue, wellFormedValueBool]
        have hsub : sizeOf elems < m := by
          have : sizeOf elems < sizeOf (Node.aot elems) := by simp
          omega
        exact (ih (sizeOf elems) hsub).2.2 elems (Nat.le_refl _) hn
    · intro entries hm hent
      cases entries with
      | nil => rfl
      | cons hd tl =>
        rcases hd with ⟨k, n⟩
        simp only [wellFormedNodeListBool, Bool.and_eq_true] at hent
        simp only [entriesToTomlList, wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true]
        have hn : sizeOf n < m := by
          have : sizeOf n < sizeOf ((k, n) :: tl) := by simp; omega
          omega
        have htl : sizeOf tl < m := by
          have : sizeOf tl < sizeOf ((k, n) :: tl) := by simp; omega
          omega
        exact ⟨(ih (sizeOf n) hn).1 n (Nat.le_refl _) hent.1,
          (ih (sizeOf tl) htl).2.1 tl (Nat.le_refl _) hent.2⟩
    · intro elems hm helems
      cases elems with
      | nil => rfl
      | cons e rest =>
        simp only [wellFormedAotBool, Bool.and_eq_true] at helems
        simp only [aotElemsToToml, wellFormedValueBool.wellFormedListBool, Bool.and_eq_true,
          wellFormedValueBool]
        have he : sizeOf e < m := by
          have : sizeOf e < sizeOf (e :: rest) := by simp; omega
          omega
        have hrest : sizeOf rest < m := by
          have : sizeOf rest < sizeOf (e :: rest) := by simp; omega
          omega
        exact ⟨⟨entriesNoDup_implies_noDupKeys e helems.1.1,
            (ih (sizeOf e) he).2.1 e (Nat.le_refl _) helems.1.2⟩,
          (ih (sizeOf rest) hrest).2.2 rest (Nat.le_refl _) helems.2⟩
  exact ⟨fun n hn => (hbound (sizeOf n)).1 n (Nat.le_refl _) hn,
    fun entries hent => (hbound (sizeOf entries)).2.1 entries (Nat.le_refl _) hent,
    fun elems helems => (hbound (sizeOf elems)).2.2 elems (Nat.le_refl _) helems⟩

/-- `EntriesWF entries` implies `WellFormedTable (entriesToTomlList entries).toArray`. -/
theorem entriesWF_implies_wellFormedTable (entries : List (String × Node)) (h : EntriesWF entries) :
    WellFormedTable (entriesToTomlList entries).toArray := by
  simp only [WellFormedTable, wellFormedTableBool, Bool.and_eq_true]
  exact ⟨entriesNoDup_implies_noDupKeys entries h.1, wellFormedNode_implies_value_aux.2.1 entries h.2⟩

/-- `assocHasKey` on `assocSetNode`. -/
theorem assocHasKey_assocSetNode (k k' : String) (v : Node) (entries : List (String × Node)) :
    assocHasKey k (assocSetNode k' v entries) = (k == k' || assocHasKey k entries) := by
  induction entries with
  | nil => simp [assocSetNode, assocHasKey]
  | cons hd tl ih =>
    rcases hd with ⟨kh, vh⟩
    simp only [assocSetNode]
    by_cases heq : (k' == kh) = true
    · have hk : k' = kh := eq_of_beq heq
      subst hk
      simp [assocHasKey]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte, assocHasKey, ih]
      cases (k == kh) <;> cases (k == k') <;> simp

/-- `assocSetNode` preserves `entriesNoDup`. -/
theorem entriesNoDup_assocSetNode (k : String) (v : Node) (entries : List (String × Node))
    (h : entriesNoDup entries = true) : entriesNoDup (assocSetNode k v entries) = true := by
  induction entries with
  | nil => simp [assocSetNode, entriesNoDup, assocHasKey]
  | cons hd tl ih =>
    rcases hd with ⟨kh, vh⟩
    simp only [entriesNoDup, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [assocSetNode]
    by_cases heq : (k == kh) = true
    · simp only [heq, ↓reduceIte, entriesNoDup, Bool.and_eq_true, Bool.not_eq_true']
      exact h
    · simp only [heq, Bool.false_eq_true, ↓reduceIte, entriesNoDup, Bool.and_eq_true,
        Bool.not_eq_true', assocHasKey_assocSetNode, Bool.or_eq_false_iff]
      have hne : (kh == k) = false := by
        cases hkh : (kh == k)
        · rfl
        · have hk1 : kh = k := eq_of_beq hkh
          rw [hk1] at heq
          simp at heq
      exact ⟨⟨hne, h.1⟩, ih h.2⟩

/-- `assocSetNode` preserves `wellFormedNodeListBool` when `v` is well-formed. -/
theorem wellFormedNodeListBool_assocSetNode (k : String) (v : Node) (entries : List (String × Node))
    (hent : wellFormedNodeListBool entries = true) (hv : wellFormedNodeBool v = true) :
    wellFormedNodeListBool (assocSetNode k v entries) = true := by
  induction entries with
  | nil => simp [assocSetNode, wellFormedNodeListBool, hv]
  | cons hd tl ih =>
    rcases hd with ⟨kh, vh⟩
    simp only [wellFormedNodeListBool, Bool.and_eq_true] at hent
    simp only [assocSetNode]
    split
    · simp [wellFormedNodeListBool, hv, hent.2]
    · simp [wellFormedNodeListBool, hent.1, ih hent.2]

/-- `assocSetNode` preserves `EntriesWF`. -/
theorem entriesWF_assocSetNode (k : String) (v : Node) (entries : List (String × Node))
    (hent : EntriesWF entries) (hv : wellFormedNodeBool v = true) :
    EntriesWF (assocSetNode k v entries) :=
  ⟨entriesNoDup_assocSetNode k v entries hent.1,
    wellFormedNodeListBool_assocSetNode k v entries hent.2 hv⟩

/-- Lookup in `wellFormedNodeListBool` returns a well-formed `Node`. -/
theorem assocLookupNode_wellFormed (k : String) (entries : List (String × Node)) (n : Node)
    (hent : wellFormedNodeListBool entries = true) (hl : assocLookupNode k entries = some n) :
    wellFormedNodeBool n = true := by
  induction entries with
  | nil => simp [assocLookupNode] at hl
  | cons hd tl ih =>
    rcases hd with ⟨kh, nh⟩
    simp only [wellFormedNodeListBool, Bool.and_eq_true] at hent
    simp only [assocLookupNode] at hl
    split at hl
    · cases hl; exact hent.1
    · exact ih hent.2 hl

/-- `valueToInlineNode` preserves well-formedness. -/
theorem wellFormedValue_implies_inlineNode :
    (∀ v, wellFormedValueBool v = true → wellFormedNodeBool (valueToInlineNode v) = true) ∧
    (∀ entries, noDupKeysBool entries = true →
      wellFormedValueBool.wellFormedTableListBool entries = true →
      EntriesWF (inlineListToNodes entries)) := by
  have hhas : ∀ k' l, assocHasKey k' (inlineListToNodes l) = hasKeyList k' l := by
    intro k' l
    induction l with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨kh, vh⟩
      simp [inlineListToNodes, assocHasKey, hasKeyList, ih]
  have hbound : ∀ m : Nat,
      (∀ v, sizeOf v ≤ m → wellFormedValueBool v = true →
        wellFormedNodeBool (valueToInlineNode v) = true) ∧
      (∀ entries, sizeOf entries ≤ m → noDupKeysBool entries = true →
        wellFormedValueBool.wellFormedTableListBool entries = true →
        EntriesWF (inlineListToNodes entries)) := by
    intro m0
    refine Nat.strongRecOn (motive := fun m =>
      (∀ v, sizeOf v ≤ m → wellFormedValueBool v = true →
        wellFormedNodeBool (valueToInlineNode v) = true) ∧
      (∀ entries, sizeOf entries ≤ m → noDupKeysBool entries = true →
        wellFormedValueBool.wellFormedTableListBool entries = true →
        EntriesWF (inlineListToNodes entries))) m0 fun m ih => ?_
    refine ⟨?_, ?_⟩
    · intro v hm hv
      cases v with
      | table t =>
        simp only [wellFormedValueBool, Bool.and_eq_true] at hv
        have hsub : sizeOf t.toList < m := by
          have h1 : sizeOf t.toList < sizeOf t := by
            cases t
            simp
          have h2 : sizeOf t < sizeOf (TomlValue.table t) := by simp
          omega
        have hent := (ih (sizeOf t.toList) hsub).2 t.toList (Nat.le_refl _) hv.1 hv.2
        simp only [valueToInlineNode, wellFormedNodeBool, Bool.and_eq_true]
        exact hent
      | _ =>
        simpa [valueToInlineNode, wellFormedNodeBool] using hv
    · intro entries hm hnd hwf
      cases entries with
      | nil => exact ⟨rfl, rfl⟩
      | cons hd tl =>
        rcases hd with ⟨k, v⟩
        simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
        simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
        have hv : sizeOf v < m := by
          have : sizeOf v < sizeOf ((k, v) :: tl) := by simp; omega
          omega
        have htl : sizeOf tl < m := by
          have : sizeOf tl < sizeOf ((k, v) :: tl) := by simp; omega
          omega
        have hrest := (ih (sizeOf tl) htl).2 tl (Nat.le_refl _) hnd.2 hwf.2
        have hnode := (ih (sizeOf v) hv).1 v (Nat.le_refl _) hwf.1
        simp only [inlineListToNodes, EntriesWF, entriesNoDup, wellFormedNodeListBool,
          Bool.and_eq_true, Bool.not_eq_true', hhas]
        exact ⟨⟨hnd.1, hrest.1⟩, ⟨hnode, hrest.2⟩⟩
  exact ⟨fun v hv => (hbound (sizeOf v)).1 v (Nat.le_refl _) hv,
    fun entries hnd hwf => (hbound (sizeOf entries)).2 entries (Nat.le_refl _) hnd hwf⟩

/-- `parseDatePart` produces valid TOML dates (`0000..9999`). -/
theorem parseDatePart_valid (cs : List Char) (d : Std.Time.PlainDate) (rest : List Char)
    (h : parseDatePart cs = .ok (d, rest)) : validTomlDate d = true := by
  unfold parseDatePart at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h
  · cases h; assumption
  · cases h

/-- `parseTimePart` produces valid TOML times (`second ≤ 59`). -/
theorem parseTimePart_valid (cs : List Char) (t : Std.Time.PlainTime) (rest : List Char)
    (h : parseTimePart cs = .ok (t, rest)) : validTomlTime t = true := by
  unfold parseTimePart at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  · rename_i hh mm ss heq1 heq2 heq3 hhh hmm hss
    split at h
    · dsimp only at h
      split at h
      · cases h
      · cases h
        simp only [validTomlTime, Std.Time.Second.Ordinal.ofNat,
          Std.Time.Internal.Bounded.LE.ofNat]
        exact decide_eq_true_eq.mpr (Int.ofNat_le.mpr hss)
    · cases h
      simp only [validTomlTime, Std.Time.Second.Ordinal.ofNat,
        Std.Time.Internal.Bounded.LE.ofNat]
      exact decide_eq_true_eq.mpr (Int.ofNat_le.mpr hss)

/-- `parseOffsetPart` produces valid TOML offsets (`±23:59`, multiple of 60s). -/
theorem parseOffsetPart_valid (cs : List Char) (o : Std.Time.TimeZone.Offset)
    (h : parseOffsetPart cs = .ok o) : validTomlOffset o = true := by
  unfold parseOffsetPart at h
  split at h
  · cases h; decide
  · cases h; decide
  · split at h <;> try cases h
    split at h <;> try cases h
    dsimp only at h
    split at h <;> try cases h
    generalize Std.Time.TimeZone.Offset.ofSeconds _ = off at h
    by_cases hv : validTomlOffset off = true
    · simp only [hv, ↓reduceIte, Except.ok.injEq] at h
      cases h; exact hv
    · simp [hv] at h
  · cases h

/-- `parseDateTimeToken` outputs satisfy `wellFormedValueBool`. -/
theorem parseDateTimeToken_wellFormed (tok : String) (v : TomlValue)
    (h : parseDateTimeToken tok = some (.ok v)) : wellFormedValueBool v = true := by
  unfold parseDateTimeToken at h
  dsimp only at h
  split at h
  · cases hd : parseDatePart tok.toList <;> simp [hd] at h
    rename_i res
    rcases res with ⟨d, rem⟩
    cases rem with
    | nil =>
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      exact parseDatePart_valid _ _ _ hd
    | cons sep timeCs =>
      simp only at h
      split at h
      · cases ht : parseTimePart timeCs <;> simp [ht] at h
        rename_i tres
        rcases tres with ⟨tm, offCs⟩
        cases offCs with
        | nil =>
          simp only [Option.some.injEq, Except.ok.injEq] at h
          subst h
          simp only [wellFormedValueBool, validTomlDateTime, Bool.and_eq_true]
          exact ⟨parseDatePart_valid _ _ _ hd, parseTimePart_valid _ _ _ ht⟩
        | cons oc orest =>
          simp only at h
          cases ho : parseOffsetPart (oc :: orest) <;> simp [ho] at h
          subst h
          simp only [wellFormedValueBool, validTomlOffsetDateTime, validTomlDateTime, Bool.and_eq_true]
          exact ⟨⟨parseDatePart_valid _ _ _ hd, parseTimePart_valid _ _ _ ht⟩,
            parseOffsetPart_valid _ _ ho⟩
      · cases h
  · split at h
    · cases ht : parseTimePart tok.toList <;> simp [ht] at h
      rename_i tres
      rcases tres with ⟨tm, rem⟩
      cases rem with
      | nil =>
        simp only [Option.some.injEq, Except.ok.injEq] at h
        subst h
        exact parseTimePart_valid _ _ _ ht
      | cons _ _ => simp at h
    · split at h <;> cases h

/-- `classifyScalarToken` outputs satisfy `wellFormedValueBool`. -/
theorem classifyScalarToken_wellFormed (numApi : NumParseApi) (tok : String) (v : TomlValue)
    (h : classifyScalarToken numApi tok = .ok v) : wellFormedValueBool v = true := by
  unfold classifyScalarToken at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · split at h
        · rename_i res hres
          rw [h] at hres
          exact parseDateTimeToken_wellFormed tok v hres
        · split at h
          · split at h
            · cases h; rfl
            · cases h
          · split at h
            · cases h
            · split at h
              · cases h; rfl
              · cases h

/-- `insertDottedEntries` preserves `EntriesWF`. -/
theorem insertDottedEntries_wellFormed (fullPath : List String)
    (entries : List (String × Node)) (relPath : List String) (newNode : Node)
    (nextEntries : List (String × Node))
    (hent : EntriesWF entries) (hnew : wellFormedNodeBool newNode = true)
    (hins : insertDottedEntries fullPath entries relPath newNode = .ok nextEntries) :
    EntriesWF nextEntries := by
  induction relPath generalizing entries nextEntries with
  | nil => simp [insertDottedEntries] at hins
  | cons k rest ih =>
    cases rest with
    | nil =>
      unfold insertDottedEntries at hins
      split at hins
      · cases hins
        exact entriesWF_assocSetNode k newNode entries hent hnew
      · cases hins
      · cases hins
    | cons k2 rest2 =>
      unfold insertDottedEntries at hins
      split at hins
      · rcases except_bind_ok hins with ⟨sub, hsub, hok⟩
        cases hok
        have hwsub := ih [] sub ⟨rfl, rfl⟩ hsub
        exact entriesWF_assocSetNode k (.table .dotted sub) entries hent
          (by simp [wellFormedNodeBool, hwsub.1, hwsub.2])
      · cases hins
      · cases hins
      · rename_i sub hl
        rcases except_bind_ok hins with ⟨nextSub, hsub, hok⟩
        cases hok
        have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
        simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
        have hwsub := ih sub nextSub hwl hsub
        exact entriesWF_assocSetNode k (.table .dotted nextSub) entries hent
          (by simp [wellFormedNodeBool, hwsub.1, hwsub.2])
      · rename_i sub hl
        rcases except_bind_ok hins with ⟨nextSub, hsub, hok⟩
        cases hok
        have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
        simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
        have hwsub := ih sub nextSub hwl hsub
        exact entriesWF_assocSetNode k (.table .dotted nextSub) entries hent
          (by simp [wellFormedNodeBool, hwsub.1, hwsub.2])
      · cases hins
      · cases hins
      · cases hins

/-- Well-formedness of `parseValueFuel`, `parseArrayFuel`, and `parseInlineTableFuel`. -/
theorem parseValArrInline_wellFormed (numApi : NumParseApi) (fuel : Nat) :
    (∀ cs v rest, parseValueFuel numApi fuel cs = .ok (v, rest) → wellFormedValueBool v = true) ∧
    (∀ cs revAcc v rest,
      wellFormedValueBool.wellFormedListBool revAcc = true →
      parseArrayFuel numApi fuel cs revAcc = .ok (v, rest) →
      wellFormedValueBool v = true) ∧
    (∀ cs entries v rest,
      EntriesWF entries →
      parseInlineTableFuel numApi fuel cs entries = .ok (v, rest) →
      wellFormedValueBool v = true) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro cs v rest h; simp [parseValueFuel] at h
    · intro cs revAcc v rest _ h; simp [parseArrayFuel] at h
    · intro cs entries v rest _ h; simp [parseInlineTableFuel] at h
  | succ fuel ih =>
    rcases ih with ⟨ihVal, ihArr, ihInl⟩
    have hrev : ∀ xs : List TomlValue,
        wellFormedValueBool.wellFormedListBool xs = true →
        wellFormedValueBool.wellFormedListBool xs.reverse = true := by
      have happ : ∀ l1 l2 : List TomlValue,
          wellFormedValueBool.wellFormedListBool l1 = true →
          wellFormedValueBool.wellFormedListBool l2 = true →
          wellFormedValueBool.wellFormedListBool (l1 ++ l2) = true := by
        intro l1 l2 h1 h2
        induction l1 with
        | nil => exact h2
        | cons x xs ihapp =>
          simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at h1
          simp only [List.cons_append, wellFormedValueBool.wellFormedListBool, Bool.and_eq_true]
          exact ⟨h1.1, ihapp h1.2⟩
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons x tl ihrev =>
        simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at hxs
        simp only [List.reverse_cons]
        exact happ tl.reverse [x] (ihrev hxs.2)
          (by simp [wellFormedValueBool.wellFormedListBool, hxs.1])
    refine ⟨?_, ?_, ?_⟩
    · intro cs v rest h
      unfold parseValueFuel at h
      split at h
      · rcases except_bind_ok h with ⟨⟨s, after⟩, _, hok⟩; cases hok; rfl
      · rcases except_bind_ok h with ⟨⟨s, after⟩, _, hok⟩; cases hok; rfl
      · rcases except_bind_ok h with ⟨⟨s, after⟩, _, hok⟩; cases hok; rfl
      · rcases except_bind_ok h with ⟨⟨s, after⟩, _, hok⟩; cases hok; rfl
      · exact ihArr _ [] v rest rfl h
      · split at h
        · cases h; decide
        · exact ihInl _ [] v rest ⟨rfl, rfl⟩ h
      · rcases except_bind_ok h with ⟨v', hv', hok⟩
        cases hok
        exact classifyScalarToken_wellFormed numApi _ v hv'
    · intro cs revAcc v rest hacc h
      unfold parseArrayFuel at h
      split at h
      · cases h
        simp [wellFormedValueBool, hrev revAcc hacc]
      · cases h
      · rcases except_bind_ok h with ⟨⟨v1, r1⟩, hv1, hok⟩
        have hwv1 := ihVal _ v1 r1 hv1
        have hnext : wellFormedValueBool.wellFormedListBool (v1 :: revAcc) = true := by
          simp [wellFormedValueBool.wellFormedListBool, hwv1, hacc]
        dsimp only at hok
        split at hok
        · exact ihArr _ (v1 :: revAcc) v rest hnext hok
        · cases hok
          simpa [wellFormedValueBool] using hrev (v1 :: revAcc) hnext
        · cases hok
    · intro cs entries v rest hent h
      unfold parseInlineTableFuel at h
      rcases except_bind_ok h with ⟨⟨relPath, r1⟩, _, h1⟩
      dsimp only at h1
      split at h1
      · rcases except_bind_ok h1 with ⟨⟨v1, r5⟩, hv1, h2⟩
        rcases except_bind_ok h2 with ⟨nextEntries, hins, h3⟩
        have hwv1 := ihVal _ v1 r5 hv1
        have hnode1 := wellFormedValue_implies_inlineNode.1 v1 hwv1
        have hnext := insertDottedEntries_wellFormed relPath entries relPath _ nextEntries hent hnode1 hins
        dsimp only at h3
        split at h3
        · split at h3
          · cases h3
          · exact ihInl _ nextEntries v rest hnext h3
        · cases h3
          have htbl := entriesWF_implies_wellFormedTable nextEntries hnext
          simpa [wellFormedTable_iff_value, WellFormedValue] using htbl
        · cases h3
      · cases h1

/-- `mapLastAot` preserves `wellFormedAotBool`. -/
theorem mapLastAot_wellFormed (f : List (String × Node) → Except TomlError (List (String × Node)))
    (hf : ∀ x y, EntriesWF x → f x = .ok y → EntriesWF y)
    (elems nextElems : List (List (String × Node)))
    (hw : wellFormedAotBool elems = true) (h : mapLastAot f elems = .ok nextElems) :
    wellFormedAotBool nextElems = true := by
  induction elems generalizing nextElems with
  | nil => simp [mapLastAot] at h
  | cons hd tl ih =>
    cases tl with
    | nil =>
      unfold mapLastAot at h
      rcases except_bind_ok h with ⟨updated, hup, hok⟩
      cases hok
      simp only [wellFormedAotBool, Bool.and_eq_true] at hw ⊢
      have hres := hf hd updated hw.1 hup
      exact ⟨hres, hw.2⟩
    | cons hd2 tl2 =>
      unfold mapLastAot at h
      rcases except_bind_ok h with ⟨rest', hrest, hok⟩
      cases hok
      simp only [wellFormedAotBool] at hw ⊢
      rw [Bool.and_eq_true] at hw ⊢
      exact ⟨hw.1, ih rest' hw.2 hrest⟩

/-- `applyTableHeader` preserves `EntriesWF`. -/
theorem applyTableHeader_wellFormed (fullPath : List String)
    (entries : List (String × Node)) (path : List String) (nextEntries : List (String × Node))
    (hent : EntriesWF entries) (h : applyTableHeader fullPath entries path = .ok nextEntries) :
    EntriesWF nextEntries := by
  induction path generalizing entries nextEntries with
  | nil => simp [applyTableHeader] at h
  | cons k rest ih =>
    cases rest with
    | nil =>
      unfold applyTableHeader at h
      cases hl : assocLookupNode k entries with
      | none =>
        simp [hl] at h
        cases h
        exact entriesWF_assocSetNode k (.table .explicit []) entries hent
          (by simp [wellFormedNodeBool, entriesNoDup, wellFormedNodeListBool])
      | some n =>
        cases n with
        | leaf v => cases v <;> simp [hl] at h
        | aot _ => simp [hl] at h
        | table kind sub =>
          cases kind <;> simp [hl] at h
          cases h
          have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
          simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
          exact entriesWF_assocSetNode k (.table .explicit sub) entries hent
            (by simp [wellFormedNodeBool, hwl.1, hwl.2])
    | cons k2 rest2 =>
      unfold applyTableHeader at h
      cases hl : assocLookupNode k entries with
      | none =>
        simp only [hl] at h
        rcases except_bind_ok h with ⟨sub, hsub, hok⟩
        cases hok
        have hwsub := ih [] sub ⟨rfl, rfl⟩ hsub
        exact entriesWF_assocSetNode k (.table .subtableImplicit sub) entries hent
          (by simp [wellFormedNodeBool, hwsub.1, hwsub.2])
      | some n =>
        cases n with
        | leaf v => cases v <;> simp [hl] at h
        | table kind sub =>
          cases kind with
          | inline => simp [hl] at h
          | _ =>
            simp only [hl] at h
            rcases except_bind_ok h with ⟨nextSub, hsub, hok⟩
            cases hok
            have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
            simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
            have hwsub := ih sub nextSub hwl hsub
            exact entriesWF_assocSetNode k (.table _ nextSub) entries hent
              (by simp [wellFormedNodeBool, hwsub.1, hwsub.2])
        | aot elems =>
          simp only [hl] at h
          rcases except_bind_ok h with ⟨nextElems, hmap, hok⟩
          cases hok
          have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
          simp only [wellFormedNodeBool] at hwl
          have hwmap := mapLastAot_wellFormed _ (fun x y hx hy => ih x y hx hy) elems nextElems hwl hmap
          exact entriesWF_assocSetNode k (.aot nextElems) entries hent
            (by simp [wellFormedNodeBool, hwmap])

/-- `applyAotHeader` preserves `EntriesWF`. -/
theorem applyAotHeader_wellFormed (fullPath : List String)
    (entries : List (String × Node)) (path : List String) (nextEntries : List (String × Node))
    (hent : EntriesWF entries) (h : applyAotHeader fullPath entries path = .ok nextEntries) :
    EntriesWF nextEntries := by
  induction path generalizing entries nextEntries with
  | nil => simp [applyAotHeader] at h
  | cons k rest ih =>
    cases rest with
    | nil =>
      unfold applyAotHeader at h
      cases hl : assocLookupNode k entries with
      | none =>
        simp [hl] at h
        cases h
        exact entriesWF_assocSetNode k (.aot [[]]) entries hent
          (by simp [wellFormedNodeBool, wellFormedAotBool, entriesNoDup, wellFormedNodeListBool])
      | some n =>
        cases n with
        | leaf v => cases v <;> simp [hl] at h
        | table kind _ => cases kind <;> simp [hl] at h
        | aot elems =>
          simp [hl] at h
          cases h
          have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
          simp only [wellFormedNodeBool] at hwl
          have happ : ∀ l : List (List (String × Node)), wellFormedAotBool l = true →
              wellFormedAotBool (l ++ [[]]) = true := by
            intro l hwl'
            induction l with
            | nil => simp [wellFormedAotBool, entriesNoDup, wellFormedNodeListBool]
            | cons hd tl ihl =>
              simp only [wellFormedAotBool, Bool.and_eq_true] at hwl'
              simp only [List.cons_append, wellFormedAotBool, Bool.and_eq_true]
              exact ⟨hwl'.1, ihl hwl'.2⟩
          exact entriesWF_assocSetNode k (.aot (elems ++ [[]])) entries hent
            (by simp [wellFormedNodeBool, happ elems hwl])
    | cons k2 rest2 =>
      unfold applyAotHeader at h
      cases hl : assocLookupNode k entries with
      | none =>
        simp only [hl] at h
        rcases except_bind_ok h with ⟨sub, hsub, hok⟩
        cases hok
        have hwsub := ih [] sub ⟨rfl, rfl⟩ hsub
        exact entriesWF_assocSetNode k (.table .subtableImplicit sub) entries hent
          (by simp [wellFormedNodeBool, hwsub.1, hwsub.2])
      | some n =>
        cases n with
        | leaf v => cases v <;> simp [hl] at h
        | table kind sub =>
          cases kind with
          | inline => simp [hl] at h
          | _ =>
            simp only [hl] at h
            rcases except_bind_ok h with ⟨nextSub, hsub, hok⟩
            cases hok
            have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
            simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
            have hwsub := ih sub nextSub hwl hsub
            exact entriesWF_assocSetNode k (.table _ nextSub) entries hent
              (by simp [wellFormedNodeBool, hwsub.1, hwsub.2])
        | aot elems =>
          simp only [hl] at h
          rcases except_bind_ok h with ⟨nextElems, hmap, hok⟩
          cases hok
          have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
          simp only [wellFormedNodeBool] at hwl
          have hwmap := mapLastAot_wellFormed _ (fun x y hx hy => ih x y hx hy) elems nextElems hwl hmap
          exact entriesWF_assocSetNode k (.aot nextElems) entries hent
            (by simp [wellFormedNodeBool, hwmap])

/-- `insertAtActivePath` preserves `EntriesWF`. -/
theorem insertAtActivePath_wellFormed (fullPath : List String)
    (entries : List (String × Node)) (activePath relPath : List String)
    (valNode : Node) (nextEntries : List (String × Node))
    (hent : EntriesWF entries) (hval : wellFormedNodeBool valNode = true)
    (h : insertAtActivePath fullPath entries activePath relPath valNode = .ok nextEntries) :
    EntriesWF nextEntries := by
  induction activePath generalizing entries nextEntries with
  | nil =>
    simp only [insertAtActivePath] at h
    exact insertDottedEntries_wellFormed fullPath entries relPath valNode nextEntries hent hval h
  | cons k rest ih =>
    unfold insertAtActivePath at h
    split at h
    · rename_i kind sub hl
      rcases except_bind_ok h with ⟨nextSub, hsub, hok⟩
      cases hok
      have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
      simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
      have hwsub := ih sub nextSub hwl hsub
      exact entriesWF_assocSetNode k (.table kind nextSub) entries hent
        (by simp [wellFormedNodeBool, hwsub.1, hwsub.2])
    · rename_i elems hl
      rcases except_bind_ok h with ⟨nextElems, hmap, hok⟩
      cases hok
      have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
      simp only [wellFormedNodeBool] at hwl
      have hwmap := mapLastAot_wellFormed _ (fun x y hx hy => ih x y hx hy) elems nextElems hwl hmap
      exact entriesWF_assocSetNode k (.aot nextElems) entries hent
        (by simp [wellFormedNodeBool, hwmap])
    · cases h

/-- `parseDocumentFuel` preserves `EntriesWF` and returns a well-formed root builder. -/
theorem parseDocumentFuel_wellFormed (numApi : NumParseApi)
    (fuel : Nat) (cs : List Char) (activePath : List String)
    (root nextRoot : List (String × Node))
    (hroot : EntriesWF root)
    (h : parseDocumentFuel numApi fuel cs activePath root = .ok nextRoot) :
    EntriesWF nextRoot := by
  induction fuel generalizing cs activePath root nextRoot with
  | zero =>
    unfold parseDocumentFuel at h
    split at h
    · cases h; exact hroot
    · cases h
  | succ fuel ih =>
    unfold parseDocumentFuel at h
    split at h
    · cases h; exact hroot
    · rcases except_bind_ok h with ⟨⟨path, r1⟩, _, h1⟩
      dsimp only at h1
      split at h1
      · rcases except_bind_ok h1 with ⟨nextCs, _, h2⟩
        rcases except_bind_ok h2 with ⟨root', haot, h3⟩
        exact ih _ _ _ _ (applyAotHeader_wellFormed path root path root' hroot haot) h3
      · cases h1
    · rcases except_bind_ok h with ⟨⟨path, r1⟩, _, h1⟩
      dsimp only at h1
      split at h1
      · rcases except_bind_ok h1 with ⟨nextCs, _, h2⟩
        rcases except_bind_ok h2 with ⟨root', htbl, h3⟩
        exact ih _ _ _ _ (applyTableHeader_wellFormed path root path root' hroot htbl) h3
      · cases h1
    · rcases except_bind_ok h with ⟨⟨relPath, r1⟩, _, h1⟩
      dsimp only at h1
      split at h1
      · rcases except_bind_ok h1 with ⟨⟨val, r3⟩, hval, h2⟩
        rcases except_bind_ok h2 with ⟨nextCs, _, h3⟩
        rcases except_bind_ok h3 with ⟨root', hins, h4⟩
        have hwval := (parseValArrInline_wellFormed numApi _).1 _ _ _ hval
        have hwnode := wellFormedValue_implies_inlineNode.1 val hwval
        have hwroot' := insertAtActivePath_wellFormed (activePath ++ relPath) root activePath relPath
          (valueToInlineNode val) root' hroot hwnode hins
        exact ih _ _ _ _ hwroot' h4
      · cases h1

/-- Every `TomlTable` parsed by `parseWithNum` satisfies `Model.WellFormedTable`. -/
theorem parseWithNum_wellFormed (numApi : NumParseApi) (s : String) (t : TomlTable)
    (h : parseWithNum numApi s = .ok t) : WellFormedTable t := by
  unfold parseWithNum at h
  rcases except_bind_ok h with ⟨norm, _, h1⟩
  rcases except_bind_ok h1 with ⟨root, hdoc, h2⟩
  cases h2
  exact entriesWF_implies_wellFormedTable root
    (parseDocumentFuel_wellFormed numApi (norm.length + 1) norm [] [] root ⟨rfl, rfl⟩ hdoc)

/-- Prove `test_toml_parse_returnsWellFormedTable` for `makeTomlApi numApi`. -/
theorem allPass_parse_returnsWellFormedTable (numApi : NumParseApi) :
    Core.AllPass (test_toml_parse_returnsWellFormedTable (makeTomlApi numApi)) := by
  dsimp only [Core.AllPass, test_toml_parse_returnsWellFormedTable, Core.NondetTest.nondet,
    NondetTest.assert, bind, pure]
  intro s
  simp only [makeTomlApi]
  cases h : parseWithNum numApi s with
  | error _ => trivial
  | ok t => exact ⟨parseWithNum_wellFormed numApi s t h, trivial⟩

/-- Witness `CanReach` for `test_toml_onError_returnsNonEmptyMessage`. -/
theorem canReach_onError (numApi : NumParseApi) :
    Core.CanReach (test_toml_onError_returnsNonEmptyMessage (makeTomlApi numApi)) := by
  dsimp only [Core.CanReach, test_toml_onError_returnsNonEmptyMessage, Core.NondetTest.nondet,
    NondetTest.assert, bind, pure]
  have h1 : "\r".toList = ['\r'] := rfl
  have h2 : normalizeChars 1 1 ['\r'] =
      .error (mkErr .invalidUtf8OrControl "bare carriage return is not allowed in TOML" (some 1) (some 1)) := rfl
  refine ⟨"\r", ?_⟩
  simp only [makeTomlApi, parseWithNum, bind, Except.bind]
  rw [h1, h2]
  simp [mkErr, nonEmptyMsg]

/-- Witness `CanReach` for `test_toml_accessorError_returnsNonEmptyMessage`. -/
theorem canReach_accessorError (numApi : NumParseApi) :
    Core.CanReach (test_toml_accessorError_returnsNonEmptyMessage (makeTomlApi numApi)) := by
  dsimp only [Core.CanReach, test_toml_accessorError_returnsNonEmptyMessage, Core.NondetTest.nondet,
    NondetTest.assert, bind, pure]
  exact ⟨.table #[], #[], "", [], by
    simp [makeTomlApi, tomlGetTable, tomlGetArray, tomlGetField, tomlGetOptField, tomlGetPath,
      tomlGetPathAux, lookupKey, lookupKeyList, mkErr, nonEmptyMsg, FromToml.fromToml]⟩

/-- Witness `CanReach` for `test_toml_parse_returnsWellFormedTable`. -/
theorem canReach_parse_returnsWellFormedTable (numApi : NumParseApi) :
    Core.CanReach (test_toml_parse_returnsWellFormedTable (makeTomlApi numApi)) := by
  dsimp only [Core.CanReach, test_toml_parse_returnsWellFormedTable, Core.NondetTest.nondet,
    NondetTest.assert, bind, pure]
  have h1 : normalizeChars 1 1 [] = .ok [] := rfl
  have h2 : skipTriviaNewlines [] = [] := rfl
  refine ⟨"", ?_⟩
  simp only [makeTomlApi, parseWithNum, String.toList_empty]
  rw [h1]
  simp [bind, Except.bind, parseDocumentFuel, h2, entriesToTomlList,
    WellFormedTable, wellFormedTableBool, noDupKeysBool,
    wellFormedValueBool.wellFormedTableListBool]

private theorem decodeTomlList_int64_map (l : List Int64) :
    decodeTomlList (l.map (fun n => TomlValue.int n)) = .ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, decodeTomlList, FromToml.fromToml, bind, Except.bind, ih]

/-- Prove `test_toml_codecsAndAccessors_conformsToSpec` for `makeTomlApi numApi`. -/
theorem allPass_codecsAndAccessors (numApi : NumParseApi) :
    Core.AllPass (test_toml_codecsAndAccessors_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [Core.AllPass, test_toml_codecsAndAccessors_conformsToSpec, Core.NondetTest.nondet,
    NondetTest.assert, bind, pure]
  intro s n64 f b odt ldt ld lt xs tbl
  have hxs : (makeTomlApi numApi).decode (α := Array Int64) ((makeTomlApi numApi).encode xs) = .ok xs := by
    cases xs with
    | mk l =>
      simp only [makeTomlApi, tomlDecode, tomlEncode, FromToml.fromToml, ToToml.toToml,
        Array.toList_map, decodeTomlList_int64_map, bind, Except.bind]
  refine ⟨rfl, rfl, floatEquiv_refl f, rfl, rfl, rfl, rfl, rfl, hxs, rfl, ?_⟩
  simp [makeTomlApi, tomlDecode, FromToml.fromToml, tomlGetTable, tomlGetArray, tomlGetField,
    tomlGetOptField, tomlGetPath, tomlGetPathAux, lookupKey, lookupKeyList, mkErr, nonEmptyMsg,
    joinPath]

/-- Witness `CanReach` for `test_toml_codecsAndAccessors_conformsToSpec`. -/
theorem canReach_codecsAndAccessors (numApi : NumParseApi) :
    Core.CanReach (test_toml_codecsAndAccessors_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [Core.CanReach, test_toml_codecsAndAccessors_conformsToSpec, Core.NondetTest.nondet,
    NondetTest.assert, bind, pure]
  refine ⟨"", 0, 0.0, false,
    ⟨Std.Time.PlainDateTime.mk (specDate 2024 1 1) (specTime 0 0 0), specOffset 0⟩,
    Std.Time.PlainDateTime.mk (specDate 2024 1 1) (specTime 0 0 0),
    specDate 2024 1 1,
    specTime 0 0 0,
    #[], #[], ?_⟩
  simp [makeTomlApi, tomlDecode, tomlEncode, FromToml.fromToml, ToToml.toToml, decodeTomlList,
    bind, Except.bind, tomlGetTable, tomlGetArray, tomlGetField, tomlGetOptField, tomlGetPath,
    tomlGetPathAux, lookupKey, lookupKeyList, mkErr, nonEmptyMsg, joinPath, floatEquiv_refl]

mutual
  /-- Exact structural value correspondence between `modelNumApi` and any valid `NumParseApi`. -/
  def ValBitMatch (a b : TomlValue) : Prop :=
    match a, b with
    | .string s1, .string s2 => s1 = s2
    | .int n1, .int n2 => n1 = n2
    | .float f1, .float f2 => FloatBitMatch f1 f2
    | .bool b1, .bool b2 => b1 = b2
    | .offsetDateTime d1, .offsetDateTime d2 => d1 = d2
    | .localDateTime d1, .localDateTime d2 => d1 = d2
    | .localDate d1, .localDate d2 => d1 = d2
    | .localTime t1, .localTime t2 => t1 = t2
    | .array xs, .array ys => ListBitMatch xs.toList ys.toList
    | .table t1, .table t2 => EntryListBitMatch t1.toList t2.toList
    | _, _ => False
  termination_by sizeOf a
  decreasing_by
    · cases xs; simp; omega
    · cases t1; simp; omega

  /-- Element-wise `ValBitMatch` over `List TomlValue`. -/
  def ListBitMatch (xs ys : List TomlValue) : Prop :=
    match xs, ys with
    | [], [] => True
    | x :: xr, y :: yr => ValBitMatch x y ∧ ListBitMatch xr yr
    | _, _ => False
  termination_by sizeOf xs
  decreasing_by
    · simp +arith
    · simp +arith

  /-- Key-ordered entry correspondence up to `ValBitMatch`. -/
  def EntryListBitMatch (e1 e2 : List (String × TomlValue)) : Prop :=
    match e1, e2 with
    | [], [] => True
    | (k1, v1) :: r1, (k2, v2) :: r2 => k1 = k2 ∧ ValBitMatch v1 v2 ∧ EntryListBitMatch r1 r2
    | _, _ => False
  termination_by sizeOf e1
  decreasing_by
    · simp +arith
    · simp +arith
end

/-- Table-level correspondence up to `ValBitMatch` on entries. -/
def TableBitMatch (t1 t2 : TomlTable) : Prop :=
  EntryListBitMatch t1.toList t2.toList

mutual
  /-- Structural correspondence on parser `Node` values up to `ValBitMatch` and preserving `TableKind`. -/
  def NodeBitMatch (n1 n2 : Node) : Prop :=
    match n1, n2 with
    | .leaf v1, .leaf v2 => ValBitMatch v1 v2
    | .table k1 e1, .table k2 e2 => k1 = k2 ∧ EntriesBitMatch e1 e2
    | .aot elems1, .aot elems2 => AotBitMatch elems1 elems2
    | _, _ => False
  termination_by sizeOf n1
  decreasing_by
    · simp +arith
    · simp +arith

  /-- Key-ordered entry correspondence on `List (String × Node)`. -/
  def EntriesBitMatch (e1 e2 : List (String × Node)) : Prop :=
    match e1, e2 with
    | [], [] => True
    | (k1, n1) :: r1, (k2, n2) :: r2 => k1 = k2 ∧ NodeBitMatch n1 n2 ∧ EntriesBitMatch r1 r2
    | _, _ => False
  termination_by sizeOf e1
  decreasing_by
    · simp +arith
    · simp +arith

  /-- Element-wise `EntriesBitMatch` over `[[aot]]` element builders. -/
  def AotBitMatch (a1 a2 : List (List (String × Node))) : Prop :=
    match a1, a2 with
    | [], [] => True
    | x :: xr, y :: yr => EntriesBitMatch x y ∧ AotBitMatch xr yr
    | _, _ => False
  termination_by sizeOf a1
  decreasing_by
    · simp +arith
    · simp +arith
end

@[simp] private theorem valBitMatch_array (xs ys : Array TomlValue) :
    ValBitMatch (.array xs) (.array ys) = ListBitMatch xs.toList ys.toList := by
  simp [ValBitMatch]

@[simp] private theorem valBitMatch_table (t1 t2 : TomlTable) :
    ValBitMatch (.table t1) (.table t2) = EntryListBitMatch t1.toList t2.toList := by
  simp [ValBitMatch]

@[simp] private theorem listBitMatch_nil : ListBitMatch [] [] = True := by
  simp [ListBitMatch]

@[simp] private theorem listBitMatch_cons (x y : TomlValue) (xs ys : List TomlValue) :
    ListBitMatch (x :: xs) (y :: ys) = (ValBitMatch x y ∧ ListBitMatch xs ys) := by
  simp [ListBitMatch]

@[simp] private theorem entryListBitMatch_nil : EntryListBitMatch [] [] = True := by
  simp [EntryListBitMatch]

@[simp] private theorem entryListBitMatch_cons (k1 k2 : String) (v1 v2 : TomlValue)
    (r1 r2 : List (String × TomlValue)) :
    EntryListBitMatch ((k1, v1) :: r1) ((k2, v2) :: r2) =
      (k1 = k2 ∧ ValBitMatch v1 v2 ∧ EntryListBitMatch r1 r2) := by
  simp [EntryListBitMatch]

@[simp] private theorem nodeBitMatch_leaf (v1 v2 : TomlValue) :
    NodeBitMatch (.leaf v1) (.leaf v2) = ValBitMatch v1 v2 := by
  simp [NodeBitMatch]

@[simp] private theorem nodeBitMatch_table (k1 k2 : TableKind) (e1 e2 : List (String × Node)) :
    NodeBitMatch (.table k1 e1) (.table k2 e2) = (k1 = k2 ∧ EntriesBitMatch e1 e2) := by
  simp [NodeBitMatch]

@[simp] private theorem nodeBitMatch_aot (a1 a2 : List (List (String × Node))) :
    NodeBitMatch (.aot a1) (.aot a2) = AotBitMatch a1 a2 := by
  simp [NodeBitMatch]

@[simp] private theorem entriesBitMatch_nil : EntriesBitMatch [] [] = True := by
  simp [EntriesBitMatch]

@[simp] private theorem entriesBitMatch_cons (k1 k2 : String) (n1 n2 : Node)
    (r1 r2 : List (String × Node)) :
    EntriesBitMatch ((k1, n1) :: r1) ((k2, n2) :: r2) =
      (k1 = k2 ∧ NodeBitMatch n1 n2 ∧ EntriesBitMatch r1 r2) := by
  simp [EntriesBitMatch]

@[simp] private theorem aotBitMatch_nil : AotBitMatch [] [] = True := by
  simp [AotBitMatch]

@[simp] private theorem aotBitMatch_cons (x y : List (String × Node))
    (xr yr : List (List (String × Node))) :
    AotBitMatch (x :: xr) (y :: yr) = (EntriesBitMatch x y ∧ AotBitMatch xr yr) := by
  simp [AotBitMatch]

/-- Refinement of `Except TomlError α` outputs (`R` on `.ok`, same `kind` and non-empty message on `.error`). -/
def ExceptMatch {α : Type} (R : α → α → Prop) : Except TomlError α → Except TomlError α → Prop
  | .ok a, .ok b => R a b
  | .error e1, .error e2 => e2.kind = e1.kind ∧ !(e2.message.isEmpty) = true
  | _, _ => False

@[simp] private theorem exceptMatch_ok {α : Type} {R : α → α → Prop} (a b : α) :
    ExceptMatch R (.ok a) (.ok b) = R a b := rfl

@[simp] private theorem exceptMatch_error {α : Type} {R : α → α → Prop} (e1 e2 : TomlError) :
    ExceptMatch R (.error e1) (.error e2) = (e2.kind = e1.kind ∧ !(e2.message.isEmpty) = true) := rfl

@[simp] private theorem exceptMatch_ok_error {α : Type} {R : α → α → Prop} (a : α) (e : TomlError) :
    ExceptMatch R (.ok a) (.error e) = False := rfl

@[simp] private theorem exceptMatch_error_ok {α : Type} {R : α → α → Prop} (e : TomlError) (b : α) :
    ExceptMatch R (.error e) (.ok b) = False := rfl

private theorem exceptMatch_bind {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    {m1 m2 : Except TomlError α} {f1 f2 : α → Except TomlError β}
    (hm : ExceptMatch R m1 m2) (hf : ∀ a b, R a b → ExceptMatch S (f1 a) (f2 b)) :
    ExceptMatch S (m1 >>= f1) (m2 >>= f2) := by
  cases m1 with
  | error e1 =>
    cases m2 with
    | error e2 => simpa [ExceptMatch, bind, Except.bind] using hm
    | ok _ => simp [ExceptMatch] at hm
  | ok a =>
    cases m2 with
    | error _ => simp [ExceptMatch] at hm
    | ok b => exact hf a b hm

private theorem exceptMatch_id {α : Type} {R : α → α → Prop} (m : Except TomlError α)
    (herr : ∀ e, m = .error e → !(e.message.isEmpty) = true)
    (hrefl : ∀ a, R a a) : ExceptMatch R m m := by
  cases m with
  | ok a => exact hrefl a
  | error e => exact ⟨rfl, herr e rfl⟩

private theorem valBitMatch_implies_tomlEquiv_aux :
    ∀ n : Nat, ∀ a b : TomlValue, sizeOf a ≤ n → ValBitMatch a b → TomlEquiv a b := by
  intro n0
  refine Nat.strongRecOn (motive := fun n =>
    ∀ a b : TomlValue, sizeOf a ≤ n → ValBitMatch a b → TomlEquiv a b) n0 fun n ih a b ha hab => ?_
  cases a with
  | string s1 =>
    cases b <;> simp [ValBitMatch, TomlEquiv] at hab ⊢; exact hab
  | int n1 =>
    cases b <;> simp [ValBitMatch, TomlEquiv] at hab ⊢; exact hab
  | float f1 =>
    cases b <;> simp [ValBitMatch, TomlEquiv] at hab ⊢
    exact floatEquiv_symm (floatBitMatch_implies_floatEquiv hab)
  | bool b1 =>
    cases b <;> simp [ValBitMatch, TomlEquiv] at hab ⊢; exact hab
  | offsetDateTime d1 =>
    cases b <;> simp [ValBitMatch, TomlEquiv] at hab ⊢; exact hab
  | localDateTime d1 =>
    cases b <;> simp [ValBitMatch, TomlEquiv] at hab ⊢; exact hab
  | localDate d1 =>
    cases b <;> simp [ValBitMatch, TomlEquiv] at hab ⊢; exact hab
  | localTime t1 =>
    cases b <;> simp [ValBitMatch, TomlEquiv] at hab ⊢; exact hab
  | array xs =>
    cases b with
    | array ys =>
      simp only [ValBitMatch] at hab
      simp only [TomlEquiv]
      have hlist : ∀ l1 l2 : List TomlValue,
          sizeOf l1 < sizeOf (TomlValue.array xs) →
          ListBitMatch l1 l2 → TomlListEquiv l1 l2 := by
        intro l1 l2 hl1 h12
        induction l1 generalizing l2 with
        | nil =>
          cases l2 with
          | nil => simp [TomlListEquiv]
          | cons _ _ => simp [ListBitMatch] at h12
        | cons x xr ihl =>
          cases l2 with
          | nil => simp [ListBitMatch] at h12
          | cons y yr =>
            simp only [ListBitMatch] at h12
            simp only [TomlListEquiv]
            have hx : sizeOf x < sizeOf (x :: xr) := by simp +arith
            have hxr : sizeOf xr < sizeOf (x :: xr) := by simp +arith
            have hxn : sizeOf x < n := by omega
            exact ⟨ih (sizeOf x) hxn x y (Nat.le_refl _) h12.1,
              ihl yr (Nat.lt_trans hxr hl1) h12.2⟩
      have hxs : sizeOf xs.toList < sizeOf (TomlValue.array xs) := by
        cases xs; simp +arith
      exact hlist xs.toList ys.toList hxs hab
    | _ => simp [ValBitMatch] at hab
  | table t1 =>
    cases b with
    | table t2 =>
      simp only [ValBitMatch] at hab
      simp only [TomlEquiv, TomlTableEquivList]
      have hent : ∀ e1 e2 : List (String × TomlValue),
          sizeOf e1 < sizeOf (TomlValue.table t1) →
          EntryListBitMatch e1 e2 →
          (∀ k, lookupKeyList k e1 = none → lookupKeyList k e2 = none) ∧
          (∀ k v1, (h1 : lookupKeyList k e1 = some v1) →
            ∃ v2, lookupKeyList k e2 = some v2 ∧ TomlEquiv v1 v2) := by
        intro e1 e2 he1 h12
        induction e1 generalizing e2 with
        | nil =>
          cases e2 with
          | nil => exact ⟨fun _ hk => hk, fun _ _ hk => by simp [lookupKeyList] at hk⟩
          | cons _ _ => simp [EntryListBitMatch] at h12
        | cons hd1 tl1 ihl =>
          rcases hd1 with ⟨k1, v1'⟩
          cases e2 with
          | nil => simp [EntryListBitMatch] at h12
          | cons hd2 tl2 =>
            rcases hd2 with ⟨k2, v2'⟩
            simp only [EntryListBitMatch] at h12
            rcases h12 with ⟨hk12, hv12, htl⟩
            subst hk12
            have hv' : sizeOf v1' < sizeOf ((k1, v1') :: tl1) := by simp +arith
            have htl' : sizeOf tl1 < sizeOf ((k1, v1') :: tl1) := by simp +arith
            have ih' := ihl tl2 (Nat.lt_trans htl' he1) htl
            refine ⟨?_, ?_⟩
            · intro k hk
              simp only [lookupKeyList] at hk ⊢
              by_cases hkk : (k == k1) = true
              · simp [hkk] at hk
              · simp only [hkk, Bool.false_eq_true, ↓reduceIte] at hk ⊢
                exact ih'.1 k hk
            · intro k v1 hk
              simp only [lookupKeyList] at hk ⊢
              by_cases hkk : (k == k1) = true
              · simp only [hkk, ↓reduceIte, Option.some.injEq] at hk ⊢
                cases hk
                exact ⟨v2', rfl, ih (sizeOf v1') (by omega) v1' v2' (Nat.le_refl _) hv12⟩
              · simp only [hkk, Bool.false_eq_true, ↓reduceIte] at hk ⊢
                exact ih'.2 k v1 hk
      have ht1 : sizeOf t1.toList < sizeOf (TomlValue.table t1) := by
        cases t1; simp +arith
      exact hent t1.toList t2.toList ht1 hab
    | _ => simp [ValBitMatch] at hab

/-- `ValBitMatch` implies `Model.TomlEquiv`. -/
theorem valBitMatch_implies_tomlEquiv {a b : TomlValue} (h : ValBitMatch a b) : TomlEquiv a b :=
  valBitMatch_implies_tomlEquiv_aux (sizeOf a) a b (Nat.le_refl _) h

/-- `TableBitMatch` implies `Model.TomlTableEquiv`. -/
theorem tableBitMatch_implies_tomlTableEquiv {t1 t2 : TomlTable} (h : TableBitMatch t1 t2) :
    TomlTableEquiv t1 t2 := by
  have hval : ValBitMatch (.table t1) (.table t2) := by
    simpa [ValBitMatch, TableBitMatch] using h
  simpa [TomlEquiv, TomlTableEquiv] using valBitMatch_implies_tomlEquiv hval

private theorem entryListBitMatch_lookupKey (k : String) (e1 e2 : List (String × TomlValue))
    (h : EntryListBitMatch e1 e2) (v1 : TomlValue) (hk : lookupKeyList k e1 = some v1) :
    ∃ v2, lookupKeyList k e2 = some v2 ∧ ValBitMatch v1 v2 := by
  induction e1 generalizing e2 v1 with
  | nil => simp [lookupKeyList] at hk
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨k1, v1'⟩
    cases e2 with
    | nil => simp [EntryListBitMatch] at h
    | cons hd2 tl2 =>
      rcases hd2 with ⟨k2, v2'⟩
      simp only [EntryListBitMatch] at h
      rcases h with ⟨hk12, hv12, htl⟩
      subst hk12
      simp only [lookupKeyList] at hk ⊢
      by_cases hkk : (k == k1) = true
      · simp only [hkk, ↓reduceIte, Option.some.injEq] at hk ⊢
        cases hk
        exact ⟨v2', rfl, hv12⟩
      · simp only [hkk, Bool.false_eq_true, ↓reduceIte] at hk ⊢
        exact ih tl2 htl v1 hk

/-- `TableBitMatch` preserves key lookup up to `ValBitMatch`. -/
theorem tableBitMatch_lookupKey (k : String) (t1 t2 : TomlTable) (h : TableBitMatch t1 t2)
    (v1 : TomlValue) (hk : lookupKey k t1 = some v1) :
    ∃ v2, lookupKey k t2 = some v2 ∧ ValBitMatch v1 v2 :=
  entryListBitMatch_lookupKey k t1.toList t2.toList h v1 hk

private theorem nodeToTomlValue_bitMatch :
    ∀ n : Nat,
      (∀ a b : Node, sizeOf a ≤ n → NodeBitMatch a b →
        ValBitMatch (nodeToTomlValue a) (nodeToTomlValue b)) ∧
      (∀ e1 e2 : List (String × Node), sizeOf e1 ≤ n → EntriesBitMatch e1 e2 →
        EntryListBitMatch (entriesToTomlList e1) (entriesToTomlList e2)) ∧
      (∀ l1 l2 : List (List (String × Node)), sizeOf l1 ≤ n → AotBitMatch l1 l2 →
        ListBitMatch (aotElemsToToml l1) (aotElemsToToml l2)) := by
  intro n0
  refine Nat.strongRecOn (motive := fun n =>
    (∀ a b : Node, sizeOf a ≤ n → NodeBitMatch a b →
      ValBitMatch (nodeToTomlValue a) (nodeToTomlValue b)) ∧
    (∀ e1 e2 : List (String × Node), sizeOf e1 ≤ n → EntriesBitMatch e1 e2 →
      EntryListBitMatch (entriesToTomlList e1) (entriesToTomlList e2)) ∧
    (∀ l1 l2 : List (List (String × Node)), sizeOf l1 ≤ n → AotBitMatch l1 l2 →
      ListBitMatch (aotElemsToToml l1) (aotElemsToToml l2))) n0 fun n ih => ?_
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hab
    cases a with
    | leaf v1 =>
      cases b with
      | leaf v2 => simpa [NodeBitMatch, nodeToTomlValue] using hab
      | _ => simp [NodeBitMatch] at hab
    | table k1 e1 =>
      cases b with
      | table k2 e2 =>
        simp only [NodeBitMatch] at hab
        simp only [nodeToTomlValue, valBitMatch_table]
        have he1 : sizeOf e1 < n := by
          have : sizeOf e1 < sizeOf (Node.table k1 e1) := by simp +arith
          omega
        exact (ih (sizeOf e1) he1).2.1 e1 e2 (Nat.le_refl _) hab.2
      | _ => simp [NodeBitMatch] at hab
    | aot l1 =>
      cases b with
      | aot l2 =>
        simp only [nodeToTomlValue, valBitMatch_array]
        have hl1 : sizeOf l1 < n := by
          have : sizeOf l1 < sizeOf (Node.aot l1) := by simp +arith
          omega
        exact (ih (sizeOf l1) hl1).2.2 l1 l2 (Nat.le_refl _) (by simpa using hab)
      | _ => simp [NodeBitMatch] at hab
  · intro e1 e2 he1 h12
    cases e1 with
    | nil =>
      cases e2 with
      | nil => simp [entriesToTomlList]
      | cons _ _ => simp [EntriesBitMatch] at h12
    | cons hd1 tl1 =>
      rcases hd1 with ⟨k1, n1⟩
      cases e2 with
      | nil => simp [EntriesBitMatch] at h12
      | cons hd2 tl2 =>
        rcases hd2 with ⟨k2, n2⟩
        simp only [EntriesBitMatch] at h12
        rcases h12 with ⟨hk, hn, htl⟩
        subst hk
        simp only [entriesToTomlList, entryListBitMatch_cons]
        have hn1 : sizeOf n1 < n := by
          have : sizeOf n1 < sizeOf ((k1, n1) :: tl1) := by simp +arith
          omega
        have htl1 : sizeOf tl1 < n := by
          have : sizeOf tl1 < sizeOf ((k1, n1) :: tl1) := by simp +arith
          omega
        exact ⟨trivial, (ih (sizeOf n1) hn1).1 n1 n2 (Nat.le_refl _) hn,
          (ih (sizeOf tl1) htl1).2.1 tl1 tl2 (Nat.le_refl _) htl⟩
  · intro l1 l2 hl1 h12
    cases l1 with
    | nil =>
      cases l2 with
      | nil => simp [aotElemsToToml]
      | cons _ _ => simp [AotBitMatch] at h12
    | cons x xr =>
      cases l2 with
      | nil => simp [AotBitMatch] at h12
      | cons y yr =>
        simp only [AotBitMatch] at h12
        simp only [aotElemsToToml, listBitMatch_cons, valBitMatch_table]
        have hx : sizeOf x < n := by
          have : sizeOf x < sizeOf (x :: xr) := by simp +arith
          omega
        have hxr : sizeOf xr < n := by
          have : sizeOf xr < sizeOf (x :: xr) := by simp +arith
          omega
        exact ⟨(ih (sizeOf x) hx).2.1 x y (Nat.le_refl _) h12.1,
          (ih (sizeOf xr) hxr).2.2 xr yr (Nat.le_refl _) h12.2⟩

private theorem entriesToTomlList_bitMatch (e1 e2 : List (String × Node))
    (h : EntriesBitMatch e1 e2) : EntryListBitMatch (entriesToTomlList e1) (entriesToTomlList e2) :=
  (nodeToTomlValue_bitMatch (sizeOf e1)).2.1 e1 e2 (Nat.le_refl _) h

private theorem valueToInlineNode_bitMatch :
    ∀ n : Nat,
      (∀ v1 v2 : TomlValue, sizeOf v1 ≤ n → ValBitMatch v1 v2 →
        NodeBitMatch (valueToInlineNode v1) (valueToInlineNode v2)) ∧
      (∀ e1 e2 : List (String × TomlValue), sizeOf e1 ≤ n → EntryListBitMatch e1 e2 →
        EntriesBitMatch (inlineListToNodes e1) (inlineListToNodes e2)) := by
  intro n0
  refine Nat.strongRecOn (motive := fun n =>
    (∀ v1 v2 : TomlValue, sizeOf v1 ≤ n → ValBitMatch v1 v2 →
      NodeBitMatch (valueToInlineNode v1) (valueToInlineNode v2)) ∧
    (∀ e1 e2 : List (String × TomlValue), sizeOf e1 ≤ n → EntryListBitMatch e1 e2 →
      EntriesBitMatch (inlineListToNodes e1) (inlineListToNodes e2))) n0 fun n ih => ?_
  refine ⟨?_, ?_⟩
  · intro v1 v2 hv1 h12
    cases v1 with
    | table t1 =>
      cases v2 with
      | table t2 =>
        simp only [ValBitMatch] at h12
        simp only [valueToInlineNode, NodeBitMatch]
        have ht1 : sizeOf t1.toList < n := by
          have hsub : sizeOf t1.toList < sizeOf (TomlValue.table t1) := by
            cases t1; simp +arith
          omega
        exact ⟨trivial, (ih (sizeOf t1.toList) ht1).2 t1.toList t2.toList (Nat.le_refl _) h12⟩
      | _ => simp [ValBitMatch] at h12
    | string _ => cases v2 <;> simp [ValBitMatch, valueToInlineNode] at h12 ⊢; exact h12
    | int _ => cases v2 <;> simp [ValBitMatch, valueToInlineNode] at h12 ⊢; exact h12
    | float _ => cases v2 <;> simp [ValBitMatch, valueToInlineNode] at h12 ⊢; exact h12
    | bool _ => cases v2 <;> simp [ValBitMatch, valueToInlineNode] at h12 ⊢; exact h12
    | offsetDateTime _ => cases v2 <;> simp [ValBitMatch, valueToInlineNode] at h12 ⊢; exact h12
    | localDateTime _ => cases v2 <;> simp [ValBitMatch, valueToInlineNode] at h12 ⊢; exact h12
    | localDate _ => cases v2 <;> simp [ValBitMatch, valueToInlineNode] at h12 ⊢; exact h12
    | localTime _ => cases v2 <;> simp [ValBitMatch, valueToInlineNode] at h12 ⊢; exact h12
    | array _ => cases v2 <;> simp [ValBitMatch, valueToInlineNode] at h12 ⊢; exact h12
  · intro e1 e2 he1 h12
    cases e1 with
    | nil =>
      cases e2 with
      | nil => simp [inlineListToNodes]
      | cons _ _ => simp [EntryListBitMatch] at h12
    | cons hd1 tl1 =>
      rcases hd1 with ⟨k1, v1⟩
      cases e2 with
      | nil => simp [EntryListBitMatch] at h12
      | cons hd2 tl2 =>
        rcases hd2 with ⟨k2, v2⟩
        simp only [EntryListBitMatch] at h12
        rcases h12 with ⟨hk, hv, htl⟩
        subst hk
        simp only [inlineListToNodes, entriesBitMatch_cons]
        have hv1 : sizeOf v1 < n := by
          have : sizeOf v1 < sizeOf ((k1, v1) :: tl1) := by simp +arith
          omega
        have htl1 : sizeOf tl1 < n := by
          have : sizeOf tl1 < sizeOf ((k1, v1) :: tl1) := by simp +arith
          omega
        exact ⟨trivial, (ih (sizeOf v1) hv1).1 v1 v2 (Nat.le_refl _) hv,
          (ih (sizeOf tl1) htl1).2 tl1 tl2 (Nat.le_refl _) htl⟩

private theorem assocLookupNode_bitMatch (k : String) (e1 e2 : List (String × Node))
    (h : EntriesBitMatch e1 e2) :
    match assocLookupNode k e1, assocLookupNode k e2 with
    | none, none => True
    | some n1, some n2 => NodeBitMatch n1 n2
    | _, _ => False := by
  induction e1 generalizing e2 with
  | nil =>
    cases e2 with
    | nil => simp [assocLookupNode]
    | cons _ _ => simp [EntriesBitMatch] at h
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨k1, n1⟩
    cases e2 with
    | nil => simp [EntriesBitMatch] at h
    | cons hd2 tl2 =>
      rcases hd2 with ⟨k2, n2⟩
      simp only [EntriesBitMatch] at h
      rcases h with ⟨hk, hn, htl⟩
      subst hk
      simp only [assocLookupNode]
      by_cases hkk : (k == k1) = true
      · simp [hkk, hn]
      · simp only [hkk, Bool.false_eq_true, ↓reduceIte]
        exact ih tl2 htl

private theorem assocSetNode_bitMatch (k : String) (n1 n2 : Node) (e1 e2 : List (String × Node))
    (hn : NodeBitMatch n1 n2) (he : EntriesBitMatch e1 e2) :
    EntriesBitMatch (assocSetNode k n1 e1) (assocSetNode k n2 e2) := by
  induction e1 generalizing e2 with
  | nil =>
    cases e2 with
    | nil => simp [assocSetNode, hn]
    | cons _ _ => simp [EntriesBitMatch] at he
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨k1, v1⟩
    cases e2 with
    | nil => simp [EntriesBitMatch] at he
    | cons hd2 tl2 =>
      rcases hd2 with ⟨k2, v2⟩
      simp only [EntriesBitMatch] at he
      rcases he with ⟨hk, hv, htl⟩
      subst hk
      simp only [assocSetNode]
      by_cases hkk : (k == k1) = true
      · simp [hkk, hn, htl]
      · simp [hkk, hv, ih tl2 htl]

private theorem insertDottedEntries_nil_bitMatch (fullPath : List String)
    (e1 e2 : List (String × Node)) (k : String) (n1 n2 : Node)
    (he : EntriesBitMatch e1 e2) (hn : NodeBitMatch n1 n2) :
    ExceptMatch EntriesBitMatch
      (insertDottedEntries fullPath e1 [k] n1)
      (insertDottedEntries fullPath e2 [k] n2) := by
  have hl := assocLookupNode_bitMatch k e1 e2 he
  unfold insertDottedEntries
  cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;>
    simp only [hl1, hl2] at hl ⊢
  · exact assocSetNode_bitMatch k n1 n2 e1 e2 hn he
  · rename_i a b
    cases a with
    | leaf _ =>
      cases b with
      | leaf _ => dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
      | _ => simp [NodeBitMatch] at hl
    | table ka _ =>
      cases b with
      | table kb _ =>
        simp only [NodeBitMatch] at hl
        rcases hl with ⟨hkab, _⟩
        subst hkab
        cases ka <;> (dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩)
      | _ => simp [NodeBitMatch] at hl
    | aot _ =>
      cases b with
      | aot _ => dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
      | _ => simp [NodeBitMatch] at hl

private theorem insertDottedEntries_bitMatch (fullPath : List String)
    (e1 e2 : List (String × Node)) (relPath : List String) (n1 n2 : Node)
    (he : EntriesBitMatch e1 e2) (hn : NodeBitMatch n1 n2) :
    ExceptMatch EntriesBitMatch
      (insertDottedEntries fullPath e1 relPath n1)
      (insertDottedEntries fullPath e2 relPath n2) := by
  induction relPath generalizing e1 e2 with
  | nil =>
    dsimp only [insertDottedEntries]
    dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
  | cons k rest ih =>
    cases rest with
    | nil =>
      exact insertDottedEntries_nil_bitMatch fullPath e1 e2 k n1 n2 he hn
    | cons k2 rest2 =>
      have hl := assocLookupNode_bitMatch k e1 e2 he
      unfold insertDottedEntries
      cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;>
        simp only [hl1, hl2] at hl ⊢
      · exact exceptMatch_bind (ih [] [] (by simp)) fun s1 s2 hs =>
          assocSetNode_bitMatch k (.table .dotted s1) (.table .dotted s2) e1 e2 (by simp [hs]) he
      · rename_i a b
        cases a with
        | leaf v1 =>
          cases b with
          | leaf v2 =>
            cases v1 <;> cases v2 <;> simp [ValBitMatch] at hl <;>
              (dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩)
          | _ => simp [NodeBitMatch] at hl
        | table ka sa =>
          cases b with
          | table kb sb =>
            simp only [NodeBitMatch] at hl
            rcases hl with ⟨hkab, hsab⟩
            subst hkab
            cases ka <;>
              first
              | (dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩)
              | exact exceptMatch_bind (ih sa sb hsab) fun s1 s2 hs =>
                  assocSetNode_bitMatch k (.table .dotted s1) (.table .dotted s2) e1 e2 (by simp [hs]) he
          | _ => simp [NodeBitMatch] at hl
        | aot _ =>
          cases b with
          | aot _ => dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
          | _ => simp [NodeBitMatch] at hl

private theorem mapLastAot_bitMatch
    (f1 f2 : List (String × Node) → Except TomlError (List (String × Node)))
    (hf : ∀ x y, EntriesBitMatch x y → ExceptMatch EntriesBitMatch (f1 x) (f2 y))
    (l1 l2 : List (List (String × Node))) (hl : AotBitMatch l1 l2) :
    ExceptMatch AotBitMatch (mapLastAot f1 l1) (mapLastAot f2 l2) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
    | cons _ _ => simp [AotBitMatch] at hl
  | cons hd1 tl1 ih =>
    cases l2 with
    | nil => simp [AotBitMatch] at hl
    | cons hd2 tl2 =>
      simp only [AotBitMatch] at hl
      cases tl1 with
      | nil =>
        cases tl2 with
        | nil =>
          simp only [mapLastAot]
          exact exceptMatch_bind (hf hd1 hd2 hl.1) fun u1 u2 hu => by simp [ExceptMatch, hu]
        | cons _ _ => simp [AotBitMatch] at hl
      | cons a1 b1 =>
        cases tl2 with
        | nil => simp [AotBitMatch] at hl
        | cons a2 b2 =>
          simp only [mapLastAot]
          exact exceptMatch_bind (ih (a2 :: b2) hl.2) fun r1 r2 hr => by simp [ExceptMatch, hl.1, hr]

private theorem applyTableHeader_bitMatch (fullPath : List String)
    (e1 e2 : List (String × Node)) (path : List String) (he : EntriesBitMatch e1 e2) :
    ExceptMatch EntriesBitMatch
      (applyTableHeader fullPath e1 path)
      (applyTableHeader fullPath e2 path) := by
  induction path generalizing e1 e2 with
  | nil => dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
  | cons k rest ih =>
    cases rest with
    | nil =>
      have hl := assocLookupNode_bitMatch k e1 e2 he
      unfold applyTableHeader
      cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;>
        simp only [hl1, hl2] at hl ⊢
      · exact assocSetNode_bitMatch k (.table .explicit []) (.table .explicit []) e1 e2 (by simp) he
      · rename_i a b
        cases a with
        | leaf v1 =>
          cases b with
          | leaf v2 =>
            cases v1 <;> cases v2 <;> simp [ValBitMatch] at hl <;>
              (dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩)
          | _ => simp [NodeBitMatch] at hl
        | table ka sa =>
          cases b with
          | table kb sb =>
            simp only [NodeBitMatch] at hl
            rcases hl with ⟨hkab, hsab⟩
            subst hkab
            cases ka
            · dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
            · exact assocSetNode_bitMatch k (.table .explicit sa) (.table .explicit sb) e1 e2
                (by simp [hsab]) he
            · dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
            · dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
          | _ => simp [NodeBitMatch] at hl
        | aot _ =>
          cases b with
          | aot _ => dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
          | _ => simp [NodeBitMatch] at hl
    | cons k2 rest2 =>
      have hl := assocLookupNode_bitMatch k e1 e2 he
      unfold applyTableHeader
      cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;>
        simp only [hl1, hl2] at hl ⊢
      · exact exceptMatch_bind (ih [] [] (by simp)) fun s1 s2 hs =>
          assocSetNode_bitMatch k (.table .subtableImplicit s1) (.table .subtableImplicit s2) e1 e2 (by simp [hs]) he
      · rename_i a b
        cases a with
        | leaf v1 =>
          cases b with
          | leaf v2 =>
            cases v1 <;> cases v2 <;> simp [ValBitMatch] at hl <;>
              (dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩)
          | _ => simp [NodeBitMatch] at hl
        | table ka sa =>
          cases b with
          | table kb sb =>
            simp only [NodeBitMatch] at hl
            rcases hl with ⟨hkab, hsab⟩
            subst hkab
            cases ka
            · exact exceptMatch_bind (ih sa sb hsab) fun s1 s2 hs =>
                assocSetNode_bitMatch k (.table .explicit s1) (.table .explicit s2) e1 e2 (by simp [hs]) he
            · exact exceptMatch_bind (ih sa sb hsab) fun s1 s2 hs =>
                assocSetNode_bitMatch k (.table .subtableImplicit s1) (.table .subtableImplicit s2) e1 e2 (by simp [hs]) he
            · exact exceptMatch_bind (ih sa sb hsab) fun s1 s2 hs =>
                assocSetNode_bitMatch k (.table .dotted s1) (.table .dotted s2) e1 e2 (by simp [hs]) he
            · dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
          | _ => simp [NodeBitMatch] at hl
        | aot la =>
          cases b with
          | aot lb =>
            simp only [NodeBitMatch] at hl
            exact exceptMatch_bind
              (mapLastAot_bitMatch _ _ (fun x y hx => ih x y hx) la lb hl) fun n1 n2 hn =>
              assocSetNode_bitMatch k (.aot n1) (.aot n2) e1 e2 (by simp [hn]) he
          | _ => simp [NodeBitMatch] at hl

private theorem append_empty_aotBitMatch (l1 l2 : List (List (String × Node)))
    (h : AotBitMatch l1 l2) : AotBitMatch (l1 ++ [[]]) (l2 ++ [[]]) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp
    | cons _ _ => simp [AotBitMatch] at h
  | cons x xr ih =>
    cases l2 with
    | nil => simp [AotBitMatch] at h
    | cons y yr =>
      simp only [AotBitMatch] at h
      simp only [List.cons_append, AotBitMatch]
      exact ⟨h.1, ih yr h.2⟩

private theorem applyAotHeader_bitMatch (fullPath : List String)
    (e1 e2 : List (String × Node)) (path : List String) (he : EntriesBitMatch e1 e2) :
    ExceptMatch EntriesBitMatch
      (applyAotHeader fullPath e1 path)
      (applyAotHeader fullPath e2 path) := by
  induction path generalizing e1 e2 with
  | nil => dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
  | cons k rest ih =>
    cases rest with
    | nil =>
      have hl := assocLookupNode_bitMatch k e1 e2 he
      unfold applyAotHeader
      cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;>
        simp only [hl1, hl2] at hl ⊢
      · exact assocSetNode_bitMatch k (.aot [[]]) (.aot [[]]) e1 e2 (by simp) he
      · rename_i a b
        cases a with
        | leaf v1 =>
          cases b with
          | leaf v2 =>
            cases v1 <;> cases v2 <;> simp [ValBitMatch] at hl <;>
              (dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩)
          | _ => simp [NodeBitMatch] at hl
        | table ka _ =>
          cases b with
          | table kb _ =>
            simp only [NodeBitMatch] at hl
            rcases hl with ⟨hkab, _⟩
            subst hkab
            cases ka <;> (dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩)
          | _ => simp [NodeBitMatch] at hl
        | aot la =>
          cases b with
          | aot lb =>
            simp only [NodeBitMatch] at hl
            exact assocSetNode_bitMatch k (.aot (la ++ [[]])) (.aot (lb ++ [[]])) e1 e2
              (by simp [append_empty_aotBitMatch la lb hl]) he
          | _ => simp [NodeBitMatch] at hl
    | cons k2 rest2 =>
      have hl := assocLookupNode_bitMatch k e1 e2 he
      unfold applyAotHeader
      cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;>
        simp only [hl1, hl2] at hl ⊢
      · exact exceptMatch_bind (ih [] [] (by simp)) fun s1 s2 hs =>
          assocSetNode_bitMatch k (.table .subtableImplicit s1) (.table .subtableImplicit s2) e1 e2 (by simp [hs]) he
      · rename_i a b
        cases a with
        | leaf v1 =>
          cases b with
          | leaf v2 =>
            cases v1 <;> cases v2 <;> simp [ValBitMatch] at hl <;>
              (dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩)
          | _ => simp [NodeBitMatch] at hl
        | table ka sa =>
          cases b with
          | table kb sb =>
            simp only [NodeBitMatch] at hl
            rcases hl with ⟨hkab, hsab⟩
            subst hkab
            cases ka
            · exact exceptMatch_bind (ih sa sb hsab) fun s1 s2 hs =>
                assocSetNode_bitMatch k (.table .explicit s1) (.table .explicit s2) e1 e2 (by simp [hs]) he
            · exact exceptMatch_bind (ih sa sb hsab) fun s1 s2 hs =>
                assocSetNode_bitMatch k (.table .subtableImplicit s1) (.table .subtableImplicit s2) e1 e2 (by simp [hs]) he
            · exact exceptMatch_bind (ih sa sb hsab) fun s1 s2 hs =>
                assocSetNode_bitMatch k (.table .dotted s1) (.table .dotted s2) e1 e2 (by simp [hs]) he
            · dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
          | _ => simp [NodeBitMatch] at hl
        | aot la =>
          cases b with
          | aot lb =>
            simp only [NodeBitMatch] at hl
            exact exceptMatch_bind
              (mapLastAot_bitMatch _ _ (fun x y hx => ih x y hx) la lb hl) fun n1 n2 hn =>
              assocSetNode_bitMatch k (.aot n1) (.aot n2) e1 e2 (by simp [hn]) he
          | _ => simp [NodeBitMatch] at hl

private theorem insertAtActivePath_bitMatch (fullPath : List String)
    (e1 e2 : List (String × Node)) (activePath relPath : List String) (n1 n2 : Node)
    (he : EntriesBitMatch e1 e2) (hn : NodeBitMatch n1 n2) :
    ExceptMatch EntriesBitMatch
      (insertAtActivePath fullPath e1 activePath relPath n1)
      (insertAtActivePath fullPath e2 activePath relPath n2) := by
  induction activePath generalizing e1 e2 with
  | nil =>
    cases relPath with
    | nil => dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
    | cons rk rr =>
      cases rr with
      | nil => exact insertDottedEntries_nil_bitMatch fullPath e1 e2 rk n1 n2 he hn
      | cons _ _ => exact insertDottedEntries_bitMatch fullPath e1 e2 (rk :: _ :: _) n1 n2 he hn
  | cons k rest ih =>
    have hl := assocLookupNode_bitMatch k e1 e2 he
    unfold insertAtActivePath
    cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;>
      simp only [hl1, hl2] at hl ⊢
    · dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
    · rename_i a b
      cases a with
      | leaf _ =>
        cases b with
        | leaf _ => dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
        | _ => simp [NodeBitMatch] at hl
      | table ka sa =>
        cases b with
        | table kb sb =>
          simp only [NodeBitMatch] at hl
          rcases hl with ⟨hkab, hsab⟩
          subst hkab
          exact exceptMatch_bind (ih sa sb hsab) fun s1 s2 hs =>
            assocSetNode_bitMatch k (.table ka s1) (.table ka s2) e1 e2 (by simp [hs]) he
        | _ => simp [NodeBitMatch] at hl
      | aot la =>
        cases b with
        | aot lb =>
          simp only [NodeBitMatch] at hl
          exact exceptMatch_bind
            (mapLastAot_bitMatch _ _ (fun x y hx => ih x y hx) la lb hl) fun m1 m2 hm =>
            assocSetNode_bitMatch k (.aot m1) (.aot m2) e1 e2 (by simp [hm]) he
        | _ => simp [NodeBitMatch] at hl

private theorem valBitMatch_refl (v : TomlValue) : ValBitMatch v v := by
  suffices h : ∀ n : Nat, ∀ x : TomlValue, sizeOf x ≤ n → ValBitMatch x x from
    h (sizeOf v) v (Nat.le_refl _)
  intro n0
  refine Nat.strongRecOn (motive := fun n => ∀ x : TomlValue, sizeOf x ≤ n → ValBitMatch x x) n0
    fun n ih x hx => ?_
  cases x with
  | string _ | int _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
    simp [ValBitMatch]
  | float f => simp [ValBitMatch, floatBitMatch_refl]
  | array xs =>
    simp only [ValBitMatch]
    have hl : ∀ l : List TomlValue, sizeOf l < sizeOf (TomlValue.array xs) → ListBitMatch l l := by
      intro l hl'
      induction l with
      | nil => simp
      | cons a xr ihl =>
        have ha : sizeOf a < n := by
          have : sizeOf a < sizeOf (a :: xr) := by simp +arith
          omega
        have hxr : sizeOf xr < sizeOf (a :: xr) := by simp +arith
        exact by simp [ih (sizeOf a) ha a (Nat.le_refl _), ihl (Nat.lt_trans hxr hl')]
    have hxs : sizeOf xs.toList < sizeOf (TomlValue.array xs) := by cases xs; simp +arith
    exact hl xs.toList hxs
  | table t =>
    simp only [ValBitMatch]
    have hl : ∀ l : List (String × TomlValue), sizeOf l < sizeOf (TomlValue.table t) →
        EntryListBitMatch l l := by
      intro l hl'
      induction l with
      | nil => simp
      | cons p r ihl =>
        rcases p with ⟨k, v⟩
        have hv : sizeOf v < n := by
          have : sizeOf v < sizeOf ((k, v) :: r) := by simp +arith
          omega
        have hr : sizeOf r < sizeOf ((k, v) :: r) := by simp +arith
        exact by simp [ih (sizeOf v) hv v (Nat.le_refl _), ihl (Nat.lt_trans hr hl')]
    have ht : sizeOf t.toList < sizeOf (TomlValue.table t) := by cases t; simp +arith
    exact hl t.toList ht

private theorem parseInt64_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi) (s : String) :
    match parseInt64Model s, numApi.parseInt64 s with
    | .ok n1, .ok n2 => n1 = n2
    | .error k1, .error e2 => e2.kind = k1 ∧ e2.message ≠ ""
    | _, _ => False := by
  have h := hnum.parseInt64 s
  dsimp only [test_numparse_parseInt64_matchesModel, Core.NondetTest.nondet, NondetTest.assert,
    bind, pure] at h
  cases hm : parseInt64Model s <;> cases ha : numApi.parseInt64 s <;> simp [hm, ha] at h
  · exact h
  · exact h.symm

private theorem parseFloat_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi) (s : String) :
    match parseFloatModel s, numApi.parseFloat s with
    | .ok f1, .ok f2 => FloatBitMatch f1 f2
    | .error k1, .error e2 => e2.kind = k1 ∧ e2.message ≠ ""
    | _, _ => False := by
  have h := hnum.parseFloat s
  dsimp only [test_numparse_parseFloat_matchesModel, Core.NondetTest.nondet, NondetTest.assert,
    bind, pure] at h
  cases hm : parseFloatModel s <;> cases ha : numApi.parseFloat s <;> simp [hm, ha] at h
  · exact h
  · exact h

private theorem classifyScalarToken_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (tok : String) :
    ExceptMatch ValBitMatch
      (classifyScalarToken modelNumApi tok)
      (classifyScalarToken numApi tok) := by
  unfold classifyScalarToken
  split
  · exact ⟨rfl, mkErr_nonEmpty'⟩
  · split
    · simp [ExceptMatch, ValBitMatch]
    · split
      · simp [ExceptMatch, ValBitMatch]
      · split
        · rename_i res hres
          cases res with
          | ok v => exact valBitMatch_refl v
          | error e => exact ⟨rfl, parseDateTimeToken_err_nonEmpty tok e hres⟩
        · split
          · have hf := parseFloat_refines numApi hnum tok
            simp only [modelNumApi]
            cases hm : parseFloatModel tok <;> cases ha : numApi.parseFloat tok <;>
              simp [hm, ha] at hf
            · simp only [mapNumParseErr, ExceptMatch]
              exact ⟨by simp [mkErr, hf.1], mkErr_nonEmpty'⟩
            · simpa [ExceptMatch, ValBitMatch] using hf
          · split
            · exact ⟨rfl, mkErr_nonEmpty'⟩
            · have hi := parseInt64_refines numApi hnum tok
              simp only [modelNumApi]
              cases hm : parseInt64Model tok <;> cases ha : numApi.parseInt64 tok <;>
                simp [hm, ha] at hi
              · simp only [mapNumParseErr, ExceptMatch]
                exact ⟨by simp [mkErr, hi.1], mkErr_nonEmpty'⟩
              · subst hi; simp [ExceptMatch, ValBitMatch]

private theorem listBitMatch_append_singleton {l1 l2 : List TomlValue} {x1 x2 : TomlValue}
    (hl : ListBitMatch l1 l2) (hx : ValBitMatch x1 x2) :
    ListBitMatch (l1 ++ [x1]) (l2 ++ [x2]) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [hx]
    | cons _ _ => simp [ListBitMatch] at hl
  | cons a xr ih =>
    cases l2 with
    | nil => simp [ListBitMatch] at hl
    | cons b yr =>
      simp only [ListBitMatch] at hl
      simp only [List.cons_append, ListBitMatch]
      exact ⟨hl.1, ih hl.2⟩

private theorem listBitMatch_reverse {l1 l2 : List TomlValue} (hl : ListBitMatch l1 l2) :
    ListBitMatch l1.reverse l2.reverse := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => trivial
    | cons _ _ => simp [ListBitMatch] at hl
  | cons a xr ih =>
    cases l2 with
    | nil => simp [ListBitMatch] at hl
    | cons b yr =>
      simp only [ListBitMatch] at hl
      simp only [List.reverse_cons]
      exact listBitMatch_append_singleton (ih hl.2) hl.1

private theorem parseValArrInline_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (fuel : Nat) :
    (∀ cs, ExceptMatch (fun p1 p2 => ValBitMatch p1.1 p2.1 ∧ p1.2 = p2.2)
      (parseValueFuel modelNumApi fuel cs) (parseValueFuel numApi fuel cs)) ∧
    (∀ cs rev1 rev2, ListBitMatch rev1 rev2 →
      ExceptMatch (fun p1 p2 => ValBitMatch p1.1 p2.1 ∧ p1.2 = p2.2)
        (parseArrayFuel modelNumApi fuel cs rev1) (parseArrayFuel numApi fuel cs rev2)) ∧
    (∀ cs e1 e2, EntriesBitMatch e1 e2 →
      ExceptMatch (fun p1 p2 => ValBitMatch p1.1 p2.1 ∧ p1.2 = p2.2)
        (parseInlineTableFuel modelNumApi fuel cs e1) (parseInlineTableFuel numApi fuel cs e2)) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro _; exact ⟨rfl, mkErr_nonEmpty'⟩
    · intro _ _ _ _; exact ⟨rfl, mkErr_nonEmpty'⟩
    · intro _ _ _ _; exact ⟨rfl, mkErr_nonEmpty'⟩
  | succ fuel ih =>
    rcases ih with ⟨ihVal, ihArr, ihInl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro cs
      unfold parseValueFuel
      split
      · refine exceptMatch_id _ ?_ (fun _ => ⟨valBitMatch_refl _, rfl⟩)
        intro e h
        rcases except_bind_err h with hm | ⟨⟨_, _⟩, _, hm⟩
        · exact parseMultilineBasicBodyFuel_err_nonEmpty _ _ _ e hm
        · cases hm
      · refine exceptMatch_id _ ?_ (fun _ => ⟨valBitMatch_refl _, rfl⟩)
        intro e h
        rcases except_bind_err h with hm | ⟨⟨_, _⟩, _, hm⟩
        · exact parseBasicStringBodyFuel_err_nonEmpty _ _ _ e hm
        · cases hm
      · refine exceptMatch_id _ ?_ (fun _ => ⟨valBitMatch_refl _, rfl⟩)
        intro e h
        rcases except_bind_err h with hm | ⟨⟨_, _⟩, _, hm⟩
        · exact parseMultilineLiteralBodyFuel_err_nonEmpty _ _ _ e hm
        · cases hm
      · refine exceptMatch_id _ ?_ (fun _ => ⟨valBitMatch_refl _, rfl⟩)
        intro e h
        rcases except_bind_err h with hm | ⟨⟨_, _⟩, _, hm⟩
        · exact parseLiteralStringBody_err_nonEmpty _ _ e hm
        · cases hm
      · exact ihArr _ [] [] (by simp)
      · split
        · simp [ExceptMatch]
        · exact ihInl _ [] [] (by simp)
      · dsimp only
        exact exceptMatch_bind (classifyScalarToken_refines numApi hnum _) fun v1 v2 hv =>
          ⟨hv, rfl⟩
    · intro cs rev1 rev2 hrev
      unfold parseArrayFuel
      split
      · exact ⟨by simpa [ValBitMatch] using listBitMatch_reverse hrev, rfl⟩
      · dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
      · exact exceptMatch_bind (ihVal _) fun p1 p2 hp => by
          rcases p1 with ⟨v1, r1⟩
          rcases p2 with ⟨v2, r2⟩
          rcases hp with ⟨hv, hr⟩
          dsimp only at hr hv ⊢
          subst hr
          have hnext : ListBitMatch (v1 :: rev1) (v2 :: rev2) := by simp [hv, hrev]
          split
          · exact ihArr _ (v1 :: rev1) (v2 :: rev2) hnext
          · exact ⟨by simpa [ValBitMatch] using listBitMatch_reverse hnext, rfl⟩
          · dsimp only [ExceptMatch]; exact ⟨rfl, mkErr_nonEmpty'⟩
    · intro cs e1 e2 he
      unfold parseInlineTableFuel
      dsimp only
      refine exceptMatch_bind
        (exceptMatch_id (parseDottedKey (skipHorizWs cs))
          (fun e herr => parseDottedKeyFuel_err_nonEmpty _ _ e herr)
          (fun _ => rfl))
        fun kp1 kp2 hkp => ?_
      subst hkp
      split
      · refine exceptMatch_bind (ihVal _) fun vp1 vp2 hvp => ?_
        rcases vp1 with ⟨v1, r5a⟩
        rcases vp2 with ⟨v2, r5b⟩
        rcases hvp with ⟨hv, hr5⟩
        dsimp only at hv hr5 ⊢
        subst hr5
        have hn12 : NodeBitMatch (valueToInlineNode v1) (valueToInlineNode v2) :=
          (valueToInlineNode_bitMatch (sizeOf v1)).1 v1 v2 (Nat.le_refl _) hv
        refine exceptMatch_bind
          (insertDottedEntries_bitMatch kp1.1 e1 e2 kp1.1 (valueToInlineNode v1) (valueToInlineNode v2) he hn12)
          fun nextE1 nextE2 hnextE => ?_
        split
        · split
          · exact ⟨rfl, mkErr_nonEmpty'⟩
          · exact ihInl _ nextE1 nextE2 hnextE
        · exact ⟨by
            dsimp only
            simp only [ValBitMatch]
            exact entriesToTomlList_bitMatch nextE1 nextE2 hnextE, rfl⟩
        · exact ⟨rfl, mkErr_nonEmpty'⟩
      · exact ⟨rfl, mkErr_nonEmpty'⟩

private theorem parseDocumentFuel_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (fuel : Nat) (cs : List Char) (activePath : List String) (r1 r2 : List (String × Node))
    (hr : EntriesBitMatch r1 r2) :
    ExceptMatch EntriesBitMatch
      (parseDocumentFuel modelNumApi fuel cs activePath r1)
      (parseDocumentFuel numApi fuel cs activePath r2) := by
  induction fuel generalizing cs activePath r1 r2 with
  | zero =>
    unfold parseDocumentFuel
    split
    · exact hr
    · exact ⟨rfl, mkErr_nonEmpty'⟩
  | succ fuel ih =>
    unfold parseDocumentFuel
    split
    · exact hr
    · refine exceptMatch_bind
        (exceptMatch_id _ (fun e herr => parseDottedKeyFuel_err_nonEmpty _ _ e herr) (fun _ => rfl))
        fun kp1 kp2 hkp => ?_
      subst hkp
      dsimp only
      split
      · refine exceptMatch_bind
          (exceptMatch_id _ (fun e herr => consumeStatementEnd_err_nonEmpty _ e herr) (fun _ => rfl))
          fun nc1 nc2 hnc => ?_
        subst hnc
        exact exceptMatch_bind (applyAotHeader_bitMatch kp1.1 r1 r2 kp1.1 hr) fun nextR1 nextR2 hnextR =>
          ih _ kp1.1 nextR1 nextR2 hnextR
      · exact ⟨rfl, mkErr_nonEmpty'⟩
    · refine exceptMatch_bind
        (exceptMatch_id _ (fun e herr => parseDottedKeyFuel_err_nonEmpty _ _ e herr) (fun _ => rfl))
        fun kp1 kp2 hkp => ?_
      subst hkp
      dsimp only
      split
      · refine exceptMatch_bind
          (exceptMatch_id _ (fun e herr => consumeStatementEnd_err_nonEmpty _ e herr) (fun _ => rfl))
          fun nc1 nc2 hnc => ?_
        subst hnc
        exact exceptMatch_bind (applyTableHeader_bitMatch kp1.1 r1 r2 kp1.1 hr) fun nextR1 nextR2 hnextR =>
          ih _ kp1.1 nextR1 nextR2 hnextR
      · exact ⟨rfl, mkErr_nonEmpty'⟩
    · refine exceptMatch_bind
        (exceptMatch_id _ (fun e herr => parseDottedKeyFuel_err_nonEmpty _ _ e herr) (fun _ => rfl))
        fun kp1 kp2 hkp => ?_
      subst hkp
      dsimp only
      split
      · refine exceptMatch_bind ((parseValArrInline_refines numApi hnum _).1 _) fun vp1 vp2 hvp => ?_
        rcases vp1 with ⟨v1, r3a⟩
        rcases vp2 with ⟨v2, r3b⟩
        rcases hvp with ⟨hv, hr3⟩
        dsimp only at hv hr3 ⊢
        subst hr3
        refine exceptMatch_bind
          (exceptMatch_id _ (fun e herr => consumeStatementEnd_err_nonEmpty _ e herr) (fun _ => rfl))
          fun nc1 nc2 hnc => ?_
        subst hnc
        have hn12 : NodeBitMatch (valueToInlineNode v1) (valueToInlineNode v2) :=
          (valueToInlineNode_bitMatch (sizeOf v1)).1 v1 v2 (Nat.le_refl _) hv
        exact exceptMatch_bind
          (insertAtActivePath_bitMatch (activePath ++ kp1.1) r1 r2 activePath kp1.1
            (valueToInlineNode v1) (valueToInlineNode v2) hr hn12)
          fun nextR1 nextR2 hnextR => ih _ activePath nextR1 nextR2 hnextR
      · exact ⟨rfl, mkErr_nonEmpty'⟩

private theorem parseWithNum_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi) (s : String) :
    ExceptMatch TableBitMatch (parseWithNum modelNumApi s) (parseWithNum numApi s) := by
  unfold parseWithNum
  refine exceptMatch_bind
    (exceptMatch_id _ (fun e herr => normalizeChars_err_nonEmpty 1 1 s.toList e herr) (fun _ => rfl))
    fun norm1 norm2 hnorm => ?_
  subst hnorm
  exact exceptMatch_bind
    (parseDocumentFuel_refines numApi hnum (norm1.length + 1) norm1 [] [] [] (by simp))
    fun r1 r2 hr => entriesToTomlList_bitMatch r1 r2 hr

private theorem allPass_forM {α : Type} (xs : List α)
    (f : α → Core.AllPassRun Unit)
    (h : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post) :
    ∀ post : Unit → Prop, post () → xs.forM f post := by
  induction xs with
  | nil =>
    intro post hpost
    exact hpost
  | cons a rest ih =>
    intro post hpost
    have ha := h a (List.Mem.head _)
    have hrest := ih (fun x hx => h x (List.Mem.tail _ hx))
    change f a (fun _ => rest.forM f post)
    exact ha (fun _ => rest.forM f post) (hrest post hpost)

private theorem canReach_forM {α : Type} (xs : List α)
    (f : α → Core.CanReachRun Unit)
    (h : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post) :
    ∀ post : Unit → Prop, post () → xs.forM f post := by
  induction xs with
  | nil =>
    intro post hpost
    exact hpost
  | cons a rest ih =>
    intro post hpost
    have ha := h a (List.Mem.head _)
    have hrest := ih (fun x hx => h x (List.Mem.tail _ hx))
    change f a (fun _ => rest.forM f post)
    exact ha (fun _ => rest.forM f post) (hrest post hpost)

private theorem checkParseEquiv_prop (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (cases : List (String × TomlTable)) (hall : cases.all checkOneOkModel = true)
    (src : String) (exp : TomlTable) (hp : (src, exp) ∈ cases) :
    ∃ t2, parseWithNum numApi src = .ok t2 ∧ TomlTableEquiv exp t2 := by
  have hmem : checkOneOkModel (src, exp) = true := List.all_eq_true.mp hall (src, exp) hp
  have href := parseWithNum_refines numApi hnum src
  simp only [checkOneOkModel] at hmem
  cases hm : parseWithNum modelNumApi src <;> simp [hm] at hmem href
  case ok t1 =>
    cases ha : parseWithNum numApi src <;> simp [ha] at href
    case ok t2 =>
      have h1 : TomlTableEquiv exp t1 := by
        have hv := tomlValueBeq_implies_equiv (.table exp) (.table t1) hmem
        simpa [TomlEquiv, TomlTableEquiv] using hv
      exact ⟨t2, rfl, tomlTableEquiv_trans h1 (tableBitMatch_implies_tomlTableEquiv href)⟩

private theorem tomlErrorKind_beq_eq (a b : TomlErrorKind) (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> revert h <;> decide

private theorem checkParseErrorKind_prop (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (cases : List (String × TomlErrorKind)) (hall : cases.all checkOneErrModel = true)
    (src : String) (expectedKind : TomlErrorKind) (hp : (src, expectedKind) ∈ cases) :
    ∃ e2, parseWithNum numApi src = .error e2 ∧ e2.kind = expectedKind ∧ !(e2.message.isEmpty) = true := by
  have hmem : checkOneErrModel (src, expectedKind) = true := List.all_eq_true.mp hall (src, expectedKind) hp
  have href := parseWithNum_refines numApi hnum src
  simp only [checkOneErrModel] at hmem
  cases hm : parseWithNum modelNumApi src with
  | ok _ =>
    simp only [hm] at hmem
    exact absurd hmem Bool.false_ne_true
  | error e1 =>
    simp only [hm] at hmem href
    cases ha : parseWithNum numApi src with
    | ok _ =>
      simp only [ha, exceptMatch_error_ok] at href
    | error e2 =>
      simp only [ha, exceptMatch_error] at href
      exact ⟨e2, rfl, href.1.trans (tomlErrorKind_beq_eq e1.kind expectedKind hmem), href.2⟩

private theorem checkParseFloatBits_prop (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (src k : String) (exp : Option UInt64) (hp : (src, k, exp) ∈ floatBitCases) :
    ∃ t2 f2, parseWithNum numApi src = .ok t2 ∧ lookupKey k t2 = some (.float f2) ∧
      (match exp with | none => f2.isNaN = true | some bits => f2.toBits = bits) := by
  have hmem : checkOneFloatBitModel (src, k, exp) = true := List.all_eq_true.mp floatBit_model_valid (src, k, exp) hp
  have href := parseWithNum_refines numApi hnum src
  simp only [checkOneFloatBitModel] at hmem
  cases hm : parseWithNum modelNumApi src <;> simp [hm] at hmem href
  case ok t1 =>
    cases ha : parseWithNum numApi src <;> simp [ha] at href
    case ok t2 =>
      cases hlook1 : lookupKey k t1 with
      | none => simp [hlook1] at hmem
      | some v1 =>
        cases v1 with
        | float f1 =>
          obtain ⟨v2, hlook2, hv12⟩ := tableBitMatch_lookupKey k t1 t2 href (.float f1) hlook1
          cases v2 with
          | float f2 =>
            simp only [ValBitMatch, FloatBitMatch] at hv12
            simp only [hlook1] at hmem
            refine ⟨t2, f2, rfl, hlook2, ?_⟩
            cases exp with
            | none =>
              simp only at hmem
              simp only [hmem, ↓reduceIte] at hv12
              exact hv12
            | some bits =>
              simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hmem
              simp only [hmem.1, Bool.false_eq_true, ↓reduceIte] at hv12
              exact hv12.trans hmem.2
          | _ => simp [ValBitMatch] at hv12
        | _ => simp [hlook1] at hmem

private theorem checkParseEquiv_allPass (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (cases : List (String × TomlTable)) (hall : cases.all checkOneOkModel = true) :
    ∀ p ∈ cases, ∀ post : Unit → Prop, post () → (checkParseEquiv (makeTomlApi numApi) p : Core.AllPassRun Unit) post := by
  rintro ⟨src, exp⟩ hp post hpost
  obtain ⟨t2, ha, heq⟩ := checkParseEquiv_prop numApi hnum cases hall src exp hp
  dsimp only [checkParseEquiv, makeTomlApi, Core.NondetTest.assert]
  rw [ha]
  exact ⟨heq, hpost⟩

private theorem checkParseEquiv_canReach (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (cases : List (String × TomlTable)) (hall : cases.all checkOneOkModel = true) :
    ∀ p ∈ cases, ∀ post : Unit → Prop, post () → (checkParseEquiv (makeTomlApi numApi) p : Core.CanReachRun Unit) post := by
  rintro ⟨src, exp⟩ hp post hpost
  obtain ⟨t2, ha, heq⟩ := checkParseEquiv_prop numApi hnum cases hall src exp hp
  dsimp only [checkParseEquiv, makeTomlApi, Core.NondetTest.assert]
  rw [ha]
  exact ⟨heq, hpost⟩

private theorem checkParseErrorKind_allPass (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (cases : List (String × TomlErrorKind)) (hall : cases.all checkOneErrModel = true) :
    ∀ p ∈ cases, ∀ post : Unit → Prop, post () → (checkParseErrorKind (makeTomlApi numApi) p : Core.AllPassRun Unit) post := by
  rintro ⟨src, expectedKind⟩ hp post hpost
  obtain ⟨e2, ha, hk, hne⟩ := checkParseErrorKind_prop numApi hnum cases hall src expectedKind hp
  dsimp only [checkParseErrorKind, makeTomlApi, Core.NondetTest.assert]
  rw [ha]
  exact ⟨⟨hk, hne⟩, hpost⟩

private theorem checkParseErrorKind_canReach (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (cases : List (String × TomlErrorKind)) (hall : cases.all checkOneErrModel = true) :
    ∀ p ∈ cases, ∀ post : Unit → Prop, post () → (checkParseErrorKind (makeTomlApi numApi) p : Core.CanReachRun Unit) post := by
  rintro ⟨src, expectedKind⟩ hp post hpost
  obtain ⟨e2, ha, hk, hne⟩ := checkParseErrorKind_prop numApi hnum cases hall src expectedKind hp
  dsimp only [checkParseErrorKind, makeTomlApi, Core.NondetTest.assert]
  rw [ha]
  exact ⟨⟨hk, hne⟩, hpost⟩

private theorem checkParseFloatBits_allPass (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    ∀ p ∈ floatBitCases, ∀ post : Unit → Prop, post () → (checkParseFloatBits (makeTomlApi numApi) p : Core.AllPassRun Unit) post := by
  rintro ⟨src, k, exp⟩ hp post hpost
  obtain ⟨t2, f2, ha, hlook2, hf2⟩ := checkParseFloatBits_prop numApi hnum src k exp hp
  dsimp only [checkParseFloatBits, makeTomlApi, Core.NondetTest.assert]
  rw [ha]
  dsimp only
  rw [hlook2]
  dsimp only
  cases exp <;> exact ⟨hf2, hpost⟩

private theorem checkParseFloatBits_canReach (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    ∀ p ∈ floatBitCases, ∀ post : Unit → Prop, post () → (checkParseFloatBits (makeTomlApi numApi) p : Core.CanReachRun Unit) post := by
  rintro ⟨src, k, exp⟩ hp post hpost
  obtain ⟨t2, f2, ha, hlook2, hf2⟩ := checkParseFloatBits_prop numApi hnum src k exp hp
  dsimp only [checkParseFloatBits, makeTomlApi, Core.NondetTest.assert]
  rw [ha]
  dsimp only
  rw [hlook2]
  dsimp only
  cases exp <;> exact ⟨hf2, hpost⟩

private theorem allPass_forM_top {α : Type} (xs : List α)
    (f : α → Core.AllPassRun Unit)
    (h : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post) :
    Core.AllPass (xs.forM f) :=
  allPass_forM xs f h (fun _ => True) trivial

private theorem canReach_forM_top {α : Type} (xs : List α)
    (f : α → Core.CanReachRun Unit)
    (h : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post) :
    Core.CanReach (xs.forM f) :=
  canReach_forM xs f h (fun _ => True) trivial

private theorem allPass_forM_seq {α β : Type} (xs : List α) (ys : List β)
    (f : α → Core.AllPassRun Unit) (g : β → Core.AllPassRun Unit)
    (hf : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post)
    (hg : ∀ y ∈ ys, ∀ post : Unit → Prop, post () → g y post) :
    Core.AllPass (do xs.forM f; ys.forM g) :=
  allPass_forM xs f hf (fun _ => ys.forM g (fun _ => True)) (allPass_forM_top ys g hg)

private theorem canReach_forM_seq {α β : Type} (xs : List α) (ys : List β)
    (f : α → Core.CanReachRun Unit) (g : β → Core.CanReachRun Unit)
    (hf : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post)
    (hg : ∀ y ∈ ys, ∀ post : Unit → Prop, post () → g y post) :
    Core.CanReach (do xs.forM f; ys.forM g) :=
  canReach_forM xs f hf (fun _ => ys.forM g (fun _ => True)) (canReach_forM_top ys g hg)

private theorem allPass_forM_seq3 {α β γ : Type} (xs : List α) (ys : List β) (zs : List γ)
    (f : α → Core.AllPassRun Unit) (g : β → Core.AllPassRun Unit) (h : γ → Core.AllPassRun Unit)
    (hf : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post)
    (hg : ∀ y ∈ ys, ∀ post : Unit → Prop, post () → g y post)
    (hh : ∀ z ∈ zs, ∀ post : Unit → Prop, post () → h z post) :
    Core.AllPass (do xs.forM f; ys.forM g; zs.forM h) :=
  allPass_forM xs f hf
    (fun _ => ys.forM g (fun _ => zs.forM h (fun _ => True)))
    (allPass_forM ys g hg (fun _ => zs.forM h (fun _ => True)) (allPass_forM_top zs h hh))

private theorem canReach_forM_seq3 {α β γ : Type} (xs : List α) (ys : List β) (zs : List γ)
    (f : α → Core.CanReachRun Unit) (g : β → Core.CanReachRun Unit) (h : γ → Core.CanReachRun Unit)
    (hf : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post)
    (hg : ∀ y ∈ ys, ∀ post : Unit → Prop, post () → g y post)
    (hh : ∀ z ∈ zs, ∀ post : Unit → Prop, post () → h z post) :
    Core.CanReach (do xs.forM f; ys.forM g; zs.forM h) :=
  canReach_forM xs f hf
    (fun _ => ys.forM g (fun _ => zs.forM h (fun _ => True)))
    (canReach_forM ys g hg (fun _ => zs.forM h (fun _ => True)) (canReach_forM_top zs h hh))

section
attribute [local irreducible] parseWithNum

/-- Prove `test_toml_keysAndProvenance_conformsToSpec` for `makeTomlApi numApi`. -/
theorem allPass_keysAndProvenance (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.AllPass (test_toml_keysAndProvenance_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [test_toml_keysAndProvenance_conformsToSpec]
  exact allPass_forM_seq keyProvenanceOkCases keyProvenanceErrCases
    (checkParseEquiv (makeTomlApi numApi)) (checkParseErrorKind (makeTomlApi numApi))
    (checkParseEquiv_allPass numApi hnum keyProvenanceOkCases keyProvenanceOk_model_valid)
    (checkParseErrorKind_allPass numApi hnum keyProvenanceErrCases keyProvenanceErr_model_valid)

/-- Witness `CanReach` for `test_toml_keysAndProvenance_conformsToSpec`. -/
theorem canReach_keysAndProvenance (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.CanReach (test_toml_keysAndProvenance_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [test_toml_keysAndProvenance_conformsToSpec]
  exact canReach_forM_seq keyProvenanceOkCases keyProvenanceErrCases
    (checkParseEquiv (makeTomlApi numApi)) (checkParseErrorKind (makeTomlApi numApi))
    (checkParseEquiv_canReach numApi hnum keyProvenanceOkCases keyProvenanceOk_model_valid)
    (checkParseErrorKind_canReach numApi hnum keyProvenanceErrCases keyProvenanceErr_model_valid)

/-- Prove `test_toml_inlineTablesAndAot_conformsToSpec` for `makeTomlApi numApi`. -/
theorem allPass_inlineTablesAndAot (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.AllPass (test_toml_inlineTablesAndAot_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [test_toml_inlineTablesAndAot_conformsToSpec]
  exact allPass_forM_seq inlineAotOkCases inlineAotErrCases
    (checkParseEquiv (makeTomlApi numApi)) (checkParseErrorKind (makeTomlApi numApi))
    (checkParseEquiv_allPass numApi hnum inlineAotOkCases inlineAotOk_model_valid)
    (checkParseErrorKind_allPass numApi hnum inlineAotErrCases inlineAotErr_model_valid)

/-- Witness `CanReach` for `test_toml_inlineTablesAndAot_conformsToSpec`. -/
theorem canReach_inlineTablesAndAot (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.CanReach (test_toml_inlineTablesAndAot_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [test_toml_inlineTablesAndAot_conformsToSpec]
  exact canReach_forM_seq inlineAotOkCases inlineAotErrCases
    (checkParseEquiv (makeTomlApi numApi)) (checkParseErrorKind (makeTomlApi numApi))
    (checkParseEquiv_canReach numApi hnum inlineAotOkCases inlineAotOk_model_valid)
    (checkParseErrorKind_canReach numApi hnum inlineAotErrCases inlineAotErr_model_valid)

/-- Prove `test_toml_stringsAndControls_conformsToSpec` for `makeTomlApi numApi`. -/
theorem allPass_stringsAndControls (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.AllPass (test_toml_stringsAndControls_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [test_toml_stringsAndControls_conformsToSpec]
  exact allPass_forM_seq stringOkCases stringErrCases
    (checkParseEquiv (makeTomlApi numApi)) (checkParseErrorKind (makeTomlApi numApi))
    (checkParseEquiv_allPass numApi hnum stringOkCases stringOk_model_valid)
    (checkParseErrorKind_allPass numApi hnum stringErrCases stringErr_model_valid)

/-- Witness `CanReach` for `test_toml_stringsAndControls_conformsToSpec`. -/
theorem canReach_stringsAndControls (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.CanReach (test_toml_stringsAndControls_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [test_toml_stringsAndControls_conformsToSpec]
  exact canReach_forM_seq stringOkCases stringErrCases
    (checkParseEquiv (makeTomlApi numApi)) (checkParseErrorKind (makeTomlApi numApi))
    (checkParseEquiv_canReach numApi hnum stringOkCases stringOk_model_valid)
    (checkParseErrorKind_canReach numApi hnum stringErrCases stringErr_model_valid)

/-- Prove `test_toml_numbersAndDatetimes_conformsToSpec` for `makeTomlApi numApi`. -/
theorem allPass_numbersAndDatetimes (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.AllPass (test_toml_numbersAndDatetimes_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [test_toml_numbersAndDatetimes_conformsToSpec]
  exact allPass_forM_seq3 numberDatetimeOkCases floatBitCases numberDatetimeErrCases
    (checkParseEquiv (makeTomlApi numApi)) (checkParseFloatBits (makeTomlApi numApi))
    (checkParseErrorKind (makeTomlApi numApi))
    (checkParseEquiv_allPass numApi hnum numberDatetimeOkCases numberDatetimeOk_model_valid)
    (checkParseFloatBits_allPass numApi hnum)
    (checkParseErrorKind_allPass numApi hnum numberDatetimeErrCases numberDatetimeErr_model_valid)

/-- Witness `CanReach` for `test_toml_numbersAndDatetimes_conformsToSpec`. -/
theorem canReach_numbersAndDatetimes (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.CanReach (test_toml_numbersAndDatetimes_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [test_toml_numbersAndDatetimes_conformsToSpec]
  exact canReach_forM_seq3 numberDatetimeOkCases floatBitCases numberDatetimeErrCases
    (checkParseEquiv (makeTomlApi numApi)) (checkParseFloatBits (makeTomlApi numApi))
    (checkParseErrorKind (makeTomlApi numApi))
    (checkParseEquiv_canReach numApi hnum numberDatetimeOkCases numberDatetimeOk_model_valid)
    (checkParseFloatBits_canReach numApi hnum)
    (checkParseErrorKind_canReach numApi hnum numberDatetimeErrCases numberDatetimeErr_model_valid)

private theorem validNumApi_parseInt64 (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (tok : String) (n : Int64) (h : parseInt64Model tok = .ok n) :
    numApi.parseInt64 tok = .ok n := by
  have href := parseInt64_refines numApi hnum tok
  rw [h] at href
  cases ha : numApi.parseInt64 tok with
  | error e => rw [ha] at href; cases href
  | ok n2 => rw [ha] at href; dsimp only at href; subst href; rfl

private theorem validNumApi_parseFloat (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (tok : String) (f : Float) (h : parseFloatModel tok = .ok f) :
    ∃ g, numApi.parseFloat tok = .ok g ∧ FloatBitMatch f g := by
  have href := parseFloat_refines numApi hnum tok
  rw [h] at href
  cases ha : numApi.parseFloat tok with
  | error e => rw [ha] at href; cases href
  | ok g => rw [ha] at href; exact ⟨g, rfl, href⟩

private theorem validNumApi_isValidIntLex (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (n : Int64) :
    isValidIntLex (numApi.formatInt n.toInt) n = true := by
  let s := numApi.formatInt n.toInt
  have hbounds : inInt64Range n.toInt = true := by
    have h1 : (-2 ^ 63 : Int) ≤ n.toInt := Int64.le_toInt n
    have h2 : n.toInt ≤ Int64.maxValue.toInt := Int64.toInt_le n
    have hmax : Int64.maxValue.toInt = 9223372036854775807 := by decide
    rw [inInt64Range, decide_eq_true_eq]
    simp only [int64MinInt, int64MaxInt]
    omega
  have hfmt := hnum.formatInt n.toInt
  dsimp only [test_numparse_formatInt_roundTrip, Core.NondetTest.nondet, NondetTest.assert,
    bind, pure] at hfmt
  simp only [hbounds, ↓reduceIte, Int64.ofInt_toInt] at hfmt
  have hapi64 : numApi.parseInt64 s = .ok n := hfmt.2.2.2.1
  have hp64 : parseInt64Model s = .ok n := by
    have href := parseInt64_refines numApi hnum s
    rw [hapi64] at href
    cases hm : parseInt64Model s with
    | error k => rw [hm] at href; cases href
    | ok m => rw [hm] at href; dsimp only at href; subst href; rfl
  have honly : ∀ c ∈ s.toList, c = '-' ∨ isAsciiDigit c = true := by
    intro c hc
    have hc' := List.all_eq_true.mp (hnum.formatIntChars n.toInt) c hc
    simp only [Bool.or_eq_true, beq_iff_eq] at hc'
    exact hc'.symm
  have hclean : (s.toList.all fun c =>
      !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' &&
      c != '.' && !isDisallowedControl c) = true := by
    rw [List.all_eq_true]
    intro c hc
    rcases honly c hc with rfl | hcd
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
  have hnot_sw : ∀ p : String, ∀ c : Char, c ∈ p.toList →
      (c = 'X' ∨ c = 'O' ∨ c = 'B') → s.startsWith p = false := by
    intro p c hc_mem hc_up
    rw [Bool.eq_false_iff]
    intro hsw
    rw [String.startsWith_string_iff] at hsw
    rcases hsw with ⟨t, ht⟩
    have hmem : c ∈ s.toList := by
      rw [← ht]
      exact List.mem_append_left t hc_mem
    rcases honly c hmem with rfl | hdig
    · rcases hc_up with h | h | h <;> cases h
    · rcases hc_up with rfl | rfl | rfl <;> revert hdig <;> decide
  have hno_upper : (s.startsWith "0X" || s.startsWith "0O" || s.startsWith "0B" ||
      s.startsWith "+0X" || s.startsWith "+0O" || s.startsWith "+0B" ||
      s.startsWith "-0X" || s.startsWith "-0O" || s.startsWith "-0B") = false := by
    simp only [Bool.or_eq_false_iff]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨hnot_sw "0X" 'X' (by decide) (by decide),
      hnot_sw "0O" 'O' (by decide) (by decide)⟩,
      hnot_sw "0B" 'B' (by decide) (by decide)⟩,
      hnot_sw "+0X" 'X' (by decide) (by decide)⟩,
      hnot_sw "+0O" 'O' (by decide) (by decide)⟩,
      hnot_sw "+0B" 'B' (by decide) (by decide)⟩,
      hnot_sw "-0X" 'X' (by decide) (by decide)⟩,
      hnot_sw "-0O" 'O' (by decide) (by decide)⟩,
      hnot_sw "-0B" 'B' (by decide) (by decide)⟩
  have hno_exp : (!(s.contains 'e' || s.contains 'E')) = true := by
    have hne1 : 'e' ∉ s.toList := fun hm => by
      rcases honly 'e' hm with h | h
      · cases h
      · revert h; decide
    have hne2 : 'E' ∉ s.toList := fun hm => by
      rcases honly 'E' hm with h | h
      · cases h
      · revert h; decide
    have he1 : s.contains 'e' = false := by simp [String.contains, hne1]
    have he2 : s.contains 'E' = false := by simp [String.contains, hne2]
    simp [he1, he2]
  change isValidIntLex s n = true
  simp only [isValidIntLex, hp64, hclean, hno_upper, beq_self_eq_true, Bool.not_false,
    Bool.true_and, Bool.and_true]
  split
  · rfl
  · exact hno_exp

private theorem validNumApi_isValidFloatLex (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (f : Float) :
    isValidFloatLex (numApi.formatFloat f) f = true := by
  have hf := hnum.formatFloat f
  dsimp only [test_numparse_formatFloat_specAndRoundTrip, Core.NondetTest.nondet, NondetTest.assert,
    bind, pure] at hf
  exact floatFormatSpec_isValidFloatLex f (numApi.formatFloat f) hf.1

/-- Prove `test_toml_render_parse_roundTrip` for `makeTomlApi numApi`. -/
theorem allPass_render_parse_roundTrip (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.AllPass (test_toml_render_parse_roundTrip (makeTomlApi numApi)) := by
  dsimp only [test_toml_render_parse_roundTrip, Core.AllPass, Core.NondetTest.nondet,
    Core.NondetTest.assume, NondetTest.assert, bind, pure]
  intro pair
  cases hr : render pair.1 pair.2 with
  | none =>
    dsimp only
    intro hfalse
    exact False.elim hfalse
  | some txt =>
    dsimp only
    obtain ⟨parsed, hp, heqv⟩ := render_parse_roundTrip_model numApi
      (validNumApi_parseInt64 numApi hnum) (validNumApi_parseFloat numApi hnum)
      pair.1 pair.2 txt hr
    simp only [makeTomlApi, hp, heqv, and_self]

/-- Witness `CanReach` for `test_toml_render_parse_roundTrip`. -/
theorem canReach_render_parse_roundTrip (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.CanReach (test_toml_render_parse_roundTrip (makeTomlApi numApi)) := by
  dsimp only [test_toml_render_parse_roundTrip, Core.CanReach, Core.NondetTest.nondet,
    Core.NondetTest.assume, NondetTest.assert, bind, pure]
  have hrender : render #[] ⟨[], none⟩ = some "\n" := by
    simp [render, wellFormedTableBool, noDupKeysBool, wellFormedValueBool.wellFormedTableListBool,
      renderTablePlan, isPlanPermutation, noDupStringsBool, renderInlineEntries,
      renderSectionEntries, bind, Option.bind, String.intercalate_nil]
  obtain ⟨parsed, hp, heqv⟩ := render_parse_roundTrip_model numApi
    (validNumApi_parseInt64 numApi hnum) (validNumApi_parseFloat numApi hnum)
    #[] ⟨[], none⟩ "\n" hrender
  refine ⟨(#[] , ⟨[], none⟩), ?_⟩
  rw [hrender]
  simp only [makeTomlApi, hp, heqv, and_self]

/-- Prove `test_toml_format_validAndRoundTrip` for `makeTomlApi numApi`. -/
theorem allPass_format_validAndRoundTrip (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.AllPass (test_toml_format_validAndRoundTrip (makeTomlApi numApi)) := by
  dsimp only [test_toml_format_validAndRoundTrip, Core.AllPass, Core.NondetTest.nondet,
    Core.NondetTest.assume, NondetTest.assert, bind, pure]
  intro doc hwf
  obtain ⟨parsed, hp, heqv⟩ := formatWithNum_roundTrip_model numApi
    (validNumApi_parseInt64 numApi hnum) (validNumApi_parseFloat numApi hnum)
    (validNumApi_isValidIntLex numApi hnum) (validNumApi_isValidFloatLex numApi hnum)
    doc hwf
  simp only [makeTomlApi, hp, heqv, and_self]

/-- Witness `CanReach` for `test_toml_format_validAndRoundTrip`. -/
theorem canReach_format_validAndRoundTrip (numApi : NumParseApi) (hnum : ValidNumApi numApi) :
    Core.CanReach (test_toml_format_validAndRoundTrip (makeTomlApi numApi)) := by
  dsimp only [test_toml_format_validAndRoundTrip, Core.CanReach, Core.NondetTest.nondet,
    Core.NondetTest.assume, NondetTest.assert, bind, pure]
  have hwf : WellFormedTable #[] := rfl
  obtain ⟨parsed, hp, heqv⟩ := formatWithNum_roundTrip_model numApi
    (validNumApi_parseInt64 numApi hnum) (validNumApi_parseFloat numApi hnum)
    (validNumApi_isValidIntLex numApi hnum) (validNumApi_isValidFloatLex numApi hnum)
    #[] hwf
  refine ⟨#[], hwf, ?_⟩
  simp only [makeTomlApi, hp, heqv, and_self]

end

end LeanSwe.Toml.Proofs
