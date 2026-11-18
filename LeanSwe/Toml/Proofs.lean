import Core.NondetTest
import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.Toml.Interface
import LeanSwe.Toml.SpecTests
import LeanSwe.Toml.Proofs.Parametric
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.SpecTests
import LeanSwe.NumParse.Proofs

namespace LeanSwe.Toml.Proofs

open Core
open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl

private theorem natToDecCharsPos_digits (n : Nat) (acc : List Char)
    (hacc : acc.all (fun c => isAsciiDigit c || c == '-') = true) :
    (LeanSwe.NumParse.Internal.natToDecCharsPos n acc).all
      (fun c => isAsciiDigit c || c == '-') = true := by
  match n with
  | 0 =>
    unfold LeanSwe.NumParse.Internal.natToDecCharsPos
    exact hacc
  | m + 1 =>
    unfold LeanSwe.NumParse.Internal.natToDecCharsPos
    apply natToDecCharsPos_digits ((m + 1) / 10) _
    simp only [List.all_cons, hacc, Bool.and_true, Bool.or_eq_true]
    left
    have hlt : (m + 1) % 10 < 10 := Nat.mod_lt _ (by decide)
    match hrm : (m + 1) % 10 with
    | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
    | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
    | _ + 10 => omega
termination_by n

private theorem defaultNumApi_formatIntChars (n : Int) :
    (LeanSwe.NumParse.defaultApi.formatInt n).toList.all
      (fun c => isAsciiDigit c || c == '-') = true := by
  change (String.ofList (LeanSwe.NumParse.Internal.formatIntChars n)).toList.all
      (fun c => isAsciiDigit c || c == '-') = true
  rw [String.toList_ofList]
  cases n with
  | ofNat k =>
    cases k with
    | zero => decide
    | succ m =>
      unfold LeanSwe.NumParse.Internal.formatIntChars
      exact natToDecCharsPos_digits (m + 1) [] rfl
  | negSucc k =>
    unfold LeanSwe.NumParse.Internal.formatIntChars
    simp only [List.all_cons, (by decide : (isAsciiDigit '-' || '-' == '-') = true), Bool.true_and]
    exact natToDecCharsPos_digits (k + 1) [] rfl

/-- Concrete `ValidNumApi` witness for `LeanSwe.NumParse.defaultApi`. -/
theorem validNumApi_defaultApi : ValidNumApi LeanSwe.NumParse.defaultApi :=
  { onError := LeanSwe.NumParse.Proofs.proof_numparse_onError_returnsNonEmptyMessage
  , parseInt64 := LeanSwe.NumParse.Proofs.proof_numparse_parseInt64_matchesModel
  , parseFloat := LeanSwe.NumParse.Proofs.proof_numparse_parseFloat_matchesModel
  , formatInt := LeanSwe.NumParse.Proofs.proof_numparse_formatInt_roundTrip
  , formatFloat := LeanSwe.NumParse.Proofs.proof_numparse_formatFloat_specAndRoundTrip
  , formatIntChars := defaultNumApi_formatIntChars
  }

private theorem defaultApi_eq :
    LeanSwe.Toml.defaultApi = Impl.makeTomlApi LeanSwe.NumParse.defaultApi := rfl

section
attribute [local irreducible] Core.AllPass Core.CanReach

/-- Concrete `AllPass` proof of `test_toml_onError_returnsNonEmptyMessage` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_onError_returnsNonEmptyMessage :
    Core.AllPass (test_toml_onError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_onError LeanSwe.NumParse.defaultApi

/-- Concrete `CanReach` witness for `test_toml_onError_returnsNonEmptyMessage`. -/
theorem reach_toml_onError_returnsNonEmptyMessage :
    Core.CanReach (test_toml_onError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_onError LeanSwe.NumParse.defaultApi

/-- Concrete `AllPass` proof of `test_toml_accessorError_returnsNonEmptyMessage` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_accessorError_returnsNonEmptyMessage :
    Core.AllPass (test_toml_accessorError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_accessorError LeanSwe.NumParse.defaultApi

/-- Concrete `CanReach` witness for `test_toml_accessorError_returnsNonEmptyMessage`. -/
theorem reach_toml_accessorError_returnsNonEmptyMessage :
    Core.CanReach (test_toml_accessorError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_accessorError LeanSwe.NumParse.defaultApi

/-- Concrete `AllPass` proof of `test_toml_parse_returnsWellFormedTable` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_parse_returnsWellFormedTable :
    Core.AllPass (test_toml_parse_returnsWellFormedTable LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_parse_returnsWellFormedTable LeanSwe.NumParse.defaultApi

/-- Concrete `CanReach` witness for `test_toml_parse_returnsWellFormedTable`. -/
theorem reach_toml_parse_returnsWellFormedTable :
    Core.CanReach (test_toml_parse_returnsWellFormedTable LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_parse_returnsWellFormedTable LeanSwe.NumParse.defaultApi

/-- Concrete `AllPass` proof of `test_toml_render_parse_roundTrip` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_render_parse_roundTrip :
    Core.AllPass (test_toml_render_parse_roundTrip LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_render_parse_roundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_render_parse_roundTrip`. -/
theorem reach_toml_render_parse_roundTrip :
    Core.CanReach (test_toml_render_parse_roundTrip LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_render_parse_roundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_format_validAndRoundTrip` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_format_validAndRoundTrip :
    Core.AllPass (test_toml_format_validAndRoundTrip LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_format_validAndRoundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_format_validAndRoundTrip`. -/
theorem reach_toml_format_validAndRoundTrip :
    Core.CanReach (test_toml_format_validAndRoundTrip LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_format_validAndRoundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_keysAndProvenance_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_keysAndProvenance_conformsToSpec :
    Core.AllPass (test_toml_keysAndProvenance_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_keysAndProvenance LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_keysAndProvenance_conformsToSpec`. -/
theorem reach_toml_keysAndProvenance_conformsToSpec :
    Core.CanReach (test_toml_keysAndProvenance_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_keysAndProvenance LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_inlineTablesAndAot_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_inlineTablesAndAot_conformsToSpec :
    Core.AllPass (test_toml_inlineTablesAndAot_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_inlineTablesAndAot LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_inlineTablesAndAot_conformsToSpec`. -/
theorem reach_toml_inlineTablesAndAot_conformsToSpec :
    Core.CanReach (test_toml_inlineTablesAndAot_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_inlineTablesAndAot LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_stringsAndControls_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_stringsAndControls_conformsToSpec :
    Core.AllPass (test_toml_stringsAndControls_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_stringsAndControls LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_stringsAndControls_conformsToSpec`. -/
theorem reach_toml_stringsAndControls_conformsToSpec :
    Core.CanReach (test_toml_stringsAndControls_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_stringsAndControls LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_numbersAndDatetimes_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_numbersAndDatetimes_conformsToSpec :
    Core.AllPass (test_toml_numbersAndDatetimes_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_numbersAndDatetimes LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_numbersAndDatetimes_conformsToSpec`. -/
theorem reach_toml_numbersAndDatetimes_conformsToSpec :
    Core.CanReach (test_toml_numbersAndDatetimes_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_numbersAndDatetimes LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_codecsAndAccessors_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_codecsAndAccessors_conformsToSpec :
    Core.AllPass (test_toml_codecsAndAccessors_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_codecsAndAccessors LeanSwe.NumParse.defaultApi

/-- Concrete `CanReach` witness for `test_toml_codecsAndAccessors_conformsToSpec`. -/
theorem reach_toml_codecsAndAccessors_conformsToSpec :
    Core.CanReach (test_toml_codecsAndAccessors_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_codecsAndAccessors LeanSwe.NumParse.defaultApi

end

private def ValidParseErr (e : TomlError) : Prop :=
  e.kind ≠ .missingField ∧ e.kind ≠ .typeMismatch ∧ e.kind ≠ .decodeError

private theorem except_bind_valid {α β : Type} (x : Except TomlError α) (k : α → Except TomlError β)
    (hx : ∀ e, x = .error e → ValidParseErr e)
    (hk : ∀ a e, k a = .error e → ValidParseErr e) {e : TomlError}
    (h : (x >>= k) = .error e) : ValidParseErr e := by
  cases x with
  | error e1 => cases h; exact hx e rfl
  | ok a => exact hk a e h

private theorem list_len_rec {α : Type} {motive : List α → Prop}
    (step : ∀ xs, (∀ ys, ys.length < xs.length → motive ys) → motive xs) : ∀ xs, motive xs := by
  suffices ∀ n xs, xs.length ≤ n → motive xs from fun xs => this xs.length xs (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro xs h
    apply step
    intro ys hy
    omega
  | succ n ih =>
    intro xs h
    apply step
    intro ys hy
    exact ih ys (by omega)

private theorem nat_lt_rec {motive : Nat → Prop}
    (step : ∀ n, (∀ k, k < n → motive k) → motive n) : ∀ n, motive n := by
  suffices h : ∀ b n, n ≤ b → motive n from fun n => h n n (Nat.le_refl _)
  intro b
  induction b with
  | zero =>
    intro n hn
    apply step
    intro k hk
    omega
  | succ b ih =>
    intro n hn
    apply step
    intro k hk
    exact ih k (by omega)

private theorem normalizeChars_validErr (line col : Nat) (cs : List Char) :
    ∀ {e : TomlError}, normalizeChars line col cs = .error e → ValidParseErr e := by
  suffices h : ∀ cs : List Char, ∀ line col {e : TomlError},
      normalizeChars line col cs = .error e → ValidParseErr e from fun {e} => h cs line col
  refine list_len_rec (motive := fun cs => ∀ line col {e : TomlError},
      normalizeChars line col cs = .error e → ValidParseErr e) (fun cs ih => ?_)
  intro line col e h
  unfold normalizeChars at h
  repeat (first
    | (cases h <;> done)
    | (cases h <;> simp [ValidParseErr, mkErr] <;> done)
    | (apply except_bind_valid _ _ _ _ h
       · intro _ hx
         refine ih _ ?_ _ _ hx
         simp only [List.length_cons]
         omega
       · intro _ _ hk; cases hk)
    | split at h)

private theorem parseUnicodeHex_validErr (count : Nat) (cs : List Char) {e : TomlError}
    (h : parseUnicodeHex count cs = .error e) : ValidParseErr e := by
  unfold parseUnicodeHex at h
  repeat (first | (cases h <;> done) | (cases h <;> simp [ValidParseErr, mkErr] <;> done) | split at h)

private theorem parseBasicEscape_validErr (cs : List Char) {e : TomlError}
    (h : parseBasicEscape cs = .error e) : ValidParseErr e := by
  unfold parseBasicEscape at h
  repeat (first
    | (cases h <;> done)
    | (cases h <;> simp [ValidParseErr, mkErr] <;> done)
    | (exact parseUnicodeHex_validErr 4 _ h)
    | (exact parseUnicodeHex_validErr 8 _ h)
    | split at h)

private theorem parseBasicStringBodyFuel_validErr (fuel : Nat) (acc cs : List Char) :
    ∀ {e : TomlError}, parseBasicStringBodyFuel fuel acc cs = .error e → ValidParseErr e := by
  suffices h : ∀ fuel acc cs {e : TomlError},
      parseBasicStringBodyFuel fuel acc cs = .error e → ValidParseErr e from fun {e} => h fuel acc cs
  refine nat_lt_rec (motive := fun fuel => ∀ acc cs {e : TomlError},
      parseBasicStringBodyFuel fuel acc cs = .error e → ValidParseErr e) (fun fuel ih => ?_)
  intro acc cs e h
  unfold parseBasicStringBodyFuel at h
  repeat (first
    | (cases h <;> done)
    | (cases h <;> simp [ValidParseErr, mkErr] <;> done)
    | (apply except_bind_valid _ _ (fun _ hx => parseBasicEscape_validErr _ hx) _ h
       intro p _ hk
       refine ih _ ?_ _ _ hk
       omega)
    | (refine ih _ ?_ _ _ h; omega)
    | split at h)

private theorem parseBasicStringBody_validErr (cs : List Char) {e : TomlError}
    (h : parseBasicStringBody cs = .error e) : ValidParseErr e :=
  parseBasicStringBodyFuel_validErr (cs.length + 1) [] cs h

private theorem parseLiteralStringBody_validErr (acc cs : List Char) :
    ∀ {e : TomlError}, parseLiteralStringBody acc cs = .error e → ValidParseErr e := by
  suffices h : ∀ cs acc {e : TomlError},
      parseLiteralStringBody acc cs = .error e → ValidParseErr e from fun {e} => h cs acc
  refine list_len_rec (motive := fun cs => ∀ acc {e : TomlError},
      parseLiteralStringBody acc cs = .error e → ValidParseErr e) (fun cs ih => ?_)
  intro acc e h
  unfold parseLiteralStringBody at h
  repeat (first
    | (cases h <;> done)
    | (cases h <;> simp [ValidParseErr, mkErr] <;> done)
    | (refine ih _ ?_ _ h; simp only [List.length_cons]; omega)
    | split at h)

private theorem parseMultilineBasicBodyFuel_validErr (fuel : Nat) (acc cs : List Char) :
    ∀ {e : TomlError}, parseMultilineBasicBodyFuel fuel acc cs = .error e → ValidParseErr e := by
  suffices h : ∀ fuel acc cs {e : TomlError},
      parseMultilineBasicBodyFuel fuel acc cs = .error e → ValidParseErr e from fun {e} => h fuel acc cs
  refine nat_lt_rec (motive := fun fuel => ∀ acc cs {e : TomlError},
      parseMultilineBasicBodyFuel fuel acc cs = .error e → ValidParseErr e) (fun fuel ih => ?_)
  intro acc cs e h
  unfold parseMultilineBasicBodyFuel at h
  repeat (first
    | (cases h <;> done)
    | (cases h <;> (apply parseBasicEscape_validErr; assumption))
    | (cases h <;> simp [ValidParseErr, mkErr] <;> done)
    | (refine ih _ ?_ _ _ h; omega)
    | split at h)

private theorem parseMultilineBasicString_validErr (cs : List Char) {e : TomlError}
    (h : parseMultilineBasicString cs = .error e) : ValidParseErr e := by
  unfold parseMultilineBasicString at h
  exact parseMultilineBasicBodyFuel_validErr _ _ _ h

private theorem parseMultilineLiteralBodyFuel_validErr (fuel : Nat) (acc cs : List Char) :
    ∀ {e : TomlError}, parseMultilineLiteralBodyFuel fuel acc cs = .error e → ValidParseErr e := by
  suffices h : ∀ fuel acc cs {e : TomlError},
      parseMultilineLiteralBodyFuel fuel acc cs = .error e → ValidParseErr e from fun {e} => h fuel acc cs
  refine nat_lt_rec (motive := fun fuel => ∀ acc cs {e : TomlError},
      parseMultilineLiteralBodyFuel fuel acc cs = .error e → ValidParseErr e) (fun fuel ih => ?_)
  intro acc cs e h
  unfold parseMultilineLiteralBodyFuel at h
  repeat (first
    | (cases h <;> done)
    | (cases h <;> simp [ValidParseErr, mkErr] <;> done)
    | (refine ih _ ?_ _ _ h; omega)
    | split at h)

private theorem parseMultilineLiteralString_validErr (cs : List Char) {e : TomlError}
    (h : parseMultilineLiteralString cs = .error e) : ValidParseErr e := by
  unfold parseMultilineLiteralString at h
  exact parseMultilineLiteralBodyFuel_validErr _ _ _ h

private theorem parseKeySegment_validErr (cs : List Char) {e : TomlError}
    (h : parseKeySegment cs = .error e) : ValidParseErr e := by
  unfold parseKeySegment at h
  split at h
  · cases h; simp [ValidParseErr, mkErr]
  · cases h; simp [ValidParseErr, mkErr]
  · exact parseBasicStringBody_validErr _ h
  · exact parseLiteralStringBody_validErr _ _ h
  · dsimp only at h
    split at h
    · cases h; simp [ValidParseErr, mkErr]
    · cases h

private theorem parseDottedKeyFuel_validErr (fuel : Nat) (cs : List Char) :
    ∀ {e : TomlError}, parseDottedKeyFuel fuel cs = .error e → ValidParseErr e := by
  induction fuel generalizing cs with
  | zero => intro e h; cases h; simp [ValidParseErr, mkErr]
  | succ f ih =>
    intro e h
    unfold parseDottedKeyFuel at h
    exact except_bind_valid _ _ (fun _ hx => parseKeySegment_validErr cs hx)
      (fun p _ hk => by
        dsimp only at hk
        split at hk
        · exact except_bind_valid _ _ (fun _ hy => ih _ hy)
            (fun _ _ hz => by cases hz) hk
        · cases hk) h

private theorem parseDottedKey_validErr (cs : List Char) {e : TomlError}
    (h : parseDottedKey cs = .error e) : ValidParseErr e :=
  parseDottedKeyFuel_validErr (cs.length + 1) cs h

private theorem parseDatePart_validErr (cs : List Char) {e : TomlError}
    (h : parseDatePart cs = .error e) : ValidParseErr e := by
  unfold parseDatePart at h
  repeat (first | (cases h <;> done) | (cases h <;> simp [ValidParseErr, mkErr] <;> done) | split at h)

private theorem parseTimePart_validErr (cs : List Char) {e : TomlError}
    (h : parseTimePart cs = .error e) : ValidParseErr e := by
  unfold parseTimePart at h
  try dsimp only at h
  repeat (first | (cases h <;> done) | (cases h <;> simp [ValidParseErr, mkErr] <;> done) | split at h)

private theorem parseOffsetPart_validErr (cs : List Char) {e : TomlError}
    (h : parseOffsetPart cs = .error e) : ValidParseErr e := by
  unfold parseOffsetPart at h
  try dsimp only at h
  repeat (first | (cases h <;> done) | (cases h <;> simp [ValidParseErr, mkErr] <;> done) | split at h)

private theorem parseDateTimeToken_validErr (tok : String) {e : TomlError}
    (h : parseDateTimeToken tok = some (.error e)) : ValidParseErr e := by
  unfold parseDateTimeToken at h
  dsimp only at h
  split at h
  · cases hd : parseDatePart tok.toList with
    | error e1 =>
      rw [hd] at h
      cases h
      exact parseDatePart_validErr tok.toList hd
    | ok res =>
      rcases res with ⟨date, tail⟩
      rw [hd] at h
      cases tail with
      | nil => cases h
      | cons sep timeCs =>
        try dsimp only at h
        split at h
        · cases ht : parseTimePart timeCs with
          | error e1 =>
            rw [ht] at h
            cases h
            exact parseTimePart_validErr timeCs ht
          | ok res2 =>
            rcases res2 with ⟨tm, offCs⟩
            rw [ht] at h
            cases offCs with
            | nil => cases h
            | cons c cs2 =>
              try dsimp only at h
              cases ho : parseOffsetPart (c :: cs2) with
              | error e1 =>
                rw [ho] at h
                cases h
                exact parseOffsetPart_validErr _ ho
              | ok _ => rw [ho] at h; cases h
        · cases h; simp [ValidParseErr, mkErr]
  · split at h
    · cases ht : parseTimePart tok.toList with
      | error e1 =>
        rw [ht] at h
        cases h
        exact parseTimePart_validErr tok.toList ht
      | ok res =>
        rcases res with ⟨tm, tail⟩
        rw [ht] at h
        cases tail with
        | nil => cases h
        | cons _ _ => cases h; simp [ValidParseErr, mkErr]
    · split at h
      · cases h; simp [ValidParseErr, mkErr]
      · cases h

private theorem mapNumParseErr_validErr (ne : LeanSwe.NumParse.NumParseError) :
    ValidParseErr (mapNumParseErr ne) := by
  unfold mapNumParseErr
  dsimp only
  split <;> simp [ValidParseErr, mkErr]

private theorem classifyScalarToken_validErr (numApi : LeanSwe.NumParse.NumParseApi) (tok : String) {e : TomlError}
    (h : classifyScalarToken numApi tok = .error e) : ValidParseErr e := by
  unfold classifyScalarToken at h
  split at h
  · cases h; simp [ValidParseErr, mkErr]
  · split at h
    · cases h
    · split at h
      · cases h
      · cases hdt : parseDateTimeToken tok with
        | some r =>
          rw [hdt] at h
          cases r with
          | error e1 => cases h; exact parseDateTimeToken_validErr tok hdt
          | ok _ => cases h
        | none =>
          rw [hdt] at h
          dsimp only at h
          split at h
          · cases hf : numApi.parseFloat tok with
            | ok _ => rw [hf] at h; cases h
            | error ne => rw [hf] at h; cases h; exact mapNumParseErr_validErr ne
          · split at h
            · cases h; simp [ValidParseErr, mkErr]
            · cases hi : numApi.parseInt64 tok with
              | ok _ => rw [hi] at h; cases h
              | error ne => rw [hi] at h; cases h; exact mapNumParseErr_validErr ne

private theorem insertDottedEntries_validErr (fullPath : List String)
    (entries : List (String × Node)) (path : List String) (newNode : Node) :
    ∀ {e : TomlError}, insertDottedEntries fullPath entries path newNode = .error e → ValidParseErr e := by
  induction path generalizing entries with
  | nil => intro e h; cases h; simp [ValidParseErr, mkErr]
  | cons k rest ih =>
    intro e h
    cases rest with
    | nil =>
      unfold insertDottedEntries at h
      cases hl : assocLookupNode k entries <;> rw [hl] at h
      · cases h
      · rename_i nd
        cases nd with
        | table tk _ => cases tk <;> cases h <;> simp [ValidParseErr, mkErr]
        | leaf _ | aot _ => cases h; simp [ValidParseErr, mkErr]
    | cons k2 rest2 =>
      unfold insertDottedEntries at h
      cases hl : assocLookupNode k entries <;> rw [hl] at h
      · exact except_bind_valid _ _ (fun _ hx => ih [] hx) (fun _ _ hk => by cases hk) h
      · rename_i nd
        cases nd with
        | table tk sub =>
          cases tk with
          | inline | explicit => cases h; simp [ValidParseErr, mkErr]
          | subtableImplicit | dotted =>
            exact except_bind_valid _ _ (fun _ hx => ih sub hx) (fun _ _ hk => by cases hk) h
        | leaf v => cases v <;> cases h <;> simp [ValidParseErr, mkErr]
        | aot _ => cases h; simp [ValidParseErr, mkErr]

private theorem parseMut_validErr (numApi : LeanSwe.NumParse.NumParseApi) (fuel : Nat) :
    (∀ cs {e : TomlError}, parseValueFuel numApi fuel cs = .error e → ValidParseErr e) ∧
    (∀ cs acc {e : TomlError}, parseArrayFuel numApi fuel cs acc = .error e → ValidParseErr e) ∧
    (∀ cs entries {e : TomlError}, parseInlineTableFuel numApi fuel cs entries = .error e → ValidParseErr e) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro cs e h; cases h; simp [ValidParseErr, mkErr]
    · intro cs acc e h; cases h; simp [ValidParseErr, mkErr]
    · intro cs entries e h; cases h; simp [ValidParseErr, mkErr]
  | succ f ih =>
    rcases ih with ⟨ihVal, ihArr, ihTab⟩
    refine ⟨?_, ?_, ?_⟩
    · intro cs e h
      unfold parseValueFuel at h
      split at h
      · exact except_bind_valid _ _ (fun _ hx => parseMultilineBasicString_validErr _ hx)
          (fun _ _ hk => by cases hk) h
      · exact except_bind_valid _ _ (fun _ hx => parseBasicStringBody_validErr _ hx)
          (fun _ _ hk => by cases hk) h
      · exact except_bind_valid _ _ (fun _ hx => parseMultilineLiteralString_validErr _ hx)
          (fun _ _ hk => by cases hk) h
      · exact except_bind_valid _ _ (fun _ hx => parseLiteralStringBody_validErr _ _ hx)
          (fun _ _ hk => by cases hk) h
      · exact ihArr _ [] h
      · split at h
        · cases h
        · exact ihTab _ [] h
      · dsimp only at h
        exact except_bind_valid _ _ (fun _ hx => classifyScalarToken_validErr numApi _ hx)
          (fun _ _ hk => by cases hk) h
    · intro cs acc e h
      unfold parseArrayFuel at h
      split at h
      · cases h
      · cases h; simp [ValidParseErr, mkErr]
      · exact except_bind_valid _ _ (fun _ hx => ihVal _ hx)
          (fun v _ hk => by
            dsimp only at hk
            split at hk
            · exact ihArr _ _ hk
            · cases hk
            · cases hk; simp [ValidParseErr, mkErr]) h
    · intro cs entries e h
      unfold parseInlineTableFuel at h
      exact except_bind_valid _ _ (fun _ hx => parseDottedKey_validErr _ hx)
        (fun p1 _ hk => by
          dsimp only at hk
          split at hk
          · exact except_bind_valid _ _ (fun _ hy => ihVal _ hy)
              (fun p2 _ hl => except_bind_valid _ _
                (fun _ hz => insertDottedEntries_validErr _ entries _ _ hz)
                (fun nextEntries _ hm => by
                  split at hm
                  · split at hm
                    · cases hm; simp [ValidParseErr, mkErr]
                    · exact ihTab _ _ hm
                  · cases hm
                  · cases hm; simp [ValidParseErr, mkErr]) hl) hk
          · cases hk; simp [ValidParseErr, mkErr]) h

private theorem parseValue_validErr (numApi : LeanSwe.NumParse.NumParseApi) (cs : List Char) {e : TomlError}
    (h : parseValue numApi cs = .error e) : ValidParseErr e := by
  unfold parseValue at h
  exact (parseMut_validErr numApi _).1 cs h

private theorem mapLastAot_validErr (f : List (String × Node) → Except TomlError (List (String × Node)))
    (hf : ∀ xs {e : TomlError}, f xs = .error e → ValidParseErr e)
    (elems : List (List (String × Node))) :
    ∀ {e : TomlError}, mapLastAot f elems = .error e → ValidParseErr e := by
  induction elems with
  | nil => intro e h; cases h; simp [ValidParseErr, mkErr]
  | cons hd tl ih =>
    intro e h
    cases tl with
    | nil =>
      unfold mapLastAot at h
      exact except_bind_valid _ _ (fun _ hx => hf hd hx) (fun _ _ hk => by cases hk) h
    | cons hd2 tl2 =>
      unfold mapLastAot at h
      exact except_bind_valid _ _ (fun _ hx => ih hx) (fun _ _ hk => by cases hk) h

private theorem applyTableHeader_validErr (fullPath : List String)
    (entries : List (String × Node)) (path : List String) :
    ∀ {e : TomlError}, applyTableHeader fullPath entries path = .error e → ValidParseErr e := by
  induction path generalizing entries with
  | nil => intro e h; cases h; simp [ValidParseErr, mkErr]
  | cons k rest ih =>
    intro e h
    cases rest with
    | nil =>
      unfold applyTableHeader at h
      cases hl : assocLookupNode k entries <;> rw [hl] at h
      · cases h
      · rename_i nd
        cases nd with
        | table tk _ => cases tk <;> cases h <;> simp [ValidParseErr, mkErr]
        | leaf v => cases v <;> cases h <;> simp [ValidParseErr, mkErr]
        | aot _ => cases h; simp [ValidParseErr, mkErr]
    | cons k2 rest2 =>
      unfold applyTableHeader at h
      cases hl : assocLookupNode k entries <;> rw [hl] at h
      · exact except_bind_valid _ _ (fun _ hx => ih [] hx) (fun _ _ hk => by cases hk) h
      · rename_i nd
        cases nd with
        | table tk sub =>
          cases tk with
          | inline => cases h; simp [ValidParseErr, mkErr]
          | explicit | subtableImplicit | dotted =>
            exact except_bind_valid _ _ (fun _ hx => ih sub hx) (fun _ _ hk => by cases hk) h
        | aot elems =>
          exact except_bind_valid _ _
            (fun _ hx => mapLastAot_validErr _ (fun elem _ hy => ih elem hy) elems hx)
            (fun _ _ hk => by cases hk) h
        | leaf v => cases v <;> cases h <;> simp [ValidParseErr, mkErr]

private theorem applyAotHeader_validErr (fullPath : List String)
    (entries : List (String × Node)) (path : List String) :
    ∀ {e : TomlError}, applyAotHeader fullPath entries path = .error e → ValidParseErr e := by
  induction path generalizing entries with
  | nil => intro e h; cases h; simp [ValidParseErr, mkErr]
  | cons k rest ih =>
    intro e h
    cases rest with
    | nil =>
      unfold applyAotHeader at h
      cases hl : assocLookupNode k entries <;> rw [hl] at h
      · cases h
      · rename_i nd
        cases nd with
        | aot _ => cases h
        | table tk _ => cases tk <;> cases h <;> simp [ValidParseErr, mkErr]
        | leaf v => cases v <;> cases h <;> simp [ValidParseErr, mkErr]
    | cons k2 rest2 =>
      unfold applyAotHeader at h
      cases hl : assocLookupNode k entries <;> rw [hl] at h
      · exact except_bind_valid _ _ (fun _ hx => ih [] hx) (fun _ _ hk => by cases hk) h
      · rename_i nd
        cases nd with
        | table tk sub =>
          cases tk with
          | inline => cases h; simp [ValidParseErr, mkErr]
          | explicit | subtableImplicit | dotted =>
            exact except_bind_valid _ _ (fun _ hx => ih sub hx) (fun _ _ hk => by cases hk) h
        | aot elems =>
          exact except_bind_valid _ _
            (fun _ hx => mapLastAot_validErr _ (fun elem _ hy => ih elem hy) elems hx)
            (fun _ _ hk => by cases hk) h
        | leaf v => cases v <;> cases h <;> simp [ValidParseErr, mkErr]

private theorem insertAtActivePath_validErr (fullPath : List String)
    (entries : List (String × Node)) (activePath relPath : List String) (valNode : Node) :
    ∀ {e : TomlError}, insertAtActivePath fullPath entries activePath relPath valNode = .error e → ValidParseErr e := by
  induction activePath generalizing entries with
  | nil => intro e h; exact insertDottedEntries_validErr fullPath entries relPath valNode h
  | cons k rest ih =>
    intro e h
    unfold insertAtActivePath at h
    cases hl : assocLookupNode k entries <;> rw [hl] at h
    · cases h; simp [ValidParseErr, mkErr]
    · rename_i nd
      cases nd with
      | table tk sub =>
        exact except_bind_valid _ _ (fun _ hx => ih sub hx) (fun _ _ hk => by cases hk) h
      | aot elems =>
        exact except_bind_valid _ _
          (fun _ hx => mapLastAot_validErr _ (fun elem _ hy => ih elem hy) elems hx)
          (fun _ _ hk => by cases hk) h
      | leaf _ => cases h; simp [ValidParseErr, mkErr]

private theorem consumeStatementEnd_validErr (cs : List Char) {e : TomlError}
    (h : consumeStatementEnd cs = .error e) : ValidParseErr e := by
  unfold consumeStatementEnd at h
  split at h
  · cases h
  · cases h
  · cases h; simp [ValidParseErr, mkErr]

private theorem parseDocumentFuel_validErr (numApi : LeanSwe.NumParse.NumParseApi) (fuel : Nat)
    (cs : List Char) (activePath : List String) (root : List (String × Node)) :
    ∀ {e : TomlError}, parseDocumentFuel numApi fuel cs activePath root = .error e → ValidParseErr e := by
  induction fuel generalizing cs activePath root with
  | zero =>
    intro e h
    unfold parseDocumentFuel at h
    split at h
    · cases h
    · cases h; simp [ValidParseErr, mkErr]
  | succ f ih =>
    intro e h
    unfold parseDocumentFuel at h
    split at h
    · cases h
    · exact except_bind_valid _ _ (fun _ hx => parseDottedKey_validErr _ hx)
        (fun p1 _ hk => by
          dsimp only at hk
          split at hk
          · exact except_bind_valid _ _ (fun _ hy => consumeStatementEnd_validErr _ hy)
              (fun nextCs _ hl => except_bind_valid _ _
                (fun _ hz => applyAotHeader_validErr _ root _ hz)
                (fun nextRoot _ hm => ih nextCs _ nextRoot hm) hl) hk
          · cases hk; simp [ValidParseErr, mkErr]) h
    · exact except_bind_valid _ _ (fun _ hx => parseDottedKey_validErr _ hx)
        (fun p1 _ hk => by
          dsimp only at hk
          split at hk
          · exact except_bind_valid _ _ (fun _ hy => consumeStatementEnd_validErr _ hy)
              (fun nextCs _ hl => except_bind_valid _ _
                (fun _ hz => applyTableHeader_validErr _ root _ hz)
                (fun nextRoot _ hm => ih nextCs _ nextRoot hm) hl) hk
          · cases hk; simp [ValidParseErr, mkErr]) h
    · exact except_bind_valid _ _ (fun _ hx => parseDottedKey_validErr _ hx)
        (fun p1 _ hk => by
          dsimp only at hk
          split at hk
          · exact except_bind_valid _ _ (fun _ hy => parseValue_validErr numApi _ hy)
              (fun p2 _ hl => except_bind_valid _ _ (fun _ hz => consumeStatementEnd_validErr _ hz)
                (fun nextCs _ hm => except_bind_valid _ _
                  (fun _ hw => insertAtActivePath_validErr _ root activePath _ _ hw)
                  (fun nextRoot _ hn => ih nextCs activePath nextRoot hn) hm) hl) hk
          · cases hk; simp [ValidParseErr, mkErr]) h

private theorem parseWithNum_validErr (numApi : LeanSwe.NumParse.NumParseApi) (input : String) {e : TomlError}
    (h : parseWithNum numApi input = .error e) : ValidParseErr e := by
  unfold parseWithNum at h
  exact except_bind_valid _ _ (fun _ hx => normalizeChars_validErr 1 1 input.toList hx)
    (fun norm _ hk => except_bind_valid _ _
      (fun _ hy => parseDocumentFuel_validErr numApi (norm.length + 1) norm [] [] hy)
      (fun _ _ hz => by cases hz) hk) h

private theorem parse_never_of (k : TomlErrorKind)
    (hk : k = .missingField ∨ k = .typeMismatch ∨ k = .decodeError) (raw : String) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.parse raw) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.parse
  cases hp : parseWithNum LeanSwe.NumParse.defaultApi raw with
  | ok _ => trivial
  | error e =>
    dsimp only
    intro hek
    have hv := parseWithNum_validErr LeanSwe.NumParse.defaultApi raw hp
    unfold ValidParseErr at hv
    rw [hek] at hv
    rcases hk with rfl | rfl | rfl
    · exact hv.1 rfl
    · exact hv.2.1 rfl
    · exact hv.2.2 rfl

/-- `Toml.parse` never returns `.missingField`. -/
theorem toml_parse_never_missingField (raw : String) :
    Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.parse raw) :=
  parse_never_of .missingField (Or.inl rfl) raw

/-- `Toml.parse` never returns `.typeMismatch`. -/
theorem toml_parse_never_typeMismatch (raw : String) :
    Core.NeverErrorKindPure TomlError.kind .typeMismatch (LeanSwe.Toml.parse raw) :=
  parse_never_of .typeMismatch (Or.inr (Or.inl rfl)) raw

/-- `Toml.parse` never returns `.decodeError`. -/
theorem toml_parse_never_decodeError (raw : String) :
    Core.NeverErrorKindPure TomlError.kind .decodeError (LeanSwe.Toml.parse raw) :=
  parse_never_of .decodeError (Or.inr (Or.inr rfl)) raw

private theorem decode_never_of (k : TomlErrorKind) (hk : k ≠ .decodeError)
    (α : Type) [FromToml α] (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.decode (α := α) v) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.decode tomlDecode
  cases (FromToml.fromToml v : Except TomlError α) with
  | ok _ => trivial
  | error _ => dsimp only; exact hk.symm

/-- `Toml.decode` never returns `.parseError`. -/
theorem toml_decode_never_parseError (α : Type) [FromToml α] (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.decode (α := α) v) :=
  decode_never_of .parseError (by decide) α v

/-- `Toml.decode` never returns `.duplicateKey`. -/
theorem toml_decode_never_duplicateKey (α : Type) [FromToml α] (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.decode (α := α) v) :=
  decode_never_of .duplicateKey (by decide) α v

/-- `Toml.decode` never returns `.redefinedTable`. -/
theorem toml_decode_never_redefinedTable (α : Type) [FromToml α] (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.decode (α := α) v) :=
  decode_never_of .redefinedTable (by decide) α v

/-- `Toml.decode` never returns `.immutableInlineTable`. -/
theorem toml_decode_never_immutableInlineTable (α : Type) [FromToml α] (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.decode (α := α) v) :=
  decode_never_of .immutableInlineTable (by decide) α v

/-- `Toml.decode` never returns `.invalidUtf8OrControl`. -/
theorem toml_decode_never_invalidUtf8OrControl (α : Type) [FromToml α] (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.decode (α := α) v) :=
  decode_never_of .invalidUtf8OrControl (by decide) α v

/-- `Toml.decode` never returns `.numericOverflow`. -/
theorem toml_decode_never_numericOverflow (α : Type) [FromToml α] (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.decode (α := α) v) :=
  decode_never_of .numericOverflow (by decide) α v

/-- `Toml.decode` never returns `.missingField`. -/
theorem toml_decode_never_missingField (α : Type) [FromToml α] (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.decode (α := α) v) :=
  decode_never_of .missingField (by decide) α v

/-- `Toml.decode` never returns `.typeMismatch`. -/
theorem toml_decode_never_typeMismatch (α : Type) [FromToml α] (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .typeMismatch (LeanSwe.Toml.decode (α := α) v) :=
  decode_never_of .typeMismatch (by decide) α v

private theorem getTable_never_of (k : TomlErrorKind) (hk : k ≠ .typeMismatch) (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.getTable v) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.getTable tomlGetTable
  cases v with
  | table _ => trivial
  | string _ | int _ | float _ | bool _ | localDate _ | localTime _ | localDateTime _ | offsetDateTime _ | array _ =>
    dsimp only [mkErr]; exact hk.symm

/-- `Toml.getTable` never returns `.parseError`. -/
theorem toml_getTable_never_parseError (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getTable v) :=
  getTable_never_of .parseError (by decide) v

/-- `Toml.getTable` never returns `.duplicateKey`. -/
theorem toml_getTable_never_duplicateKey (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getTable v) :=
  getTable_never_of .duplicateKey (by decide) v

/-- `Toml.getTable` never returns `.redefinedTable`. -/
theorem toml_getTable_never_redefinedTable (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getTable v) :=
  getTable_never_of .redefinedTable (by decide) v

/-- `Toml.getTable` never returns `.immutableInlineTable`. -/
theorem toml_getTable_never_immutableInlineTable (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getTable v) :=
  getTable_never_of .immutableInlineTable (by decide) v

/-- `Toml.getTable` never returns `.invalidUtf8OrControl`. -/
theorem toml_getTable_never_invalidUtf8OrControl (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getTable v) :=
  getTable_never_of .invalidUtf8OrControl (by decide) v

/-- `Toml.getTable` never returns `.numericOverflow`. -/
theorem toml_getTable_never_numericOverflow (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getTable v) :=
  getTable_never_of .numericOverflow (by decide) v

/-- `Toml.getTable` never returns `.missingField`. -/
theorem toml_getTable_never_missingField (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.getTable v) :=
  getTable_never_of .missingField (by decide) v

/-- `Toml.getTable` never returns `.decodeError`. -/
theorem toml_getTable_never_decodeError (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .decodeError (LeanSwe.Toml.getTable v) :=
  getTable_never_of .decodeError (by decide) v

private theorem getArray_never_of (k : TomlErrorKind) (hk : k ≠ .typeMismatch) (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.getArray v) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.getArray tomlGetArray
  cases v with
  | array _ => trivial
  | string _ | int _ | float _ | bool _ | localDate _ | localTime _ | localDateTime _ | offsetDateTime _ | table _ =>
    dsimp only [mkErr]; exact hk.symm

/-- `Toml.getArray` never returns `.parseError`. -/
theorem toml_getArray_never_parseError (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getArray v) :=
  getArray_never_of .parseError (by decide) v

/-- `Toml.getArray` never returns `.duplicateKey`. -/
theorem toml_getArray_never_duplicateKey (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getArray v) :=
  getArray_never_of .duplicateKey (by decide) v

/-- `Toml.getArray` never returns `.redefinedTable`. -/
theorem toml_getArray_never_redefinedTable (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getArray v) :=
  getArray_never_of .redefinedTable (by decide) v

/-- `Toml.getArray` never returns `.immutableInlineTable`. -/
theorem toml_getArray_never_immutableInlineTable (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getArray v) :=
  getArray_never_of .immutableInlineTable (by decide) v

/-- `Toml.getArray` never returns `.invalidUtf8OrControl`. -/
theorem toml_getArray_never_invalidUtf8OrControl (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getArray v) :=
  getArray_never_of .invalidUtf8OrControl (by decide) v

/-- `Toml.getArray` never returns `.numericOverflow`. -/
theorem toml_getArray_never_numericOverflow (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getArray v) :=
  getArray_never_of .numericOverflow (by decide) v

/-- `Toml.getArray` never returns `.missingField`. -/
theorem toml_getArray_never_missingField (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.getArray v) :=
  getArray_never_of .missingField (by decide) v

/-- `Toml.getArray` never returns `.decodeError`. -/
theorem toml_getArray_never_decodeError (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind .decodeError (LeanSwe.Toml.getArray v) :=
  getArray_never_of .decodeError (by decide) v

private theorem getField_never_of (k : TomlErrorKind) (hk1 : k ≠ .missingField) (hk2 : k ≠ .decodeError)
    (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.getField (α := α) t key) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.getField tomlGetField
  cases lookupKey key t with
  | none => dsimp only [mkErr]; exact hk1.symm
  | some v =>
    dsimp only
    cases (FromToml.fromToml v : Except TomlError α) with
    | ok _ => trivial
    | error _ => dsimp only; exact hk2.symm

/-- `Toml.getField` never returns `.parseError`. -/
theorem toml_getField_never_parseError (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getField (α := α) t key) :=
  getField_never_of .parseError (by decide) (by decide) α t key

/-- `Toml.getField` never returns `.duplicateKey`. -/
theorem toml_getField_never_duplicateKey (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getField (α := α) t key) :=
  getField_never_of .duplicateKey (by decide) (by decide) α t key

/-- `Toml.getField` never returns `.redefinedTable`. -/
theorem toml_getField_never_redefinedTable (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getField (α := α) t key) :=
  getField_never_of .redefinedTable (by decide) (by decide) α t key

/-- `Toml.getField` never returns `.immutableInlineTable`. -/
theorem toml_getField_never_immutableInlineTable (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getField (α := α) t key) :=
  getField_never_of .immutableInlineTable (by decide) (by decide) α t key

/-- `Toml.getField` never returns `.invalidUtf8OrControl`. -/
theorem toml_getField_never_invalidUtf8OrControl (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getField (α := α) t key) :=
  getField_never_of .invalidUtf8OrControl (by decide) (by decide) α t key

/-- `Toml.getField` never returns `.numericOverflow`. -/
theorem toml_getField_never_numericOverflow (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getField (α := α) t key) :=
  getField_never_of .numericOverflow (by decide) (by decide) α t key

/-- `Toml.getField` never returns `.typeMismatch`. -/
theorem toml_getField_never_typeMismatch (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .typeMismatch (LeanSwe.Toml.getField (α := α) t key) :=
  getField_never_of .typeMismatch (by decide) (by decide) α t key

private theorem getOptField_never_of (k : TomlErrorKind) (hk : k ≠ .decodeError)
    (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.getOptField (α := α) t key) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.getOptField tomlGetOptField
  cases lookupKey key t with
  | none => trivial
  | some v =>
    dsimp only
    cases (FromToml.fromToml v : Except TomlError α) with
    | ok _ => trivial
    | error _ => dsimp only; exact hk.symm

/-- `Toml.getOptField` never returns `.parseError`. -/
theorem toml_getOptField_never_parseError (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getOptField (α := α) t key) :=
  getOptField_never_of .parseError (by decide) α t key

/-- `Toml.getOptField` never returns `.duplicateKey`. -/
theorem toml_getOptField_never_duplicateKey (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getOptField (α := α) t key) :=
  getOptField_never_of .duplicateKey (by decide) α t key

/-- `Toml.getOptField` never returns `.redefinedTable`. -/
theorem toml_getOptField_never_redefinedTable (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getOptField (α := α) t key) :=
  getOptField_never_of .redefinedTable (by decide) α t key

/-- `Toml.getOptField` never returns `.immutableInlineTable`. -/
theorem toml_getOptField_never_immutableInlineTable (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getOptField (α := α) t key) :=
  getOptField_never_of .immutableInlineTable (by decide) α t key

/-- `Toml.getOptField` never returns `.invalidUtf8OrControl`. -/
theorem toml_getOptField_never_invalidUtf8OrControl (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getOptField (α := α) t key) :=
  getOptField_never_of .invalidUtf8OrControl (by decide) α t key

/-- `Toml.getOptField` never returns `.numericOverflow`. -/
theorem toml_getOptField_never_numericOverflow (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getOptField (α := α) t key) :=
  getOptField_never_of .numericOverflow (by decide) α t key

/-- `Toml.getOptField` never returns `.missingField`. -/
theorem toml_getOptField_never_missingField (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.getOptField (α := α) t key) :=
  getOptField_never_of .missingField (by decide) α t key

/-- `Toml.getOptField` never returns `.typeMismatch`. -/
theorem toml_getOptField_never_typeMismatch (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind .typeMismatch (LeanSwe.Toml.getOptField (α := α) t key) :=
  getOptField_never_of .typeMismatch (by decide) α t key

private theorem getPathAux_never_of (k : TomlErrorKind)
    (hk1 : k ≠ .missingField) (hk2 : k ≠ .typeMismatch) (hk3 : k ≠ .decodeError)
    (α : Type) [FromToml α] (revPrefix : List String) (t : TomlTable) (keys : List String) :
    Core.NeverErrorKindPure TomlError.kind k (tomlGetPathAux (α := α) revPrefix t keys) := by
  induction keys generalizing revPrefix t with
  | nil =>
    unfold Core.NeverErrorKindPure tomlGetPathAux
    cases (FromToml.fromToml (.table t) : Except TomlError α) with
    | ok _ => trivial
    | error _ => dsimp only; exact hk3.symm
  | cons hd tl ih =>
    cases tl with
    | nil =>
      unfold Core.NeverErrorKindPure tomlGetPathAux
      cases lookupKey hd t with
      | none => dsimp only [mkErr]; exact hk1.symm
      | some v =>
        dsimp only
        cases (FromToml.fromToml v : Except TomlError α) with
        | ok _ => trivial
        | error _ => dsimp only; exact hk3.symm
    | cons hd2 tl2 =>
      unfold Core.NeverErrorKindPure tomlGetPathAux
      cases lookupKey hd t with
      | none => dsimp only [mkErr]; exact hk1.symm
      | some v =>
        dsimp only
        cases v with
        | table sub => exact ih (hd :: revPrefix) sub
        | string _ | int _ | float _ | bool _ | localDate _ | localTime _ | localDateTime _ | offsetDateTime _ | array _ =>
          dsimp only [mkErr]; exact hk2.symm

private theorem getPath_never_of (k : TomlErrorKind)
    (hk1 : k ≠ .missingField) (hk2 : k ≠ .typeMismatch) (hk3 : k ≠ .decodeError)
    (α : Type) [FromToml α] (t : TomlTable) (keys : List String) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.getPath (α := α) t keys) :=
  getPathAux_never_of k hk1 hk2 hk3 α [] t keys

/-- `Toml.getPath` never returns `.parseError`. -/
theorem toml_getPath_never_parseError (α : Type) [FromToml α] (t : TomlTable) (keys : List String) :
    Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getPath (α := α) t keys) :=
  getPath_never_of .parseError (by decide) (by decide) (by decide) α t keys

/-- `Toml.getPath` never returns `.duplicateKey`. -/
theorem toml_getPath_never_duplicateKey (α : Type) [FromToml α] (t : TomlTable) (keys : List String) :
    Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getPath (α := α) t keys) :=
  getPath_never_of .duplicateKey (by decide) (by decide) (by decide) α t keys

/-- `Toml.getPath` never returns `.redefinedTable`. -/
theorem toml_getPath_never_redefinedTable (α : Type) [FromToml α] (t : TomlTable) (keys : List String) :
    Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getPath (α := α) t keys) :=
  getPath_never_of .redefinedTable (by decide) (by decide) (by decide) α t keys

/-- `Toml.getPath` never returns `.immutableInlineTable`. -/
theorem toml_getPath_never_immutableInlineTable (α : Type) [FromToml α] (t : TomlTable) (keys : List String) :
    Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getPath (α := α) t keys) :=
  getPath_never_of .immutableInlineTable (by decide) (by decide) (by decide) α t keys

/-- `Toml.getPath` never returns `.invalidUtf8OrControl`. -/
theorem toml_getPath_never_invalidUtf8OrControl (α : Type) [FromToml α] (t : TomlTable) (keys : List String) :
    Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getPath (α := α) t keys) :=
  getPath_never_of .invalidUtf8OrControl (by decide) (by decide) (by decide) α t keys

/-- `Toml.getPath` never returns `.numericOverflow`. -/
theorem toml_getPath_never_numericOverflow (α : Type) [FromToml α] (t : TomlTable) (keys : List String) :
    Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getPath (α := α) t keys) :=
  getPath_never_of .numericOverflow (by decide) (by decide) (by decide) α t keys

end LeanSwe.Toml.Proofs
