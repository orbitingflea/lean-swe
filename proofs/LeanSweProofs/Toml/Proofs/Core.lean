import Core.NondetTest
import LeanSwe.Toml.Types
import LeanSweProofs.Toml.Model
import LeanSwe.Toml.Impl
import LeanSweProofs.Toml.SpecTests
import LeanSwe.NumParse.Types
import LeanSweProofs.NumParse.Model

/-!
Core invariants, error classification, well-formedness, and `ValidNumApi` refinement for `LeanSwe/Toml`.

Combines parser error validity (`ParseErrOK`) and builder well-formedness (`EntriesWF`) into a
single `PostOK` monadic traversal, establishes `ValBitMatch`/`TableBitMatch` transport via mutual
inductive predicates from `modelNumApi` to any `ValidNumApi`, and provides `AllPass`/`CanReach` combinators.
-/

namespace LeanSwe.Toml.Proofs

open Core LeanSwe.Toml LeanSwe.Toml.Model LeanSwe.Toml.Impl LeanSwe.NumParse LeanSwe.NumParse.Model

@[simp] theorem isBareKeyCharImpl_eq (c : Char) : isBareKeyCharImpl c = isBareKeyChar c := rfl
@[simp] theorem isDisallowedControlImpl_eq (c : Char) : isDisallowedControlImpl c = isDisallowedControl c := rfl
@[simp] theorem validTomlDateImpl_eq (d : Std.Time.PlainDate) : validTomlDateImpl d = validTomlDate d := rfl
@[simp] theorem validTomlOffsetImpl_eq (o : Std.Time.TimeZone.Offset) : validTomlOffsetImpl o = validTomlOffset o := rfl
@[simp] theorem isValidBareKeyImpl_eq (s : String) : isValidBareKeyImpl s = isValidBareKey s := rfl
@[simp] theorem hexDigitUpperImpl_eq (n : Nat) : hexDigitUpperImpl n = hexDigitUpper n := rfl
@[simp] theorem escapeBasicCharImpl_eq (b : Bool) (c : Char) : escapeBasicCharImpl b c = escapeBasicChar b c := rfl
@[simp] theorem escapeBasicBodyImpl_eq (b : Bool) (s : String) : escapeBasicBodyImpl b s = escapeBasicBody b s := rfl
@[simp] theorem padNatZeroImpl_eq (w n : Nat) : padNatZeroImpl w n = padNatZero w n := rfl
@[simp] theorem lookupKeyListImpl_eq (k : String) : ∀ xs, lookupKeyListImpl k xs = lookupKeyList k xs
  | [] => rfl
  | (k', v) :: rest => by simp only [lookupKeyListImpl, lookupKeyList, lookupKeyListImpl_eq k rest]
@[simp] theorem lookupKeyImpl_eq (k : String) (t : TomlTable) : lookupKeyImpl k t = lookupKey k t :=
  lookupKeyListImpl_eq k t.toList

/-- Bundle of `NumParse` specification proofs assumed for a parametric `numApi : NumParseApi`. -/
structure ValidNumApi (numApi : NumParseApi) : Prop where
  /-- Errors returned by `numApi` carry non-empty diagnostic messages. -/
  onError : ∀ s : String,
    (∀ e, numApi.parseInt s = .error e → e.message ≠ "") ∧
    (∀ e, numApi.parseInt64 s = .error e → e.message ≠ "") ∧
    (∀ e, numApi.parseFloat s = .error e → e.message ≠ "")
  /-- `parseInt64` refines `parseInt64Model` with non-empty error messages. -/
  parseInt64 : ∀ s : String, allowedParseInt64 s (numApi.parseInt64 s)
  /-- `parseFloat` refines `parseFloatModel` up to `FloatBitMatch` with non-empty error messages. -/
  parseFloat : ∀ s : String,
    match numApi.parseFloat s, parseFloatModel s with
    | .ok actual, .ok expected => FloatBitMatch expected actual
    | .error e, .error expectedKind => e.kind = expectedKind ∧ e.message ≠ ""
    | _, _ => False
  /-- `formatInt` emits underscore-free decimal text that round-trips through `parseIntModel`, `parseInt`, and `parseInt64`. -/
  formatInt : ∀ n : Int,
    !(numApi.formatInt n).contains '_' ∧
    parseIntModel (numApi.formatInt n) = .ok n ∧
    numApi.parseInt (numApi.formatInt n) = .ok n ∧
    (if inInt64Range n then numApi.parseInt64 (numApi.formatInt n) = .ok (Int64.ofInt n)
     else match numApi.parseInt64 (numApi.formatInt n) with
       | .error e => e.kind = .overflow ∧ e.message ≠ ""
       | .ok _ => False)
  /-- `formatFloat` satisfies `FloatFormatSpec` and round-trips through `parseFloat`. -/
  formatFloat : ∀ x : Float,
    FloatFormatSpec x (numApi.formatFloat x) ∧
    match numApi.parseFloat (numApi.formatFloat x) with
    | .ok y => FloatBitMatch x y ∧ FloatEquiv x y
    | .error _ => False
  /-- `formatInt` emits canonical signed decimal characters (`'-'` or `'0'..'9'`). -/
  formatIntChars : ∀ n : Int, (numApi.formatInt n).toList.all (fun c => isAsciiDigit c || c == '-') = true

/-- Reference `NumParseApi` built directly from the `NumParse` mathematical model specs. -/
def modelNumApi : NumParseApi :=
  { parseInt := fun s => match parseIntModel s with | .ok n => .ok n | .error k => .error { kind := k, message := "model error" }
  , parseInt64 := fun s => match parseInt64Model s with | .ok n => .ok n | .error k => .error { kind := k, message := "model error" }
  , parseFloat := fun s => match parseFloatModel s with | .ok f => .ok f | .error k => .error { kind := k, message := "model error" }
  , formatInt := fun _ => ""
  , formatFloat := fun _ => "" }

/-- Reference `CharNumApi` matching `modelNumApi` with zero `String.ofList`/`toList` overhead. -/
def modelCharNumApi : CharNumApi :=
  { parseInt64Chars := fun cs =>
      match parseIntModelChars cs with
      | .error k => .error { kind := k, message := "model error" }
      | .ok n => if inInt64Range n then .ok (Int64.ofInt n) else .error { kind := .overflow, message := "model error" }
  , parseFloatChars := fun cs => match parseFloatModelChars cs with | .ok f => .ok f | .error k => .error { kind := k, message := "model error" } }

/-- Lifting `modelNumApi` via `toCharNumApi` equals `modelCharNumApi`. -/
theorem toCharNumApi_modelNumApi_eq : toCharNumApi modelNumApi = modelCharNumApi := by
  unfold toCharNumApi modelNumApi modelCharNumApi; congr 1 <;> funext cs
  · simp only [parseInt64Model, parseIntModel, String.toList_ofList]
    cases parseIntModelChars cs with
    | error _ => rfl
    | ok n => dsimp only; by_cases hr : inInt64Range n = true <;> simp [hr]
  · simp only [parseFloatModel, String.toList_ofList]

/-- Rewrite `parseWithNum modelNumApi s` into `parseCharsWithNum modelCharNumApi s.toList`. -/
theorem parseWithNum_model_eq (s : String) : parseWithNum modelNumApi s = parseCharsWithNum modelCharNumApi s.toList := by
  simp [parseWithNum, toCharNumApi_modelNumApi_eq]

/-- `nonEmptyMsg` always returns a non-empty string. -/
@[simp] theorem nonEmptyMsg_nonEmpty (msg : String) : (!(nonEmptyMsg msg).isEmpty) = true := by
  unfold nonEmptyMsg; split
  · decide
  · rename_i h; simp [h]

/-- Errors built by `mkErr` always have non-empty messages. -/
@[simp] theorem mkErr_nonEmpty (kind : TomlErrorKind) (msg : String)
    (line : Option Nat := none) (col : Option Nat := none) (path : Option String := none) :
    (!(mkErr kind msg line col path).message.isEmpty) = true := nonEmptyMsg_nonEmpty msg

private theorem not_decide_isEmpty_eq_true {s : String} (h : (!s.isEmpty) = true) : (!decide (s.isEmpty = true)) = true := by simpa using h

/-- Combined error invariant: non-empty diagnostic message and parser-only error kind. -/
def ParseErrOK (e : TomlError) : Prop :=
  !e.message.isEmpty = true ∧ e.kind ≠ .missingField ∧ e.kind ≠ .typeMismatch ∧ e.kind ≠ .decodeError

/-- Constructor lemma for `mkErr` satisfying `ParseErrOK`. -/
@[simp] theorem parseErrOK_mkErr {k : TomlErrorKind} {msg : String} {line col : Option Nat} {path : Option String}
    (hk1 : k ≠ .missingField := by decide) (hk2 : k ≠ .typeMismatch := by decide) (hk3 : k ≠ .decodeError := by decide) :
    ParseErrOK (mkErr k msg line col path) := ⟨nonEmptyMsg_nonEmpty msg, hk1, hk2, hk3⟩

/-- Monadic bind preserves `ParseErrOK`. -/
theorem except_bind_err_ok {α β : Type} {x : Except TomlError α} {f : α → Except TomlError β} {e : TomlError}
    (hx : ∀ e', x = .error e' → ParseErrOK e') (hf : ∀ a e', x = .ok a → f a = .error e' → ParseErrOK e')
    (h : (x >>= f) = .error e) : ParseErrOK e := by
  cases x with
  | error e' => simp only [bind, Except.bind, Except.error.injEq] at h; subst h; exact hx e' rfl
  | ok a => exact hf a e rfl h

/-- Unified total correctness predicate: `P` on `.ok`, `ParseErrOK` on `.error`. -/
def PostOK {α : Type} (P : α → Prop) : Except TomlError α → Prop
  | .ok a => P a
  | .error e => ParseErrOK e

private theorem postOK_bind {α β : Type} {P : α → Prop} {Q : β → Prop} {x : Except TomlError α} {f : α → Except TomlError β}
    (hx : PostOK P x) (hf : ∀ a, P a → PostOK Q (f a)) : PostOK Q (x >>= f) := by
  cases x with | error _ => exact hx | ok a => exact hf a hx

private theorem postOK_err {α : Type} {P : α → Prop} {x : Except TomlError α} (hx : PostOK P x) {e : TomlError} (h : x = .error e) : ParseErrOK e := by rw [h] at hx; exact hx
private theorem postOK_ok {α : Type} {P : α → Prop} {x : Except TomlError α} (hx : PostOK P x) {a : α} (h : x = .ok a) : P a := by rw [h] at hx; exact hx

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
def EntriesWF (entries : List (String × Node)) : Prop := entriesNoDup entries = true ∧ wellFormedNodeListBool entries = true

private theorem assocHasKey_eq_hasKeyList (k : String) (entries : List (String × Node)) :
    hasKeyList k (entriesToTomlList entries) = assocHasKey k entries := by
  induction entries with | nil => rfl | cons _ _ ih => simp [entriesToTomlList, hasKeyList, assocHasKey, ih]

private theorem entriesNoDup_implies_noDupKeys (entries : List (String × Node)) (h : entriesNoDup entries = true) :
    noDupKeysBool (entriesToTomlList entries) = true := by
  induction entries with
  | nil => rfl
  | cons _ tl ih =>
    simp only [entriesNoDup, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [entriesToTomlList, noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true', assocHasKey_eq_hasKeyList]
    exact ⟨h.1, ih h.2⟩

mutual
  private theorem wellFormedNode_implies_value (n : Node) (h : wellFormedNodeBool n = true) :
      wellFormedValueBool (nodeToTomlValue n) = true := by
    cases n with
    | leaf v => simpa [wellFormedNodeBool, nodeToTomlValue] using h
    | table _ entries =>
      simp only [wellFormedNodeBool, nodeToTomlValue, wellFormedValueBool, Bool.and_eq_true] at h ⊢
      exact ⟨entriesNoDup_implies_noDupKeys entries h.1, wellFormedNodeList_implies_value entries h.2⟩
    | aot elems => simpa [wellFormedNodeBool, nodeToTomlValue, wellFormedValueBool] using wellFormedAot_implies_value elems h
  termination_by sizeOf n
  private theorem wellFormedNodeList_implies_value :
      (entries : List (String × Node)) → wellFormedNodeListBool entries = true →
      wellFormedValueBool.wellFormedTableListBool (entriesToTomlList entries) = true
    | [], _ => rfl
    | (_, n) :: tl, h => by
      simp only [wellFormedNodeListBool, entriesToTomlList, wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at h ⊢
      exact ⟨wellFormedNode_implies_value n h.1, wellFormedNodeList_implies_value tl h.2⟩
  termination_by entries => sizeOf entries
  private theorem wellFormedAot_implies_value :
      (elems : List (List (String × Node))) → wellFormedAotBool elems = true →
      wellFormedValueBool.wellFormedListBool (aotElemsToToml elems) = true
    | [], _ => rfl
    | e :: rest, h => by
      simp only [wellFormedAotBool, aotElemsToToml, wellFormedValueBool.wellFormedListBool, wellFormedValueBool, Bool.and_eq_true] at h ⊢
      exact ⟨⟨entriesNoDup_implies_noDupKeys e h.1.1, wellFormedNodeList_implies_value e h.1.2⟩, wellFormedAot_implies_value rest h.2⟩
  termination_by elems => sizeOf elems
end

/-- `EntriesWF entries` implies `WellFormedTable (entriesToTomlList entries).toArray`. -/
theorem entriesWF_implies_wellFormedTable (entries : List (String × Node)) (h : EntriesWF entries) :
    WellFormedTable (entriesToTomlList entries).toArray := by
  simp only [WellFormedTable, wellFormedTableBool, Bool.and_eq_true]
  exact ⟨entriesNoDup_implies_noDupKeys entries h.1, wellFormedNodeList_implies_value entries h.2⟩

private theorem assocHasKey_assocSetNode (k k' : String) (v : Node) (entries : List (String × Node)) :
    assocHasKey k (assocSetNode k' v entries) = (k == k' || assocHasKey k entries) := by
  induction entries with
  | nil => simp [assocSetNode, assocHasKey]
  | cons hd _ ih =>
    rcases hd with ⟨kh, _⟩; simp only [assocSetNode]
    by_cases heq : (k' == kh) = true
    · have hk := eq_of_beq heq; subst hk; simp [assocHasKey]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte, assocHasKey, ih]; cases (k == kh) <;> cases (k == k') <;> simp

private theorem entriesNoDup_assocSetNode (k : String) (v : Node) (entries : List (String × Node))
    (h : entriesNoDup entries = true) : entriesNoDup (assocSetNode k v entries) = true := by
  induction entries with
  | nil => simp [assocSetNode, entriesNoDup, assocHasKey]
  | cons hd tl ih =>
    rcases hd with ⟨kh, _⟩; simp only [entriesNoDup, Bool.and_eq_true, Bool.not_eq_true'] at h; simp only [assocSetNode]
    by_cases heq : (k == kh) = true
    · simpa [heq, entriesNoDup] using h
    · simp only [heq, Bool.false_eq_true, ↓reduceIte, entriesNoDup, Bool.and_eq_true, Bool.not_eq_true', assocHasKey_assocSetNode, Bool.or_eq_false_iff]
      have hne : (kh == k) = false := by
        cases hkh : (kh == k)
        · rfl
        · have hk := eq_of_beq hkh; subst hk; simp at heq
      exact ⟨⟨hne, h.1⟩, ih h.2⟩

private theorem wellFormedNodeListBool_assocSetNode (k : String) (v : Node) (entries : List (String × Node))
    (hent : wellFormedNodeListBool entries = true) (hv : wellFormedNodeBool v = true) :
    wellFormedNodeListBool (assocSetNode k v entries) = true := by
  induction entries with
  | nil => simp [assocSetNode, wellFormedNodeListBool, hv]
  | cons _ _ ih =>
    simp only [wellFormedNodeListBool, Bool.and_eq_true] at hent
    simp only [assocSetNode]; split <;> simp [wellFormedNodeListBool, hv, hent.1, hent.2, ih hent.2]

private theorem entriesWF_assocSetNode (k : String) (v : Node) (entries : List (String × Node))
    (hent : EntriesWF entries) (hv : wellFormedNodeBool v = true) : EntriesWF (assocSetNode k v entries) :=
  ⟨entriesNoDup_assocSetNode k v entries hent.1, wellFormedNodeListBool_assocSetNode k v entries hent.2 hv⟩

private theorem assocLookupNode_wellFormed (k : String) (entries : List (String × Node)) (n : Node)
    (hent : wellFormedNodeListBool entries = true) (hl : assocLookupNode k entries = some n) : wellFormedNodeBool n = true := by
  induction entries with
  | nil => simp [assocLookupNode] at hl
  | cons _ _ ih =>
    simp only [wellFormedNodeListBool, Bool.and_eq_true] at hent; simp only [assocLookupNode] at hl
    split at hl
    · cases hl; exact hent.1
    · exact ih hent.2 hl

private theorem assocHasKey_inlineListToNodes (k' : String) (l : List (String × TomlValue)) :
    assocHasKey k' (inlineListToNodes l) = hasKeyList k' l := by
  induction l with | nil => rfl | cons _ _ ih => simp [inlineListToNodes, assocHasKey, hasKeyList, ih]

mutual
  private theorem wellFormedValue_implies_inlineNode :
      (v : TomlValue) → wellFormedValueBool v = true → wellFormedNodeBool (valueToInlineNode v) = true
    | .table t, hv => by
      simp only [wellFormedValueBool, Bool.and_eq_true] at hv
      have hent := wellFormedTableList_implies_inlineNodes t.toList hv.1 hv.2
      simp only [valueToInlineNode, wellFormedNodeBool, Bool.and_eq_true]; exact hent
    | .string _, hv | .int _, hv | .float _, hv | .bool _, hv
    | .offsetDateTime _, hv | .localDateTime _, hv | .localDate _, hv
    | .localTime _, hv | .array _, hv => by simpa [valueToInlineNode, wellFormedNodeBool] using hv
  termination_by v => sizeOf v
  decreasing_by exact Nat.lt_trans (sizeOf_toList_lt_array t) (by simp +arith)
  private theorem wellFormedTableList_implies_inlineNodes :
      (entries : List (String × TomlValue)) → noDupKeysBool entries = true →
      wellFormedValueBool.wellFormedTableListBool entries = true → EntriesWF (inlineListToNodes entries)
    | [], _, _ => ⟨rfl, rfl⟩
    | (_, v) :: tl, hnd, hwf => by
      simp only [noDupKeysBool, wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd hwf
      have hrest := wellFormedTableList_implies_inlineNodes tl hnd.2 hwf.2
      simp only [inlineListToNodes, EntriesWF, entriesNoDup, wellFormedNodeListBool, Bool.and_eq_true, Bool.not_eq_true', assocHasKey_inlineListToNodes]
      exact ⟨⟨hnd.1, hrest.1⟩, ⟨wellFormedValue_implies_inlineNode v hwf.1, hrest.2⟩⟩
  termination_by entries => sizeOf entries
end

private theorem wellFormedListBool_reverse (xs : List TomlValue) (h : wellFormedValueBool.wellFormedListBool xs = true) :
    wellFormedValueBool.wellFormedListBool xs.reverse = true := by
  have happ : ∀ l1 l2 : List TomlValue, wellFormedValueBool.wellFormedListBool l1 = true →
      wellFormedValueBool.wellFormedListBool l2 = true → wellFormedValueBool.wellFormedListBool (l1 ++ l2) = true := by
    intro l1 l2 h1 h2; induction l1 with
    | nil => exact h2
    | cons _ _ ih =>
      simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at h1
      simp only [List.cons_append, wellFormedValueBool.wellFormedListBool, Bool.and_eq_true]; exact ⟨h1.1, ih h1.2⟩
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at h
    simp only [List.reverse_cons]; exact happ tl.reverse [x] (ih h.2) (by simp [wellFormedValueBool.wellFormedListBool, h.1])

private theorem wellFormedAotBool_append_empty (l : List (List (String × Node))) (h : wellFormedAotBool l = true) :
    wellFormedAotBool (l ++ [[]]) = true := by
  induction l with
  | nil => simp [wellFormedAotBool, entriesNoDup, wellFormedNodeListBool]
  | cons _ _ ih => simp only [List.cons_append, wellFormedAotBool, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih h.2⟩

private theorem normalizeCharsAux_post (line col : Nat) (acc cs : List Char) :
    PostOK (fun _ => True) (normalizeCharsAux line col acc cs) := by
  fun_induction normalizeCharsAux line col acc cs <;>
    first | trivial | exact parseErrOK_mkErr | assumption

private theorem normalizeChars_post (line col : Nat) (cs : List Char) : PostOK (fun _ => True) (normalizeChars line col cs) :=
  normalizeCharsAux_post line col [] cs

private theorem parseUnicodeHex_post (count : Nat) (cs : List Char) : PostOK (fun _ => True) (parseUnicodeHex count cs) := by
  unfold parseUnicodeHex; cases takeHexDigits count 0 cs with
  | none => exact parseErrOK_mkErr
  | some _ => dsimp only; split <;> first | exact parseErrOK_mkErr | trivial

private theorem parseBasicEscape_post (cs : List Char) : PostOK (fun _ => True) (parseBasicEscape cs) := by
  unfold parseBasicEscape; split <;> first | trivial | exact parseUnicodeHex_post _ _ | exact parseErrOK_mkErr

private theorem parseBasicStringBodyFuel_post (fuel : Nat) (acc cs : List Char) : PostOK (fun _ => True) (parseBasicStringBodyFuel fuel acc cs) := by
  fun_induction parseBasicStringBodyFuel fuel acc cs with
  | case1 | case2 | case3 => exact parseErrOK_mkErr
  | case4 => trivial
  | case5 _ _ _ ih => exact postOK_bind (parseBasicEscape_post _) fun ⟨ch, afterEsc⟩ _ => ih ch afterEsc
  | case6 _ _ _ _ _ _ _ ih => exact ih

private theorem parseLiteralStringBody_post (acc cs : List Char) : PostOK (fun _ => True) (parseLiteralStringBody acc cs) := by
  fun_induction parseLiteralStringBody acc cs with
  | case1 | case2 => exact parseErrOK_mkErr | case3 => trivial | case4 _ _ _ _ _ ih => exact ih

private theorem parseMultilineBasicBodyFuel_post (fuel : Nat) (acc cs : List Char) : PostOK (fun _ => True) (parseMultilineBasicBodyFuel fuel acc cs) := by
  fun_induction parseMultilineBasicBodyFuel fuel acc cs <;>
    first | exact parseErrOK_mkErr | trivial | assumption | exact postOK_err (parseBasicEscape_post _) ‹parseBasicEscape _ = .error _›

private theorem parseMultilineLiteralBodyFuel_post (fuel : Nat) (acc cs : List Char) : PostOK (fun _ => True) (parseMultilineLiteralBodyFuel fuel acc cs) := by
  fun_induction parseMultilineLiteralBodyFuel fuel acc cs <;> first | exact parseErrOK_mkErr | trivial | assumption

private theorem parseKeySegment_post (cs : List Char) : PostOK (fun _ => True) (parseKeySegment cs) := by
  unfold parseKeySegment; split <;> first | exact parseErrOK_mkErr | exact parseBasicStringBodyFuel_post _ _ _ | exact parseLiteralStringBody_post _ _ | (dsimp only; split <;> first | exact parseErrOK_mkErr | trivial)

private theorem parseDottedKeyFuel_post (fuel : Nat) (cs : List Char) : PostOK (fun _ => True) (parseDottedKeyFuel fuel cs) := by
  induction fuel generalizing cs with
  | zero => exact parseErrOK_mkErr
  | succ _ ih =>
    unfold parseDottedKeyFuel; refine postOK_bind (parseKeySegment_post _) fun _ _ => ?_
    dsimp only; split <;> first | (exact postOK_bind (ih _) fun _ _ => trivial) | trivial

private theorem parseDatePart_post (cs : List Char) : PostOK (fun p => validTomlDate p.1 = true) (parseDatePart cs) := by
  unfold parseDatePart; repeat (first | assumption | exact parseErrOK_mkErr | split)

private theorem parseTimePart_post (cs : List Char) : PostOK (fun p => validTomlTime p.1 = true) (parseTimePart cs) := by
  unfold parseTimePart; iterate 5 (split <;> try exact parseErrOK_mkErr)
  rename_i hss; split <;> (try dsimp only; try split) <;> first
    | exact parseErrOK_mkErr
    | (show validTomlTime _ = true; simp only [validTomlTime, Std.Time.Second.Ordinal.ofNat, Std.Time.Internal.Bounded.LE.ofNat]; exact decide_eq_true_eq.mpr (Int.ofNat_le.mpr hss))

private theorem parseOffsetPart_post (cs : List Char) : PostOK (fun o => validTomlOffset o = true) (parseOffsetPart cs) := by
  unfold parseOffsetPart; split
  · show validTomlOffset _ = true; decide
  · show validTomlOffset _ = true; decide
  · iterate 2 (split <;> try exact parseErrOK_mkErr)
    dsimp only; split
    · generalize Std.Time.TimeZone.Offset.ofSeconds _ = off; by_cases hv : validTomlOffset off = true <;> simp [hv, PostOK]
    · exact parseErrOK_mkErr
  · exact parseErrOK_mkErr

private theorem parseDateTimeChars_post (cs : List Char) (res : Except TomlError TomlValue) (h : parseDateTimeChars cs = some res) :
    PostOK (fun v => wellFormedValueBool v = true) res := by
  unfold parseDateTimeChars at h
  by_cases hdp : hasDatePrefix cs = true
  · simp only [hdp, ↓reduceIte] at h; have hdate := parseDatePart_post cs
    cases hd : parseDatePart cs with
    | error _ => rw [hd] at h hdate; cases h; exact hdate
    | ok drem =>
      rcases drem with ⟨d, _ | ⟨_, timeCs⟩⟩ <;> rw [hd] at h hdate
      · cases h; exact hdate
      · have hd_ok : validTomlDate d = true := hdate
        dsimp only at h; split at h <;> try (cases h; exact parseErrOK_mkErr)
        have htime := parseTimePart_post timeCs
        cases ht : parseTimePart timeCs with
        | error _ => rw [ht] at h htime; cases h; exact htime
        | ok trem =>
          rcases trem with ⟨tm, _ | ⟨oc, orest⟩⟩ <;> rw [ht] at h htime
          · have ht_ok : validTomlTime tm = true := htime
            cases h; simp [PostOK, wellFormedValueBool, validTomlDateTime, hd_ok, ht_ok]
          · have ht_ok : validTomlTime tm = true := htime
            dsimp only at h; have hoff := parseOffsetPart_post (oc :: orest)
            cases ho : parseOffsetPart (oc :: orest) with
            | error _ => rw [ho] at h hoff; cases h; exact hoff
            | ok off =>
              rw [ho] at h hoff; cases h; have ho_ok : validTomlOffset off = true := hoff
              simp [PostOK, wellFormedValueBool, validTomlOffsetDateTime, validTomlDateTime, hd_ok, ht_ok, ho_ok]
  · simp only [hdp, Bool.false_eq_true, ↓reduceIte] at h; split at h
    · have htime := parseTimePart_post cs
      cases ht : parseTimePart cs with
      | error _ => rw [ht] at h htime; cases h; exact htime
      | ok trem => rcases trem with ⟨_, _ | _⟩ <;> rw [ht] at h htime <;> cases h <;> first | exact htime | exact parseErrOK_mkErr
    · split at h <;> cases h; exact parseErrOK_mkErr

private theorem mapNumParseErr_err_ok (ne : NumParseError) : ParseErrOK (mapNumParseErr ne) := by
  unfold mapNumParseErr; cases ne.kind <;> exact parseErrOK_mkErr

private theorem classifyScalarChars_post (numApi : CharNumApi) (cs : List Char) :
    PostOK (fun v => wellFormedValueBool v = true) (classifyScalarChars numApi cs) := by
  unfold classifyScalarChars; split <;> first | exact parseErrOK_mkErr | rfl | (
    cases hdt : parseDateTimeChars cs with
    | some res => exact parseDateTimeChars_post cs res hdt
    | none =>
      dsimp only; split
      · cases numApi.parseFloatChars cs with | ok _ => rfl | error ne => exact mapNumParseErr_err_ok ne
      · split
        · exact parseErrOK_mkErr
        · cases numApi.parseInt64Chars cs with | ok _ => rfl | error ne => exact mapNumParseErr_err_ok ne)

private theorem insertDottedEntries_post (fullPath : List String) (entries : List (String × Node)) (relPath : List String)
    (newNode : Node) (hent : EntriesWF entries) (hnew : wellFormedNodeBool newNode = true) :
    PostOK EntriesWF (insertDottedEntries fullPath entries relPath newNode) := by
  induction relPath generalizing entries with
  | nil => exact parseErrOK_mkErr
  | cons k rest ih =>
    cases rest <;> unfold insertDottedEntries <;> cases hl : assocLookupNode k entries
    · exact entriesWF_assocSetNode k newNode entries hent hnew
    · rename_i n; cases n with | table kind _ => cases kind <;> exact parseErrOK_mkErr | leaf v => cases v <;> exact parseErrOK_mkErr | aot _ => exact parseErrOK_mkErr
    · exact postOK_bind (ih [] ⟨rfl, rfl⟩) fun sub hw => entriesWF_assocSetNode k (.table .dotted sub) entries hent (by simp [wellFormedNodeBool, hw.1, hw.2])
    · rename_i n; cases n with
      | leaf v => cases v <;> exact parseErrOK_mkErr
      | aot _ => exact parseErrOK_mkErr
      | table kind sub =>
        have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl; simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
        cases kind with
        | explicit | inline => exact parseErrOK_mkErr
        | subtableImplicit | dotted => exact postOK_bind (ih sub hwl) fun nextSub hw => entriesWF_assocSetNode k (.table .dotted nextSub) entries hent (by simp [wellFormedNodeBool, hw.1, hw.2])

private theorem parseValArrInline_post (numApi : CharNumApi) (fuel : Nat) :
    (∀ cs, PostOK (fun p => wellFormedValueBool p.1 = true) (parseValueFuel numApi fuel cs)) ∧
    (∀ cs revAcc, wellFormedValueBool.wellFormedListBool revAcc = true → PostOK (fun p => wellFormedValueBool p.1 = true) (parseArrayFuel numApi fuel cs revAcc)) ∧
    (∀ cs entries, EntriesWF entries → PostOK (fun p => wellFormedValueBool p.1 = true) (parseInlineTableFuel numApi fuel cs entries)) := by
  induction fuel with
  | zero => exact ⟨fun _ => parseErrOK_mkErr, fun _ _ _ => parseErrOK_mkErr, fun _ _ _ => parseErrOK_mkErr⟩
  | succ _ ih =>
    rcases ih with ⟨ihVal, ihArr, ihInl⟩; refine ⟨?_, ?_, ?_⟩
    · intro cs; unfold parseValueFuel; split
      · exact postOK_bind (parseMultilineBasicBodyFuel_post _ _ _) fun _ _ => rfl
      · exact postOK_bind (parseBasicStringBodyFuel_post _ _ _) fun _ _ => rfl
      · exact postOK_bind (parseMultilineLiteralBodyFuel_post _ _ _) fun _ _ => rfl
      · exact postOK_bind (parseLiteralStringBody_post _ _) fun _ _ => rfl
      · exact ihArr _ [] rfl
      · split <;> first | (show wellFormedValueBool (.table #[]) = true; decide) | exact ihInl _ [] ⟨rfl, rfl⟩
      · exact postOK_bind (classifyScalarChars_post numApi _) fun _ hv => hv
    · intro cs revAcc hacc; unfold parseArrayFuel; split
      · exact wellFormedListBool_reverse revAcc hacc
      · exact parseErrOK_mkErr
      · refine postOK_bind (ihVal _) fun ⟨v1, _⟩ hv1 => ?_
        have hnext : wellFormedValueBool.wellFormedListBool (v1 :: revAcc) = true := by simp [wellFormedValueBool.wellFormedListBool, hv1, hacc]
        dsimp only; split <;> first | exact ihArr _ (v1 :: revAcc) hnext | exact wellFormedListBool_reverse (v1 :: revAcc) hnext | exact parseErrOK_mkErr
    · intro cs entries hent; unfold parseInlineTableFuel; dsimp only
      refine postOK_bind (parseDottedKeyFuel_post _ _) fun ⟨relPath, _⟩ _ => ?_; dsimp only; split
      · refine postOK_bind (ihVal _) fun ⟨v1, _⟩ hv1 => ?_
        refine postOK_bind (insertDottedEntries_post relPath entries relPath _ hent (wellFormedValue_implies_inlineNode v1 hv1)) fun nextEntries hnext => ?_
        dsimp only; split
        · split <;> first | exact parseErrOK_mkErr | exact ihInl _ nextEntries hnext
        · simpa [PostOK, wellFormedTable_iff_value, WellFormedValue] using entriesWF_implies_wellFormedTable nextEntries hnext
        · exact parseErrOK_mkErr
      · exact parseErrOK_mkErr

private theorem mapLastAot_post (f : List (String × Node) → Except TomlError (List (String × Node)))
    (hf : ∀ x, EntriesWF x → PostOK EntriesWF (f x)) (elems : List (List (String × Node))) (hw : wellFormedAotBool elems = true) :
    PostOK (fun next => wellFormedAotBool next = true) (mapLastAot f elems) := by
  induction elems with
  | nil => exact parseErrOK_mkErr
  | cons hd tl ih =>
    cases tl <;> unfold mapLastAot
    · have hhd : EntriesWF hd := by simp only [wellFormedAotBool, Bool.and_eq_true] at hw; exact hw.1
      exact postOK_bind (hf hd hhd) fun u hu => by simp [PostOK, wellFormedAotBool, hu.1, hu.2]
    · rename_i hd2 tl2; unfold wellFormedAotBool at hw; have hparts := Bool.and_eq_true_iff.mp hw
      exact postOK_bind (ih hparts.2) fun u hu => Bool.and_eq_true_iff.mpr ⟨hparts.1, hu⟩

private theorem applyHeaderLeaf_post (mode : HeaderMode) (fullPath : List String) (entries : List (String × Node)) (k : String) (hent : EntriesWF entries) :
    PostOK EntriesWF (applyHeaderLeaf mode fullPath entries k) := by
  unfold applyHeaderLeaf; cases mode <;> cases hl : assocLookupNode k entries
  · exact entriesWF_assocSetNode k (.table .explicit []) entries hent (by simp [wellFormedNodeBool, entriesNoDup, wellFormedNodeListBool])
  · rename_i n; have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
    cases n with
    | leaf v => cases v <;> exact parseErrOK_mkErr | aot _ => exact parseErrOK_mkErr
    | table kind sub =>
      simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
      cases kind with
      | subtableImplicit => exact entriesWF_assocSetNode k (.table .explicit sub) entries hent (by simp [wellFormedNodeBool, hwl.1, hwl.2])
      | explicit | dotted | inline => exact parseErrOK_mkErr
  · exact entriesWF_assocSetNode k (.aot [[]]) entries hent (by simp [wellFormedNodeBool, wellFormedAotBool, entriesNoDup, wellFormedNodeListBool])
  · rename_i n; have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
    cases n with
    | leaf v => cases v <;> exact parseErrOK_mkErr | table kind _ => cases kind <;> exact parseErrOK_mkErr
    | aot elems => exact entriesWF_assocSetNode k (.aot (elems ++ [[]])) entries hent (by simp [wellFormedNodeBool, wellFormedAotBool_append_empty elems hwl])

private theorem applyHeader_post (mode : HeaderMode) (fullPath : List String) (entries : List (String × Node)) (path : List String) (hent : EntriesWF entries) :
    PostOK EntriesWF (applyHeader mode fullPath entries path) := by
  induction path generalizing entries with
  | nil => cases mode <;> exact parseErrOK_mkErr
  | cons k rest ih =>
    cases rest with
    | nil => exact applyHeaderLeaf_post mode fullPath entries k hent
    | cons _ _ =>
      unfold applyHeader; cases hl : assocLookupNode k entries with
      | none => exact postOK_bind (ih [] ⟨rfl, rfl⟩) fun sub hw => entriesWF_assocSetNode k (.table .subtableImplicit sub) entries hent (by simp [wellFormedNodeBool, hw.1, hw.2])
      | some n =>
        have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
        cases n with
        | leaf v => cases v <;> exact parseErrOK_mkErr
        | table kind sub =>
          simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
          cases kind with
          | inline => exact parseErrOK_mkErr
          | explicit | subtableImplicit | dotted => exact postOK_bind (ih sub hwl) fun nextSub hw => entriesWF_assocSetNode k (.table _ nextSub) entries hent (by simp [wellFormedNodeBool, hw.1, hw.2])
        | aot elems => exact postOK_bind (mapLastAot_post _ ih elems hwl) fun nextElems hw => entriesWF_assocSetNode k (.aot nextElems) entries hent (by simp [wellFormedNodeBool, hw])

private theorem insertAtActivePath_post (fullPath : List String) (entries : List (String × Node)) (activePath relPath : List String)
    (valNode : Node) (hent : EntriesWF entries) (hval : wellFormedNodeBool valNode = true) :
    PostOK EntriesWF (insertAtActivePath fullPath entries activePath relPath valNode) := by
  induction activePath generalizing entries with
  | nil => exact insertDottedEntries_post fullPath entries relPath valNode hent hval
  | cons k _ ih =>
    unfold insertAtActivePath; cases hl : assocLookupNode k entries with
    | none => exact parseErrOK_mkErr
    | some n =>
      have hwl := assocLookupNode_wellFormed k entries _ hent.2 hl
      cases n with
      | leaf _ => exact parseErrOK_mkErr
      | table kind sub =>
        simp only [wellFormedNodeBool, Bool.and_eq_true] at hwl
        exact postOK_bind (ih sub hwl) fun nextSub hw => entriesWF_assocSetNode k (.table kind nextSub) entries hent (by simp [wellFormedNodeBool, hw.1, hw.2])
      | aot elems => exact postOK_bind (mapLastAot_post _ ih elems hwl) fun nextElems hw => entriesWF_assocSetNode k (.aot nextElems) entries hent (by simp [wellFormedNodeBool, hw])

private theorem consumeStatementEnd_post (cs : List Char) : PostOK (fun _ => True) (consumeStatementEnd cs) := by
  unfold consumeStatementEnd; split <;> first | trivial | exact parseErrOK_mkErr

private theorem parseDocumentFuel_post (numApi : CharNumApi) (fuel : Nat) (cs : List Char) (activePath : List String)
    (root : List (String × Node)) (hroot : EntriesWF root) : PostOK EntriesWF (parseDocumentFuel numApi fuel cs activePath root) := by
  induction fuel generalizing cs activePath root with
  | zero => unfold parseDocumentFuel; split <;> first | exact hroot | exact parseErrOK_mkErr
  | succ _ ih =>
    unfold parseDocumentFuel; split
    · exact hroot
    · refine postOK_bind (parseDottedKeyFuel_post _ _) fun ⟨path, _⟩ _ => ?_; dsimp only; split <;> try exact parseErrOK_mkErr
      exact postOK_bind (consumeStatementEnd_post _) fun _ _ => postOK_bind (applyHeader_post .aot path root path hroot) (ih _ path)
    · refine postOK_bind (parseDottedKeyFuel_post _ _) fun ⟨path, _⟩ _ => ?_; dsimp only; split <;> try exact parseErrOK_mkErr
      exact postOK_bind (consumeStatementEnd_post _) fun _ _ => postOK_bind (applyHeader_post .table path root path hroot) (ih _ path)
    · refine postOK_bind (parseDottedKeyFuel_post _ _) fun ⟨relPath, _⟩ _ => ?_; dsimp only; split <;> try exact parseErrOK_mkErr
      refine postOK_bind ((parseValArrInline_post numApi _).1 _) fun ⟨val, _⟩ hval => postOK_bind (consumeStatementEnd_post _) fun _ _ => ?_
      exact postOK_bind (insertAtActivePath_post (activePath ++ relPath) root activePath relPath (valueToInlineNode val) hroot (wellFormedValue_implies_inlineNode val hval)) (ih _ activePath)

private theorem parseCharsWithNum_post (api : CharNumApi) (cs : List Char) : PostOK WellFormedTable (parseCharsWithNum api cs) :=
  postOK_bind (normalizeChars_post 1 1 cs) fun norm _ =>
    postOK_bind (parseDocumentFuel_post api (norm.length + 1) norm [] [] ⟨rfl, rfl⟩) fun root hroot => entriesWF_implies_wellFormedTable root hroot

/-- Master error invariant: every error from `parseCharsWithNum` satisfies `ParseErrOK`. -/
theorem parseCharsWithNum_err_ok (api : CharNumApi) (cs : List Char) {e : TomlError} (h : parseCharsWithNum api cs = .error e) : ParseErrOK e :=
  postOK_err (parseCharsWithNum_post api cs) h

/-- Every error from `parseWithNum` satisfies `ParseErrOK`. -/
theorem parseWithNum_err_ok (numApi : NumParseApi) (s : String) {e : TomlError} (h : parseWithNum numApi s = .error e) : ParseErrOK e :=
  parseCharsWithNum_err_ok (toCharNumApi numApi) s.toList h

/-- Every `TomlTable` parsed by `parseWithNum` satisfies `Model.WellFormedTable`. -/
theorem parseWithNum_wellFormed (numApi : NumParseApi) (s : String) (t : TomlTable) (h : parseWithNum numApi s = .ok t) : WellFormedTable t :=
  postOK_ok (parseCharsWithNum_post (toCharNumApi numApi) s.toList) h

/-- `TomlOffsetDateTime` boolean equality reflects Leibniz equality. -/
theorem tomlOffsetDateTime_eq_of_beq {a b : TomlOffsetDateTime} (h : (a == b) = true) : a = b := by
  cases a with | mk ad ao => cases b with | mk bd bo =>
  have h1 : (ad == bd && ao == bo) = true := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h1; rcases h1 with ⟨rfl, rfl⟩; rfl

private theorem lookupKeyList_of_tomlTableListBeq (e1 e2 : List (String × TomlValue))
    (h : tomlValueBeq.tomlTableListBeq e1 e2 = true) (k : String) :
    (lookupKeyList k e1 = none → lookupKeyList k e2 = none) ∧
    (∀ v1, lookupKeyList k e1 = some v1 → ∃ v2, lookupKeyList k e2 = some v2 ∧ tomlValueBeq v1 v2 = true) := by
  induction e1 generalizing e2 with
  | nil => cases e2 with | nil => exact ⟨fun _ => rfl, fun _ hk => by simp [lookupKeyList] at hk⟩ | cons _ _ => simp [tomlValueBeq.tomlTableListBeq] at h
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨k1, v1'⟩; cases e2 with
    | nil => simp [tomlValueBeq.tomlTableListBeq] at h
    | cons hd2 tl2 =>
      rcases hd2 with ⟨k2, v2'⟩; simp only [tomlValueBeq.tomlTableListBeq, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨rfl, hv12⟩, htl⟩; simp only [lookupKeyList]
      by_cases heqk : (k == k1) = true
      · simp [heqk, hv12]
      · simp only [heqk, Bool.false_eq_true, ↓reduceIte]; exact ih tl2 htl

mutual
  /-- `tomlValueBeq` returning `true` implies `TomlEquiv`. -/
  theorem tomlValueBeq_implies_equiv : (a b : TomlValue) → tomlValueBeq a b = true → TomlEquiv a b
    | .string _, b, h | .int _, b, h | .bool _, b, h | .localDateTime _, b, h | .localDate _, b, h | .localTime _, b, h => by
      cases b <;> simp [tomlValueBeq, TomlEquiv] at h ⊢; exact h
    | .float _, b, h => by cases b <;> simp [tomlValueBeq, TomlEquiv] at h ⊢; exact Or.inr h
    | .offsetDateTime _, b, h => by cases b <;> simp [tomlValueBeq, TomlEquiv] at h ⊢; exact tomlOffsetDateTime_eq_of_beq h
    | .array xs, b, h => by cases b <;> simp [tomlValueBeq, TomlEquiv] at h ⊢; exact tomlArrayBeq_implies_equiv xs.toList _ h
    | .table t1, b, h => by cases b <;> simp [tomlValueBeq, TomlEquiv] at h ⊢; exact tomlTableListBeq_implies_equiv t1.toList _ h
  termination_by a _ _ => sizeOf a
  decreasing_by
    · exact Nat.lt_trans (sizeOf_toList_lt_array xs) (by simp +arith)
    · exact Nat.lt_trans (sizeOf_toList_lt_array t1) (by simp +arith)
  private theorem tomlArrayBeq_implies_equiv : (xs ys : List TomlValue) → tomlValueBeq.tomlArrayBeq xs ys = true → TomlListEquiv xs ys
    | [], ys, h => by cases ys <;> simp [tomlValueBeq.tomlArrayBeq, TomlListEquiv] at h ⊢
    | x :: xr, ys, h => by
      cases ys with | nil => simp [tomlValueBeq.tomlArrayBeq] at h | cons y yr =>
      simp only [tomlValueBeq.tomlArrayBeq, Bool.and_eq_true, TomlListEquiv] at h ⊢
      exact ⟨tomlValueBeq_implies_equiv x y h.1, tomlArrayBeq_implies_equiv xr yr h.2⟩
  termination_by xs _ _ => sizeOf xs
  private theorem tomlTableListBeq_implies_equiv (e1 e2 : List (String × TomlValue)) (h : tomlValueBeq.tomlTableListBeq e1 e2 = true) : TomlTableEquivList e1 e2 := by
    simp only [TomlTableEquivList]; refine ⟨fun k => (lookupKeyList_of_tomlTableListBeq e1 e2 h k).1, fun k v1 hk1 => ?_⟩
    obtain ⟨v2, hk2, hv12⟩ := (lookupKeyList_of_tomlTableListBeq e1 e2 h k).2 v1 hk1
    exact ⟨v2, hk2, tomlValueBeq_implies_equiv v1 v2 hv12⟩
  termination_by sizeOf e1
  decreasing_by exact lookupKeyList_sizeOf hk1
end

/-- Structural boolean table equality implies `TomlTableEquiv`. -/
theorem tomlTableBeq_implies_equiv {t1 t2 : TomlTable} (h : (t1 == t2) = true) : TomlTableEquiv t1 t2 := by
  have hval : tomlValueBeq (.table t1) (.table t2) = true := by
    rcases t1 with ⟨l1⟩; rcases t2 with ⟨l2⟩; have hlist : (l1 == l2) = true := by simpa using h
    clear h; change tomlValueBeq.tomlTableListBeq l1 l2 = true
    induction l1 generalizing l2 with
    | nil => cases l2 with | nil => rfl | cons _ _ => simp at hlist
    | cons a l1' ih =>
      cases l2 with
      | nil => simp at hlist
      | cons b l2' =>
        rcases a with ⟨k1, v1⟩; rcases b with ⟨k2, v2⟩
        change ((k1 == k2 && tomlValueBeq v1 v2) && (l1' == l2')) = true at hlist
        simp only [Bool.and_eq_true, tomlValueBeq.tomlTableListBeq] at hlist ⊢; exact ⟨hlist.1, ih l2' hlist.2⟩
  simpa [TomlEquiv, TomlTableEquiv] using tomlValueBeq_implies_equiv (.table t1) (.table t2) hval

mutual
  /-- Exact structural value correspondence between `modelNumApi` and any valid `NumParseApi`. -/
  inductive ValBitMatch : TomlValue → TomlValue → Prop where
    /-- Identical string value. -/
    | string (s : String) : ValBitMatch (.string s) (.string s)
    /-- Identical integer value. -/
    | int (n : Int64) : ValBitMatch (.int n) (.int n)
    /-- Bit-matched float value. -/
    | float {f1 f2 : Float} : FloatBitMatch f1 f2 → ValBitMatch (.float f1) (.float f2)
    /-- Identical boolean value. -/
    | bool (b : Bool) : ValBitMatch (.bool b) (.bool b)
    /-- Identical offset date-time value. -/
    | offsetDateTime (d : TomlOffsetDateTime) : ValBitMatch (.offsetDateTime d) (.offsetDateTime d)
    /-- Identical local date-time value. -/
    | localDateTime (d : Std.Time.PlainDateTime) : ValBitMatch (.localDateTime d) (.localDateTime d)
    /-- Identical local date value. -/
    | localDate (d : Std.Time.PlainDate) : ValBitMatch (.localDate d) (.localDate d)
    /-- Identical local time value. -/
    | localTime (t : Std.Time.PlainTime) : ValBitMatch (.localTime t) (.localTime t)
    /-- Element-wise bit-matched array value. -/
    | array {xs ys : Array TomlValue} : ListBitMatch xs.toList ys.toList → ValBitMatch (.array xs) (.array ys)
    /-- Entry-wise bit-matched table value. -/
    | table {t1 t2 : TomlTable} : EntryListBitMatch t1.toList t2.toList → ValBitMatch (.table t1) (.table t2)
  /-- Element-wise `ValBitMatch` over `List TomlValue`. -/
  inductive ListBitMatch : List TomlValue → List TomlValue → Prop where
    /-- Empty lists match. -/
    | nil : ListBitMatch [] []
    /-- Cons elements and tails match. -/
    | cons {x y xr yr} : ValBitMatch x y → ListBitMatch xr yr → ListBitMatch (x :: xr) (y :: yr)
  /-- Key-ordered entry correspondence up to `ValBitMatch`. -/
  inductive EntryListBitMatch : List (String × TomlValue) → List (String × TomlValue) → Prop where
    /-- Empty entry lists match. -/
    | nil : EntryListBitMatch [] []
    /-- Head key/values and tails match. -/
    | cons (k : String) {v1 v2 r1 r2} : ValBitMatch v1 v2 → EntryListBitMatch r1 r2 → EntryListBitMatch ((k, v1) :: r1) ((k, v2) :: r2)
end

/-- Table-level correspondence up to `ValBitMatch` on entries. -/
def TableBitMatch (t1 t2 : TomlTable) : Prop := EntryListBitMatch t1.toList t2.toList

mutual
  /-- Structural correspondence on parser `Node` values up to `ValBitMatch` and preserving `TableKind`. -/
  inductive NodeBitMatch : Node → Node → Prop where
    /-- Leaf values match. -/
    | leaf {v1 v2} : ValBitMatch v1 v2 → NodeBitMatch (.leaf v1) (.leaf v2)
    /-- Tables with identical provenance kind and matching entries. -/
    | table (k : TableKind) {e1 e2} : EntriesBitMatch e1 e2 → NodeBitMatch (.table k e1) (.table k e2)
    /-- Arrays of tables with matching element lists. -/
    | aot {a1 a2} : AotBitMatch a1 a2 → NodeBitMatch (.aot a1) (.aot a2)
  /-- Key-ordered entry correspondence on `List (String × Node)`. -/
  inductive EntriesBitMatch : List (String × Node) → List (String × Node) → Prop where
    /-- Empty node entry lists match. -/
    | nil : EntriesBitMatch [] []
    /-- Head key/nodes and tails match. -/
    | cons (k : String) {n1 n2 r1 r2} : NodeBitMatch n1 n2 → EntriesBitMatch r1 r2 → EntriesBitMatch ((k, n1) :: r1) ((k, n2) :: r2)
  /-- Element-wise `EntriesBitMatch` over `[[aot]]` element builders. -/
  inductive AotBitMatch : List (List (String × Node)) → List (List (String × Node)) → Prop where
    /-- Empty AoT element lists match. -/
    | nil : AotBitMatch [] []
    /-- Head element tables and tails match. -/
    | cons {x y xr yr} : EntriesBitMatch x y → AotBitMatch xr yr → AotBitMatch (x :: xr) (y :: yr)
end

/-- Refinement of `Except TomlError α` outputs (`R` on `.ok`, same `kind` and non-empty message on `.error`). -/
def ExceptMatch {α : Type} (R : α → α → Prop) : Except TomlError α → Except TomlError α → Prop
  | .ok a, .ok b => R a b
  | .error e1, .error e2 => e2.kind = e1.kind ∧ !(e2.message.isEmpty) = true
  | _, _ => False

private theorem exceptMatch_bind {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    {m1 m2 : Except TomlError α} {f1 f2 : α → Except TomlError β}
    (hm : ExceptMatch R m1 m2) (hf : ∀ a b, R a b → ExceptMatch S (f1 a) (f2 b)) :
    ExceptMatch S (m1 >>= f1) (m2 >>= f2) := by
  cases m1 <;> cases m2 <;> simp only [ExceptMatch, bind, Except.bind] at hm ⊢
  · exact hm
  · exact hf _ _ hm

private theorem exceptMatch_of_post {α : Type} {P : α → Prop} {R : α → α → Prop} (m : Except TomlError α)
    (hpost : PostOK P m) (hrefl : ∀ a, R a a) : ExceptMatch R m m := by
  cases m with | ok a => exact hrefl a | error _ => exact ⟨rfl, hpost.1⟩

private theorem entryListBitMatch_lookup (k : String) {e1 e2 : List (String × TomlValue)} (h : EntryListBitMatch e1 e2) :
    (lookupKeyList k e1 = none → lookupKeyList k e2 = none) ∧
    (∀ v1, lookupKeyList k e1 = some v1 → ∃ v2, lookupKeyList k e2 = some v2 ∧ ValBitMatch v1 v2) := by
  induction e1 generalizing e2 with
  | nil => cases h; exact ⟨fun _ => rfl, fun _ hk => by simp [lookupKeyList] at hk⟩
  | cons _ _ ih =>
    cases h with
    | cons k1 hv htl =>
      simp only [lookupKeyList]; by_cases hkk : (k == k1) = true
      · simp [hkk, hv]
      · simp only [hkk, Bool.false_eq_true, ↓reduceIte]; exact ih htl

mutual
  /-- `ValBitMatch` implies `Model.TomlEquiv`. -/
  theorem valBitMatch_implies_tomlEquiv : {a b : TomlValue} → ValBitMatch a b → TomlEquiv a b
    | _, _, .string _ | _, _, .int _ | _, _, .bool _ | _, _, .offsetDateTime _
    | _, _, .localDateTime _ | _, _, .localDate _ | _, _, .localTime _ => by simp [TomlEquiv]
    | _, _, .float hf => by simpa [TomlEquiv] using floatEquiv_symm (floatBitMatch_implies_floatEquiv hf)
    | _, _, .array hl => by simpa [TomlEquiv] using listBitMatch_implies_tomlListEquiv hl
    | _, _, .table he => by simpa [TomlEquiv] using entryListBitMatch_implies_tomlTableEquiv he
  termination_by a _ _ => sizeOf a
  decreasing_by
    · rename_i xs _ _; exact Nat.lt_trans (sizeOf_toList_lt_array xs) (by simp +arith)
    · rename_i t1 _ _; exact Nat.lt_trans (sizeOf_toList_lt_array t1) (by simp +arith)
  private theorem listBitMatch_implies_tomlListEquiv : {xs ys : List TomlValue} → ListBitMatch xs ys → TomlListEquiv xs ys
    | _, _, .nil => by simp [TomlListEquiv]
    | _, _, .cons hx hxr => by simp only [TomlListEquiv]; exact ⟨valBitMatch_implies_tomlEquiv hx, listBitMatch_implies_tomlListEquiv hxr⟩
  termination_by xs _ _ => sizeOf xs
  private theorem entryListBitMatch_implies_tomlTableEquiv {e1 e2 : List (String × TomlValue)} (h : EntryListBitMatch e1 e2) : TomlTableEquivList e1 e2 := by
    simp only [TomlTableEquivList]; refine ⟨fun k => (entryListBitMatch_lookup k h).1, fun k v1 hk1 => ?_⟩
    obtain ⟨v2, hk2, hv12⟩ := (entryListBitMatch_lookup k h).2 v1 hk1
    exact ⟨v2, hk2, valBitMatch_implies_tomlEquiv hv12⟩
  termination_by sizeOf e1
  decreasing_by exact lookupKeyList_sizeOf hk1
end

/-- `TableBitMatch` implies `Model.TomlTableEquiv`. -/
theorem tableBitMatch_implies_tomlTableEquiv {t1 t2 : TomlTable} (h : TableBitMatch t1 t2) : TomlTableEquiv t1 t2 := by
  simpa [TomlEquiv, TomlTableEquiv] using valBitMatch_implies_tomlEquiv (ValBitMatch.table h)

/-- `TableBitMatch` preserves key lookup up to `ValBitMatch`. -/
theorem tableBitMatch_lookupKey (k : String) (t1 t2 : TomlTable) (h : TableBitMatch t1 t2)
    (v1 : TomlValue) (hk : lookupKey k t1 = some v1) : ∃ v2, lookupKey k t2 = some v2 ∧ ValBitMatch v1 v2 :=
  (entryListBitMatch_lookup k h).2 v1 hk

mutual
  private theorem nodeToTomlValue_bitMatch : {a b : Node} → NodeBitMatch a b → ValBitMatch (nodeToTomlValue a) (nodeToTomlValue b)
    | _, _, .leaf hv => hv
    | _, _, .table _ he => .table (entriesToTomlList_bitMatch he)
    | _, _, .aot ha => .array (aotToToml_bitMatch ha)
  termination_by a _ _ => sizeOf a
  private theorem entriesToTomlList_bitMatch : {e1 e2 : List (String × Node)} → EntriesBitMatch e1 e2 → EntryListBitMatch (entriesToTomlList e1) (entriesToTomlList e2)
    | _, _, .nil => .nil
    | _, _, .cons k hn htl => .cons k (nodeToTomlValue_bitMatch hn) (entriesToTomlList_bitMatch htl)
  termination_by e1 _ _ => sizeOf e1
  private theorem aotToToml_bitMatch : {l1 l2 : List (List (String × Node))} → AotBitMatch l1 l2 → ListBitMatch (aotElemsToToml l1) (aotElemsToToml l2)
    | _, _, .nil => .nil
    | _, _, .cons hx hxr => .cons (.table (entriesToTomlList_bitMatch hx)) (aotToToml_bitMatch hxr)
  termination_by l1 _ _ => sizeOf l1
end

mutual
  private theorem valueToInlineNode_bitMatch : {v1 v2 : TomlValue} → ValBitMatch v1 v2 → NodeBitMatch (valueToInlineNode v1) (valueToInlineNode v2)
    | _, _, .table he => .table .inline (inlineListToNodes_bitMatch he)
    | _, _, .string s => .leaf (.string s) | _, _, .int n => .leaf (.int n) | _, _, .float hf => .leaf (.float hf)
    | _, _, .bool b => .leaf (.bool b) | _, _, .offsetDateTime d => .leaf (.offsetDateTime d)
    | _, _, .localDateTime d => .leaf (.localDateTime d) | _, _, .localDate d => .leaf (.localDate d)
    | _, _, .localTime t => .leaf (.localTime t) | _, _, .array hl => .leaf (.array hl)
  termination_by v1 _ _ => sizeOf v1
  decreasing_by rename_i t1 _ _; exact Nat.lt_trans (sizeOf_toList_lt_array t1) (by simp +arith)
  private theorem inlineListToNodes_bitMatch : {e1 e2 : List (String × TomlValue)} → EntryListBitMatch e1 e2 → EntriesBitMatch (inlineListToNodes e1) (inlineListToNodes e2)
    | _, _, .nil => .nil
    | _, _, .cons k hv htl => .cons k (valueToInlineNode_bitMatch hv) (inlineListToNodes_bitMatch htl)
  termination_by e1 _ _ => sizeOf e1
end

mutual
  private theorem valBitMatch_refl : (v : TomlValue) → ValBitMatch v v
    | .string s => .string s | .int n => .int n | .float f => .float (floatBitMatch_refl f)
    | .bool b => .bool b | .offsetDateTime d => .offsetDateTime d | .localDateTime d => .localDateTime d
    | .localDate d => .localDate d | .localTime t => .localTime t
    | .array xs => .array (listBitMatch_refl xs.toList)
    | .table t => .table (entryListBitMatch_refl t.toList)
  termination_by v => sizeOf v
  decreasing_by
    · exact Nat.lt_trans (sizeOf_toList_lt_array xs) (by simp +arith)
    · exact Nat.lt_trans (sizeOf_toList_lt_array t) (by simp +arith)
  private theorem listBitMatch_refl : (l : List TomlValue) → ListBitMatch l l
    | [] => .nil | a :: xr => .cons (valBitMatch_refl a) (listBitMatch_refl xr)
  termination_by l => sizeOf l
  private theorem entryListBitMatch_refl : (l : List (String × TomlValue)) → EntryListBitMatch l l
    | [] => .nil | (k, v) :: r => .cons k (valBitMatch_refl v) (entryListBitMatch_refl r)
  termination_by l => sizeOf l
end

private theorem assocLookupNode_bitMatch (k : String) {e1 e2 : List (String × Node)} (h : EntriesBitMatch e1 e2) :
    match assocLookupNode k e1, assocLookupNode k e2 with
    | none, none => True | some n1, some n2 => NodeBitMatch n1 n2 | _, _ => False := by
  induction e1 generalizing e2 with
  | nil => cases h; trivial
  | cons _ _ ih =>
    cases h with
    | cons k1 hn htl =>
      simp only [assocLookupNode]; by_cases hkk : (k == k1) = true
      · simp [hkk, hn]
      · simp only [hkk, Bool.false_eq_true, ↓reduceIte]; exact ih htl

private theorem assocSetNode_bitMatch (k : String) {n1 n2 : Node} {e1 e2 : List (String × Node)}
    (hn : NodeBitMatch n1 n2) (he : EntriesBitMatch e1 e2) : EntriesBitMatch (assocSetNode k n1 e1) (assocSetNode k n2 e2) := by
  induction e1 generalizing e2 with
  | nil => cases he; exact .cons k hn .nil
  | cons _ _ ih =>
    cases he with
    | cons k1 hv htl =>
      simp only [assocSetNode]; by_cases hkk : (k == k1) = true
      · simp only [hkk, ↓reduceIte]; exact .cons k1 hn htl
      · simp only [hkk, Bool.false_eq_true, ↓reduceIte]; exact .cons k1 hv (ih htl)

private theorem insertDottedEntries_bitMatch (fullPath : List String) {e1 e2 : List (String × Node)}
    (relPath : List String) {n1 n2 : Node} (he : EntriesBitMatch e1 e2) (hn : NodeBitMatch n1 n2) :
    ExceptMatch EntriesBitMatch (insertDottedEntries fullPath e1 relPath n1) (insertDottedEntries fullPath e2 relPath n2) := by
  induction relPath generalizing e1 e2 with
  | nil => exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
  | cons k rest ih =>
    have hl := assocLookupNode_bitMatch k he
    cases rest <;> unfold insertDottedEntries <;>
      cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;> simp only [hl1, hl2] at hl ⊢
    · exact assocSetNode_bitMatch k hn he
    · cases hl with
      | leaf hv => exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
      | table ka _ => cases ka <;> exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
      | aot _ => exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
    · exact exceptMatch_bind (ih .nil) fun _ _ hs => assocSetNode_bitMatch k (.table .dotted hs) he
    · cases hl with
      | leaf hv => cases hv <;> exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
      | table ka hsab =>
        cases ka with
        | inline | explicit => exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
        | subtableImplicit | dotted => exact exceptMatch_bind (ih hsab) fun _ _ hs => assocSetNode_bitMatch k (.table .dotted hs) he
      | aot _ => exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩

private theorem mapLastAot_bitMatch (f1 f2 : List (String × Node) → Except TomlError (List (String × Node)))
    (hf : ∀ {x y}, EntriesBitMatch x y → ExceptMatch EntriesBitMatch (f1 x) (f2 y))
    {l1 l2 : List (List (String × Node))} (hl : AotBitMatch l1 l2) :
    ExceptMatch AotBitMatch (mapLastAot f1 l1) (mapLastAot f2 l2) := by
  induction l1 generalizing l2 with
  | nil => cases hl; exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
  | cons _ _ ih =>
    cases hl with
    | cons hhd htl =>
      cases htl with
      | nil => exact exceptMatch_bind (hf hhd) fun _ _ hu => AotBitMatch.cons hu .nil
      | cons hhd2 htl2 => exact exceptMatch_bind (ih (.cons hhd2 htl2)) fun _ _ hr => AotBitMatch.cons hhd hr

private theorem append_empty_aotBitMatch {l1 l2 : List (List (String × Node))} (h : AotBitMatch l1 l2) :
    AotBitMatch (l1 ++ [[]]) (l2 ++ [[]]) := by
  induction l1 generalizing l2 with
  | nil => cases h; exact .cons .nil .nil
  | cons _ _ ih => cases h with | cons hx htl => exact .cons hx (ih htl)

private theorem applyHeaderLeaf_bitMatch (mode : HeaderMode) (fullPath : List String)
    {e1 e2 : List (String × Node)} (k : String) (he : EntriesBitMatch e1 e2) :
    ExceptMatch EntriesBitMatch (applyHeaderLeaf mode fullPath e1 k) (applyHeaderLeaf mode fullPath e2 k) := by
  have hl := assocLookupNode_bitMatch k he; unfold applyHeaderLeaf
  cases mode <;> cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;> simp only [hl1, hl2] at hl ⊢
  · exact assocSetNode_bitMatch k (.table .explicit .nil) he
  · cases hl with
    | leaf hv => cases hv <;> exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
    | table ka hsab =>
      cases ka with
      | subtableImplicit => exact assocSetNode_bitMatch k (.table .explicit hsab) he
      | explicit | inline | dotted => exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
    | aot _ => exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
  · exact assocSetNode_bitMatch k (.aot (.cons .nil .nil)) he
  · cases hl with
    | leaf hv => cases hv <;> exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
    | table ka _ => cases ka <;> exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
    | aot hab => exact assocSetNode_bitMatch k (.aot (append_empty_aotBitMatch hab)) he

private theorem applyHeader_bitMatch (mode : HeaderMode) (fullPath : List String)
    {e1 e2 : List (String × Node)} (path : List String) (he : EntriesBitMatch e1 e2) :
    ExceptMatch EntriesBitMatch (applyHeader mode fullPath e1 path) (applyHeader mode fullPath e2 path) := by
  induction path generalizing e1 e2 with
  | nil => cases mode <;> exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
  | cons k rest ih =>
    cases rest with
    | nil => exact applyHeaderLeaf_bitMatch mode fullPath k he
    | cons _ _ =>
      have hl := assocLookupNode_bitMatch k he; unfold applyHeader
      cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;> simp only [hl1, hl2] at hl ⊢
      · exact exceptMatch_bind (ih .nil) fun _ _ hs => assocSetNode_bitMatch k (.table .subtableImplicit hs) he
      · cases hl with
        | leaf hv => cases hv <;> exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
        | table ka hsab =>
          cases ka with
          | inline => exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
          | explicit | subtableImplicit | dotted => exact exceptMatch_bind (ih hsab) fun _ _ hs => assocSetNode_bitMatch k (.table _ hs) he
        | aot hab => exact exceptMatch_bind (mapLastAot_bitMatch _ _ ih hab) fun _ _ hn => assocSetNode_bitMatch k (.aot hn) he

private theorem insertAtActivePath_bitMatch (fullPath : List String) {e1 e2 : List (String × Node)}
    (activePath relPath : List String) {n1 n2 : Node} (he : EntriesBitMatch e1 e2) (hn : NodeBitMatch n1 n2) :
    ExceptMatch EntriesBitMatch (insertAtActivePath fullPath e1 activePath relPath n1) (insertAtActivePath fullPath e2 activePath relPath n2) := by
  induction activePath generalizing e1 e2 with
  | nil => exact insertDottedEntries_bitMatch fullPath relPath he hn
  | cons k _ ih =>
    have hl := assocLookupNode_bitMatch k he; unfold insertAtActivePath
    cases hl1 : assocLookupNode k e1 <;> cases hl2 : assocLookupNode k e2 <;> simp only [hl1, hl2] at hl ⊢
    · exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
    · cases hl with
      | leaf _ => exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
      | table ka hsab => exact exceptMatch_bind (ih hsab) fun _ _ hs => assocSetNode_bitMatch k (.table ka hs) he
      | aot hab => exact exceptMatch_bind (mapLastAot_bitMatch _ _ ih hab) fun _ _ hm => assocSetNode_bitMatch k (.aot hm) he

private theorem parseInt64_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi) (s : String) :
    match parseInt64Model s, numApi.parseInt64 s with | .ok n1, .ok n2 => n1 = n2 | .error k1, .error e2 => e2.kind = k1 ∧ e2.message ≠ "" | _, _ => False := by
  have h := hnum.parseInt64 s
  have h1 := h.1
  cases hm : parseInt64Model s with
  | ok n1 =>
    cases ha : numApi.parseInt64 s with
    | ok n2 => simp [Except.mapError, ha, hm] at h1; exact h1.symm
    | error _ => simp [Except.mapError, ha, hm] at h1
  | error k1 =>
    cases ha : numApi.parseInt64 s with
    | ok _ => simp [Except.mapError, ha, hm] at h1
    | error e2 => simp [Except.mapError, ha, hm] at h1; exact ⟨h1, h.2 e2 ha⟩

private theorem parseFloat_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi) (s : String) :
    match parseFloatModel s, numApi.parseFloat s with | .ok f1, .ok f2 => FloatBitMatch f1 f2 | .error k1, .error e2 => e2.kind = k1 ∧ e2.message ≠ "" | _, _ => False := by
  have h := hnum.parseFloat s
  cases ha : numApi.parseFloat s <;> cases hm : parseFloatModel s <;> simp [ha, hm] at h ⊢ <;> exact h

private theorem classifyScalarChars_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi) (cs : List Char) :
    ExceptMatch ValBitMatch (classifyScalarChars modelCharNumApi cs) (classifyScalarChars (toCharNumApi numApi) cs) := by
  unfold classifyScalarChars; split
  · exact ⟨rfl, mkErr_nonEmpty _ _ _ _⟩
  · exact .bool true
  · exact .bool false
  · split
    · rename_i res hres; exact exceptMatch_of_post res (parseDateTimeChars_post cs res hres) valBitMatch_refl
    · split
      · have hf := parseFloat_refines numApi hnum (String.ofList cs)
        simp only [modelCharNumApi, toCharNumApi, parseFloatModel, String.toList_ofList] at hf ⊢
        cases hm : parseFloatModelChars cs <;> cases ha : numApi.parseFloat (String.ofList cs) <;> simp [hm, ha] at hf
        · exact ⟨by simp [mapNumParseErr, mkErr, hf.1], mkErr_nonEmpty _ _ _ _⟩
        · exact ValBitMatch.float hf
      · split
        · exact ⟨rfl, mkErr_nonEmpty _ _ _ _⟩
        · have hi := parseInt64_refines numApi hnum (String.ofList cs)
          simp only [modelCharNumApi, toCharNumApi, parseInt64Model, parseIntModel, String.toList_ofList] at hi ⊢
          cases hm : parseIntModelChars cs with
          | error _ =>
            cases ha : numApi.parseInt64 (String.ofList cs) <;> simp [hm, ha] at hi
            exact ⟨by simp [mapNumParseErr, mkErr, hi.1], mkErr_nonEmpty _ _ _ _⟩
          | ok n =>
            dsimp only; by_cases hr : inInt64Range n = true
            · simp only [hr, ↓reduceIte]; cases ha : numApi.parseInt64 (String.ofList cs) <;> simp [hm, hr, ha] at hi
              subst hi; exact ValBitMatch.int _
            · simp only [hr, Bool.false_eq_true, ↓reduceIte]; cases ha : numApi.parseInt64 (String.ofList cs) <;> simp [hm, hr, ha] at hi
              exact ⟨by simp [mapNumParseErr, mkErr, hi.1], mkErr_nonEmpty _ _ _ _⟩

private theorem listBitMatch_reverse {l1 l2 : List TomlValue} (hl : ListBitMatch l1 l2) : ListBitMatch l1.reverse l2.reverse := by
  have happ : ∀ {a1 a2 : List TomlValue} {x1 x2 : TomlValue}, ListBitMatch a1 a2 → ValBitMatch x1 x2 → ListBitMatch (a1 ++ [x1]) (a2 ++ [x2]) := by
    intro a1; induction a1 with
    | nil => intro _ _ _ h hx; cases h; exact .cons hx .nil
    | cons _ _ ih => intro _ _ _ h hx; cases h with | cons hh htl => exact .cons hh (ih htl hx)
  induction l1 generalizing l2 with
  | nil => cases hl; exact .nil
  | cons _ _ ih => cases hl with | cons hh htl => simp only [List.reverse_cons]; exact happ (ih htl) hh

private theorem parseValArrInline_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi) (fuel : Nat) :
    (∀ cs, ExceptMatch (fun p1 p2 => ValBitMatch p1.1 p2.1 ∧ p1.2 = p2.2) (parseValueFuel modelCharNumApi fuel cs) (parseValueFuel (toCharNumApi numApi) fuel cs)) ∧
    (∀ cs {rev1 rev2}, ListBitMatch rev1 rev2 → ExceptMatch (fun p1 p2 => ValBitMatch p1.1 p2.1 ∧ p1.2 = p2.2) (parseArrayFuel modelCharNumApi fuel cs rev1) (parseArrayFuel (toCharNumApi numApi) fuel cs rev2)) ∧
    (∀ cs {e1 e2}, EntriesBitMatch e1 e2 → ExceptMatch (fun p1 p2 => ValBitMatch p1.1 p2.1 ∧ p1.2 = p2.2) (parseInlineTableFuel modelCharNumApi fuel cs e1) (parseInlineTableFuel (toCharNumApi numApi) fuel cs e2)) := by
  induction fuel with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> intros <;> exact ⟨rfl, mkErr_nonEmpty _ _ _ _⟩
  | succ _ ih =>
    rcases ih with ⟨ihVal, ihArr, ihInl⟩; refine ⟨?_, ?_, ?_⟩
    · intro cs; unfold parseValueFuel; split
      · exact exceptMatch_bind (exceptMatch_of_post _ (parseMultilineBasicBodyFuel_post _ _ _) fun _ => rfl) fun _ _ h => by subst h; exact ⟨valBitMatch_refl _, rfl⟩
      · exact exceptMatch_bind (exceptMatch_of_post _ (parseBasicStringBodyFuel_post _ _ _) fun _ => rfl) fun _ _ h => by subst h; exact ⟨valBitMatch_refl _, rfl⟩
      · exact exceptMatch_bind (exceptMatch_of_post _ (parseMultilineLiteralBodyFuel_post _ _ _) fun _ => rfl) fun _ _ h => by subst h; exact ⟨valBitMatch_refl _, rfl⟩
      · exact exceptMatch_bind (exceptMatch_of_post _ (parseLiteralStringBody_post _ _) fun _ => rfl) fun _ _ h => by subst h; exact ⟨valBitMatch_refl _, rfl⟩
      · exact ihArr _ .nil
      · split
        · exact ⟨.table .nil, rfl⟩
        · exact ihInl _ .nil
      · exact exceptMatch_bind (classifyScalarChars_refines numApi hnum _) fun _ _ hv => ⟨hv, rfl⟩
    · intro cs _ _ hrev; unfold parseArrayFuel; split
      · exact ⟨.array (listBitMatch_reverse hrev), rfl⟩
      · exact ⟨rfl, mkErr_nonEmpty _ _ _ _⟩
      · exact exceptMatch_bind (ihVal _) fun ⟨_, _⟩ ⟨_, _⟩ ⟨hv, hr⟩ => by
          dsimp only at hr hv ⊢; subst hr; split
          · exact ihArr _ (.cons hv hrev)
          · exact ⟨.array (listBitMatch_reverse (.cons hv hrev)), rfl⟩
          · exact ⟨rfl, mkErr_nonEmpty _ _ _ _⟩
    · intro cs _ _ he; unfold parseInlineTableFuel; dsimp only
      refine exceptMatch_bind (exceptMatch_of_post _ (parseDottedKeyFuel_post _ _) fun _ => rfl) fun kp _ hkp => ?_
      subst hkp; split <;> try exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
      refine exceptMatch_bind (ihVal _) fun ⟨_, _⟩ ⟨_, _⟩ ⟨hv, hr5⟩ => ?_
      dsimp only at hv hr5 ⊢; subst hr5
      refine exceptMatch_bind (insertDottedEntries_bitMatch kp.1 kp.1 he (valueToInlineNode_bitMatch hv)) fun _ _ hnextE => ?_
      split
      · split
        · exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
        · exact ihInl _ hnextE
      · exact ⟨.table (entriesToTomlList_bitMatch hnextE), rfl⟩
      · exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩

private theorem parseDocumentFuel_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (fuel : Nat) (cs : List Char) (activePath : List String) {r1 r2 : List (String × Node)} (hr : EntriesBitMatch r1 r2) :
    ExceptMatch EntriesBitMatch (parseDocumentFuel modelCharNumApi fuel cs activePath r1) (parseDocumentFuel (toCharNumApi numApi) fuel cs activePath r2) := by
  induction fuel generalizing cs activePath r1 r2 with
  | zero =>
    unfold parseDocumentFuel; split
    · exact hr
    · exact ⟨rfl, mkErr_nonEmpty _ _ _ _⟩
  | succ _ ih =>
    have hse : ∀ x, ExceptMatch Eq (consumeStatementEnd x) (consumeStatementEnd x) := fun x =>
      exceptMatch_of_post _ (consumeStatementEnd_post x) fun _ => rfl
    unfold parseDocumentFuel; split
    · exact hr
    · refine exceptMatch_bind (exceptMatch_of_post _ (parseDottedKeyFuel_post _ _) fun _ => rfl) fun kp _ hkp => ?_
      subst hkp; dsimp only; split <;> try exact ⟨rfl, mkErr_nonEmpty _ _ _ _⟩
      exact exceptMatch_bind (hse _) fun _ _ hnc => by subst hnc; exact exceptMatch_bind (applyHeader_bitMatch .aot kp.1 kp.1 hr) (fun _ _ h => ih _ kp.1 h)
    · refine exceptMatch_bind (exceptMatch_of_post _ (parseDottedKeyFuel_post _ _) fun _ => rfl) fun kp _ hkp => ?_
      subst hkp; dsimp only; split <;> try exact ⟨rfl, mkErr_nonEmpty _ _ _ _⟩
      exact exceptMatch_bind (hse _) fun _ _ hnc => by subst hnc; exact exceptMatch_bind (applyHeader_bitMatch .table kp.1 kp.1 hr) (fun _ _ h => ih _ kp.1 h)
    · refine exceptMatch_bind (exceptMatch_of_post _ (parseDottedKeyFuel_post _ _) fun _ => rfl) fun kp _ hkp => ?_
      subst hkp; dsimp only; split <;> try exact ⟨rfl, nonEmptyMsg_nonEmpty _⟩
      refine exceptMatch_bind ((parseValArrInline_refines numApi hnum _).1 _) fun ⟨_, _⟩ ⟨_, _⟩ ⟨hv, hr3⟩ => ?_
      dsimp only at hv hr3 ⊢; subst hr3
      exact exceptMatch_bind (hse _) fun _ _ hnc => by
        subst hnc; exact exceptMatch_bind (insertAtActivePath_bitMatch (activePath ++ kp.1) activePath kp.1 hr (valueToInlineNode_bitMatch hv)) (fun _ _ h => ih _ activePath h)

/-- Parametric refinement: `parseWithNum numApi s` refines `parseWithNum modelNumApi s` up to `TableBitMatch`. -/
theorem parseWithNum_refines (numApi : NumParseApi) (hnum : ValidNumApi numApi) (s : String) :
    ExceptMatch TableBitMatch (parseWithNum modelNumApi s) (parseWithNum numApi s) := by
  rw [parseWithNum_model_eq]; unfold parseWithNum parseCharsWithNum
  refine exceptMatch_bind (exceptMatch_of_post _ (normalizeChars_post 1 1 s.toList) fun _ => rfl) fun norm _ hnorm => ?_
  subst hnorm; exact exceptMatch_bind (parseDocumentFuel_refines numApi hnum (norm.length + 1) norm [] .nil) (fun _ _ h => entriesToTomlList_bitMatch h)

/-- Lift `parseWithNum modelNumApi s = .ok t1` to `parseWithNum numApi s` via `ValidNumApi`. -/
theorem parseWithNum_ok_of_model (numApi : NumParseApi) (hnum : ValidNumApi numApi) (s : String)
    (t1 : TomlTable) (hm : parseWithNum modelNumApi s = .ok t1) : ∃ t2, parseWithNum numApi s = .ok t2 ∧ TableBitMatch t1 t2 := by
  have href := parseWithNum_refines numApi hnum s; rw [hm] at href
  cases ha : parseWithNum numApi s with | error _ => rw [ha] at href; cases href | ok t2 => rw [ha] at href; exact ⟨t2, rfl, href⟩

/-- Prove `test_toml_onError_returnsNonEmptyMessage` for `makeTomlApi numApi`. -/
theorem allPass_onError (numApi : NumParseApi) : Core.AllPass (test_toml_onError_returnsNonEmptyMessage (makeTomlApi numApi)) := by
  intro s; dsimp only [test_toml_onError_returnsNonEmptyMessage, makeTomlApi, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  cases h : parseWithNum numApi s with | ok _ => trivial | error e => exact ⟨by simpa using (parseWithNum_err_ok numApi s h).1, trivial⟩

/-- Witness `CanReach` for `test_toml_onError_returnsNonEmptyMessage`. -/
theorem canReach_onError (numApi : NumParseApi) : Core.CanReach (test_toml_onError_returnsNonEmptyMessage (makeTomlApi numApi)) := by
  refine ⟨"\r", ?_⟩
  have h1 : "\r".toList = ['\r'] := rfl
  have h2 : normalizeChars 1 1 ['\r'] = .error (mkErr .invalidUtf8OrControl "bare carriage return is not allowed in TOML" (some 1) (some 1)) := rfl
  dsimp only [test_toml_onError_returnsNonEmptyMessage, makeTomlApi, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  simp only [parseWithNum, parseCharsWithNum, bind, Except.bind, h1, h2]; simp [mkErr, nonEmptyMsg]

/-- Prove `test_toml_accessorError_returnsNonEmptyMessage` for `makeTomlApi numApi`. -/
theorem allPass_accessorError (numApi : NumParseApi) : Core.AllPass (test_toml_accessorError_returnsNonEmptyMessage (makeTomlApi numApi)) := by
  intro v t k path
  dsimp only [test_toml_accessorError_returnsNonEmptyMessage, makeTomlApi, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  have htab : ∀ e, tomlGetTable v = .error e → (!decide (e.message.isEmpty = true)) = true := by
    intro e he; cases v <;> simp [tomlGetTable] at he <;> subst he <;> exact not_decide_isEmpty_eq_true (nonEmptyMsg_nonEmpty _)
  have harr : ∀ e, tomlGetArray v = .error e → (!decide (e.message.isEmpty = true)) = true := by
    intro e he; cases v <;> simp [tomlGetArray] at he <;> subst he <;> exact not_decide_isEmpty_eq_true (nonEmptyMsg_nonEmpty _)
  have hfld : ∀ e, tomlGetField (α := TomlValue) t k = .error e → (!decide (e.message.isEmpty = true)) = true := by
    intro e he; simp only [tomlGetField, lookupKeyImpl_eq] at he; cases hl : lookupKey k t <;> simp [hl, FromToml.fromToml] at he; subst he; exact not_decide_isEmpty_eq_true (nonEmptyMsg_nonEmpty _)
  have hopt : ∀ e, tomlGetOptField (α := String) t k = .error e → (!decide (e.message.isEmpty = true)) = true := by
    intro e he; simp only [tomlGetOptField, lookupKeyImpl_eq] at he; cases hl : lookupKey k t with
    | none => simp [hl] at he
    | some val => simp only [hl] at he; cases val <;> simp [FromToml.fromToml] at he <;> subst he <;> exact not_decide_isEmpty_eq_true (nonEmptyMsg_nonEmpty _)
  have hpath : ∀ (p acc : List String) (tbl : TomlTable) (e : TomlError), tomlGetPathAux (α := TomlValue) acc tbl p = .error e → (!decide (e.message.isEmpty = true)) = true := by
    intro p; induction p with
    | nil => intro _ _ _ he; simp [tomlGetPathAux, FromToml.fromToml] at he
    | cons seg rest ih =>
      intro acc tbl e he; cases rest <;> simp only [tomlGetPathAux, lookupKeyImpl_eq] at he
      · cases hl : lookupKey seg tbl <;> simp [hl, FromToml.fromToml] at he; subst he; exact not_decide_isEmpty_eq_true (nonEmptyMsg_nonEmpty _)
      · cases hl : lookupKey seg tbl with
        | none => simp [hl] at he; subst he; exact not_decide_isEmpty_eq_true (nonEmptyMsg_nonEmpty _)
        | some val => simp only [hl] at he; cases val with | table sub => exact ih (seg :: acc) sub e he | _ => cases he; exact not_decide_isEmpty_eq_true (nonEmptyMsg_nonEmpty _)
  cases h1 : tomlGetTable v <;> (try refine ⟨htab _ h1, ?_⟩) <;> dsimp only
  all_goals (cases h2 : tomlGetArray v <;> (try refine ⟨harr _ h2, ?_⟩) <;> dsimp only)
  all_goals (cases h3 : tomlGetField (α := TomlValue) t k <;> (try refine ⟨hfld _ h3, ?_⟩) <;> dsimp only)
  all_goals (cases h4 : tomlGetOptField (α := String) t k <;> (try refine ⟨hopt _ h4, ?_⟩) <;> dsimp only)
  all_goals (cases h5 : tomlGetPath (α := TomlValue) t path <;> (try exact ⟨hpath path [] t _ h5, trivial⟩) <;> trivial)

/-- Witness `CanReach` for `test_toml_accessorError_returnsNonEmptyMessage`. -/
theorem canReach_accessorError (numApi : NumParseApi) : Core.CanReach (test_toml_accessorError_returnsNonEmptyMessage (makeTomlApi numApi)) := by
  dsimp only [Core.CanReach, test_toml_accessorError_returnsNonEmptyMessage, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  exact ⟨.table #[], #[], "", [], by simp [makeTomlApi, tomlGetTable, tomlGetArray, tomlGetField, tomlGetOptField, tomlGetPath, tomlGetPathAux, lookupKey, lookupKeyList, mkErr, nonEmptyMsg, FromToml.fromToml]⟩

/-- Prove `test_toml_parse_returnsWellFormedTable` for `makeTomlApi numApi`. -/
theorem allPass_parse_returnsWellFormedTable (numApi : NumParseApi) : Core.AllPass (test_toml_parse_returnsWellFormedTable (makeTomlApi numApi)) := by
  intro s; dsimp only [test_toml_parse_returnsWellFormedTable, makeTomlApi, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  cases h : parseWithNum numApi s with | error _ => trivial | ok t => exact ⟨parseWithNum_wellFormed numApi s t h, trivial⟩

/-- Witness `CanReach` for `test_toml_parse_returnsWellFormedTable`. -/
theorem canReach_parse_returnsWellFormedTable (numApi : NumParseApi) : Core.CanReach (test_toml_parse_returnsWellFormedTable (makeTomlApi numApi)) := by
  refine ⟨"", ?_⟩; have h1 : normalizeChars 1 1 [] = .ok [] := rfl; have h2 : skipTriviaNewlines [] = [] := rfl
  dsimp only [test_toml_parse_returnsWellFormedTable, makeTomlApi, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  simp only [parseWithNum, parseCharsWithNum, String.toList_empty, h1]
  simp [bind, Except.bind, parseDocumentFuel, h2, entriesToTomlList, WellFormedTable, wellFormedTableBool, noDupKeysBool, wellFormedValueBool.wellFormedTableListBool]

private theorem decodeTomlList_int64_map (l : List Int64) : decodeTomlList (l.map TomlValue.int) = .ok l := by
  induction l with | nil => rfl | cons _ _ ih => simp [decodeTomlList, FromToml.fromToml, bind, Except.bind, ih]

/-- Prove `test_toml_codecsAndAccessors_conformsToSpec` for `makeTomlApi numApi`. -/
theorem allPass_codecsAndAccessors (numApi : NumParseApi) : Core.AllPass (test_toml_codecsAndAccessors_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [Core.AllPass, test_toml_codecsAndAccessors_conformsToSpec, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  intro s n64 f b odt ldt ld lt xs tbl
  have hxs : (makeTomlApi numApi).decode (α := Array Int64) ((makeTomlApi numApi).encode xs) = .ok xs := by
    cases xs with | mk l => simp only [makeTomlApi, tomlDecode, tomlEncode, FromToml.fromToml, ToToml.toToml, Array.toList_map, decodeTomlList_int64_map, bind, Except.bind]
  refine ⟨rfl, rfl, floatEquiv_refl f, rfl, rfl, rfl, rfl, rfl, hxs, rfl, ?_⟩
  simp [makeTomlApi, tomlDecode, FromToml.fromToml, tomlGetTable, tomlGetArray, tomlGetField, tomlGetOptField, tomlGetPath, tomlGetPathAux, lookupKey, lookupKeyList, mkErr, nonEmptyMsg, joinPath]

/-- Witness `CanReach` for `test_toml_codecsAndAccessors_conformsToSpec`. -/
theorem canReach_codecsAndAccessors (numApi : NumParseApi) : Core.CanReach (test_toml_codecsAndAccessors_conformsToSpec (makeTomlApi numApi)) := by
  dsimp only [Core.CanReach, test_toml_codecsAndAccessors_conformsToSpec, Core.NondetTest.nondet, NondetTest.assert, bind, pure]
  refine ⟨"", 0, 0.0, false, ⟨Std.Time.PlainDateTime.mk (specDate 2024 1 1) (specTime 0 0 0), specOffset 0⟩,
    Std.Time.PlainDateTime.mk (specDate 2024 1 1) (specTime 0 0 0), specDate 2024 1 1, specTime 0 0 0, #[], #[], ?_⟩
  simp [makeTomlApi, tomlDecode, tomlEncode, FromToml.fromToml, ToToml.toToml, decodeTomlList, bind, Except.bind, tomlGetTable, tomlGetArray, tomlGetField, tomlGetOptField, tomlGetPath, tomlGetPathAux, lookupKey, lookupKeyList, mkErr, nonEmptyMsg, joinPath, floatEquiv_refl]

/-- Evaluate one positive parse spec case against `modelNumApi`. -/
def checkOneOkModel (p : String × TomlTable) : Bool := match parseWithNum modelNumApi p.1 with | .ok t => tomlValueBeq (.table p.2) (.table t) | .error _ => false
/-- Evaluate one negative parse error spec case against `modelNumApi`. -/
def checkOneErrModel (p : String × TomlErrorKind) : Bool := match parseWithNum modelNumApi p.1 with | .ok _ => false | .error e => e.kind == p.2
/-- Evaluate one float bit-pattern spec case against `modelNumApi`. -/
def checkOneFloatBitModel (p : String × String × Option UInt64) : Bool :=
  match parseWithNum modelNumApi p.1 with
  | .error _ => false
  | .ok parsed => match lookupKey p.2.1 parsed with | some (.float f) => (match p.2.2 with | none => f.isNaN | some bits => !f.isNaN && f.toBits == bits) | _ => false

private theorem tomlErrorKind_beq_eq (a b : TomlErrorKind) (h : (a == b) = true) : a = b := by cases a <;> cases b <;> revert h <;> decide

private theorem forM_lift {m : Type → Type} [Monad m] {α : Type} (lift : (Unit → Prop) → m Unit → Prop)
    (hbind : ∀ {a : m Unit} {b : Unit → m Unit} {post : Unit → Prop}, lift (fun _ => lift post (b ())) a → lift post (a >>= b))
    (hpure : ∀ {post : Unit → Prop}, post () → lift post (pure ()))
    (xs : List α) (f : α → m Unit) (h : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → lift post (f x)) (post : Unit → Prop) (hpost : post ()) : lift post (xs.forM f) := by
  induction xs with | nil => exact hpure hpost | cons a rest ih => exact hbind (h a (List.Mem.head _) _ (ih fun x hx => h x (List.Mem.tail _ hx)))

/-- Lift a `List.forM` step proof into `Core.AllPass (do xs.forM f; ys.forM g)`. -/
theorem allPass_forM_seq {α β : Type} (xs : List α) (ys : List β) (f : α → Core.AllPassRun Unit) (g : β → Core.AllPassRun Unit)
    (hf : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post) (hg : ∀ y ∈ ys, ∀ post : Unit → Prop, post () → g y post) :
    Core.AllPass (do xs.forM f; ys.forM g) := forM_lift (fun post r => r post) id id xs f hf _ (forM_lift (fun post r => r post) id id ys g hg _ trivial)
/-- Lift a `List.forM` step proof into `Core.CanReach (do xs.forM f; ys.forM g)`. -/
theorem canReach_forM_seq {α β : Type} (xs : List α) (ys : List β) (f : α → Core.CanReachRun Unit) (g : β → Core.CanReachRun Unit)
    (hf : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post) (hg : ∀ y ∈ ys, ∀ post : Unit → Prop, post () → g y post) :
    Core.CanReach (do xs.forM f; ys.forM g) := forM_lift (fun post r => r post) id id xs f hf _ (forM_lift (fun post r => r post) id id ys g hg _ trivial)
/-- Lift three `List.forM` step proofs into `Core.AllPass (do xs.forM f; ys.forM g; zs.forM h)`. -/
theorem allPass_forM_seq3 {α β γ : Type} (xs : List α) (ys : List β) (zs : List γ) (f : α → Core.AllPassRun Unit) (g : β → Core.AllPassRun Unit) (h : γ → Core.AllPassRun Unit)
    (hf : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post) (hg : ∀ y ∈ ys, ∀ post : Unit → Prop, post () → g y post) (hh : ∀ z ∈ zs, ∀ post : Unit → Prop, post () → h z post) :
    Core.AllPass (do xs.forM f; ys.forM g; zs.forM h) := forM_lift (fun post r => r post) id id xs f hf _ (allPass_forM_seq ys zs g h hg hh)
/-- Lift three `List.forM` step proofs into `Core.CanReach (do xs.forM f; ys.forM g; zs.forM h)`. -/
theorem canReach_forM_seq3 {α β γ : Type} (xs : List α) (ys : List β) (zs : List γ) (f : α → Core.CanReachRun Unit) (g : β → Core.CanReachRun Unit) (h : γ → Core.CanReachRun Unit)
    (hf : ∀ x ∈ xs, ∀ post : Unit → Prop, post () → f x post) (hg : ∀ y ∈ ys, ∀ post : Unit → Prop, post () → g y post) (hh : ∀ z ∈ zs, ∀ post : Unit → Prop, post () → h z post) :
    Core.CanReach (do xs.forM f; ys.forM g; zs.forM h) := forM_lift (fun post r => r post) id id xs f hf _ (canReach_forM_seq ys zs g h hg hh)

private theorem checkParseEquiv_prop (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (cases : List (String × TomlTable)) (hall : cases.all checkOneOkModel = true) (src : String) (exp : TomlTable) (hp : (src, exp) ∈ cases) :
    ∃ t2, parseWithNum numApi src = .ok t2 ∧ TomlTableEquiv exp t2 := by
  have hmem := List.all_eq_true.mp hall (src, exp) hp; have href := parseWithNum_refines numApi hnum src
  simp only [checkOneOkModel] at hmem
  cases hm : parseWithNum modelNumApi src <;> simp [hm, ExceptMatch] at hmem href
  case ok t1 =>
    cases ha : parseWithNum numApi src <;> simp [ha] at href
    exact ⟨_, rfl, tomlTableEquiv_trans (by simpa [TomlEquiv, TomlTableEquiv] using tomlValueBeq_implies_equiv (.table exp) (.table t1) hmem) (tableBitMatch_implies_tomlTableEquiv href)⟩

private theorem checkParseErrorKind_prop (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (cases : List (String × TomlErrorKind)) (hall : cases.all checkOneErrModel = true) (src : String) (expectedKind : TomlErrorKind) (hp : (src, expectedKind) ∈ cases) :
    ∃ e2, parseWithNum numApi src = .error e2 ∧ e2.kind = expectedKind ∧ !(e2.message.isEmpty) = true := by
  have hmem := List.all_eq_true.mp hall (src, expectedKind) hp; have href := parseWithNum_refines numApi hnum src
  simp only [checkOneErrModel] at hmem
  cases hm : parseWithNum modelNumApi src with
  | ok _ => simp [hm] at hmem
  | error e1 =>
    simp only [hm] at hmem href; cases ha : parseWithNum numApi src with
    | ok _ => simp [ha, ExceptMatch] at href
    | error e2 => simp only [ha, ExceptMatch] at href; exact ⟨e2, rfl, href.1.trans (tomlErrorKind_beq_eq _ _ hmem), href.2⟩

private theorem checkParseFloatBits_prop (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (hall : floatBitCases.all checkOneFloatBitModel = true) (src k : String) (exp : Option UInt64) (hp : (src, k, exp) ∈ floatBitCases) :
    ∃ t2 f2, parseWithNum numApi src = .ok t2 ∧ lookupKey k t2 = some (.float f2) ∧ (match exp with | none => f2.isNaN = true | some bits => f2.toBits = bits) := by
  have hmem := List.all_eq_true.mp hall (src, k, exp) hp; have href := parseWithNum_refines numApi hnum src
  simp only [checkOneFloatBitModel] at hmem
  cases hm : parseWithNum modelNumApi src <;> simp [hm, ExceptMatch] at hmem href
  case ok t1 =>
    cases ha : parseWithNum numApi src <;> simp [ha] at href
    case ok t2 =>
      cases hlook1 : lookupKey k t1 with
      | none => simp [hlook1] at hmem
      | some v1 =>
        cases v1 with
        | float f1 =>
          obtain ⟨v2, hlook2, hv12⟩ := tableBitMatch_lookupKey k t1 t2 href (.float f1) hlook1
          cases hv12 with
          | float hf12 =>
            simp only [FloatBitMatch] at hf12; simp only [hlook1] at hmem; refine ⟨t2, _, rfl, hlook2, ?_⟩
            cases exp with
            | none => simp only at hmem; simpa [hmem] using hf12
            | some bits =>
              simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hmem
              simp only [hmem.1, Bool.false_eq_true, ↓reduceIte] at hf12; exact hf12.trans hmem.2
        | _ => simp [hlook1] at hmem

/-- Lift `cases.all checkOneOkModel = true` to `checkParseEquiv` under `Core.AllPassRun`. -/
theorem checkParseEquiv_allPass (numApi : NumParseApi) (hnum : ValidNumApi numApi) (cases : List (String × TomlTable)) (hall : cases.all checkOneOkModel = true) :
    ∀ p ∈ cases, ∀ post : Unit → Prop, post () → (checkParseEquiv (makeTomlApi numApi) p : Core.AllPassRun Unit) post := by
  rintro ⟨src, exp⟩ hp post hpost; obtain ⟨_, ha, heq⟩ := checkParseEquiv_prop numApi hnum cases hall src exp hp
  dsimp only [checkParseEquiv, makeTomlApi, Core.NondetTest.assert]; rw [ha]; exact ⟨heq, hpost⟩

/-- Lift `cases.all checkOneOkModel = true` to `checkParseEquiv` under `Core.CanReachRun`. -/
theorem checkParseEquiv_canReach (numApi : NumParseApi) (hnum : ValidNumApi numApi) (cases : List (String × TomlTable)) (hall : cases.all checkOneOkModel = true) :
    ∀ p ∈ cases, ∀ post : Unit → Prop, post () → (checkParseEquiv (makeTomlApi numApi) p : Core.CanReachRun Unit) post := by
  rintro ⟨src, exp⟩ hp post hpost; obtain ⟨_, ha, heq⟩ := checkParseEquiv_prop numApi hnum cases hall src exp hp
  dsimp only [checkParseEquiv, makeTomlApi, Core.NondetTest.assert]; rw [ha]; exact ⟨heq, hpost⟩

/-- Lift `cases.all checkOneErrModel = true` to `checkParseErrorKind` under `Core.AllPassRun`. -/
theorem checkParseErrorKind_allPass (numApi : NumParseApi) (hnum : ValidNumApi numApi) (cases : List (String × TomlErrorKind)) (hall : cases.all checkOneErrModel = true) :
    ∀ p ∈ cases, ∀ post : Unit → Prop, post () → (checkParseErrorKind (makeTomlApi numApi) p : Core.AllPassRun Unit) post := by
  rintro ⟨src, expectedKind⟩ hp post hpost; obtain ⟨_, ha, hk, hne⟩ := checkParseErrorKind_prop numApi hnum cases hall src expectedKind hp
  dsimp only [checkParseErrorKind, makeTomlApi, Core.NondetTest.assert]; rw [ha]; exact ⟨⟨hk, hne⟩, hpost⟩

/-- Lift `cases.all checkOneErrModel = true` to `checkParseErrorKind` under `Core.CanReachRun`. -/
theorem checkParseErrorKind_canReach (numApi : NumParseApi) (hnum : ValidNumApi numApi) (cases : List (String × TomlErrorKind)) (hall : cases.all checkOneErrModel = true) :
    ∀ p ∈ cases, ∀ post : Unit → Prop, post () → (checkParseErrorKind (makeTomlApi numApi) p : Core.CanReachRun Unit) post := by
  rintro ⟨src, expectedKind⟩ hp post hpost; obtain ⟨_, ha, hk, hne⟩ := checkParseErrorKind_prop numApi hnum cases hall src expectedKind hp
  dsimp only [checkParseErrorKind, makeTomlApi, Core.NondetTest.assert]; rw [ha]; exact ⟨⟨hk, hne⟩, hpost⟩

/-- Lift `floatBitCases.all checkOneFloatBitModel = true` to `checkParseFloatBits` under `Core.AllPassRun`. -/
theorem checkParseFloatBits_allPass (numApi : NumParseApi) (hnum : ValidNumApi numApi) (hall : floatBitCases.all checkOneFloatBitModel = true) :
    ∀ p ∈ floatBitCases, ∀ post : Unit → Prop, post () → (checkParseFloatBits (makeTomlApi numApi) p : Core.AllPassRun Unit) post := by
  rintro ⟨src, k, exp⟩ hp post hpost; obtain ⟨_, _, ha, hlook2, hf2⟩ := checkParseFloatBits_prop numApi hnum hall src k exp hp
  dsimp only [checkParseFloatBits, makeTomlApi, Core.NondetTest.assert]; rw [ha]; dsimp only; rw [hlook2]; dsimp only; cases exp <;> exact ⟨hf2, hpost⟩

/-- Lift `floatBitCases.all checkOneFloatBitModel = true` to `checkParseFloatBits` under `Core.CanReachRun`. -/
theorem checkParseFloatBits_canReach (numApi : NumParseApi) (hnum : ValidNumApi numApi) (hall : floatBitCases.all checkOneFloatBitModel = true) :
    ∀ p ∈ floatBitCases, ∀ post : Unit → Prop, post () → (checkParseFloatBits (makeTomlApi numApi) p : Core.CanReachRun Unit) post := by
  rintro ⟨src, k, exp⟩ hp post hpost; obtain ⟨_, _, ha, hlook2, hf2⟩ := checkParseFloatBits_prop numApi hnum hall src k exp hp
  dsimp only [checkParseFloatBits, makeTomlApi, Core.NondetTest.assert]; rw [ha]; dsimp only; rw [hlook2]; dsimp only; cases exp <;> exact ⟨hf2, hpost⟩

end LeanSwe.Toml.Proofs
