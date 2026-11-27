import LeanSwe.Base64.Interface
import LeanSwe.Base64.Model

namespace LeanSwe.Base64.Proofs

open LeanSwe.Base64
open LeanSwe.Base64.Model

private theorem errorKindLabel_ne_empty (k : Base64ErrorKind) :
    Internal.errorKindLabel k ≠ "" := by
  cases k <;> decide

/-- `Internal.makeError` always constructs a non-empty diagnostic message. -/
theorem makeError_msg_ne_empty (k : Base64ErrorKind) (offset : Nat) (detail : String) :
    (Internal.makeError k offset detail).message ≠ "" := by
  unfold Internal.makeError
  intro heq
  have hlen := congrArg String.length heq
  simp only [String.length_append] at hlen
  have h1 : (" at offset " : String).length = 11 := rfl
  have h2 : (": " : String).length = 2 := rfl
  have h3 : ("" : String).length = 0 := rfl
  omega

private theorem scanInvalidChar_eq (a : Alphabet) (idx : Nat) (cs : List Char) :
    Internal.scanInvalidChar a idx cs = Model.scanInvalidChar a idx cs := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c cs ih =>
    unfold Internal.scanInvalidChar Model.scanInvalidChar
    change (if Model.isAlphabetChar a c || c == '=' then Internal.scanInvalidChar a (idx + 1) cs else some idx) =
      (if Model.isAlphabetChar a c || c == '=' then Model.scanInvalidChar a (idx + 1) cs else some idx)
    split
    · exact ih (idx + 1)
    · rfl

private theorem findFirstEq_eq (idx : Nat) (cs : List Char) :
    Internal.findFirstEq idx cs = Model.findFirstEq idx cs := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c cs ih =>
    unfold Internal.findFirstEq Model.findFirstEq
    split
    · rfl
    · exact ih (idx + 1)

private theorem decodeChar?_eq (a : Alphabet) (c : Char) :
    Internal.decodeChar? a c = Model.decodeChar? a c := rfl

private theorem encodeSextet_eq (a : Alphabet) (s : Nat) :
    Internal.encodeSextet a s = Model.encodeSextet a s := rfl

private theorem decodeDataChars_spec (a : Alphabet) (strict : Bool) (offset : Nat) (cs : List Char) :
    (Internal.decodeDataChars a strict offset cs).mapError (fun e => (e.kind, e.offset)) =
        Model.decodeDataChars a strict offset cs ∧
      ∀ e, Internal.decodeDataChars a strict offset cs = .error e → e.message ≠ "" := by
  match cs with
  | [] =>
    exact ⟨rfl, fun _ h => by cases h⟩
  | [_] =>
    exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _ _⟩
  | [c0, c1] =>
    unfold Internal.decodeDataChars Model.decodeDataChars
    simp only [decodeChar?_eq]
    cases h0 : Model.decodeChar? a c0 with
    | none =>
      exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
    | some s0 =>
      cases h1 : Model.decodeChar? a c1 with
      | none =>
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      | some s1 =>
        by_cases hst : (strict && decide ((s1 &&& 0x0F) ≠ 0)) = true
        · simp only [hst, ↓reduceIte, Except.mapError]
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        · simp only [hst, Bool.false_eq_true, ↓reduceIte, Except.mapError]
          exact ⟨trivial, fun _ he => by cases he⟩
  | [c0, c1, c2] =>
    unfold Internal.decodeDataChars Model.decodeDataChars
    simp only [decodeChar?_eq]
    cases h0 : Model.decodeChar? a c0 with
    | none =>
      exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
    | some s0 =>
      cases h1 : Model.decodeChar? a c1 with
      | none =>
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      | some s1 =>
        cases h2 : Model.decodeChar? a c2 with
        | none =>
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        | some s2 =>
          by_cases hst : (strict && decide ((s2 &&& 0x03) ≠ 0)) = true
          · simp only [hst, ↓reduceIte, Except.mapError]
            exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
          · simp only [hst, Bool.false_eq_true, ↓reduceIte, Except.mapError]
            exact ⟨trivial, fun _ he => by cases he⟩
  | c0 :: c1 :: c2 :: c3 :: rest =>
    have ih := decodeDataChars_spec a strict (offset + 4) rest
    unfold Internal.decodeDataChars Model.decodeDataChars
    simp only [decodeChar?_eq]
    cases h0 : Model.decodeChar? a c0 with
    | none =>
      exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
    | some s0 =>
      cases h1 : Model.decodeChar? a c1 with
      | none =>
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      | some s1 =>
        cases h2 : Model.decodeChar? a c2 with
        | none =>
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        | some s2 =>
          cases h3 : Model.decodeChar? a c3 with
          | none =>
            exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
          | some s3 =>
            cases hrec : Internal.decodeDataChars a strict (offset + 4) rest with
            | ok bs =>
              have hm : Model.decodeDataChars a strict (offset + 4) rest = .ok bs := by
                rw [← ih.1, hrec]; rfl
              simp only [hm, Except.mapError]
              exact ⟨trivial, fun _ he => by cases he⟩
            | error err =>
              have hm : Model.decodeDataChars a strict (offset + 4) rest = .error (err.kind, err.offset) := by
                rw [← ih.1, hrec]; rfl
              simp only [hm, Except.mapError]
              exact ⟨trivial, fun e he => by cases he; exact ih.2 err hrec⟩

private theorem decodeChars_spec (opts : DecodeOptions) (chars : List Char) :
    (Internal.decodeChars opts chars).mapError (fun e => (e.kind, e.offset)) =
        Model.decodeModelChars opts chars ∧
      ∀ e, Internal.decodeChars opts chars = .error e → e.message ≠ "" := by
  unfold Internal.decodeChars Model.decodeModelChars
  rw [scanInvalidChar_eq, findFirstEq_eq]
  cases hscan : Model.scanInvalidChar opts.alphabet 0 chars with
  | some idx =>
    exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
  | none =>
    cases heq : Model.findFirstEq 0 chars with
    | some p =>
      by_cases hforb : opts.padding = .forbidden
      · simp only [hforb, ↓reduceIte, Except.mapError]
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      · cases hall : (chars.drop p).all (· == '=')
        · simp only [hforb, ↓reduceIte, hall, Bool.not_false, Except.mapError]
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        · simp only [hforb, ↓reduceIte, hall, Bool.not_true, Bool.false_eq_true]
          split
          · exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
          · split
            · exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
            · exact decodeDataChars_spec opts.alphabet opts.strictCanonicalBits 0 (chars.take p)
    | none =>
      by_cases hmod1 : (chars.length % 4 == 1) = true
      · simp only [hmod1, ↓reduceIte, Except.mapError]
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      · by_cases hreq : (opts.padding = .required && decide (chars.length % 4 ≠ 0)) = true
        · simp only [hmod1, Bool.false_eq_true, ↓reduceIte, hreq, Except.mapError]
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        · have hds := decodeDataChars_spec opts.alphabet opts.strictCanonicalBits 0 chars
          simp only [hmod1, Bool.false_eq_true, ↓reduceIte, hreq]
          exact hds

/-- `decodeWith` matches `Model.decodeModel` on `.ok` and `(kind, offset)` with non-empty errors. -/
theorem decodeWith_matchesModel_aux (opts : DecodeOptions) (s : String) :
    (decodeWith opts s).mapError (fun e => (e.kind, e.offset)) = decodeModel opts s ∧
      ∀ e, decodeWith opts s = .error e → e.message ≠ "" := by
  have h := decodeChars_spec opts s.toList
  change ((Internal.decodeChars opts s.toList).map (fun bs => ByteArray.mk bs.toArray)).mapError
      (fun e => (e.kind, e.offset)) =
      (Model.decodeModelChars opts s.toList).map (fun bs => ByteArray.mk bs.toArray) ∧
    ∀ e, (Internal.decodeChars opts s.toList).map (fun bs => ByteArray.mk bs.toArray) = .error e →
      e.message ≠ ""
  cases hres : Internal.decodeChars opts s.toList with
  | ok bs =>
    have hm : Model.decodeModelChars opts s.toList = .ok bs := by
      rw [← h.1, hres]; rfl
    simp [Except.map, Except.mapError, hm]
  | error err =>
    have hm : Model.decodeModelChars opts s.toList = .error (err.kind, err.offset) := by
      rw [← h.1, hres]; rfl
    refine ⟨?_, fun e he => ?_⟩
    · simp [Except.map, Except.mapError, hm]
    · simp [Except.map] at he; subst he; exact h.2 err hres

/-- `Internal.encodeBytesList` equals `Model.encodeBytesList`. -/
theorem encodeBytesList_eq (a : Alphabet) (pad : Bool) (bs : List UInt8) :
    Internal.encodeBytesList a pad bs = Model.encodeBytesList a pad bs := by
  match bs with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: rest =>
    unfold Internal.encodeBytesList Model.encodeBytesList
    simp only [encodeSextet_eq, encodeBytesList_eq]

/-- `encodeWith` equals `Model.encodeModel`. -/
theorem encodeWith_eq_encodeModel (opts : EncodeOptions) (bs : ByteArray) :
    encodeWith opts bs = encodeModel opts bs := by
  change String.ofList (Internal.encodeBytesList opts.alphabet opts.pad bs.data.toList) =
    String.ofList (Model.encodeBytesList opts.alphabet opts.pad bs.data.toList)
  rw [encodeBytesList_eq]

end LeanSwe.Base64.Proofs
