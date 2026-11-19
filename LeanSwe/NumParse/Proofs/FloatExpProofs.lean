import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests
import LeanSwe.NumParse.Proofs.IntProofs

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Mapping `.kind` over `Internal.scanDecFloatDigits` matches `consumeDecFloatDigits`. -/
theorem scanDecFloatDigits_mapError (raw : String) (acc count : Nat) (cs : List Char) :
    (Internal.scanDecFloatDigits raw acc count cs).mapError (·.kind) =
      consumeDecFloatDigits acc count cs := by
  fun_induction Internal.scanDecFloatDigits raw acc count cs with
  | case1 | case4 => rfl
  | case2 _ _ c _ hd ih =>
    have hd' : isDecDigit c = true := hd; simpa [consumeDecFloatDigits, hd'] using ih
  | case3 _ _ c _ hd =>
    have hd' : isDecDigit c = false := by simpa [isDecDigit_eq] using hd
    simp [consumeDecFloatDigits, hd', mapError_makeError]
  | case5 _ _ c _ hc1 hc2 hd ih =>
    have hd' : isDecDigit c = true := hd
    rw [consumeDecFloatDigits.eq_4 _ _ _ _ hc1 hc2]; simpa [hd'] using ih
  | case6 _ _ c _ hc1 hc2 hd =>
    have hd' : isDecDigit c = false := by simpa [isDecDigit_eq] using hd
    rw [consumeDecFloatDigits.eq_4 _ _ _ _ hc1 hc2]; simp [hd', Except.mapError]

/-- `Internal.scanDecFloatDigits` produces non-empty error messages. -/
theorem scanDecFloatDigits_msg (raw : String) (acc count : Nat) (cs : List Char)
    (e : NumParseError) :
    Internal.scanDecFloatDigits raw acc count cs = .error e → e.message ≠ "" := by
  fun_induction Internal.scanDecFloatDigits raw acc count cs with
  | case1 | case6 => intro h; cases h
  | case2 _ _ _ _ _ ih | case5 _ _ _ _ _ _ _ ih => exact ih
  | case3 | case4 => intro h; cases h; exact makeError_msg_ne_empty _ _

/-- Specification connecting `Internal.parseFloatIntPart` to `Model.parseFloatIntPart`. -/
theorem parseFloatIntPart_spec (raw : String) (cs : List Char) :
    (Internal.parseFloatIntPart raw cs).mapError (·.kind) = parseFloatIntPart cs ∧
      ∀ e, Internal.parseFloatIntPart raw cs = .error e → e.message ≠ "" := by
  rcases cs with _ | ⟨c, cs⟩
  · exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
  · by_cases hcU : c = '_'
    · subst hcU; exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
    · by_cases hc0 : c = '0'
      · subst hc0; unfold Internal.parseFloatIntPart parseFloatIntPart
        rcases cs with _ | ⟨c1, cs1⟩
        · exact ⟨rfl, fun _ h => nomatch h⟩
        · by_cases hdec : isDecDigit c1
          · simp [isDecDigit_eq, hdec, mapError_makeError, makeError_msg_ne_empty]
          · by_cases hc1u : c1 = '_'
            · subst hc1u; rcases cs1 with _ | ⟨c2, cs2⟩
              · simp [isDecDigit_eq, hdec, mapError_makeError, makeError_msg_ne_empty]
              · by_cases hdec2 : isDecDigit c2 <;>
                  simp [isDecDigit_eq, hdec, hdec2, mapError_makeError, makeError_msg_ne_empty]
            · simp [isDecDigit_eq, hdec, hc1u, Except.mapError]
      · rw [Internal.parseFloatIntPart.eq_5 raw c cs hcU hc0,
            parseFloatIntPart.eq_5 c cs hcU hc0, isDecDigit_eq]
        by_cases hdec : isDecDigit c
        · simp only [hdec, ↓reduceIte]
          have hm := scanDecFloatDigits_mapError raw (c.toNat - '0'.toNat) 1 cs
          cases hsc : Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 cs with
          | error e =>
            have hsc' : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 cs = .error e.kind := by rw [← hm, hsc]; rfl
            exact ⟨by rw [hsc']; rfl, fun _ h => by cases h; exact scanDecFloatDigits_msg _ _ _ _ e hsc⟩
          | ok r =>
            have hsc' : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 cs = .ok r := by rw [← hm, hsc]; rfl
            exact ⟨by rw [hsc']; rfl, fun _ h => nomatch h⟩
        · simp [hdec, mapError_makeError, makeError_msg_ne_empty]

/-- Specification connecting `Internal.parseFloatExpPart` to `Model.parseFloatExpPart`. -/
theorem parseFloatExpPart_spec_aux (raw : String) (expNeg : Bool)
    (afterSign : List Char) :
    Except.mapError NumParseError.kind
      (match afterSign with
        | [] => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)
        | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore raw)
        | c :: rest =>
          if Internal.isDecDigit c then
            match Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
            | .ok (eMag, _, rem) =>
              Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
            | .error e => Except.error e
          else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)) =
      (match afterSign with
        | [] => Except.error NumParseErrorKind.invalidSyntax
        | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
        | c :: rest =>
          if isDecDigit c then
            match consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest with
            | .ok (eMag, _, rem) =>
              Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
            | .error k => Except.error k
          else Except.error NumParseErrorKind.invalidSyntax) ∧
      ∀ e,
        (match afterSign with
          | [] => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)
          | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore raw)
          | c :: rest =>
            if Internal.isDecDigit c then
              match Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
              | .ok (eMag, _, rem) =>
                Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
              | .error e => Except.error e
            else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)) = Except.error e →
          e.message ≠ "" := by
  constructor
  · split
    · rfl
    · rfl
    · rename_i c rest _
      rw [isDecDigit_eq]; by_cases hdec : isDecDigit c
      · simp only [hdec, ↓reduceIte]
        have hm := scanDecFloatDigits_mapError raw (c.toNat - '0'.toNat) 1 rest
        cases hsc : Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
        | error e => have : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest = .error e.kind := by rw [← hm, hsc]; rfl
                     rw [this]; rfl
        | ok r => have : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest = .ok r := by rw [← hm, hsc]; rfl
                  rw [this]; rfl
      · simp [hdec, mapError_makeError]
  · intro e he
    repeat' (first
      | (cases he; exact makeError_msg_ne_empty _ _; done)
      | (cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›; done)
      | (cases he; done)
      | split at he)

/-- Specification connecting `Internal.parseFloatExpPart` to `Model.parseFloatExpPart`. -/
theorem parseFloatExpPart_spec (raw : String) (cs : List Char) :
    (Internal.parseFloatExpPart raw cs).mapError (·.kind) = parseFloatExpPart cs ∧
      ∀ e, Internal.parseFloatExpPart raw cs = .error e → e.message ≠ "" := by
  have hstrip : ∀ (c : Char) (rest : List Char), c ≠ '+' → c ≠ '-' →
      Internal.parseFloatExpPart raw (c :: rest) = Internal.parseFloatExpPart raw ('+' :: c :: rest) ∧
      parseFloatExpPart (c :: rest) = parseFloatExpPart ('+' :: c :: rest) := by
    intro c rest hp hm
    constructor
    · have h : (Internal.parseFloatExpPart.match_1 (fun _ => Bool × List Char) (c :: rest)
          (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, c :: rest))) = (false, c :: rest) := by
        split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
      unfold Internal.parseFloatExpPart; dsimp only; rw [h]; rfl
    · have h : (parseFloatExpPart.match_1 (fun _ => Bool × List Char) (c :: rest)
          (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, c :: rest))) = (false, c :: rest) := by
        split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
      unfold parseFloatExpPart; dsimp only; rw [h]; rfl
  have hbase : ∀ (s : Char) (rest : List Char), (s = '+' ∨ s = '-') →
      (Internal.parseFloatExpPart raw (s :: rest)).mapError (·.kind) = parseFloatExpPart (s :: rest) ∧
        ∀ e, Internal.parseFloatExpPart raw (s :: rest) = .error e → e.message ≠ "" := by
    rintro _ rest (rfl | rfl) <;>
      exact ⟨(parseFloatExpPart_spec_aux raw _ rest).1, fun e he => by
        unfold Internal.parseFloatExpPart at he; dsimp only at he
        repeat' (first
          | (cases he; exact makeError_msg_ne_empty _ _; done)
          | (cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›; done)
          | (cases he; done)
          | split at he)⟩
  rcases cs with _ | ⟨c, rest⟩
  · exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
  · by_cases hp : c = '+'
    · subst hp; exact hbase '+' rest (Or.inl rfl)
    · by_cases hm : c = '-'
      · subst hm; exact hbase '-' rest (Or.inr rfl)
      · rw [(hstrip c rest hp hm).1, (hstrip c rest hp hm).2]
        exact hbase '+' (c :: rest) (Or.inl rfl)

/-- Specification connecting `Internal.parseFloatExpTail` to `Model.parseFloatExpPart`. -/
theorem parseFloatExpTail_spec (raw : String) (neg : Bool) (mantissa : Nat)
    (fracAdj : Int) (afterE : List Char) :
    Except.mapError NumParseError.kind (Internal.parseFloatExpTail raw neg mantissa fracAdj afterE) =
      (match parseFloatExpPart afterE with
        | .error k => .error k
        | .ok (expVal, afterExp) =>
          if afterExp.isEmpty then .ok (evalFloat neg mantissa (expVal + fracAdj))
          else .error .trailingChars) ∧
      ∀ e, Internal.parseFloatExpTail raw neg mantissa fracAdj afterE = .error e → e.message ≠ "" := by
  unfold Internal.parseFloatExpTail
  rcases parseFloatExpPart_spec raw afterE with ⟨hm, hmsg⟩
  cases hpe : Internal.parseFloatExpPart raw afterE with
  | error e =>
    have hpe' : parseFloatExpPart afterE = .error e.kind := by rw [← hm, hpe]; rfl
    simp [hpe', Except.mapError, hmsg e hpe]
  | ok r =>
    have hpe' : parseFloatExpPart afterE = .ok r := by rw [← hm, hpe]; rfl
    rcases r with ⟨expVal, afterExp⟩; rw [hpe']
    by_cases hemp : afterExp.isEmpty
    · simp [hemp, Except.mapError, Internal.evalScientificFloat, evalFloat, evalFloatModel]
    · simp [hemp, mapError_makeError, makeError_msg_ne_empty]

end LeanSwe.NumParse.Proofs
