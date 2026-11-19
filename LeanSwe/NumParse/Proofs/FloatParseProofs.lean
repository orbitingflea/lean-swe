import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests
import LeanSwe.NumParse.Proofs.IntProofs
import LeanSwe.NumParse.Proofs.FloatExpProofs

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem parseFloat_signed_spec (s : String) (neg : Bool) (body : List Char) :
    let ch := if neg then '-' else '+'
    (Internal.parseFloatChars s (ch :: body)).mapError (·.kind) = parseFloatModelChars (ch :: body) ∧
      ∀ e, Internal.parseFloatChars s (ch :: body) = .error e → e.message ≠ "" := by
  dsimp only
  have hi : Internal.parseFloatExpPart.match_1 (fun _ => Bool × List Char) ((if neg then '-' else '+') :: body)
      (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, (if neg then '-' else '+') :: body)) = (neg, body) := by
    cases neg <;> rfl
  have hm : parseFloatExpPart.match_1 (fun _ => Bool × List Char) ((if neg then '-' else '+') :: body)
      (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, (if neg then '-' else '+') :: body)) = (neg, body) := by
    cases neg <;> rfl
  unfold Internal.parseFloatChars parseFloatModelChars
  dsimp only; rw [hi, hm]; dsimp only
  split
  · rename_i rest; cases rest <;> exact ⟨rfl, fun _ h => by cases h; try exact makeError_msg_ne_empty _ _⟩
  · rename_i rest; cases rest <;> exact ⟨rfl, fun _ h => by cases h; try exact makeError_msg_ne_empty _ _⟩
  · simp only []
    have hint_spec := parseFloatIntPart_spec s body
    cases hint : Internal.parseFloatIntPart s body with
    | error e =>
      have hm' : parseFloatIntPart body = .error e.kind := by rw [← hint_spec.1, hint]; rfl
      exact ⟨by rw [hm']; rfl, fun _ h => by cases h; exact hint_spec.2 e hint⟩
    | ok p =>
      have hm' : parseFloatIntPart body = .ok p := by rw [← hint_spec.1, hint]; rfl
      rw [hm']; rcases p with ⟨intVal, afterInt⟩; dsimp only
      split
      · rename_i afterDot
        split
        · exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
        · rename_i c rest _
          rw [isDecDigit_eq]
          by_cases hdec : isDecDigit c
          · simp only [hdec, ↓reduceIte]
            have hsm := scanDecFloatDigits_mapError s (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest
            cases hs : Internal.scanDecFloatDigits s (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest with
            | error e =>
              have hs' : consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest = .error e.kind := by
                rw [← hsm, hs]; rfl
              exact ⟨by rw [hs']; rfl, fun _ h => by cases h; exact scanDecFloatDigits_msg _ _ _ _ e hs⟩
            | ok q =>
              have hs' : consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest = .ok q := by
                rw [← hsm, hs]; rfl
              rw [hs']; rcases q with ⟨mantissa, fracCount, afterFrac⟩; dsimp only
              split
              · rename_i afterE
                rcases parseFloatExpTail_spec s neg mantissa (-Int.ofNat fracCount) afterE with ⟨h1, h2⟩
                exact ⟨by simp only [Int.sub_eq_add_neg]; rw [h1]; cases parseFloatExpPart afterE <;> rfl, h2⟩
              · rename_i afterE
                rcases parseFloatExpTail_spec s neg mantissa (-Int.ofNat fracCount) afterE with ⟨h1, h2⟩
                exact ⟨by simp only [Int.sub_eq_add_neg]; rw [h1]; cases parseFloatExpPart afterE <;> rfl, h2⟩
              · exact ⟨rfl, fun _ h => nomatch h⟩
              · simp only []; exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
          · simp [hdec, mapError_makeError, makeError_msg_ne_empty]
        · exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
      · rename_i afterE
        rcases parseFloatExpTail_spec s neg intVal 0 afterE with ⟨h1, h2⟩
        exact ⟨by simp only []; rw [h1]; cases parseFloatExpPart afterE with | error _ => rfl | ok p => rcases p with ⟨_, _⟩; simp [Int.add_zero], h2⟩
      · rename_i afterE
        rcases parseFloatExpTail_spec s neg intVal 0 afterE with ⟨h1, h2⟩
        exact ⟨by simp only []; rw [h1]; cases parseFloatExpPart afterE with | error _ => rfl | ok p => rcases p with ⟨_, _⟩; simp [Int.add_zero], h2⟩
      · simp only []; exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩

/-- Specification connecting `Internal.parseFloat` to `parseFloatModel` and non-empty error messages. -/
theorem parseFloat_spec (s : String) :
    (Internal.parseFloat s).mapError (·.kind) = parseFloatModel s ∧
      ∀ e, Internal.parseFloat s = .error e → e.message ≠ "" := by
  unfold Internal.parseFloat parseFloatModel
  rcases s.toList with _ | ⟨c0, cs0⟩
  · exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
  · by_cases hp : c0 = '+'
    · subst hp; exact parseFloat_signed_spec s false cs0
    · by_cases hm : c0 = '-'
      · subst hm; exact parseFloat_signed_spec s true cs0
      · have hi : Internal.parseFloatChars s (c0 :: cs0) = Internal.parseFloatChars s ('+' :: c0 :: cs0) := by
          have h : Internal.parseFloatExpPart.match_1 (fun _ => Bool × List Char) (c0 :: cs0)
              (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, c0 :: cs0)) = (false, c0 :: cs0) := by
            split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
          unfold Internal.parseFloatChars; dsimp only; rw [h]; rfl
        have hm' : parseFloatModelChars (c0 :: cs0) = parseFloatModelChars ('+' :: c0 :: cs0) := by
          have h : parseFloatExpPart.match_1 (fun _ => Bool × List Char) (c0 :: cs0)
              (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, c0 :: cs0)) = (false, c0 :: cs0) := by
            split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
          unfold parseFloatModelChars; dsimp only; rw [h]; rfl
        rw [hi, hm']; exact parseFloat_signed_spec s false (c0 :: cs0)

end LeanSwe.NumParse.Proofs
