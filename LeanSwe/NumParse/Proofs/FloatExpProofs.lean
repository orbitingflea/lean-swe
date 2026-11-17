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
  | case1 _ _ => rfl
  | case2 acc count c cs hd ih =>
    have hd' : isDecDigit c = true := hd
    simpa [consumeDecFloatDigits, hd'] using ih
  | case3 acc count c cs hd =>
    have hd' : isDecDigit c = false := by simp [isDecDigit_eq] at hd ⊢; exact hd
    simp [consumeDecFloatDigits, hd', mapError_makeError]
  | case4 acc count => rfl
  | case5 acc count c cs hc1 hc2 hd ih =>
    by_cases hunder : c = '_'
    · subst hunder
      rcases cs with _ | ⟨c1, cs1⟩
      · exact False.elim (hc2 rfl rfl)
      · exact False.elim (hc1 c1 cs1 rfl rfl)
    · have hd' : isDecDigit c = true := hd
      rw [consumeDecFloatDigits.eq_4]
      · simpa [hd'] using ih
      · intro c1 cs1 heq _; exact hunder heq
      · intro heq _; exact hunder heq
  | case6 acc count c cs hc1 hc2 hd =>
    by_cases hunder : c = '_'
    · subst hunder
      rcases cs with _ | ⟨c1, cs1⟩
      · exact False.elim (hc2 rfl rfl)
      · exact False.elim (hc1 c1 cs1 rfl rfl)
    · have hd' : isDecDigit c = false := by simp [isDecDigit_eq] at hd ⊢; exact hd
      rw [consumeDecFloatDigits.eq_4]
      · simp [hd', Except.mapError]
      · intro c1 cs1 heq _; exact hunder heq
      · intro heq _; exact hunder heq

/-- `Internal.scanDecFloatDigits` produces non-empty error messages. -/
theorem scanDecFloatDigits_msg (raw : String) (acc count : Nat) (cs : List Char)
    (e : NumParseError) :
    Internal.scanDecFloatDigits raw acc count cs = .error e → e.message ≠ "" := by
  fun_induction Internal.scanDecFloatDigits raw acc count cs with
  | case1 _ _ => intro h; cases h
  | case2 _ _ _ _ _ ih => exact ih
  | case3 _ _ _ _ => intro h; cases h; exact makeError_msg_ne_empty _ _
  | case4 _ _ => intro h; cases h; exact makeError_msg_ne_empty _ _
  | case5 _ _ _ _ _ _ _ ih => exact ih
  | case6 _ _ _ _ _ _ => intro h; cases h

/-- Specification connecting `Internal.parseFloatIntPart` to `Model.parseFloatIntPart`. -/
theorem parseFloatIntPart_spec (raw : String) (cs : List Char) :
    (Internal.parseFloatIntPart raw cs).mapError (·.kind) = parseFloatIntPart cs ∧
      ∀ e, Internal.parseFloatIntPart raw cs = .error e → e.message ≠ "" := by
  rcases cs with _ | ⟨c, cs⟩
  · exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
  · by_cases hcU : c = '_'
    · subst hcU; exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
    · by_cases hc0 : c = '0'
      · subst hc0
        unfold Internal.parseFloatIntPart parseFloatIntPart
        rcases cs with _ | ⟨c1, cs1⟩
        · exact ⟨rfl, fun e h => by cases h⟩
        · by_cases hdec : isDecDigit c1
          · simp [isDecDigit_eq, hdec, mapError_makeError, makeError_msg_ne_empty]
          · by_cases hc1u : c1 = '_'
            · subst hc1u
              rcases cs1 with _ | ⟨c2, cs2⟩
              · simp [isDecDigit_eq, hdec, mapError_makeError, makeError_msg_ne_empty]
              · by_cases hdec2 : isDecDigit c2 <;>
                  simp [isDecDigit_eq, hdec, hdec2, mapError_makeError, makeError_msg_ne_empty]
            · simp [isDecDigit_eq, hdec, hc1u, Except.mapError]
      · rw [Internal.parseFloatIntPart.eq_5 raw c cs (fun h => hcU h) (fun r => hc0 r)]
        rw [parseFloatIntPart.eq_5 c cs (fun h => hcU h) (fun r => hc0 r)]
        rw [isDecDigit_eq]
        by_cases hdec : isDecDigit c
        · simp only [hdec, ↓reduceIte]
          have hm := scanDecFloatDigits_mapError raw (c.toNat - '0'.toNat) 1 cs
          have hmsg := scanDecFloatDigits_msg raw (c.toNat - '0'.toNat) 1 cs
          cases hsc : Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 cs with
          | error e =>
            have hsc' : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 cs = .error e.kind := by
              rw [← hm, hsc]; rfl
            rw [hsc']
            exact ⟨rfl, fun _ h => by cases h; exact hmsg e hsc⟩
          | ok r =>
            have hsc' : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 cs = .ok r := by
              rw [← hm, hsc]; rfl
            rw [hsc']
            exact ⟨rfl, fun _ h => by cases h⟩
        · simp [hdec, mapError_makeError, makeError_msg_ne_empty]

private theorem parseFloatExpPart_aux_mapError (raw : String) (expNeg : Bool)
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
          else Except.error NumParseErrorKind.invalidSyntax) := by
  rcases afterSign with _ | ⟨c, rest⟩
  · rfl
  · by_cases hcU : c = '_'
    · subst hcU; rfl
    · have h1 :
          (match c :: rest with
            | [] => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)
            | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore raw)
            | c :: rest =>
              if Internal.isDecDigit c then
                match Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
                | .ok (eMag, _, rem) =>
                  Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
                | .error e => Except.error e
              else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)) =
          (if isDecDigit c then
            match Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
            | .ok (eMag, _, rem) =>
              Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
            | .error e => Except.error e
          else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)) := by
        split <;> first | contradiction | (rename_i heq; cases heq; rfl) | (rename_i h; exact False.elim (hcU (List.cons.inj h).1))
      have h2 :
          (match c :: rest with
            | [] => Except.error NumParseErrorKind.invalidSyntax
            | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
            | c :: rest =>
              if isDecDigit c then
                match consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest with
                | .ok (eMag, _, rem) =>
                  Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
                | .error k => Except.error k
              else Except.error NumParseErrorKind.invalidSyntax) =
          (if isDecDigit c then
            match consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest with
            | .ok (eMag, _, rem) =>
              Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
            | .error k => Except.error k
          else Except.error NumParseErrorKind.invalidSyntax) := by
        split <;> first | contradiction | (rename_i heq; cases heq; rfl) | (rename_i h; exact False.elim (hcU (List.cons.inj h).1))
      rw [h1, h2]
      by_cases hdec : isDecDigit c
      · simp only [hdec, ↓reduceIte]
        have hm := scanDecFloatDigits_mapError raw (c.toNat - '0'.toNat) 1 rest
        cases hsc : Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
        | error e =>
          have hsc' : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest = .error e.kind := by
            rw [← hm, hsc]; rfl
          rw [hsc']; rfl
        | ok r =>
          have hsc' : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest = .ok r := by
            rw [← hm, hsc]; rfl
          rw [hsc']; rfl
      · simp [hdec, mapError_makeError]

private theorem parseFloatExpPart_aux_msg (raw : String) (expNeg : Bool)
    (afterSign : List Char) :
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
  intro e he
  split at he
  · cases he; exact makeError_msg_ne_empty _ _
  · cases he; exact makeError_msg_ne_empty _ _
  · split at he
    · split at he
      · cases he
      · cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›
    · cases he; exact makeError_msg_ne_empty _ _

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
          e.message ≠ "" :=
  ⟨parseFloatExpPart_aux_mapError raw expNeg afterSign,
    parseFloatExpPart_aux_msg raw expNeg afterSign⟩

private theorem parseFloatExpPart_impl_other (raw : String) (s0 : Char) (rest0 : List Char)
    (hs0 : s0 ≠ '+') (hm0 : s0 ≠ '-') :
    Internal.parseFloatExpPart raw (s0 :: rest0) =
      match s0 :: rest0 with
      | [] => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)
      | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore raw)
      | c :: rest =>
        if Internal.isDecDigit c then
          match Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
          | .ok (eMag, _, rem) => Except.ok (if false then -Int.ofNat eMag else Int.ofNat eMag, rem)
          | .error e => Except.error e
        else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw) := by
  unfold Internal.parseFloatExpPart
  dsimp only
  split
  · rename_i h
    split at h
    · rename_i heq; exact absurd (List.cons.inj heq).1 hs0
    · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
    · cases h
  · rename_i tail h
    split at h
    · rename_i heq; exact absurd (List.cons.inj heq).1 hs0
    · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
    · rcases List.cons.inj h with ⟨hs_eq, _⟩
      subst hs_eq
      rfl
  · rename_i c rest hcU h
    split at h
    · rename_i heq; exact absurd (List.cons.inj heq).1 hs0
    · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
    · cases h
      by_cases hdec : Internal.isDecDigit s0 = true
      · simp only [hdec, ↓reduceIte]
        cases hsc : Internal.scanDecFloatDigits raw (s0.toNat - '0'.toNat) 1 rest0 <;> rfl
      · simp [hdec]

private theorem parseFloatExpPart_model_other (s0 : Char) (rest0 : List Char)
    (hs0 : s0 ≠ '+') (hm0 : s0 ≠ '-') :
    parseFloatExpPart (s0 :: rest0) =
      match s0 :: rest0 with
      | [] => Except.error NumParseErrorKind.invalidSyntax
      | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
      | c :: rest =>
        if isDecDigit c then
          match consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest with
          | .ok (eMag, _, rem) => Except.ok (if false then -Int.ofNat eMag else Int.ofNat eMag, rem)
          | .error k => Except.error k
        else Except.error NumParseErrorKind.invalidSyntax := by
  unfold parseFloatExpPart
  dsimp only
  split
  · rename_i h
    split at h
    · rename_i heq; exact absurd (List.cons.inj heq).1 hs0
    · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
    · cases h
  · rename_i tail h
    split at h
    · rename_i heq; exact absurd (List.cons.inj heq).1 hs0
    · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
    · rcases List.cons.inj h with ⟨hs_eq, _⟩
      subst hs_eq
      rfl
  · rename_i c rest hcU h
    split at h
    · rename_i heq; exact absurd (List.cons.inj heq).1 hs0
    · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
    · cases h
      by_cases hdec : isDecDigit s0 = true
      · simp only [hdec, ↓reduceIte]
        cases hsc : consumeDecFloatDigits (s0.toNat - '0'.toNat) 1 rest0 <;> rfl
      · simp [hdec]

local macro "solve_exp_digit" raw:term "," c:term "," r:term : tactic =>
  `(tactic| (
    have hm := scanDecFloatDigits_mapError $raw (($c).toNat - '0'.toNat) 1 $r
    rw [isDecDigit_eq $c]
    by_cases hdec : isDecDigit $c
    · simp only [hdec, ↓reduceIte]
      cases hsc : Internal.scanDecFloatDigits $raw (($c).toNat - '0'.toNat) 1 $r with
      | error e =>
        have hsc' : consumeDecFloatDigits (($c).toNat - '0'.toNat) 1 $r = .error e.kind := by
          rw [← hm, hsc]; rfl
        rw [hsc']; rfl
      | ok res =>
        have hsc' : consumeDecFloatDigits (($c).toNat - '0'.toNat) 1 $r = .ok res := by
          rw [← hm, hsc]; rfl
        rw [hsc']; rfl
    · simp [hdec, mapError_makeError]))

private theorem parseFloatExpPart_mapError (raw : String) (cs : List Char) :
    Except.mapError NumParseError.kind (Internal.parseFloatExpPart raw cs) = parseFloatExpPart cs := by
  rcases cs with _ | ⟨s0, rest0⟩
  · rfl
  · by_cases hs0 : s0 = '+'
    · subst hs0
      rcases rest0 with _ | ⟨c0, r0⟩
      · rfl
      · by_cases hc0 : c0 = '_'
        · subst hc0; rfl
        · unfold Internal.parseFloatExpPart parseFloatExpPart
          simp only []
          solve_exp_digit raw, c0, r0
    · by_cases hm0 : s0 = '-'
      · subst hm0
        rcases rest0 with _ | ⟨c0, r0⟩
        · rfl
        · by_cases hc0 : c0 = '_'
          · subst hc0; rfl
          · unfold Internal.parseFloatExpPart parseFloatExpPart
            simp only []
            solve_exp_digit raw, c0, r0
      · rw [parseFloatExpPart_impl_other raw s0 rest0 hs0 hm0,
            parseFloatExpPart_model_other s0 rest0 hs0 hm0]
        by_cases hc0 : s0 = '_'
        · subst hc0; rfl
        · split
          · contradiction
          · rename_i h; exact absurd (List.cons.inj h).1 hc0
          · rename_i h
            rcases List.cons.inj h with ⟨h_eq1, h_eq2⟩
            rw [← h_eq1, ← h_eq2]
            solve_exp_digit raw, s0, rest0

private theorem parseFloatExpPart_msg (raw : String) (cs : List Char) :
    ∀ e, Internal.parseFloatExpPart raw cs = .error e → e.message ≠ "" := by
  rcases cs with _ | ⟨s0, rest0⟩
  · intro e h; cases h; exact makeError_msg_ne_empty _ _
  · intro e he
    by_cases hs0 : s0 = '+'
    · subst hs0
      unfold Internal.parseFloatExpPart at he
      simp only [] at he
      rcases rest0 with _ | ⟨c0, r0⟩
      · cases he; exact makeError_msg_ne_empty _ _
      · by_cases hc0 : c0 = '_'
        · subst hc0; cases he; exact makeError_msg_ne_empty _ _
        · split at he
          · contradiction
          · rename_i h; exact absurd (List.cons.inj h).1 hc0
          · split at he
            · split at he
              · cases he
              · cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›
            · cases he; exact makeError_msg_ne_empty _ _
    · by_cases hm0 : s0 = '-'
      · subst hm0
        unfold Internal.parseFloatExpPart at he
        simp only [] at he
        rcases rest0 with _ | ⟨c0, r0⟩
        · cases he; exact makeError_msg_ne_empty _ _
        · by_cases hc0 : c0 = '_'
          · subst hc0; cases he; exact makeError_msg_ne_empty _ _
          · split at he
            · contradiction
            · rename_i h; exact absurd (List.cons.inj h).1 hc0
            · split at he
              · split at he
                · cases he
                · cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›
              · cases he; exact makeError_msg_ne_empty _ _
      · rw [parseFloatExpPart_impl_other raw s0 rest0 hs0 hm0] at he
        by_cases hc0 : s0 = '_'
        · subst hc0; cases he; exact makeError_msg_ne_empty _ _
        · split at he
          · contradiction
          · rename_i h; exact absurd (List.cons.inj h).1 hc0
          · split at he
            · split at he
              · cases he
              · cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›
            · cases he; exact makeError_msg_ne_empty _ _

/-- Specification connecting `Internal.parseFloatExpPart` to `Model.parseFloatExpPart`. -/
theorem parseFloatExpPart_spec (raw : String) (cs : List Char) :
    (Internal.parseFloatExpPart raw cs).mapError (·.kind) = parseFloatExpPart cs ∧
      ∀ e, Internal.parseFloatExpPart raw cs = .error e → e.message ≠ "" :=
  ⟨parseFloatExpPart_mapError raw cs, parseFloatExpPart_msg raw cs⟩

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
    rcases r with ⟨expVal, afterExp⟩
    rw [hpe']
    by_cases hemp : afterExp.isEmpty
    · simp [hemp, Except.mapError, Internal.evalScientificFloat, evalFloat, evalFloatModel]
    · simp [hemp, mapError_makeError, makeError_msg_ne_empty]

end LeanSwe.NumParse.Proofs
