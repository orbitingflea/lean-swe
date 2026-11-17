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

private theorem parseFloatAfterInt_spec (s : String) (neg : Bool) (body : List Char) :
    Except.mapError NumParseError.kind
      (match Internal.parseFloatIntPart s body with
      | Except.error e => Except.error e
      | Except.ok (intVal, afterInt) =>
        match afterInt with
        | '.' :: afterDot =>
          match afterDot with
          | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore s)
          | c :: rest =>
            if Internal.isDecDigit c then
              match Internal.scanDecFloatDigits s (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest with
              | Except.error e => Except.error e
              | Except.ok (mantissa, fracCount, afterFrac) =>
                match afterFrac with
                | 'e' :: afterE => Internal.parseFloatExpTail s neg mantissa (-Int.ofNat fracCount) afterE
                | 'E' :: afterE => Internal.parseFloatExpTail s neg mantissa (-Int.ofNat fracCount) afterE
                | [] => Except.ok (Internal.evalScientificFloat neg mantissa (-Int.ofNat fracCount))
                | _ :: _ => Except.error (Internal.makeError NumParseErrorKind.trailingChars s)
            else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax s)
          | [] => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax s)
        | 'e' :: afterE => Internal.parseFloatExpTail s neg intVal 0 afterE
        | 'E' :: afterE => Internal.parseFloatExpTail s neg intVal 0 afterE
        | _ => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax s)) =
      (match parseFloatIntPart body with
        | Except.error k => Except.error k
        | Except.ok (intVal, afterInt) =>
          match afterInt with
          | '.' :: afterDot =>
            match afterDot with
            | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
            | c :: rest =>
              if isDecDigit c then
                match consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest with
                | Except.error k => Except.error k
                | Except.ok (mantissa, fracCount, afterFrac) =>
                  match afterFrac with
                  | 'e' :: afterE =>
                    match parseFloatExpPart afterE with
                    | Except.error k => Except.error k
                    | Except.ok (expVal, afterExp) =>
                      if afterExp.isEmpty then Except.ok (evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                      else Except.error NumParseErrorKind.trailingChars
                  | 'E' :: afterE =>
                    match parseFloatExpPart afterE with
                    | Except.error k => Except.error k
                    | Except.ok (expVal, afterExp) =>
                      if afterExp.isEmpty then Except.ok (evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                      else Except.error NumParseErrorKind.trailingChars
                  | [] => Except.ok (evalFloat neg mantissa (-Int.ofNat fracCount))
                  | _ :: _ => Except.error NumParseErrorKind.trailingChars
              else Except.error NumParseErrorKind.invalidSyntax
            | [] => Except.error NumParseErrorKind.invalidSyntax
          | 'e' :: afterE =>
            match parseFloatExpPart afterE with
            | Except.error k => Except.error k
            | Except.ok (expVal, afterExp) =>
              if afterExp.isEmpty then Except.ok (evalFloat neg intVal expVal)
              else Except.error NumParseErrorKind.trailingChars
          | 'E' :: afterE =>
            match parseFloatExpPart afterE with
            | Except.error k => Except.error k
            | Except.ok (expVal, afterExp) =>
              if afterExp.isEmpty then Except.ok (evalFloat neg intVal expVal)
              else Except.error NumParseErrorKind.trailingChars
          | _ => Except.error NumParseErrorKind.invalidSyntax) ∧
      ∀ e,
        (match Internal.parseFloatIntPart s body with
          | Except.error e => Except.error e
          | Except.ok (intVal, afterInt) =>
            match afterInt with
            | '.' :: afterDot =>
              match afterDot with
              | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore s)
              | c :: rest =>
                if Internal.isDecDigit c then
                  match Internal.scanDecFloatDigits s (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest with
                  | Except.error e => Except.error e
                  | Except.ok (mantissa, fracCount, afterFrac) =>
                    match afterFrac with
                    | 'e' :: afterE => Internal.parseFloatExpTail s neg mantissa (-Int.ofNat fracCount) afterE
                    | 'E' :: afterE => Internal.parseFloatExpTail s neg mantissa (-Int.ofNat fracCount) afterE
                    | [] => Except.ok (Internal.evalScientificFloat neg mantissa (-Int.ofNat fracCount))
                    | _ :: _ => Except.error (Internal.makeError NumParseErrorKind.trailingChars s)
                else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax s)
              | [] => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax s)
            | 'e' :: afterE => Internal.parseFloatExpTail s neg intVal 0 afterE
            | 'E' :: afterE => Internal.parseFloatExpTail s neg intVal 0 afterE
            | _ => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax s)) = Except.error e →
          e.message ≠ "" := by
  rcases parseFloatIntPart_spec s body with ⟨hint_m, hint_msg⟩
  cases hint : Internal.parseFloatIntPart s body with
  | error e =>
    have hint' : parseFloatIntPart body = .error e.kind := by rw [← hint_m, hint]; rfl
    simp [hint', Except.mapError, hint_msg e hint]
  | ok p =>
    have hint' : parseFloatIntPart body = .ok p := by rw [← hint_m, hint]; rfl
    rcases p with ⟨intVal, afterInt⟩
    rw [hint']
    dsimp only
    rcases afterInt with _ | ⟨a0, as0⟩
    · exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
    · by_cases ha_dot : a0 = '.'
      · subst ha_dot
        simp only
        rcases as0 with _ | ⟨d0, ds0⟩
        · exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
        · by_cases hdU : d0 = '_'
          · subst hdU; exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
          · have ha1 :
                (match d0 :: ds0 with
                  | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore s)
                  | c :: rest =>
                    if Internal.isDecDigit c then
                      match Internal.scanDecFloatDigits s (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest with
                      | .error e => .error e
                      | .ok (mantissa, fracCount, afterFrac) =>
                        match afterFrac with
                        | 'e' :: afterE => Internal.parseFloatExpTail s neg mantissa (-Int.ofNat fracCount) afterE
                        | 'E' :: afterE => Internal.parseFloatExpTail s neg mantissa (-Int.ofNat fracCount) afterE
                        | [] => .ok (Internal.evalScientificFloat neg mantissa (-Int.ofNat fracCount))
                        | _ :: _ => .error (Internal.makeError NumParseErrorKind.trailingChars s)
                    else .error (Internal.makeError NumParseErrorKind.invalidSyntax s)
                  | [] => .error (Internal.makeError NumParseErrorKind.invalidSyntax s)) =
                (if isDecDigit d0 then
                  match Internal.scanDecFloatDigits s (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 with
                  | Except.error e => Except.error e
                  | Except.ok (mantissa, fracCount, afterFrac) =>
                    match afterFrac with
                    | 'e' :: afterE => Internal.parseFloatExpTail s neg mantissa (-Int.ofNat fracCount) afterE
                    | 'E' :: afterE => Internal.parseFloatExpTail s neg mantissa (-Int.ofNat fracCount) afterE
                    | [] => Except.ok (Internal.evalScientificFloat neg mantissa (-Int.ofNat fracCount))
                    | _ :: _ => Except.error (Internal.makeError NumParseErrorKind.trailingChars s)
                else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax s)) := by
              split <;> first | (rename_i heq; cases heq; rfl) | (rename_i h; cases h; try contradiction)
            have ha2 :
                (match d0 :: ds0 with
                  | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
                  | c :: rest =>
                    if isDecDigit c then
                      match consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest with
                      | .error k => .error k
                      | .ok (mantissa, fracCount, afterFrac) =>
                        match afterFrac with
                        | 'e' :: afterE =>
                          match parseFloatExpPart afterE with
                          | .error k => .error k
                          | .ok (expVal, afterExp) =>
                            if afterExp.isEmpty then .ok (evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                            else .error NumParseErrorKind.trailingChars
                        | 'E' :: afterE =>
                          match parseFloatExpPart afterE with
                          | .error k => .error k
                          | .ok (expVal, afterExp) =>
                            if afterExp.isEmpty then .ok (evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                            else .error NumParseErrorKind.trailingChars
                        | [] => .ok (evalFloat neg mantissa (-Int.ofNat fracCount))
                        | _ :: _ => .error NumParseErrorKind.trailingChars
                    else .error NumParseErrorKind.invalidSyntax
                  | [] => .error NumParseErrorKind.invalidSyntax) =
                (if isDecDigit d0 then
                  match consumeDecFloatDigits (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 with
                  | Except.error k => Except.error k
                  | Except.ok (mantissa, fracCount, afterFrac) =>
                    match afterFrac with
                    | 'e' :: afterE =>
                      match parseFloatExpPart afterE with
                      | Except.error k => Except.error k
                      | Except.ok (expVal, afterExp) =>
                        if afterExp.isEmpty then Except.ok (evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                        else Except.error NumParseErrorKind.trailingChars
                    | 'E' :: afterE =>
                      match parseFloatExpPart afterE with
                      | Except.error k => Except.error k
                      | Except.ok (expVal, afterExp) =>
                        if afterExp.isEmpty then Except.ok (evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                        else Except.error NumParseErrorKind.trailingChars
                    | [] => Except.ok (evalFloat neg mantissa (-Int.ofNat fracCount))
                    | _ :: _ => Except.error NumParseErrorKind.trailingChars
                else Except.error NumParseErrorKind.invalidSyntax) := by
              split <;> first | (rename_i heq; cases heq; rfl) | (rename_i h; cases h; try contradiction)
            rw [ha1, ha2]
            by_cases hdec : isDecDigit d0
            · simp only [hdec, ↓reduceIte]
              have hsm := scanDecFloatDigits_mapError s (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0
              have hsmsg := scanDecFloatDigits_msg s (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0
              cases hs : Internal.scanDecFloatDigits s (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 with
              | error e =>
                have hs' : consumeDecFloatDigits (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 = .error e.kind := by
                  rw [← hsm, hs]; rfl
                rw [hs']
                exact ⟨rfl, fun _ h => by cases h; exact hsmsg e hs⟩
              | ok q =>
                have hs' : consumeDecFloatDigits (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 = .ok q := by
                  rw [← hsm, hs]; rfl
                rw [hs']
                dsimp only
                rcases q with ⟨mantissa, fracCount, afterFrac⟩
                rcases afterFrac with _ | ⟨f0, fs0⟩
                · exact ⟨rfl, fun e h => by cases h⟩
                · by_cases hf_e : f0 = 'e'
                  · subst hf_e
                    simp only [Int.sub_eq_add_neg]
                    rcases parseFloatExpTail_spec s neg mantissa (-Int.ofNat fracCount) fs0 with ⟨hm, hmsg⟩
                    refine ⟨?_, hmsg⟩
                    rw [hm]
                    cases parseFloatExpPart fs0 <;> rfl
                  · by_cases hf_E : f0 = 'E'
                    · subst hf_E
                      simp only [Int.sub_eq_add_neg]
                      rcases parseFloatExpTail_spec s neg mantissa (-Int.ofNat fracCount) fs0 with ⟨hm, hmsg⟩
                      refine ⟨?_, hmsg⟩
                      rw [hm]
                      cases parseFloatExpPart fs0 <;> rfl
                    · split
                      · rename_i h; exact absurd (List.cons.inj h).1 hf_e
                      · rename_i h; exact absurd (List.cons.inj h).1 hf_E
                      · rename_i h; cases h
                      · exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
            · simp [hdec, mapError_makeError, makeError_msg_ne_empty]
      · by_cases ha_e : a0 = 'e'
        · subst ha_e
          simp only
          rcases parseFloatExpTail_spec s neg intVal 0 as0 with ⟨hm, hmsg⟩
          refine ⟨?_, hmsg⟩
          rw [hm]
          cases parseFloatExpPart as0 with
          | error k => rfl
          | ok r => simp [Int.add_zero]
        · by_cases ha_E : a0 = 'E'
          · subst ha_E
            simp only
            rcases parseFloatExpTail_spec s neg intVal 0 as0 with ⟨hm, hmsg⟩
            refine ⟨?_, hmsg⟩
            rw [hm]
            cases parseFloatExpPart as0 with
            | error k => rfl
            | ok r => simp [Int.add_zero]
          · split
            · rename_i h; exact absurd (List.cons.inj h).1 ha_dot
            · rename_i h; exact absurd (List.cons.inj h).1 ha_e
            · rename_i h; exact absurd (List.cons.inj h).1 ha_E
            · exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩

local macro "solve_exp_tail_map" s:term "," afterE:term : tactic =>
  `(tactic| (
    try unfold Internal.parseFloatExpTail
    have hp := (parseFloatExpPart_spec $s $afterE).1
    cases hp_i : Internal.parseFloatExpPart $s $afterE with
    | error e =>
      have hp_m : parseFloatExpPart $afterE = .error e.kind := by rw [← hp, hp_i]; rfl
      simp [hp_i, hp_m, Except.mapError]
    | ok r =>
      have hp_m : parseFloatExpPart $afterE = .ok r := by rw [← hp, hp_i]; rfl
      rcases r with ⟨expVal, afterExp⟩
      rcases afterExp with _ | ⟨_, _⟩ <;>
        simp [hp_i, hp_m, Except.mapError, mapError_makeError, Internal.makeError,
          Internal.evalScientificFloat, evalFloat, evalFloatModel, Int.sub_eq_add_neg]))

local macro "solve_after_int_map" s:term "," body:term : tactic =>
  `(tactic| (
    have hpi := parseFloatIntPart_spec $s $body
    cases hpi_impl : Internal.parseFloatIntPart $s $body with
    | error e =>
      have hpi_m : parseFloatIntPart $body = .error e.kind := by rw [← hpi.1, hpi_impl]; rfl
      simp [hpi_m, Except.mapError]
    | ok r =>
      have hpi_m : parseFloatIntPart $body = .ok r := by rw [← hpi.1, hpi_impl]; rfl
      try contradiction
      all_goals (
      rcases r with ⟨intVal, afterInt⟩
      simp only [hpi_m]
      rcases afterInt with _ | ⟨a0, as0⟩
      · rfl
      · by_cases ha_dot : a0 = '.'
        · subst ha_dot
          simp only []
          rcases as0 with _ | ⟨d0, ds0⟩
          · rfl
          · by_cases hd_u : d0 = '_'
            · subst hd_u; rfl
            · split <;> first
                | contradiction
                | (rename_i h; exact absurd (List.cons.inj h).1 hd_u)
                | (rename_i h; rcases List.cons.inj h with ⟨hc_eq, hr_eq⟩; rw [← hc_eq, ← hr_eq])
              symm
              split <;> first
                | contradiction
                | (rename_i h; exact absurd (List.cons.inj h).1 hd_u)
                | (rename_i h; rcases List.cons.inj h with ⟨hc_eq, hr_eq⟩; rw [← hc_eq, ← hr_eq])
              symm
              rw [isDecDigit_eq d0]
              by_cases hdec : isDecDigit d0
              · simp only [hdec, ↓reduceIte]
                have hsm := scanDecFloatDigits_mapError $s (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0
                cases hs : Internal.scanDecFloatDigits $s (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 with
                | error e =>
                  have hs' : consumeDecFloatDigits (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 = .error e.kind := by
                    rw [← hsm, hs]; rfl
                  dsimp only; rw [hs']; rfl
                | ok q =>
                  have hs' : consumeDecFloatDigits (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 = .ok q := by
                    rw [← hsm, hs]; rfl
                  rcases q with ⟨mantissa, fracCount, afterFrac⟩
                  dsimp only; rw [hs']; dsimp only
                  rcases afterFrac with _ | ⟨f0, fs0⟩
                  · simp [Except.mapError, Internal.evalScientificFloat, evalFloat, evalFloatModel]
                  · by_cases hf_e : f0 = 'e'
                    · subst hf_e
                      solve_exp_tail_map $s, fs0
                    · by_cases hf_E : f0 = 'E'
                      · subst hf_E
                        solve_exp_tail_map $s, fs0
                      · split
                        · rename_i h; exact absurd (List.cons.inj h).1 hf_e
                        · rename_i h; exact absurd (List.cons.inj h).1 hf_E
                        · rename_i h; cases h
                        · symm; split
                          · rename_i h; exact absurd (List.cons.inj h).1 hf_e
                          · rename_i h; exact absurd (List.cons.inj h).1 hf_E
                          · rename_i h; cases h
                          · rfl
              · simp [hdec, mapError_makeError]
        · by_cases ha_e : a0 = 'e'
          · subst ha_e
            solve_exp_tail_map $s, as0
          · by_cases ha_E : a0 = 'E'
            · subst ha_E
              solve_exp_tail_map $s, as0
            · split
              · rename_i h; exact absurd (List.cons.inj h).1 ha_dot
              · rename_i h; exact absurd (List.cons.inj h).1 ha_e
              · rename_i h; exact absurd (List.cons.inj h).1 ha_E
              · symm; split
                · rename_i h; exact absurd (List.cons.inj h).1 ha_dot
                · rename_i h; exact absurd (List.cons.inj h).1 ha_e
                · rename_i h; exact absurd (List.cons.inj h).1 ha_E
                · rfl)))

local macro "solve_after_int_msg" s:term "," neg:term "," body:term : tactic =>
  `(tactic| (
    intro e he
    try simp only [] at he
    split at he
    · rename_i e' heq; cases he; exact (parseFloatIntPart_spec $s $body).2 e heq
    · split at he
      · split at he
        · cases he; exact makeError_msg_ne_empty _ _
        · split at he
          · split at he
            · cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›
            · split at he
              · exact (parseFloatExpTail_spec $s $neg _ _ _).2 e he
              · exact (parseFloatExpTail_spec $s $neg _ _ _).2 e he
              · cases he
              · cases he; exact makeError_msg_ne_empty _ _
          · cases he; exact makeError_msg_ne_empty _ _
        · cases he; exact makeError_msg_ne_empty _ _
      · exact (parseFloatExpTail_spec $s $neg _ 0 _).2 e he
      · exact (parseFloatExpTail_spec $s $neg _ 0 _).2 e he
      · cases he; exact makeError_msg_ne_empty _ _))

private theorem parseFloat_mapError (s : String) :
    (Internal.parseFloat s).mapError (·.kind) = parseFloatModel s := by
  unfold Internal.parseFloat parseFloatModel
  rcases hcs : s.toList with _ | ⟨c0, cs0⟩
  · rfl
  · by_cases hc0 : c0 = '+'
    · subst hc0
      unfold Internal.parseFloatChars parseFloatModelChars
      simp only []
      rcases cs0 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, brest⟩⟩⟩
      · solve_after_int_map s, []
      · solve_after_int_map s, [b0]
      · solve_after_int_map s, [b0, b1]
      · split
        · rename_i rest h
          have h' : b0 :: b1 :: b2 :: brest = 'i' :: 'n' :: 'f' :: rest := by simpa using h
          rw [h']; rcases rest with _ | ⟨_, _⟩ <;> first | rfl | exact mapError_makeError _ _
        · rename_i rest h
          have h' : b0 :: b1 :: b2 :: brest = 'n' :: 'a' :: 'n' :: rest := by simpa using h
          rw [h']; rcases rest with _ | ⟨_, _⟩ <;> first | rfl | exact mapError_makeError _ _
        · rename_i hnot1 hnot2
          symm; split
          · rename_i rest h; exact False.elim (hnot1 rest (by simpa using h))
          · rename_i rest h; exact False.elim (hnot2 rest (by simpa using h))
          · symm; solve_after_int_map s, (b0 :: b1 :: b2 :: brest)
    · by_cases hm0 : c0 = '-'
      · subst hm0
        unfold Internal.parseFloatChars parseFloatModelChars
        simp only []
        rcases cs0 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, brest⟩⟩⟩
        · solve_after_int_map s, []
        · solve_after_int_map s, [b0]
        · solve_after_int_map s, [b0, b1]
        · split
          · rename_i rest h
            have h' : b0 :: b1 :: b2 :: brest = 'i' :: 'n' :: 'f' :: rest := by simpa using h
            rw [h']; rcases rest with _ | ⟨_, _⟩ <;> first | rfl | exact mapError_makeError _ _
          · rename_i rest h
            have h' : b0 :: b1 :: b2 :: brest = 'n' :: 'a' :: 'n' :: rest := by simpa using h
            rw [h']; rcases rest with _ | ⟨_, _⟩ <;> first | rfl | exact mapError_makeError _ _
          · rename_i hnot1 hnot2
            symm; split
            · rename_i rest h; exact False.elim (hnot1 rest (by simpa using h))
            · rename_i rest h; exact False.elim (hnot2 rest (by simpa using h))
            · symm; solve_after_int_map s, (b0 :: b1 :: b2 :: brest)
      · unfold Internal.parseFloatChars parseFloatModelChars
        dsimp only
        split
        · rename_i rest h
          split at h
          · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
          · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
          · rcases List.cons.inj h with ⟨rfl, rfl⟩
            symm; split
            · rename_i rest2 h2
              split at h2
              · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
              · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
              · rcases List.cons.inj h2 with ⟨_, h2b⟩
                have h2c : rest = rest2 := by simpa using h2b
                subst h2c
                rcases rest with _ | ⟨_, _⟩ <;> rfl
            · rename_i rest2 h2
              split at h2
              · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
              · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
              · cases h2
            · rename_i hnot1 _
              exfalso; apply hnot1 rest
              simp
        · rename_i rest h
          split at h
          · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
          · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
          · rcases List.cons.inj h with ⟨rfl, rfl⟩
            symm; split
            · rename_i rest2 h2
              split at h2
              · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
              · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
              · cases h2
            · rename_i rest2 h2
              split at h2
              · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
              · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
              · rcases List.cons.inj h2 with ⟨_, h2b⟩
                have h2c : rest = rest2 := by simpa using h2b
                subst h2c
                rcases rest with _ | ⟨_, _⟩ <;> rfl
            · rename_i _ hnot2
              exfalso; apply hnot2 rest
              simp
        · rename_i hnot1 hnot2
          symm
          split
          · rename_i rest h
            exfalso; apply hnot1 rest
            split
            · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
            · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
            · split at h
              · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
              · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
              · exact h
          · rename_i rest h
            exfalso; apply hnot2 rest
            split
            · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
            · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
            · split at h
              · rename_i heq; exact absurd (List.cons.inj heq).1 hc0
              · rename_i heq; exact absurd (List.cons.inj heq).1 hm0
              · exact h
          · symm
            split
            · rename_i e' heq
              split at heq
              · rename_i h; exact absurd (List.cons.inj h).1 hc0
              · rename_i h; exact absurd (List.cons.inj h).1 hm0
              · have hpi := parseFloatIntPart_spec s (c0 :: cs0)
                have hpi_m : parseFloatIntPart (c0 :: cs0) = .error e'.kind := by rw [← hpi.1, heq]; rfl
                symm; split
                · rename_i e2 heq2
                  split at heq2
                  · rename_i h; exact absurd (List.cons.inj h).1 hc0
                  · rename_i h; exact absurd (List.cons.inj h).1 hm0
                  · rw [hpi_m] at heq2; cases heq2; rfl
                · rename_i intVal afterInt heq2
                  split at heq2
                  · rename_i h; exact absurd (List.cons.inj h).1 hc0
                  · rename_i h; exact absurd (List.cons.inj h).1 hm0
                  · rw [hpi_m] at heq2; cases heq2
            · rename_i intVal afterInt heq
              split at heq
              · rename_i h; exact absurd (List.cons.inj h).1 hc0
              · rename_i h; exact absurd (List.cons.inj h).1 hm0
              · have hpi := parseFloatIntPart_spec s (c0 :: cs0)
                have hpi_m : parseFloatIntPart (c0 :: cs0) = .ok (intVal, afterInt) := by rw [← hpi.1, heq]; rfl
                symm; split
                · rename_i e2 heq2
                  split at heq2
                  · rename_i h; exact absurd (List.cons.inj h).1 hc0
                  · rename_i h; exact absurd (List.cons.inj h).1 hm0
                  · rw [hpi_m] at heq2; cases heq2
                · rename_i intVal2 afterInt2 heq2
                  split at heq2
                  · rename_i h; exact absurd (List.cons.inj h).1 hc0
                  · rename_i h; exact absurd (List.cons.inj h).1 hm0
                  · rw [hpi_m] at heq2
                    rcases Except.ok.inj heq2 with hprod
                    rcases Prod.mk.inj hprod with ⟨rfl, rfl⟩
                    symm
                    rcases afterInt with _ | ⟨a0, as0⟩
                    · rfl
                    · by_cases ha_dot : a0 = '.'
                      · subst ha_dot
                        simp only []
                        rcases as0 with _ | ⟨d0, ds0⟩
                        · rfl
                        · by_cases hd_u : d0 = '_'
                          · subst hd_u; rfl
                          · split <;> first
                              | contradiction
                              | (rename_i h; exact absurd (List.cons.inj h).1 hd_u)
                              | (rename_i h; rcases List.cons.inj h with ⟨hc_eq, hr_eq⟩; rw [← hc_eq, ← hr_eq])
                            symm
                            split <;> first
                              | contradiction
                              | (rename_i h; exact absurd (List.cons.inj h).1 hd_u)
                              | (rename_i h; rcases List.cons.inj h with ⟨hc_eq, hr_eq⟩; rw [← hc_eq, ← hr_eq])
                            symm
                            rw [isDecDigit_eq d0]
                            by_cases hdec : isDecDigit d0
                            · simp only [hdec, ↓reduceIte]
                              have hsm := scanDecFloatDigits_mapError s (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0
                              cases hs : Internal.scanDecFloatDigits s (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 with
                              | error e =>
                                have hs' : consumeDecFloatDigits (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 = .error e.kind := by
                                  rw [← hsm, hs]; rfl
                                dsimp only; rw [hs']; rfl
                              | ok q =>
                                have hs' : consumeDecFloatDigits (intVal * 10 + (d0.toNat - '0'.toNat)) 1 ds0 = .ok q := by
                                  rw [← hsm, hs]; rfl
                                rcases q with ⟨mantissa, fracCount, afterFrac⟩
                                dsimp only; rw [hs']; dsimp only
                                rcases afterFrac with _ | ⟨f0, fs0⟩
                                · simp [Except.mapError, Internal.evalScientificFloat, evalFloat, evalFloatModel]
                                · by_cases hf_e : f0 = 'e'
                                  · subst hf_e
                                    simp only []
                                    solve_exp_tail_map s, fs0
                                    try (split <;> first
                                      | (rename_i h; exact absurd (List.cons.inj h).1 hc0)
                                      | (rename_i h; exact absurd (List.cons.inj h).1 hm0)
                                      | rfl)
                                  · by_cases hf_E : f0 = 'E'
                                    · subst hf_E
                                      simp only []
                                      solve_exp_tail_map s, fs0
                                      try (split <;> first
                                        | (rename_i h; exact absurd (List.cons.inj h).1 hc0)
                                        | (rename_i h; exact absurd (List.cons.inj h).1 hm0)
                                        | rfl)
                                    · split
                                      · rename_i h; exact absurd (List.cons.inj h).1 hf_e
                                      · rename_i h; exact absurd (List.cons.inj h).1 hf_E
                                      · rename_i h; cases h
                                      · symm; split
                                        · rename_i h; exact absurd (List.cons.inj h).1 hf_e
                                        · rename_i h; exact absurd (List.cons.inj h).1 hf_E
                                        · rename_i h; cases h
                                        · rfl
                            · simp [hdec, mapError_makeError]
                      · by_cases ha_e : a0 = 'e'
                        · subst ha_e
                          simp only []
                          solve_exp_tail_map s, as0
                          try (split <;> first
                            | (rename_i h; exact absurd (List.cons.inj h).1 hc0)
                            | (rename_i h; exact absurd (List.cons.inj h).1 hm0)
                            | rfl)
                        · by_cases ha_E : a0 = 'E'
                          · subst ha_E
                            simp only []
                            solve_exp_tail_map s, as0
                            try (split <;> first
                              | (rename_i h; exact absurd (List.cons.inj h).1 hc0)
                              | (rename_i h; exact absurd (List.cons.inj h).1 hm0)
                              | rfl)
                          · split
                            · rename_i h; exact absurd (List.cons.inj h).1 ha_dot
                            · rename_i h; exact absurd (List.cons.inj h).1 ha_e
                            · rename_i h; exact absurd (List.cons.inj h).1 ha_E
                            · symm; split
                              · rename_i h; exact absurd (List.cons.inj h).1 ha_dot
                              · rename_i h; exact absurd (List.cons.inj h).1 ha_e
                              · rename_i h; exact absurd (List.cons.inj h).1 ha_E
                              · rfl

private theorem parseFloat_msg (s : String) :
    ∀ e, Internal.parseFloat s = .error e → e.message ≠ "" := by
  unfold Internal.parseFloat
  rcases hcs : s.toList with _ | ⟨c0, cs0⟩
  · intro e h; cases h; exact makeError_msg_ne_empty _ _
  · by_cases hc0 : c0 = '+'
    · subst hc0
      unfold Internal.parseFloatChars
      simp only []
      rcases cs0 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, brest⟩⟩⟩
      · solve_after_int_msg s, false, []
      · solve_after_int_msg s, false, [b0]
      · solve_after_int_msg s, false, [b0, b1]
      · intro e he
        split at he
        · split at he
          · cases he
          · cases he; exact makeError_msg_ne_empty _ _
        · split at he
          · cases he
          · cases he; exact makeError_msg_ne_empty _ _
        · revert e he
          solve_after_int_msg s, false, (b0 :: b1 :: b2 :: brest)
    · by_cases hm0 : c0 = '-'
      · subst hm0
        unfold Internal.parseFloatChars
        simp only []
        rcases cs0 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, brest⟩⟩⟩
        · solve_after_int_msg s, true, []
        · solve_after_int_msg s, true, [b0]
        · solve_after_int_msg s, true, [b0, b1]
        · intro e he
          split at he
          · split at he
            · cases he
            · cases he; exact makeError_msg_ne_empty _ _
          · split at he
            · cases he
            · cases he; exact makeError_msg_ne_empty _ _
          · revert e he
            solve_after_int_msg s, true, (b0 :: b1 :: b2 :: brest)
      · intro e he
        unfold Internal.parseFloatChars at he
        dsimp only at he
        split at he
        · split at he
          · cases he
          · cases he; exact makeError_msg_ne_empty _ _
        · split at he
          · cases he
          · cases he; exact makeError_msg_ne_empty _ _
        · split at he
          · rename_i e' heq
            split at heq
            · rename_i h; exact absurd (List.cons.inj h).1 hc0
            · rename_i h; exact absurd (List.cons.inj h).1 hm0
            · cases he; exact (parseFloatIntPart_spec s (c0 :: cs0)).2 e heq
          · rename_i intVal afterInt heq
            split at heq
            · rename_i h; exact absurd (List.cons.inj h).1 hc0
            · rename_i h; exact absurd (List.cons.inj h).1 hm0
            · split at he
              · split at he
                · cases he; exact makeError_msg_ne_empty _ _
                · split at he
                  · split at he
                    · cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›
                    · split at he
                      · split at he
                        · rename_i h; exact absurd (List.cons.inj h).1 hc0
                        · rename_i h; exact absurd (List.cons.inj h).1 hm0
                        · exact (parseFloatExpTail_spec s false _ _ _).2 e he
                      · split at he
                        · rename_i h; exact absurd (List.cons.inj h).1 hc0
                        · rename_i h; exact absurd (List.cons.inj h).1 hm0
                        · exact (parseFloatExpTail_spec s false _ _ _).2 e he
                      · cases he
                      · cases he; exact makeError_msg_ne_empty _ _
                  · cases he; exact makeError_msg_ne_empty _ _
                · cases he; exact makeError_msg_ne_empty _ _
              · split at he
                · rename_i h; exact absurd (List.cons.inj h).1 hc0
                · rename_i h; exact absurd (List.cons.inj h).1 hm0
                · exact (parseFloatExpTail_spec s false intVal 0 _).2 e he
              · split at he
                · rename_i h; exact absurd (List.cons.inj h).1 hc0
                · rename_i h; exact absurd (List.cons.inj h).1 hm0
                · exact (parseFloatExpTail_spec s false intVal 0 _).2 e he
              · cases he; exact makeError_msg_ne_empty _ _

/-- Specification connecting `Internal.parseFloat` to `parseFloatModel` and non-empty error messages. -/
theorem parseFloat_spec (s : String) :
    (Internal.parseFloat s).mapError (·.kind) = parseFloatModel s ∧
      ∀ e, Internal.parseFloat s = .error e → e.message ≠ "" :=
  ⟨parseFloat_mapError s, parseFloat_msg s⟩

end LeanSwe.NumParse.Proofs
