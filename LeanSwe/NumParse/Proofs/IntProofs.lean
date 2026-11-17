import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem makeError_kind (k : NumParseErrorKind) (detail : String) :
    (Internal.makeError k detail).kind = k := rfl

private theorem errorKindLabel_ne_empty (k : NumParseErrorKind) :
    Internal.errorKindLabel k ≠ "" := by
  cases k <;> decide

/-- `Internal.makeError` always produces a non-empty message. -/
theorem makeError_msg_ne_empty (k : NumParseErrorKind) (detail : String) :
    (Internal.makeError k detail).message ≠ "" := by
  unfold Internal.makeError
  intro heq
  have hlen := congrArg String.length heq
  simp only [String.length_append] at hlen
  have h1 : (": " : String).length = 2 := rfl
  have h2 : ("" : String).length = 0 := rfl
  omega

/-- Mapping `.kind` over `Internal.makeError` yields `Except.error k`. -/
theorem mapError_makeError {α : Type} (k : NumParseErrorKind) (detail : String) :
    (Except.error (Internal.makeError k detail) : Except NumParseError α).mapError (·.kind) =
      .error k := rfl

/-- `Internal.isDecDigit` agrees with `Model.isDecDigit`. -/
theorem isDecDigit_eq (c : Char) :
    Internal.isDecDigit c = isDecDigit c := rfl

private theorem digitValue_eq_digitVal (b : NumBase) (c : Char) :
    Internal.digitValue? b.radix c = digitVal? b c := by
  cases b <;> rfl

private theorem parseBasePrefix_eq_basePrefix (c : Char) :
    Internal.parseBasePrefix? c = Option.map NumBase.radix (basePrefix? c) := by
  unfold Internal.parseBasePrefix? basePrefix?
  split <;> simp [NumBase.radix]

private theorem parseBasePrefix_isSome (c : Char) :
    (Internal.parseBasePrefix? c).isSome = (basePrefix? c).isSome := by
  rw [parseBasePrefix_eq_basePrefix]
  cases basePrefix? c <;> rfl

private theorem scanIntDigits_mapError (raw : String) (b : NumBase) (acc : Nat) (cs : List Char) :
    (Internal.scanIntDigits raw b.radix acc cs).mapError (·.kind) =
      consumeIntDigits b acc cs := by
  fun_induction Internal.scanIntDigits raw b.radix acc cs with
  | case1 _ => rfl
  | case2 acc c cs d hd ih =>
    have hd' : digitVal? b c = some d := by rw [← digitValue_eq_digitVal]; exact hd
    simpa [consumeIntDigits, hd'] using ih
  | case3 acc c cs hnone =>
    have hnone' : digitVal? b c = none := by rw [← digitValue_eq_digitVal]; exact hnone
    simp [consumeIntDigits, hnone', mapError_makeError]
  | case4 acc => rfl
  | case5 acc c cs hc1 hc2 d hd ih =>
    have hd' : digitVal? b c = some d := by rw [← digitValue_eq_digitVal]; exact hd
    by_cases hunder : c = '_'
    · subst hunder
      rcases cs with _ | ⟨c1, cs1⟩
      · exact False.elim (hc2 rfl rfl)
      · exact False.elim (hc1 c1 cs1 rfl rfl)
    · rw [consumeIntDigits.eq_4]
      · simpa [hd'] using ih
      · intro c1 cs1 heq _; exact hunder heq
      · intro heq _; exact hunder heq
  | case6 acc c cs hc1 hc2 hnone =>
    have hnone' : digitVal? b c = none := by rw [← digitValue_eq_digitVal]; exact hnone
    by_cases hunder : c = '_'
    · subst hunder
      rcases cs with _ | ⟨c1, cs1⟩
      · exact False.elim (hc2 rfl rfl)
      · exact False.elim (hc1 c1 cs1 rfl rfl)
    · rw [consumeIntDigits.eq_4]
      · simp [hnone', mapError_makeError]
      · intro c1 cs1 heq _; exact hunder heq
      · intro heq _; exact hunder heq

private theorem scanIntDigits_msg (raw : String) (radix acc : Nat) (cs : List Char)
    (e : NumParseError) :
    Internal.scanIntDigits raw radix acc cs = .error e → e.message ≠ "" := by
  fun_induction Internal.scanIntDigits raw radix acc cs with
  | case1 _ => intro h; cases h
  | case2 _ _ _ _ _ ih => exact ih
  | case3 _ _ _ _ => intro h; cases h; exact makeError_msg_ne_empty _ _
  | case4 _ => intro h; cases h; exact makeError_msg_ne_empty _ _
  | case5 _ _ _ _ _ _ _ ih => exact ih
  | case6 _ _ _ _ _ _ => intro h; cases h; exact makeError_msg_ne_empty _ _

private theorem parseDecSigned_spec (raw : String) (neg : Bool) (cs : List Char) :
    (Internal.parseDecSigned raw neg cs).mapError (·.kind) = parseDecAfterSign neg cs ∧
      ∀ e, Internal.parseDecSigned raw neg cs = .error e → e.message ≠ "" := by
  rcases cs with _ | ⟨c, cs⟩
  · exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
  · by_cases hcU : c = '_'
    · subst hcU; exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
    · by_cases hc0 : c = '0'
      · subst hc0
        unfold Internal.parseDecSigned parseDecAfterSign
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
            · simp [isDecDigit_eq, hdec, hc1u, mapError_makeError, makeError_msg_ne_empty]
      · rw [Internal.parseDecSigned.eq_5 raw neg c cs (fun h => hcU h) (fun r => hc0 r)]
        rw [parseDecAfterSign.eq_5 neg c cs (fun h => hcU h) (fun r => hc0 r)]
        have hdv_eq : Internal.digitValue? 10 c = digitVal? .dec c := digitValue_eq_digitVal .dec c
        rw [hdv_eq]
        cases hdv : digitVal? .dec c with
        | none =>
          simp only [mapError_makeError, true_and]
          intro e h; cases h; exact makeError_msg_ne_empty _ _
        | some d =>
          simp only []
          have hm := scanIntDigits_mapError raw .dec d cs
          have hmsg := scanIntDigits_msg raw 10 d cs
          cases hsc : Internal.scanIntDigits raw 10 d cs with
          | error e =>
            have hsc' : consumeIntDigits .dec d cs = .error e.kind := by
              rw [show (10 : Nat) = NumBase.dec.radix from rfl] at hsc
              rw [← hm, hsc]; rfl
            simp [hsc', hmsg e hsc, Except.mapError]
          | ok n =>
            have hsc' : consumeIntDigits .dec d cs = .ok n := by
              rw [show (10 : Nat) = NumBase.dec.radix from rfl] at hsc
              rw [← hm, hsc]; rfl
            simp [hsc', Except.mapError]

/-- Specification connecting `Internal.parseInt` to `parseIntModel` and non-empty error messages. -/
theorem parseInt_spec (s : String) :
    (Internal.parseInt s).mapError (·.kind) = parseIntModel s ∧
      ∀ e, Internal.parseInt s = .error e → e.message ≠ "" := by
  unfold Internal.parseInt parseIntModel
  rcases s.toList with _ | ⟨c0, cs0⟩
  · exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
  · by_cases hc0p : c0 = '+'
    · subst hc0p
      rcases cs0 with _ | ⟨c1, cs1⟩
      · rw [Internal.parseIntChars.eq_4 s [], parseIntModelChars.eq_4 []]
        · exact parseDecSigned_spec s false []
        · intro b r h; cases h
        · intro b r h; cases h
      · by_cases hc1z : c1 = '0'
        · subst hc1z
          rcases cs1 with _ | ⟨b, rest⟩
          · rw [Internal.parseIntChars.eq_4 s ['0'], parseIntModelChars.eq_4 ['0']]
            · exact parseDecSigned_spec s false ['0']
            · intro b r h; cases h
            · intro b r h; cases h
          · rw [Internal.parseIntChars.eq_2, parseIntModelChars.eq_2]
            rw [parseBasePrefix_isSome b]
            cases hbp : basePrefix? b with
            | some _ => simp [mapError_makeError, makeError_msg_ne_empty]
            | none => simpa [hbp] using parseDecSigned_spec s false ('0' :: b :: rest)
        · rw [Internal.parseIntChars.eq_4 s (c1 :: cs1) (fun b r h => hc1z (List.cons.inj h).1)]
          rw [parseIntModelChars.eq_4 (c1 :: cs1) (fun b r h => hc1z (List.cons.inj h).1)]
          exact parseDecSigned_spec s false (c1 :: cs1)
    · by_cases hc0m : c0 = '-'
      · subst hc0m
        rcases cs0 with _ | ⟨c1, cs1⟩
        · rw [Internal.parseIntChars.eq_5 s [], parseIntModelChars.eq_5 []]
          · exact parseDecSigned_spec s true []
          · intro b r h; cases h
          · intro b r h; cases h
        · by_cases hc1z : c1 = '0'
          · subst hc1z
            rcases cs1 with _ | ⟨b, rest⟩
            · rw [Internal.parseIntChars.eq_5 s ['0'], parseIntModelChars.eq_5 ['0']]
              · exact parseDecSigned_spec s true ['0']
              · intro b r h; cases h
              · intro b r h; cases h
            · rw [Internal.parseIntChars.eq_3, parseIntModelChars.eq_3]
              rw [parseBasePrefix_isSome b]
              cases hbp : basePrefix? b with
              | some _ => simp [mapError_makeError, makeError_msg_ne_empty]
              | none => simpa [hbp] using parseDecSigned_spec s true ('0' :: b :: rest)
          · rw [Internal.parseIntChars.eq_5 s (c1 :: cs1) (fun b r h => hc1z (List.cons.inj h).1)]
            rw [parseIntModelChars.eq_5 (c1 :: cs1) (fun b r h => hc1z (List.cons.inj h).1)]
            exact parseDecSigned_spec s true (c1 :: cs1)
      · by_cases hc0z : c0 = '0'
        · subst hc0z
          rcases cs0 with _ | ⟨b, rest⟩
          · rw [Internal.parseIntChars.eq_7 s ['0'] (fun h => by cases h) (fun b r h => by cases h) (fun b r h => by cases h) (fun r h => by cases h) (fun r h => by cases h) (fun b r h => by cases h)]
            rw [parseIntModelChars.eq_7 ['0'] (fun h => by cases h) (fun b r h => by cases h) (fun b r h => by cases h) (fun r h => by cases h) (fun r h => by cases h) (fun b r h => by cases h)]
            exact parseDecSigned_spec s false ['0']
          · rw [Internal.parseIntChars.eq_6, parseIntModelChars.eq_6]
            rw [parseBasePrefix_eq_basePrefix b]
            cases hbp : basePrefix? b with
            | none => simpa [hbp] using parseDecSigned_spec s false ('0' :: b :: rest)
            | some base =>
              rcases rest with _ | ⟨c2, cs2⟩
              · simp [mapError_makeError, makeError_msg_ne_empty]
              · by_cases hc2u : c2 = '_'
                · subst hc2u; simp [mapError_makeError, makeError_msg_ne_empty]
                · simp only [Option.map_some]
                  have ha1 :
                      (match c2 :: cs2 with
                        | [] => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax s)
                        | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore s)
                        | c :: cs =>
                          match Internal.digitValue? base.radix c with
                          | some d =>
                            match Internal.scanIntDigits s base.radix d cs with
                            | .ok n => .ok (Int.ofNat n)
                            | .error e => .error e
                          | none => .error (Internal.makeError NumParseErrorKind.invalidSyntax s)) =
                      (match Internal.digitValue? base.radix c2 with
                        | some d =>
                          match Internal.scanIntDigits s base.radix d cs2 with
                          | Except.ok n => Except.ok (Int.ofNat n)
                          | Except.error e => Except.error e
                        | none => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax s)) := by
                    split <;> first | (rename_i heq; cases heq; rfl) | (rename_i h; cases h; try contradiction)
                  have ha2 :
                      (match c2 :: cs2 with
                        | [] => Except.error NumParseErrorKind.invalidSyntax
                        | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
                        | c :: cs =>
                          match digitVal? base c with
                          | some d =>
                            match consumeIntDigits base d cs with
                            | .ok n => .ok (Int.ofNat n)
                            | .error k => .error k
                          | none => .error NumParseErrorKind.invalidSyntax) =
                      (match digitVal? base c2 with
                        | some d =>
                          match consumeIntDigits base d cs2 with
                          | Except.ok n => Except.ok (Int.ofNat n)
                          | Except.error k => Except.error k
                        | none => Except.error NumParseErrorKind.invalidSyntax) := by
                    split <;> first | (rename_i heq; cases heq; rfl) | (rename_i h; cases h; try contradiction)
                  rw [digitValue_eq_digitVal base c2]
                  cases hdv : digitVal? base c2 with
                  | none => simp [mapError_makeError, makeError_msg_ne_empty]
                  | some d =>
                    have hm := scanIntDigits_mapError s base d cs2
                    have hmsg := scanIntDigits_msg s base.radix d cs2
                    cases hsc : Internal.scanIntDigits s base.radix d cs2 with
                    | error e =>
                      have hsc' : consumeIntDigits base d cs2 = .error e.kind := by
                        rw [← hm, hsc]; rfl
                      simp [hsc, hsc', Except.mapError, hmsg e hsc]
                    | ok n =>
                      have hsc' : consumeIntDigits base d cs2 = .ok n := by
                        rw [← hm, hsc]; rfl
                      simp [hsc, hsc', Except.mapError]
        · rw [Internal.parseIntChars.eq_7 s (c0 :: cs0) (fun h => by cases h) (fun b r h => hc0p (List.cons.inj h).1) (fun b r h => hc0m (List.cons.inj h).1) (fun r h => hc0p (List.cons.inj h).1) (fun r h => hc0m (List.cons.inj h).1) (fun b r h => hc0z (List.cons.inj h).1)]
          rw [parseIntModelChars.eq_7 (c0 :: cs0) (fun h => by cases h) (fun b r h => hc0p (List.cons.inj h).1) (fun b r h => hc0m (List.cons.inj h).1) (fun r h => hc0p (List.cons.inj h).1) (fun r h => hc0m (List.cons.inj h).1) (fun b r h => hc0z (List.cons.inj h).1)]
          exact parseDecSigned_spec s false (c0 :: cs0)

/-- Specification connecting `Internal.parseInt64` to `parseInt64Model` and non-empty error messages. -/
theorem parseInt64_spec (s : String) :
    (Internal.parseInt64 s).mapError (·.kind) = parseInt64Model s ∧
      ∀ e, Internal.parseInt64 s = .error e → e.message ≠ "" := by
  unfold Internal.parseInt64
  rw [parseInt64Model_eq_parseIntModel]
  rcases parseInt_spec s with ⟨hm, hmsg⟩
  cases hpi : Internal.parseInt s with
  | error e =>
    have hpm : parseIntModel s = .error e.kind := by rw [← hm, hpi]; rfl
    simp [hpm, Except.mapError, hmsg e hpi]
  | ok n =>
    have hpm : parseIntModel s = .ok n := by rw [← hm, hpi]; rfl
    rw [hpm]
    by_cases hlo : -9223372036854775808 ≤ n <;> by_cases hhi : n ≤ 9223372036854775807
    · have hb : (Internal.minInt64Bound ≤ n && n ≤ Internal.maxInt64Bound) = true := by
        simp [Internal.minInt64Bound, Internal.maxInt64Bound, hlo, hhi]
      have hr : inInt64Range n = true := by simp [inInt64Range, int64MinInt, int64MaxInt, hlo, hhi]
      simp [hb, hr, Except.mapError]
    · have hb : (Internal.minInt64Bound ≤ n && n ≤ Internal.maxInt64Bound) = false := by
        simp [Internal.minInt64Bound, Internal.maxInt64Bound, hlo, hhi]
      have hr : inInt64Range n = false := by simp [inInt64Range, int64MinInt, int64MaxInt, hlo, hhi]
      simp [hb, hr, mapError_makeError, makeError_msg_ne_empty]
    · have hb : (Internal.minInt64Bound ≤ n && n ≤ Internal.maxInt64Bound) = false := by
        simp [Internal.minInt64Bound, Internal.maxInt64Bound, hlo, hhi]
      have hr : inInt64Range n = false := by simp [inInt64Range, int64MinInt, int64MaxInt, hlo, hhi]
      simp [hb, hr, mapError_makeError, makeError_msg_ne_empty]
    · have hb : (Internal.minInt64Bound ≤ n && n ≤ Internal.maxInt64Bound) = false := by
        simp [Internal.minInt64Bound, Internal.maxInt64Bound, hlo, hhi]
      have hr : inInt64Range n = false := by simp [inInt64Range, int64MinInt, int64MaxInt, hlo, hhi]
      simp [hb, hr, mapError_makeError, makeError_msg_ne_empty]

private theorem char_ofNat_decDigit (d : Nat) (hd : d < 10) :
    isDecDigit (Char.ofNat ('0'.toNat + d)) = true ∧
      (Char.ofNat ('0'.toNat + d)).toNat - '0'.toNat = d ∧
      Char.ofNat ('0'.toNat + d) ≠ '_' := by
  match d with
  | 0 => exact by decide
  | 1 => exact by decide
  | 2 => exact by decide
  | 3 => exact by decide
  | 4 => exact by decide
  | 5 => exact by decide
  | 6 => exact by decide
  | 7 => exact by decide
  | 8 => exact by decide
  | 9 => exact by decide
  | _ + 10 => omega

private theorem decDigit_ne_underscore (c : Char) (hc : isDecDigit c = true) : c ≠ '_' := by
  intro h; subst h; revert hc; decide

private theorem decDigit_digitVal (c : Char) (hc : isDecDigit c = true) :
    digitVal? .dec c = some (c.toNat - '0'.toNat) := by
  simp only [digitVal?, isDecDigit] at hc ⊢
  simp [hc]

private theorem consumeIntDigits_dec_digits (cs : List Char)
    (hdigits : ∀ c ∈ cs, isDecDigit c = true) (acc : Nat) :
    consumeIntDigits .dec acc cs =
      .ok (evalDigitsAux 10 acc (cs.map (fun c => c.toNat - '0'.toNat))) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    have hc : isDecDigit c = true := hdigits c (by simp)
    have hne : c ≠ '_' := decDigit_ne_underscore c hc
    have hdv := decDigit_digitVal c hc
    have ih' := ih (fun x hx => hdigits x (by simp [hx])) (acc * 10 + (c.toNat - '0'.toNat))
    rw [consumeIntDigits.eq_4]
    · simpa [NumBase.radix, hdv, evalDigitsAux] using ih'
    · intro c1 cs1 heq _; exact hne heq
    · intro heq _; exact hne heq

private theorem evalDigitsAux_shift (d0 : Nat) (ds : List Nat) :
    evalDigitsAux 10 d0 ds = d0 * 10 ^ ds.length + evalDigitsAux 10 0 ds := by
  induction ds generalizing d0 with
  | nil => simp [evalDigitsAux]
  | cons d ds ih =>
    simp only [evalDigitsAux, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (d0 * 10 + d), ih d]
    have hpow : 10 ^ (ds.length + 1) = 10 * 10 ^ ds.length := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, Nat.right_distrib, ← Nat.mul_assoc]
    omega

private theorem natToDecCharsPos_spec (n : Nat) (hn : 0 < n) (acc : List Char)
    (hacc : ∀ c ∈ acc, isDecDigit c = true) :
    ∃ c rest, Internal.natToDecCharsPos n acc = c :: rest ∧
      isDecDigit c = true ∧ c ≠ '0' ∧ (∀ r ∈ rest, isDecDigit r = true) ∧
      evalDigits 10 ((c :: rest).map (fun x => x.toNat - '0'.toNat)) =
        n * 10 ^ acc.length + evalDigits 10 (acc.map (fun x => x.toNat - '0'.toNat)) := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    rcases n with _ | m
    · omega
    · unfold Internal.natToDecCharsPos
      dsimp only
      let q := (m + 1) / 10
      let r := (m + 1) % 10
      have hr : r < 10 := Nat.mod_lt _ (by decide)
      rcases char_ofNat_decDigit r hr with ⟨hdig, hval, _⟩
      let ch := Char.ofNat ('0'.toNat + r)
      have hacc' : ∀ c ∈ ch :: acc, isDecDigit c = true := by
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hmem
        · exact hdig
        · exact hacc c hmem
      by_cases hq0 : q = 0
      · have hdm : r = m + 1 := by omega
        have hch_ne : ch ≠ '0' := by
          intro heq
          have h0 : ch.toNat - '0'.toNat = 0 := by rw [heq]; rfl
          dsimp only [ch] at h0
          rw [hval] at h0
          omega
        refine ⟨ch, acc, ?_, hdig, hch_ne, hacc, ?_⟩
        · unfold Internal.natToDecCharsPos
          dsimp only
          have hq0' : (m + 1) / 10 = 0 := hq0
          rw [hq0']
        · simp only [evalDigits, List.map_cons, evalDigitsAux, Nat.zero_mul, Nat.zero_add]
          rw [evalDigitsAux_shift, List.length_map, hval, hdm]
      · have hq_lt : q < m + 1 := Nat.div_lt_self (by omega) (by decide)
        have hq_pos : 0 < q := Nat.pos_of_ne_zero hq0
        rcases ih q hq_lt hq_pos (ch :: acc) hacc' with ⟨c, rest, hrec, hc_dig, hc_ne, hrest_dig, heval⟩
        refine ⟨c, rest, ?_, hc_dig, hc_ne, hrest_dig, ?_⟩
        · simpa [q, r, ch] using hrec
        · rw [heval]
          simp only [List.length_cons, evalDigits, List.map_cons, evalDigitsAux, Nat.zero_mul, Nat.zero_add]
          rw [evalDigitsAux_shift, List.length_map, hval]
          have hpow : 10 ^ (acc.length + 1) = 10 * 10 ^ acc.length := by rw [Nat.pow_succ, Nat.mul_comm]
          have hdivmod : q * 10 + r = m + 1 := by omega
          rw [hpow, ← Nat.mul_assoc, ← Nat.add_assoc, ← Nat.right_distrib, hdivmod]

private theorem parseDecAfterSign_dec_pos (neg : Bool) (c : Char) (rest : List Char)
    (hc : isDecDigit c = true) (hne0 : c ≠ '0')
    (hrest : ∀ r ∈ rest, isDecDigit r = true) :
    parseDecAfterSign neg (c :: rest) =
      let v := evalDigits 10 ((c :: rest).map (fun x => x.toNat - '0'.toNat))
      .ok (if neg then -Int.ofNat v else Int.ofNat v) := by
  have hcU : c ≠ '_' := decDigit_ne_underscore c hc
  have hdv := decDigit_digitVal c hc
  have hcon := consumeIntDigits_dec_digits rest hrest (c.toNat - '0'.toNat)
  rw [parseDecAfterSign.eq_5]
  · simp only [hdv]
    rw [hcon]
    simp only [evalDigits, evalDigitsAux, Nat.zero_mul, Nat.zero_add, List.map_cons]
  · intro heq; exact hcU heq
  · intro heq; exact hne0 heq

private theorem list_not_mem_underscore_of_dec (cs : List Char)
    (hcs : ∀ c ∈ cs, isDecDigit c = true) : '_' ∉ cs := by
  intro hmem
  exact decDigit_ne_underscore '_' (hcs '_' hmem) rfl

/-- `parseIntModel` round-trips `Internal.formatInt` without underscores. -/
theorem parseIntModel_formatInt (n : Int) :
    !(Internal.formatInt n).contains '_' ∧ parseIntModel (Internal.formatInt n) = .ok n := by
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      refine ⟨?_, rfl⟩
      simp only [Internal.formatInt, Internal.formatIntChars, String.contains_char_eq, String.toList_ofList]
      decide
    | succ m =>
      have hm_pos : 0 < m + 1 := by omega
      rcases natToDecCharsPos_spec (m + 1) hm_pos [] (fun _ h => nomatch h) with
        ⟨c, rest, hchars, hc_dig, hc_ne0, hrest_dig, heval⟩
      have hfmt : Internal.formatInt (Int.ofNat (m + 1)) = String.ofList (c :: rest) := by
        simp [Internal.formatInt, Internal.formatIntChars, hchars]
      rw [hfmt]
      refine ⟨?_, ?_⟩
      · have hnot : '_' ∉ c :: rest := by
          intro hm
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact decDigit_ne_underscore '_' hc_dig rfl
          · exact list_not_mem_underscore_of_dec rest hrest_dig hm'
        simp [String.contains_char_eq, String.toList_ofList, hnot]
      · simp only [parseIntModel, String.toList_ofList]
        have hpd := parseDecAfterSign_dec_pos false c rest hc_dig hc_ne0 hrest_dig
        have hval : evalDigits 10 ((c :: rest).map (fun x => x.toNat - '0'.toNat)) = m + 1 := by
          simpa [evalDigits, evalDigitsAux] using heval
        rw [hval] at hpd
        dsimp only at hpd
        simp only [Bool.false_eq_true, ↓reduceIte] at hpd
        rw [parseIntModelChars.eq_7]
        · exact hpd
        · intro heq; cases heq
        · intro b rest' heq; cases heq; revert hc_dig; decide
        · intro b rest' heq; cases heq; revert hc_dig; decide
        · intro rest' heq; cases heq; revert hc_dig; decide
        · intro rest' heq; cases heq; revert hc_dig; decide
        · intro b rest' heq; cases heq; exact hc_ne0 rfl
  | negSucc m =>
    have hm_pos : 0 < m + 1 := by omega
    rcases natToDecCharsPos_spec (m + 1) hm_pos [] (fun _ h => nomatch h) with
      ⟨c, rest, hchars, hc_dig, hc_ne0, hrest_dig, heval⟩
    have hfmt : Internal.formatInt (Int.negSucc m) = String.ofList ('-' :: c :: rest) := by
      simp [Internal.formatInt, Internal.formatIntChars, hchars]
    rw [hfmt]
    refine ⟨?_, ?_⟩
    · have hnot : '_' ∉ '-' :: c :: rest := by
        intro hm
        rcases List.mem_cons.mp hm with h_ | hm1
        · revert h_; decide
        · rcases List.mem_cons.mp hm1 with rfl | hm2
          · exact decDigit_ne_underscore '_' hc_dig rfl
          · exact list_not_mem_underscore_of_dec rest hrest_dig hm2
      simp [String.contains_char_eq, String.toList_ofList, hnot]
    · simp only [parseIntModel, String.toList_ofList]
      have hpd := parseDecAfterSign_dec_pos true c rest hc_dig hc_ne0 hrest_dig
      have hval : evalDigits 10 ((c :: rest).map (fun x => x.toNat - '0'.toNat)) = m + 1 := by
        simpa [evalDigits, evalDigitsAux] using heval
      rw [hval] at hpd
      dsimp only at hpd
      simp only [↓reduceIte] at hpd
      have hneg : -Int.ofNat (m + 1) = Int.negSucc m := rfl
      rw [hneg] at hpd
      rw [parseIntModelChars.eq_5]
      · exact hpd
      · intro b rest' heq; cases heq; exact hc_ne0 rfl

end LeanSwe.NumParse.Proofs
