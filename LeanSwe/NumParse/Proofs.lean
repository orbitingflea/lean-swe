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

private theorem makeError_msg_ne_empty (k : NumParseErrorKind) (detail : String) :
    (Internal.makeError k detail).message ≠ "" := by
  unfold Internal.makeError
  intro heq
  have hlen := congrArg String.length heq
  simp only [String.length_append] at hlen
  have h1 : (": " : String).length = 2 := rfl
  have h2 : ("" : String).length = 0 := rfl
  omega

private theorem mapError_makeError {α : Type} (k : NumParseErrorKind) (detail : String) :
    (Except.error (Internal.makeError k detail) : Except NumParseError α).mapError (·.kind) =
      .error k := rfl

private theorem isDecDigit_eq (c : Char) :
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

private theorem parseInt_spec (s : String) :
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

private theorem parseInt64_spec (s : String) :
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

private theorem parseIntModel_formatInt (n : Int) :
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

private theorem scanDecFloatDigits_mapError (raw : String) (acc count : Nat) (cs : List Char) :
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

private theorem scanDecFloatDigits_msg (raw : String) (acc count : Nat) (cs : List Char)
    (e : NumParseError) :
    Internal.scanDecFloatDigits raw acc count cs = .error e → e.message ≠ "" := by
  fun_induction Internal.scanDecFloatDigits raw acc count cs with
  | case1 _ _ => intro h; cases h
  | case2 _ _ _ _ _ ih => exact ih
  | case3 _ _ _ _ => intro h; cases h; exact makeError_msg_ne_empty _ _
  | case4 _ _ => intro h; cases h; exact makeError_msg_ne_empty _ _
  | case5 _ _ _ _ _ _ _ ih => exact ih
  | case6 _ _ _ _ _ _ => intro h; cases h

private theorem parseFloatIntPart_spec (raw : String) (cs : List Char) :
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

private theorem parseFloatExpPart_spec_aux (raw : String) (expNeg : Bool)
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

private theorem parseFloatExpPart_spec (raw : String) (cs : List Char) :
    (Internal.parseFloatExpPart raw cs).mapError (·.kind) = parseFloatExpPart cs ∧
      ∀ e, Internal.parseFloatExpPart raw cs = .error e → e.message ≠ "" :=
  ⟨parseFloatExpPart_mapError raw cs, parseFloatExpPart_msg raw cs⟩

private theorem parseFloatExpTail_spec (raw : String) (neg : Bool) (mantissa : Nat)
    (fracAdj : Int) (afterE : List Char) :
    (Internal.parseFloatExpTail raw neg mantissa fracAdj afterE).mapError (·.kind) =
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
                    simpa [Int.sub_eq_add_neg] using
                      parseFloatExpTail_spec s neg mantissa (-Int.ofNat fracCount) fs0
                  · by_cases hf_E : f0 = 'E'
                    · subst hf_E
                      simpa [Int.sub_eq_add_neg] using
                        parseFloatExpTail_spec s neg mantissa (-Int.ofNat fracCount) fs0
                    · split
                      · rename_i h; exact absurd (List.cons.inj h).1 hf_e
                      · rename_i h; exact absurd (List.cons.inj h).1 hf_E
                      · rename_i h; cases h
                      · exact ⟨rfl, fun e h => by cases h; exact makeError_msg_ne_empty _ _⟩
            · simp [hdec, mapError_makeError, makeError_msg_ne_empty]
      · by_cases ha_e : a0 = 'e'
        · subst ha_e
          simpa [Int.add_zero] using parseFloatExpTail_spec s neg intVal 0 as0
        · by_cases ha_E : a0 = 'E'
          · subst ha_E
            simpa [Int.add_zero] using parseFloatExpTail_spec s neg intVal 0 as0
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

private theorem parseFloat_spec (s : String) :
    (Internal.parseFloat s).mapError (·.kind) = parseFloatModel s ∧
      ∀ e, Internal.parseFloat s = .error e → e.message ≠ "" :=
  ⟨parseFloat_mapError s, parseFloat_msg s⟩

/-- Proof of `test_numparse_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_numparse_onError_returnsNonEmptyMessage :
    AllPass (test_numparse_onError_returnsNonEmptyMessage defaultApi) := by
  intro s
  dsimp [test_numparse_onError_returnsNonEmptyMessage, defaultApi, Internal.defaultApi,
    Bind.bind, Core.NondetTest.assert]
  have p1 : ∀ e, Internal.parseInt s = .error e → e.message ≠ "" := (parseInt_spec s).2
  have p2 : ∀ e, Internal.parseInt64 s = .error e → e.message ≠ "" := (parseInt64_spec s).2
  have p3 : ∀ e, Internal.parseFloat s = .error e → e.message ≠ "" := (parseFloat_spec s).2
  cases h1 : Internal.parseInt s <;>
    cases h2 : Internal.parseInt64 s <;>
    cases h3 : Internal.parseFloat s <;>
    dsimp only <;>
    refine ⟨?_, ?_, ?_, trivial⟩
  all_goals first | trivial | exact p1 _ h1 | exact p2 _ h2 | exact p3 _ h3

/-- Non-vacuity `CanReach` witness for `test_numparse_onError_returnsNonEmptyMessage`. -/
theorem reach_numparse_onError_returnsNonEmptyMessage :
    CanReach (test_numparse_onError_returnsNonEmptyMessage defaultApi) :=
  ⟨"", proof_numparse_onError_returnsNonEmptyMessage ""⟩

/-- Proof of `test_numparse_parseInt_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseInt_matchesModel :
    AllPass (test_numparse_parseInt_matchesModel defaultApi) := by
  intro s
  dsimp [test_numparse_parseInt_matchesModel, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  rcases parseInt_spec s with ⟨hm, hmsg⟩
  cases hpi : Internal.parseInt s with
  | error e =>
    have hpm : parseIntModel s = .error e.kind := by rw [← hm, hpi]; rfl
    simp [hpm, hmsg e hpi]
  | ok v =>
    have hpm : parseIntModel s = .ok v := by rw [← hm, hpi]; rfl
    simp [hpm]

/-- Non-vacuity `CanReach` witness for `test_numparse_parseInt_matchesModel`. -/
theorem reach_numparse_parseInt_matchesModel :
    CanReach (test_numparse_parseInt_matchesModel defaultApi) :=
  ⟨"0", proof_numparse_parseInt_matchesModel "0"⟩

/-- Proof of `test_numparse_parseInt64_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseInt64_matchesModel :
    AllPass (test_numparse_parseInt64_matchesModel defaultApi) := by
  intro s
  dsimp [test_numparse_parseInt64_matchesModel, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  rcases parseInt64_spec s with ⟨hm, hmsg⟩
  cases hpi : Internal.parseInt64 s with
  | error e =>
    have hpm : parseInt64Model s = .error e.kind := by rw [← hm, hpi]; rfl
    simp [hpm, hmsg e hpi]
  | ok v =>
    have hpm : parseInt64Model s = .ok v := by rw [← hm, hpi]; rfl
    simp [hpm]

/-- Non-vacuity `CanReach` witness for `test_numparse_parseInt64_matchesModel`. -/
theorem reach_numparse_parseInt64_matchesModel :
    CanReach (test_numparse_parseInt64_matchesModel defaultApi) :=
  ⟨"0", proof_numparse_parseInt64_matchesModel "0"⟩

/-- Proof of `test_numparse_formatInt_roundTrip` for `defaultApi`. -/
theorem proof_numparse_formatInt_roundTrip :
    AllPass (test_numparse_formatInt_roundTrip defaultApi) := by
  intro n
  rcases parseIntModel_formatInt n with ⟨hnoU, hmodel⟩
  rcases parseInt_spec (Internal.formatInt n) with ⟨hpi_m, _⟩
  have hpi_ok : Internal.parseInt (Internal.formatInt n) = .ok n := by
    cases h1 : Internal.parseInt (Internal.formatInt n) with
    | error e => have : parseIntModel (Internal.formatInt n) = .error e.kind := by rw [← hpi_m, h1]; rfl
                 rw [hmodel] at this; cases this
    | ok v => have : parseIntModel (Internal.formatInt n) = .ok v := by rw [← hpi_m, h1]; rfl
              rw [hmodel] at this; cases this; rfl
  rcases parseInt64_spec (Internal.formatInt n) with ⟨h64_m, h64_msg⟩
  dsimp [test_numparse_formatInt_roundTrip, defaultApi, Internal.defaultApi,
    Bind.bind, Core.NondetTest.assert]
  refine ⟨hnoU, hmodel, hpi_ok, ?_⟩
  by_cases hr : inInt64Range n = true
  · simp only [hr, ↓reduceIte]
    have hm64 : parseInt64Model (Internal.formatInt n) = .ok (Int64.ofInt n) := by
      rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hr]
    cases h1 : Internal.parseInt64 (Internal.formatInt n) with
    | error e =>
      have : parseInt64Model (Internal.formatInt n) = .error e.kind := by rw [← h64_m, h1]; rfl
      rw [hm64] at this; cases this
    | ok v =>
      have : parseInt64Model (Internal.formatInt n) = .ok v := by rw [← h64_m, h1]; rfl
      rw [hm64] at this; cases this; exact ⟨rfl, trivial⟩
  · have hr' : inInt64Range n = false := Bool.eq_false_iff.mpr hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte]
    have hm64 : parseInt64Model (Internal.formatInt n) = .error .overflow := by
      rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hr']
    cases h1 : Internal.parseInt64 (Internal.formatInt n) with
    | error e =>
      have heq : parseInt64Model (Internal.formatInt n) = .error e.kind := by rw [← h64_m, h1]; rfl
      rw [hm64] at heq
      injection heq with hk
      exact ⟨⟨hk.symm, h64_msg e h1⟩, trivial⟩
    | ok v =>
      have : parseInt64Model (Internal.formatInt n) = .ok v := by rw [← h64_m, h1]; rfl
      rw [hm64] at this; cases this

/-- Non-vacuity `CanReach` witness for `test_numparse_formatInt_roundTrip`. -/
theorem reach_numparse_formatInt_roundTrip :
    CanReach (test_numparse_formatInt_roundTrip defaultApi) :=
  ⟨0, proof_numparse_formatInt_roundTrip 0⟩

/-- Proof of `test_numparse_parseFloat_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseFloat_matchesModel :
    AllPass (test_numparse_parseFloat_matchesModel defaultApi) := by
  intro s
  dsimp [test_numparse_parseFloat_matchesModel, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  rcases parseFloat_spec s with ⟨hm, hmsg⟩
  cases hpf : Internal.parseFloat s with
  | error e =>
    have hpm : parseFloatModel s = .error e.kind := by rw [← hm, hpf]; rfl
    simp [hpm, hmsg e hpf]
  | ok v =>
    have hpm : parseFloatModel s = .ok v := by rw [← hm, hpf]; rfl
    simp [hpm, floatBitMatch_refl]

/-- Non-vacuity `CanReach` witness for `test_numparse_parseFloat_matchesModel`. -/
theorem reach_numparse_parseFloat_matchesModel :
    CanReach (test_numparse_parseFloat_matchesModel defaultApi) :=
  ⟨"0.0", proof_numparse_parseFloat_matchesModel "0.0"⟩

private theorem defaultApi_parseInt_of_model {s : String} {expected : Int}
    (hm : parseIntModel s = .ok expected) :
    match defaultApi.parseInt s with
    | .ok v => v = expected
    | .error _ => False := by
  have hs := (parseInt_spec s).1
  change (Internal.parseInt s).mapError (·.kind) = parseIntModel s at hs
  change match Internal.parseInt s with | .ok v => v = expected | .error _ => False
  cases h : Internal.parseInt s with
  | error e => have : parseIntModel s = .error e.kind := by rw [← hs, h]; rfl
               rw [hm] at this; cases this
  | ok v => have : parseIntModel s = .ok v := by rw [← hs, h]; rfl
            rw [hm] at this; exact (Except.ok.inj this).symm

private theorem defaultApi_parseInt_err_of_model {s : String} {expected : NumParseErrorKind}
    (hm : parseIntModel s = .error expected) :
    match defaultApi.parseInt s with
    | .ok _ => False
    | .error e => e.kind = expected ∧ e.message ≠ "" := by
  have hs := parseInt_spec s
  change match Internal.parseInt s with | .ok _ => False | .error e => e.kind = expected ∧ e.message ≠ ""
  cases h : Internal.parseInt s with
  | error e =>
    have heq : parseIntModel s = .error e.kind := by rw [← hs.1, h]; rfl
    rw [hm] at heq
    exact ⟨(Except.error.inj heq).symm, hs.2 e h⟩
  | ok v =>
    have heq : parseIntModel s = .ok v := by rw [← hs.1, h]; rfl
    rw [hm] at heq; cases heq

private theorem defaultApi_parseInt64_of_model {s : String} {expected : Int64}
    (hm : parseInt64Model s = .ok expected) :
    match defaultApi.parseInt64 s with
    | .ok v => v = expected
    | .error _ => False := by
  have hs := (parseInt64_spec s).1
  change match Internal.parseInt64 s with | .ok v => v = expected | .error _ => False
  cases h : Internal.parseInt64 s with
  | error e => have : parseInt64Model s = .error e.kind := by rw [← hs, h]; rfl
               rw [hm] at this; cases this
  | ok v => have : parseInt64Model s = .ok v := by rw [← hs, h]; rfl
            rw [hm] at this; exact (Except.ok.inj this).symm

private theorem defaultApi_parseInt64_err_of_model {s : String} {expected : NumParseErrorKind}
    (hm : parseInt64Model s = .error expected) :
    match defaultApi.parseInt64 s with
    | .ok _ => False
    | .error e => e.kind = expected ∧ e.message ≠ "" := by
  have hs := parseInt64_spec s
  change match Internal.parseInt64 s with | .ok _ => False | .error e => e.kind = expected ∧ e.message ≠ ""
  cases h : Internal.parseInt64 s with
  | error e =>
    have heq : parseInt64Model s = .error e.kind := by rw [← hs.1, h]; rfl
    rw [hm] at heq
    exact ⟨(Except.error.inj heq).symm, hs.2 e h⟩
  | ok v =>
    have heq : parseInt64Model s = .ok v := by rw [← hs.1, h]; rfl
    rw [hm] at heq; cases heq

private theorem defaultApi_parseFloat_bits_of_model {s : String} {expected : Float}
    (hm : ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch expected y) :
    match defaultApi.parseFloat s with
    | .ok actual => FloatBitMatch expected actual
    | .error _ => False := by
  rcases hm with ⟨y, hmy, hbit⟩
  have hs := (parseFloat_spec s).1
  change match Internal.parseFloat s with | .ok actual => FloatBitMatch expected actual | .error _ => False
  cases h : Internal.parseFloat s with
  | error e => have : parseFloatModel s = .error e.kind := by rw [← hs, h]; rfl
               rw [hmy] at this; cases this
  | ok v => have : parseFloatModel s = .ok v := by rw [← hs, h]; rfl
            rw [hmy] at this
            cases Except.ok.inj this
            exact hbit

private theorem defaultApi_parseFloat_err_of_model {s : String} {expected : NumParseErrorKind}
    (hm : parseFloatModel s = .error expected) :
    match defaultApi.parseFloat s with
    | .ok _ => False
    | .error e => e.kind = expected ∧ e.message ≠ "" := by
  have hs := parseFloat_spec s
  change match Internal.parseFloat s with | .ok _ => False | .error e => e.kind = expected ∧ e.message ≠ ""
  cases h : Internal.parseFloat s with
  | error e =>
    have heq : parseFloatModel s = .error e.kind := by rw [← hs.1, h]; rfl
    rw [hm] at heq
    exact ⟨(Except.error.inj heq).symm, hs.2 e h⟩
  | ok v =>
    have heq : parseFloatModel s = .ok v := by rw [← hs.1, h]; rfl
    rw [hm] at heq; cases heq

private theorem pow2_3n_le_pow10 (n : Nat) : 2 ^ (3 * n) ≤ 10 ^ n := by
  rw [Nat.pow_mul]
  exact Nat.pow_le_pow_left (by decide) n

private theorem shiftRight_mantissa (em : Float.Model.UnpackedFloat.ExtendedMantissa) (k : Nat) :
    (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  change (Nat.repeat Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne k em).mantissa = em.mantissa / 2 ^ k
  induction k generalizing em with
  | zero => simp [Nat.repeat]
  | succ k ih =>
    simp only [Nat.repeat, Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne]
    rw [ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

private theorem roundedMantissa_ge (em : Float.Model.UnpackedFloat.ExtendedMantissa) :
    em.mantissa ≤ em.roundedMantissa := by
  rcases em with ⟨m, r, s⟩
  cases r <;> cases s <;> simp [Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
    Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
    Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]

private theorem div_pow2_pos {x k : Nat} (hx : x ≠ 0) (hk : k ≤ x.log2) :
    0 < x / 2 ^ k :=
  Nat.div_pos
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) ((Nat.le_log2 hx).1 (Nat.le_refl _)))
    (Nat.pow_pos (by decide))

private theorem pack_finite_pos_ge972 {m : Nat} {e : Int} (hm : 0 < m) (he : 972 ≤ e) :
    Float.ofModel (Float.Model.pack (.finite .positive m e hm)) = Float.inf := by
  have hpow : 2 ^ Float.Model.Format.binary64.exponentBits = 2048 := by decide
  have hbias : Float.Model.Format.binary64.exponentBias = 1023 := by decide
  have hmbi : Float.Model.Format.binary64.mantissaBitsWithoutImplicit = 52 := by decide
  have hge : 2 ^ Float.Model.Format.binary64.exponentBits ≤
      (e + Float.Model.Format.binary64.exponentBias +
        Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat + 1 := by
    omega
  show Float.ofModel (Float.Model.pack (.finite .positive m e hm)) =
    Float.ofModel (Float.Model.pack (.infinity .positive))
  congr 1
  unfold Float.Model.pack
  congr 1
  unfold Float.Model.UnpackedFloat.pack
  simp only [hge, ↓reduceIte]

private theorem evalFloat_overflow_ge360 (e : Int) (he : 360 ≤ e) (he2 : e ≤ 2048) :
    evalFloat false 1 e = Float.inf := by
  have he_nonneg : 0 ≤ e := by omega
  have h10 := pow2_3n_le_pow10 e.toNat
  have hmb : Float.Model.Format.binary64.mantissaBits = 53 := by decide
  have hmin : Float.Model.Format.binary64.minExponent = -1074 := by decide
  have hpow2_11 : (2 ^ Float.Model.Format.binary64.exponentBits : Int) = 2048 := by decide
  have hlog1 : Nat.log2 1 = 0 := by decide
  let mant := (1 <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ e.toNat
  have hmul_pos : mant ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
  have h2pow : 2 ^ (3 * e.toNat) ≤ mant := Nat.le_trans h10 (Nat.le_mul_of_pos_left _ (by decide))
  have hlog : 3 * e.toNat ≤ mant.log2 := (Nat.le_log2 hmul_pos).2 h2pow
  have hlog1080 : 1080 ≤ mant.log2 := by omega
  unfold evalFloat evalFloatModel Float.Model.ofScientific Float.Model.UnpackedFloat.ofScientific
  have hnot1 : ¬(e > 2 ^ Float.Model.Format.binary64.exponentBits) := by omega
  have hnot2 : ¬(e < -((2 ^ Float.Model.Format.binary64.exponentBits : Int) + (Nat.log2 1 : Int))) := by omega
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero, ↓reduceDIte, hnot1, hnot2, he_nonneg]
  change Float.ofModel (Float.Model.pack (Float.Model.UnpackedFloat.mul Float.Model.Format.binary64
    (.finite .positive (1 <<< Float.Model.Format.binary64.mantissaBits)
      (-Float.Model.Format.binary64.mantissaBits) _)
    (.finite .positive (10 ^ e.toNat) 0 _))) = Float.inf
  unfold Float.Model.UnpackedFloat.mul Float.Model.UnpackedFloat.roundWithAccuracy
  dsimp only []
  let st1 := Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 mant
    (-(Float.Model.Format.binary64.mantissaBits : Int) + 0) .exact
  have hsh1_le : (Float.Model.Format.binary64.targetExponent
      (Float.Model.totalExponent mant (-(Float.Model.Format.binary64.mantissaBits : Int) + 0)) -
      (-(Float.Model.Format.binary64.mantissaBits : Int) + 0)).toNat ≤ mant.log2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent; omega
  have hm1_pos : 0 < st1.1.mantissa := by
    change 0 < (Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 mant
      (-(Float.Model.Format.binary64.mantissaBits : Int) + 0) .exact).1.mantissa
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
    dsimp only [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy]
    rw [shiftRight_mantissa]
    exact div_pow2_pos hmul_pos hsh1_le
  have hrem_pos : 0 < st1.1.roundedMantissa := Nat.lt_of_lt_of_le hm1_pos (roundedMantissa_ge _)
  have he1_ge : (972 : Int) ≤ st1.2 := by
    change (972 : Int) ≤ (Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 mant
      (-(Float.Model.Format.binary64.mantissaBits : Int) + 0) .exact).2
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
      Float.Model.Format.targetExponent Float.Model.totalExponent
    dsimp only []; omega
  let st2 := Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64
    st1.1.roundedMantissa st1.2 .exact
  have hsh2_le : (Float.Model.Format.binary64.targetExponent
      (Float.Model.totalExponent st1.1.roundedMantissa st1.2) - st1.2).toNat ≤
      st1.1.roundedMantissa.log2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent; omega
  have hm2_pos : st2.1.mantissa ≠ 0 := by
    change (Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64
      st1.1.roundedMantissa st1.2 .exact).1.mantissa ≠ 0
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
    dsimp only [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy]
    rw [shiftRight_mantissa]
    exact Nat.ne_of_gt (div_pow2_pos (Nat.ne_of_gt hrem_pos) hsh2_le)
  change Float.ofModel (Float.Model.pack (if h : st2.1.mantissa = 0 then _ else _)) = Float.inf
  simp only [hm2_pos, ↓reduceDIte]
  have he2_ge : (972 : Int) ≤ st2.2 := by
    change (972 : Int) ≤ (Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64
      st1.1.roundedMantissa st1.2 .exact).2
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
    dsimp only []; omega
  exact pack_finite_pos_ge972 (Nat.pos_of_ne_zero hm2_pos) he2_ge

private theorem round_zero_lt_neg1074 :
    Float.ofModel (Float.Model.pack
      (Float.Model.UnpackedFloat.roundWithAccuracy Float.Model.Format.binary64 .positive 0 (-1074)
        (.inexact .lt))) = (0.0 : Float) := by
  decide

private theorem accuracy_one_shiftLeft_lt {k d : Nat} (hk : 2 ^ (k + 1) < d) :
    (1 <<< k) / d = 0 ∧
    Float.Model.UnpackedFloat.accuracyOfFraction ((1 <<< k) % d) d = .inexact .lt := by
  have hpow : 1 <<< k = 2 ^ k := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have h2mul : 2 * (1 <<< k) = 2 ^ (k + 1) := by
    rw [hpow, Nat.mul_comm, Nat.pow_succ]
  have h1lt2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k)
  have hlt : 1 <<< k < d := hpow ▸ Nat.lt_trans h1lt2 hk
  have hne : (1 <<< k) ≠ 0 := hpow ▸ Nat.ne_of_gt (Nat.pow_pos (by decide))
  refine ⟨Nat.div_eq_of_lt hlt, ?_⟩
  rw [Nat.mod_eq_of_lt hlt]
  unfold Float.Model.UnpackedFloat.accuracyOfFraction
  simp only [hne, ↓reduceIte, h2mul]
  have hcmp : compare (2 ^ (k + 1)) d = .lt := by
    simp [compare, compareOfLessAndEq, hk]
  rw [hcmp]

private theorem evalFloat_underflow_le_neg360 (e : Int) (he : e ≤ -360) (he2 : -(2048 : Int) ≤ e) :
    evalFloat false 1 e = (0.0 : Float) := by
  have he_neg : ¬(0 ≤ e) := by omega
  let p := (-e).toNat
  have hp_ge : 360 ≤ p := by omega
  have h10 := pow2_3n_le_pow10 p
  have h10_pos : 10 ^ p ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
  have hlog : 3 * p ≤ (10 ^ p).log2 := (Nat.le_log2 h10_pos).2 h10
  have hlog1080 : 1080 ≤ (10 ^ p).log2 := by omega
  unfold evalFloat evalFloatModel Float.Model.ofScientific Float.Model.UnpackedFloat.ofScientific
  have hpow2_11 : (2 ^ Float.Model.Format.binary64.exponentBits : Int) = 2048 := by decide
  have hlog1 : Nat.log2 1 = 0 := by decide
  have hnot1 : ¬(e > 2 ^ Float.Model.Format.binary64.exponentBits) := by omega
  have hnot2 : ¬(e < -((2 ^ Float.Model.Format.binary64.exponentBits : Int) + (Nat.log2 1 : Int))) := by omega
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero, ↓reduceDIte, hnot1, hnot2, he_neg]
  change Float.ofModel (Float.Model.pack
    (Float.Model.UnpackedFloat.div Float.Model.Format.binary64
      (.finite .positive 1 0 _) (.finite .positive (10 ^ p) 0 _))) = 0.0
  unfold Float.Model.UnpackedFloat.div Float.Model.UnpackedFloat.divCore
  have hmin : Float.Model.Format.binary64.minExponent = -1074 := by decide
  have hmb : Float.Model.Format.binary64.mantissaBits = 53 := by decide
  have hte : min ((0 : Int) - 0) (Float.Model.Format.binary64.targetExponent
      (Float.Model.totalExponent 1 0 - Float.Model.totalExponent (10 ^ p) 0)) = -1074 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent; omega
  have hsh : ((0 : Int) - 0 - (-1074 : Int)).toNat = 1074 := rfl
  have hk_lt : 2 ^ (1074 + 1) < 10 ^ p := by
    calc 2 ^ (1074 + 1) < 2 ^ (3 * p) := Nat.pow_lt_pow_right (by decide) (by omega)
      _ ≤ 10 ^ p := h10
  have ⟨hdiv, hacc⟩ := accuracy_one_shiftLeft_lt (k := 1074) hk_lt
  dsimp only []
  rw [hte, hsh, hdiv, hacc]
  exact round_zero_lt_neg1074

private theorem float_zero_neg_zero_checks :
    match defaultApi.parseFloat "0.0", defaultApi.parseFloat "-0.0" with
    | .ok p, .ok n =>
      p.toBits = (0.0 : Float).toBits ∧
      (n.toBits = (-0.0 : Float).toBits ∧
        (n.toBits ≠ p.toBits ∧ (FloatEquiv p n ∧ True)))
    | _, _ => False := by
  have hp_spec := (parseFloat_spec "0.0").1
  have hn_spec := (parseFloat_spec "-0.0").1
  change match Internal.parseFloat "0.0", Internal.parseFloat "-0.0" with
    | .ok p, .ok n => _ | _, _ => False
  cases hp : Internal.parseFloat "0.0" with
  | error e =>
    have : parseFloatModel "0.0" = .error e.kind := by rw [← hp_spec, hp]; rfl
    cases this
  | ok p =>
    cases hn : Internal.parseFloat "-0.0" with
    | error e =>
      have : parseFloatModel "-0.0" = .error e.kind := by rw [← hn_spec, hn]; rfl
      cases this
    | ok n =>
      have hp_m : parseFloatModel "0.0" = .ok p := by rw [← hp_spec, hp]; rfl
      have hn_m : parseFloatModel "-0.0" = .ok n := by rw [← hn_spec, hn]; rfl
      have hp_eq : p = evalFloat false 0 (-1) := (Except.ok.inj hp_m).symm
      have hn_eq : n = evalFloat true 0 (-1) := (Except.ok.inj hn_m).symm
      subst hp_eq; subst hn_eq
      refine ⟨by decide, by decide, by decide, by unfold FloatEquiv; decide, trivial⟩

private def pubCheckFloatOkBits (cases : List (String × Float)) : AllPassRun Unit :=
  cases.forM fun (s, expected) =>
    match defaultApi.parseFloat s with
    | .ok actual => NondetTest.assert (FloatBitMatch expected actual)
    | .error _ => NondetTest.assert False

private theorem pubCheckFloatOkBits_bind (cases : List (String × Float))
    (k : Unit → AllPassRun Unit) (post : Unit → Prop)
    (hcases : ∀ p ∈ cases, ∃ y, parseFloatModel p.1 = .ok y ∧ FloatBitMatch p.2 y)
    (hk : k () post) :
    (pubCheckFloatOkBits cases >>= k) post := by
  induction cases with
  | nil => exact hk
  | cons p ps ih =>
    change ((match defaultApi.parseFloat p.1 with
      | .ok actual => NondetTest.assert (FloatBitMatch p.2 actual)
      | .error _ => NondetTest.assert False) : AllPassRun Unit)
      (fun _ => (pubCheckFloatOkBits ps >>= k) post)
    have hp := defaultApi_parseFloat_bits_of_model (hcases p (by simp))
    have hps := ih (fun q hq => hcases q (by simp [hq]))
    cases hd : defaultApi.parseFloat p.1 with
    | error e => rw [hd] at hp; exact False.elim hp
    | ok actual =>
      rw [hd] at hp
      exact ⟨hp, hps⟩

private def pubCheckFloatErr (cases : List (String × NumParseErrorKind)) : AllPassRun Unit :=
  cases.forM fun (s, expected) =>
    match defaultApi.parseFloat s with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = expected ∧ e.message ≠ "")

private theorem pubCheckFloatErr_bind (cases : List (String × NumParseErrorKind))
    (k : Unit → AllPassRun Unit) (post : Unit → Prop)
    (hcases : ∀ p ∈ cases, parseFloatModel p.1 = .error p.2)
    (hk : k () post) :
    (pubCheckFloatErr cases >>= k) post := by
  induction cases with
  | nil => exact hk
  | cons p ps ih =>
    change ((match defaultApi.parseFloat p.1 with
      | .ok _ => NondetTest.assert False
      | .error e => NondetTest.assert (e.kind = p.2 ∧ e.message ≠ "")) : AllPassRun Unit)
      (fun _ => (pubCheckFloatErr ps >>= k) post)
    have hp := defaultApi_parseFloat_err_of_model (hcases p (by simp))
    have hps := ih (fun q hq => hcases q (by simp [hq]))
    cases hd : defaultApi.parseFloat p.1 with
    | ok v => rw [hd] at hp; exact False.elim hp
    | error e =>
      rw [hd] at hp
      exact ⟨hp, hps⟩

private def pubZeroCheck : AllPassRun Unit :=
  match defaultApi.parseFloat "0.0", defaultApi.parseFloat "-0.0" with
  | .ok p, .ok n => do
    NondetTest.assert (p.toBits = (0.0 : Float).toBits)
    NondetTest.assert (n.toBits = (-0.0 : Float).toBits)
    NondetTest.assert (n.toBits ≠ p.toBits)
    NondetTest.assert (FloatEquiv p n)
  | _, _ => NondetTest.assert False

private def floatOkCases : List (String × Float) :=
  [ ("inf", Float.inf), ("+inf", Float.inf), ("-inf", -Float.inf)
  , ("nan", Float.nan), ("+nan", Float.nan), ("-nan", Float.nan)
  , ("0.0", 0.0), ("+0.0", 0.0), ("-0.0", -0.0)
  , ("1e05", evalFloat false 1 5), ("1e-00", 1.0), ("1e+01", 10.0)
  , ("1e400", Float.inf), ("-1e400", -Float.inf)
  , ("1e-400", 0.0), ("-1e-400", -0.0)
  , ("1e1000000000", Float.inf), ("-1e1000000000", -Float.inf)
  , ("1e-1000000000", 0.0), ("-1e-1000000000", -0.0)
  , ("5e-324", evalFloat false 5 (-324)), ("2.47e-324", evalFloat false 247 (-326))
  , ("2.5e-324", evalFloat false 25 (-325)), ("1e-323", evalFloat false 1 (-323)) ]

private def floatErrCases : List (String × NumParseErrorKind) :=
  [ ("", .emptyInput), ("Inf", .invalidSyntax), ("INF", .invalidSyntax)
  , ("Infinity", .invalidSyntax), ("-Infinity", .invalidSyntax)
  , ("NaN", .invalidSyntax), ("NAN", .invalidSyntax), ("42", .invalidSyntax)
  , ("-0", .invalidSyntax), ("1_000", .invalidSyntax), (".5", .invalidSyntax)
  , ("1.", .invalidSyntax), ("1.5e", .invalidSyntax), ("1.5e+", .invalidSyntax)
  , ("01.5", .leadingZero), ("-00e1", .leadingZero), ("0_1.5", .leadingZero)
  , ("1._5", .invalidUnderscore), ("1.5_", .invalidUnderscore)
  , ("1.5e_", .invalidUnderscore), ("1.5e_1", .invalidUnderscore)
  , ("1.5e1_", .invalidUnderscore), ("infx", .trailingChars)
  , ("nanx", .trailingChars), ("1.5x", .trailingChars), ("1.5 ", .trailingChars) ]

/-- Proof of `test_numparse_int_concreteBoundaries` for `defaultApi`. -/
theorem proof_numparse_int_concreteBoundaries :
    AllPass (test_numparse_int_concreteBoundaries defaultApi) := by
  have hrt : ∀ n : Int,
      parseIntModel (defaultApi.formatInt n) = .ok n ∧ defaultApi.parseInt (defaultApi.formatInt n) = .ok n := by
    intro n
    have hm := (parseIntModel_formatInt n).2
    have hok : defaultApi.parseInt (defaultApi.formatInt n) = .ok n := by
      have hs := (parseInt_spec (Internal.formatInt n)).1
      change Internal.parseInt (Internal.formatInt n) = .ok n
      cases h : Internal.parseInt (Internal.formatInt n) with
      | error e =>
        have : parseIntModel (Internal.formatInt n) = .error e.kind := by rw [← hs, h]; rfl
        rw [hm] at this; cases this
      | ok v =>
        have : parseIntModel (Internal.formatInt n) = .ok v := by rw [← hs, h]; rfl
        rw [hm] at this; cases this; rfl
    exact ⟨hm, hok⟩
  dsimp [AllPass, test_numparse_int_concreteBoundaries, Bind.bind, Pure.pure, List.forM, Core.NondetTest.assert]
  repeat'
    first
    | exact True.intro
    | exact rfl
    | exact makeError_msg_ne_empty _ _
    | exact hrt _
    | exact defaultApi_parseInt_of_model (by decide)
    | exact defaultApi_parseInt_err_of_model (by decide)
    | exact defaultApi_parseInt64_of_model (by decide)
    | exact defaultApi_parseInt64_err_of_model (by decide)
    | constructor

/-- Non-vacuity `CanReach` witness for `test_numparse_int_concreteBoundaries`. -/
theorem reach_numparse_int_concreteBoundaries :
    CanReach (test_numparse_int_concreteBoundaries defaultApi) :=
  proof_numparse_int_concreteBoundaries

private theorem exists_parseFloatModel_of_eq {s : String} {neg : Bool} {m : Nat} {e : Int}
    (h : parseFloatModel s = .ok (evalFloat neg m e)) :
    ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch (evalFloat neg m e) y :=
  ⟨evalFloat neg m e, h, floatBitMatch_refl _⟩

/-- Proof of `test_numparse_float_concreteSpecialsAndEdges` for `defaultApi`. -/
theorem proof_numparse_float_concreteSpecialsAndEdges :
    AllPass (test_numparse_float_concreteSpecialsAndEdges defaultApi) := by
  have h1e400 : evalFloat false 1 400 = Float.inf :=
    evalFloat_overflow_ge360 400 (by decide) (by decide)
  have hn1e400 : evalFloat true 1 400 = -Float.inf := by
    rw [evalFloat_neg, h1e400]
  have h1en400 : evalFloat false 1 (-400) = (0.0 : Float) :=
    evalFloat_underflow_le_neg360 (-400) (by decide) (by decide)
  have hn1en400 : evalFloat true 1 (-400) = (-0.0 : Float) := by
    rw [evalFloat_neg, h1en400]
  have h1eBig : evalFloat false 1 1000000000 = Float.inf :=
    evalFloat_overflow_pos (by decide) (by decide)
  have hn1eBig : evalFloat true 1 1000000000 = -Float.inf :=
    evalFloat_overflow_neg (by decide) (by decide)
  have h1enBig : evalFloat false 1 (-1000000000) = (0.0 : Float) :=
    evalFloat_underflow_pos (by decide)
  have hn1enBig : evalFloat true 1 (-1000000000) = (-0.0 : Float) :=
    evalFloat_underflow_neg (by decide)
  change (do pubCheckFloatOkBits floatOkCases; pubCheckFloatErr floatErrCases; pubZeroCheck) (fun _ => True)
  apply pubCheckFloatOkBits_bind
  · intro p hp
    simp only [floatOkCases, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, (by rw [show parseFloatModel "1e400" = .ok (evalFloat false 1 400) from rfl, h1e400]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "-1e400" = .ok (evalFloat true 1 400) from rfl, hn1e400]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "1e-400" = .ok (evalFloat false 1 (-400)) from rfl, h1en400]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "-1e-400" = .ok (evalFloat true 1 (-400)) from rfl, hn1en400]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "1e1000000000" = .ok (evalFloat false 1 1000000000) from rfl, h1eBig]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "-1e1000000000" = .ok (evalFloat true 1 1000000000) from rfl, hn1eBig]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "1e-1000000000" = .ok (evalFloat false 1 (-1000000000)) from rfl, h1enBig]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "-1e-1000000000" = .ok (evalFloat true 1 (-1000000000)) from rfl, hn1enBig]), floatBitMatch_refl _⟩
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
  · apply pubCheckFloatErr_bind
    · intro p hp
      simp only [floatErrCases, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · exact float_zero_neg_zero_checks

/-- Non-vacuity `CanReach` witness for `test_numparse_float_concreteSpecialsAndEdges`. -/
theorem reach_numparse_float_concreteSpecialsAndEdges :
    CanReach (test_numparse_float_concreteSpecialsAndEdges defaultApi) :=
  proof_numparse_float_concreteSpecialsAndEdges


private theorem char_ofNat_decDigit_props (d : Nat) (hd : d < 10) :
    Model.isDecDigit (Char.ofNat ('0'.toNat + d)) = true ∧
      Char.ofNat ('0'.toNat + d) ≠ '_' ∧
      (Char.ofNat ('0'.toNat + d)).toNat - '0'.toNat = d := by
  match d with
  | 0 => exact ⟨by decide, by decide, by decide⟩
  | 1 => exact ⟨by decide, by decide, by decide⟩
  | 2 => exact ⟨by decide, by decide, by decide⟩
  | 3 => exact ⟨by decide, by decide, by decide⟩
  | 4 => exact ⟨by decide, by decide, by decide⟩
  | 5 => exact ⟨by decide, by decide, by decide⟩
  | 6 => exact ⟨by decide, by decide, by decide⟩
  | 7 => exact ⟨by decide, by decide, by decide⟩
  | 8 => exact ⟨by decide, by decide, by decide⟩
  | 9 => exact ⟨by decide, by decide, by decide⟩
  | k + 10 => omega

private theorem decDigit_props {c : Char} (hc : Model.isDecDigit c = true) :
    c ≠ '_' ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' ∧ c.toNat - '0'.toNat < 10 := by
  simp only [Model.isDecDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h0 : '0'.toNat = 48 := by decide
  have h9 : '9'.toNat = 57 := by decide
  have hu : '_'.toNat = 95 := by decide
  have hd : '.'.toNat = 46 := by decide
  have he : 'e'.toNat = 101 := by decide
  have hE : 'E'.toNat = 69 := by decide
  have h1 : '0'.toNat ≤ c.toNat := hc.1
  have h2 : c.toNat ≤ '9'.toNat := hc.2
  refine ⟨?_, ?_, ?_, ?_, by omega⟩ <;> intro h <;> have hcn := congrArg Char.toNat h <;> omega

private theorem natToDecCharsPos_append (n : Nat) (acc : List Char) :
    Internal.natToDecCharsPos n acc = Internal.natToDecCharsPos n [] ++ acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    cases n with
    | zero => simp [Internal.natToDecCharsPos.eq_1]
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, Internal.natToDecCharsPos.eq_2]
      have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      rw [ih ((m + 1) / 10) hlt (Char.ofNat ('0'.toNat + (m + 1) % 10) :: acc)]
      rw [ih ((m + 1) / 10) hlt [Char.ofNat ('0'.toNat + (m + 1) % 10)]]
      simp [List.append_assoc]

private def decStep (acc : Nat) (c : Char) : Nat := acc * 10 + (c.toNat - '0'.toNat)

private theorem decFold_zeros (acc k : Nat) :
    (List.replicate k '0').foldl decStep acc = acc * 10 ^ k := by
  induction k generalizing acc with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.foldl_cons, decStep]
    have h0 : '0'.toNat - '0'.toNat = 0 := by decide
    rw [h0, Nat.add_zero, ih (acc * 10), Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ k)]

private theorem decFold_zeros_zero (k : Nat) :
    (List.replicate k '0').foldl decStep 0 = 0 := by
  rw [decFold_zeros, Nat.zero_mul]

private theorem natToDecCharsPos_eval (n acc : Nat) :
    (Internal.natToDecCharsPos n []).foldl decStep acc =
      acc * 10 ^ (Internal.natToDecCharsPos n []).length + n := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    cases n with
    | zero => simp [Internal.natToDecCharsPos.eq_1]
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
      have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      rw [List.foldl_append, ih ((m + 1) / 10) hlt acc]
      simp only [List.foldl_cons, List.foldl_nil, decStep, List.length_append, List.length_singleton]
      have hd := (char_ofNat_decDigit_props ((m + 1) % 10) (Nat.mod_lt _ (by decide))).2.2
      rw [hd, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc]
      have hdiv : (m + 1) / 10 * 10 + (m + 1) % 10 = m + 1 := by omega
      omega

private theorem natToDecCharsPos_all_dec (n : Nat) :
    ∀ c ∈ Internal.natToDecCharsPos n [], Model.isDecDigit c = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [Internal.natToDecCharsPos.eq_1]
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
      have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · exact ih ((m + 1) / 10) hlt c h1
      · simp only [List.mem_singleton] at h2
        subst h2
        exact (char_ofNat_decDigit_props ((m + 1) % 10) (Nat.mod_lt _ (by decide))).1

private theorem natToDecCharsPos_nonempty {n : Nat} (hn : 0 < n) :
    Internal.natToDecCharsPos n [] ≠ [] := by
  cases n with
  | zero => omega
  | succ m =>
    rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
    simp

private theorem natToDecCharsPos_head_ne_zero {n : Nat} (hn : 0 < n) :
    (Internal.natToDecCharsPos n []).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
      by_cases hq : (m + 1) / 10 = 0
      · rw [hq, Internal.natToDecCharsPos.eq_1, List.nil_append]
        simp only [List.head?_cons]
        intro heq
        have heq' : Char.ofNat ('0'.toNat + (m + 1) % 10) = '0' := Option.some.inj heq
        have hsub := congrArg (fun x : Char => x.toNat - '0'.toNat) heq'
        have hd := (char_ofNat_decDigit_props ((m + 1) % 10) (Nat.mod_lt _ (by decide))).2.2
        rw [hd] at hsub
        have hz : '0'.toNat - '0'.toNat = 0 := by decide
        rw [hz] at hsub
        omega
      · have hqpos : 0 < (m + 1) / 10 := Nat.pos_of_ne_zero hq
        have hne := natToDecCharsPos_nonempty hqpos
        have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
        cases hql : Internal.natToDecCharsPos ((m + 1) / 10) [] with
        | nil => exact absurd hql hne
        | cons x xs =>
          simp only [List.cons_append, List.head?_cons]
          have hih := ih ((m + 1) / 10) hlt hqpos
          rw [hql, List.head?_cons] at hih
          exact hih

private theorem consumeDecFloatDigits_append_dec
    (ds : List Char) (hds : ∀ c ∈ ds, Model.isDecDigit c = true)
    (rest : List Char)
    (hrest : rest = [] ∨ ∃ r0 rem, rest = r0 :: rem ∧ Model.isDecDigit r0 = false ∧ r0 ≠ '_')
    (acc count : Nat) :
    Model.consumeDecFloatDigits acc count (ds ++ rest) =
      Except.ok (ds.foldl decStep acc, count + ds.length, rest) := by
  induction ds generalizing acc count with
  | nil =>
    simp only [List.nil_append, List.foldl_nil, List.length_nil, Nat.add_zero]
    rcases hrest with rfl | ⟨r0, rem, rfl, hnd, hnu⟩
    · rw [Model.consumeDecFloatDigits.eq_1]
    · rw [Model.consumeDecFloatDigits.eq_4 acc count r0 rem (fun _ _ h => absurd h hnu) (fun h => absurd h hnu)]
      simp [hnd]
  | cons d ds ih =>
    have hd : Model.isDecDigit d = true := hds d (by simp)
    have hdnu : d ≠ '_' := (decDigit_props hd).1
    have hds' : ∀ c ∈ ds, Model.isDecDigit c = true := fun c hc => hds c (by simp [hc])
    rw [List.cons_append, Model.consumeDecFloatDigits.eq_4 acc count d (ds ++ rest) (fun _ _ h => absurd h hdnu) (fun h => absurd h hdnu)]
    simp only [hd, ↓reduceIte, List.foldl_cons, List.length_cons, decStep]
    rw [ih hds' (acc * 10 + (d.toNat - '0'.toNat)) (count + 1)]
    have hadd : count + 1 + ds.length = count + (ds.length + 1) := by omega
    rw [hadd]

private theorem parseFloatIntPart_append_dec
    (ds : List Char) (hne : ds ≠ [])
    (hds : ∀ c ∈ ds, Model.isDecDigit c = true)
    (hhd : ds.head? ≠ some '0')
    (rest : List Char)
    (hrest : rest = [] ∨ ∃ r0 rem, rest = r0 :: rem ∧ Model.isDecDigit r0 = false ∧ r0 ≠ '_') :
    Model.parseFloatIntPart (ds ++ rest) = Except.ok (ds.foldl decStep 0, rest) := by
  cases ds with
  | nil => exact absurd rfl hne
  | cons d ds =>
    have hd : Model.isDecDigit d = true := hds d (by simp)
    have hdnu : d ≠ '_' := (decDigit_props hd).1
    have hdz : d ≠ '0' := by intro h; subst h; exact hhd rfl
    have hds' : ∀ c ∈ ds, Model.isDecDigit c = true := fun c hc => hds c (by simp [hc])
    rw [List.cons_append]
    unfold Model.parseFloatIntPart
    simp only []
    split
    · rw [consumeDecFloatDigits_append_dec ds hds' rest hrest (d.toNat - '0'.toNat) 1]
      simp [decStep]
    · rename_i hnd; exact absurd hd hnd

private theorem decDigit_cases {c : Char} (hc : Model.isDecDigit c = true) :
    c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨
    c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' := by
  simp only [Model.isDecDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h0 : '0'.toNat = 48 := by decide
  have h9 : '9'.toNat = 57 := by decide
  have hlo : 48 ≤ c.toNat := h0 ▸ hc.1
  have hhi : c.toNat ≤ 57 := h9 ▸ hc.2
  have hsub : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨ c.toNat = 51 ∨ c.toNat = 52 ∨
      c.toNat = 53 ∨ c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56 ∨ c.toNat = 57 := by omega
  have hc_ofNat : Char.ofNat c.toNat = c := Char.ofNat_toNat c
  rcases hsub with h | h | h | h | h | h | h | h | h | h
  · left; exact hc_ofNat.symm.trans (by rw [h])
  · right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; right; right; right; right; exact hc_ofNat.symm.trans (by rw [h])

private theorem parseFloatExpPart_cons_decDigit (d : Char) (ds : List Char)
    (hd : Model.isDecDigit d = true) :
    Model.parseFloatExpPart (d :: ds) =
      match Model.consumeDecFloatDigits (d.toNat - '0'.toNat) 1 ds with
      | Except.ok (eMag, _, rem) => Except.ok (Int.ofNat eMag, rem)
      | Except.error k => Except.error k := by
  rcases decDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem parseFloatExpPart_formatIntChars (e : Int) :
    Model.parseFloatExpPart (Internal.formatIntChars e) = Except.ok (e, []) := by
  cases e with
  | ofNat n =>
    cases n with
    | zero =>
      have hfmt : Internal.formatIntChars (Int.ofNat 0) = ['0'] := rfl
      rw [hfmt]
      have hz : Model.isDecDigit '0' = true := by decide
      rw [parseFloatExpPart_cons_decDigit '0' [] hz, Model.consumeDecFloatDigits.eq_1]
      rfl
    | succ m =>
      have hfmt : Internal.formatIntChars (Int.ofNat (Nat.succ m)) = Internal.natToDecCharsPos (m + 1) [] := rfl
      rw [hfmt]
      have hpos : 0 < m + 1 := Nat.succ_pos m
      have hne := natToDecCharsPos_nonempty hpos
      have hall := natToDecCharsPos_all_dec (m + 1)
      have hev := natToDecCharsPos_eval (m + 1) 0
      simp only [Nat.zero_mul, Nat.zero_add] at hev
      cases hcs : Internal.natToDecCharsPos (m + 1) [] with
      | nil => exact absurd hcs hne
      | cons d ds =>
        rw [hcs] at hall hev
        have hhd : Model.isDecDigit d = true := hall d (by simp)
        have hds : ∀ c ∈ ds, Model.isDecDigit c = true := fun c hc => hall c (by simp [hc])
        rw [parseFloatExpPart_cons_decDigit d ds hhd]
        have hcon := consumeDecFloatDigits_append_dec ds hds [] (Or.inl rfl) (d.toNat - '0'.toNat) 1
        simp only [List.append_nil] at hcon
        rw [hcon]
        have hfold : ds.foldl decStep (d.toNat - '0'.toNat) = (d :: ds).foldl decStep 0 := by
          simp [decStep, List.foldl_cons]
        rw [hfold, hev]
  | negSucc n =>
    have hfmt : Internal.formatIntChars (Int.negSucc n) = '-' :: Internal.natToDecCharsPos (n + 1) [] := rfl
    rw [hfmt]
    have hpos : 0 < n + 1 := Nat.succ_pos n
    have hne := natToDecCharsPos_nonempty hpos
    have hall := natToDecCharsPos_all_dec (n + 1)
    have hev := natToDecCharsPos_eval (n + 1) 0
    simp only [Nat.zero_mul, Nat.zero_add] at hev
    cases hcs : Internal.natToDecCharsPos (n + 1) [] with
    | nil => exact absurd hcs hne
    | cons d ds =>
      rw [hcs] at hall hev
      have hhd : Model.isDecDigit d = true := hall d (by simp)
      have hdu : d ≠ '_' := (decDigit_props hhd).1
      have hds : ∀ c ∈ ds, Model.isDecDigit c = true := fun c hc => hall c (by simp [hc])
      unfold Model.parseFloatExpPart
      simp only []
      split
      · simp only [↓reduceIte]
        have hcon := consumeDecFloatDigits_append_dec ds hds [] (Or.inl rfl) (d.toNat - '0'.toNat) 1
        simp only [List.append_nil] at hcon
        rw [hcon]
        have hfold : ds.foldl decStep (d.toNat - '0'.toNat) = (d :: ds).foldl decStep 0 := by
          simp [decStep, List.foldl_cons]
        rw [hfold, hev]
        rfl
      · rename_i hnd; exact absurd hhd hnd

private theorem formatIntChars_all_non_underscore (e : Int) :
    ∀ c ∈ Internal.formatIntChars e, c ≠ '_' := by
  unfold Internal.formatIntChars
  cases e with
  | ofNat n =>
    cases n with
    | zero =>
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      decide
    | succ m =>
      intro c hc
      exact (decDigit_props (natToDecCharsPos_all_dec (m + 1) c hc)).1
  | negSucc n =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    · exact (decDigit_props (natToDecCharsPos_all_dec (n + 1) c hc)).1

private theorem list_contains_eq_false_of_forall {cs : List Char} {x : Char}
    (h : ∀ c ∈ cs, c ≠ x) : cs.contains x = false := by
  simp only [Bool.eq_false_iff]
  intro hc
  have hmem : x ∈ cs := List.contains_iff_mem.mp hc
  exact absurd rfl (h x hmem)
private theorem decDigit_not_special {c : Char} (hc : Model.isDecDigit c = true) :
    c ≠ '_' ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' ∧ c ≠ '+' ∧ c ≠ '-' ∧ c ≠ 'i' ∧ c ≠ 'n' := by
  simp only [Model.isDecDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h0 : '0'.toNat = 48 := by decide
  have h9 : '9'.toNat = 57 := by decide
  have hu : '_'.toNat = 95 := by decide
  have hd : '.'.toNat = 46 := by decide
  have he : 'e'.toNat = 101 := by decide
  have hE : 'E'.toNat = 69 := by decide
  have hp : '+'.toNat = 43 := by decide
  have hm : '-'.toNat = 45 := by decide
  have hi : 'i'.toNat = 105 := by decide
  have hn : 'n'.toNat = 110 := by decide
  have h1 : '0'.toNat ≤ c.toNat := hc.1
  have h2 : c.toNat ≤ '9'.toNat := hc.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have hcn := congrArg Char.toNat h <;> omega

private theorem parseFloatModelChars_cons_decDigit (neg : Bool) (d : Char) (rest : List Char)
    (hd : Model.isDecDigit d = true) :
    Model.parseFloatModelChars ((if neg then ['-'] else []) ++ d :: rest) =
      match Model.parseFloatIntPart (d :: rest) with
      | Except.error k => Except.error k
      | Except.ok (intVal, afterInt) =>
        match afterInt with
        | '.' :: afterDot =>
          match afterDot with
          | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
          | c :: rest2 =>
            if Model.isDecDigit c = true then
              match Model.consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest2 with
              | Except.error k => Except.error k
              | Except.ok (mantissa, fracCount, afterFrac) =>
                match afterFrac with
                | 'e' :: afterE =>
                  match Model.parseFloatExpPart afterE with
                  | Except.error k => Except.error k
                  | Except.ok (expVal, afterExp) =>
                    if afterExp.isEmpty = true then
                      Except.ok (Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                    else Except.error NumParseErrorKind.trailingChars
                | 'E' :: afterE =>
                  match Model.parseFloatExpPart afterE with
                  | Except.error k => Except.error k
                  | Except.ok (expVal, afterExp) =>
                    if afterExp.isEmpty = true then
                      Except.ok (Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                    else Except.error NumParseErrorKind.trailingChars
                | [] => Except.ok (Model.evalFloat neg mantissa (-Int.ofNat fracCount))
                | _ :: _ => Except.error NumParseErrorKind.trailingChars
            else Except.error NumParseErrorKind.invalidSyntax
          | [] => Except.error NumParseErrorKind.invalidSyntax
        | 'e' :: afterE =>
          match Model.parseFloatExpPart afterE with
          | Except.error k => Except.error k
          | Except.ok (expVal, afterExp) =>
            if afterExp.isEmpty = true then Except.ok (Model.evalFloat neg intVal expVal)
            else Except.error NumParseErrorKind.trailingChars
        | 'E' :: afterE =>
          match Model.parseFloatExpPart afterE with
          | Except.error k => Except.error k
          | Except.ok (expVal, afterExp) =>
            if afterExp.isEmpty = true then Except.ok (Model.evalFloat neg intVal expVal)
            else Except.error NumParseErrorKind.trailingChars
        | _ => Except.error NumParseErrorKind.invalidSyntax := by
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rcases decDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  | true =>
    simp only [↓reduceIte, List.cons_append, List.nil_append]
    rcases decDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem renderScientific_spec (neg : Bool) (mant : Nat) (hm : 0 < mant) (exp10 : Int) :
    let s := Internal.renderScientific neg mant exp10
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      Model.parseFloatModel s = Except.ok (Model.evalFloat neg mant exp10) := by
  unfold Internal.renderScientific
  have hne := natToDecCharsPos_nonempty hm
  have hall := natToDecCharsPos_all_dec mant
  have hhd := natToDecCharsPos_head_ne_zero hm
  have hev := natToDecCharsPos_eval mant 0
  simp only [Nat.zero_mul, Nat.zero_add] at hev
  cases hds : Internal.natToDecCharsPos mant [] with
  | nil => exact absurd hds hne
  | cons d rest =>
    have hd : Model.isDecDigit d = true := hall d (by rw [hds]; simp)
    have hrest : ∀ c ∈ rest, Model.isDecDigit c = true := fun c hc => hall c (by rw [hds]; simp [hc])
    have hd0 : d ≠ '0' := by intro h; subst h; rw [hds] at hhd; exact hhd rfl
    cases rest with
    | nil =>
      simp only []
      have hfold : d.toNat - '0'.toNat = mant := by
        rw [← hev, hds]
        simp [decStep]
      have hnu : ∀ c ∈ (if neg = true then ['-'] else []) ++ [d, 'e'] ++ Internal.formatIntChars exp10, c ≠ '_' := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · rcases List.mem_append.mp h1 with h1a | h1b
          · cases neg <;> simp at h1a; subst h1a; decide
          · simp at h1b
            rcases h1b with rfl | rfl
            · exact (decDigit_props hd).1
            · decide
        · exact formatIntChars_all_non_underscore exp10 c h2
      have hhasE : ((if neg = true then ['-'] else []) ++ [d, 'e'] ++ Internal.formatIntChars exp10).contains 'e' = true := by
        simp
      refine ⟨?_, Or.inr (Or.inl ?_), ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_eq_false_of_forall hnu
      · simp only [String.contains_char_eq, String.toList_ofList]
        exact hhasE
      · unfold Model.parseFloatModel
        rw [String.toList_ofList, List.append_assoc]
        have hcons : [d, 'e'] ++ Internal.formatIntChars exp10 = d :: 'e' :: Internal.formatIntChars exp10 := rfl
        rw [hcons, parseFloatModelChars_cons_decDigit neg d ('e' :: Internal.formatIntChars exp10) hd]
        have he_nd : Model.isDecDigit 'e' = false := by decide
        have he_nu : 'e' ≠ '_' := by decide
        have hpint := parseFloatIntPart_append_dec [d] (by simp) (fun c hc => by simp at hc; subst hc; exact hd)
          (by simp [hd0]) ('e' :: Internal.formatIntChars exp10)
          (Or.inr ⟨'e', Internal.formatIntChars exp10, rfl, he_nd, he_nu⟩)
        simp only [List.singleton_append, List.foldl_cons, List.foldl_nil, decStep, Nat.zero_mul,
          Nat.zero_add, hfold] at hpint
        rw [hpint]
        simp only [parseFloatExpPart_formatIntChars]
        rfl
    | cons r0 rs =>
      simp only []
      have hfold : (d :: r0 :: rs).foldl decStep 0 = mant := by
        rw [← hev, hds]
      have hallrest : ∀ c ∈ r0 :: rs, Model.isDecDigit c = true := hrest
      have hnu : ∀ c ∈ (if neg = true then ['-'] else []) ++ [d, '.'] ++ (r0 :: rs) ++ ['e'] ++
          Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length), c ≠ '_' := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · rcases List.mem_append.mp h1 with h1a | h1b
          · rcases List.mem_append.mp h1a with h1aa | h1ab
            · rcases List.mem_append.mp h1aa with h1aaa | h1aab
              · cases neg <;> simp at h1aaa; subst h1aaa; decide
              · simp at h1aab; rcases h1aab with rfl | rfl; exact (decDigit_props hd).1; decide
            · exact (decDigit_props (hallrest c h1ab)).1
          · simp at h1b; subst h1b; decide
        · exact formatIntChars_all_non_underscore _ c h2
      have hhasDot : ((if neg = true then ['-'] else []) ++ [d, '.'] ++ (r0 :: rs) ++ ['e'] ++
          Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length)).contains '.' = true := by
        simp
      refine ⟨?_, Or.inl ?_, ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_eq_false_of_forall hnu
      · simp only [String.contains_char_eq, String.toList_ofList]
        exact hhasDot
      · unfold Model.parseFloatModel
        rw [String.toList_ofList]
        have hreassoc : (if neg = true then ['-'] else []) ++ [d, '.'] ++ (r0 :: rs) ++ ['e'] ++
            Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length) =
            (if neg = true then ['-'] else []) ++
              d :: ('.' :: ((r0 :: rs) ++ 'e' ::
                Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length))) := by
          simp [List.append_assoc]
        rw [hreassoc, parseFloatModelChars_cons_decDigit neg d _ hd]
        have hdot_nd : Model.isDecDigit '.' = false := by decide
        have hdot_nu : '.' ≠ '_' := by decide
        have hpint := parseFloatIntPart_append_dec [d] (by simp) (fun c hc => by simp at hc; subst hc; exact hd)
          (by simp [hd0]) ('.' :: ((r0 :: rs) ++ 'e' :: Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length)))
          (Or.inr ⟨'.', _, rfl, hdot_nd, hdot_nu⟩)
        simp only [List.singleton_append, List.foldl_cons, List.foldl_nil, decStep, Nat.zero_mul,
          Nat.zero_add] at hpint
        rw [hpint]
        have hr0 : Model.isDecDigit r0 = true := hallrest r0 (by simp)
        have hr0nu : r0 ≠ '_' := (decDigit_props hr0).1
        have hrs : ∀ c ∈ rs, Model.isDecDigit c = true := fun c hc => hallrest c (by simp [hc])
        have he_nd : Model.isDecDigit 'e' = false := by decide
        have he_nu : 'e' ≠ '_' := by decide
        rw [List.cons_append]
        simp only []
        have hcon := consumeDecFloatDigits_append_dec rs hrs ('e' :: Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length))
          (Or.inr ⟨'e', _, rfl, he_nd, he_nu⟩) ((d.toNat - '0'.toNat) * 10 + (r0.toNat - '0'.toNat)) 1
        have hmant : rs.foldl decStep ((d.toNat - '0'.toNat) * 10 + (r0.toNat - '0'.toNat)) = mant := by
          rw [← hfold]
          simp [List.foldl_cons, decStep]
        have hexp : exp10 + Int.ofNat (r0 :: rs).length - Int.ofNat (1 + rs.length) = exp10 := by
          simp only [List.length_cons, Nat.add_comm rs.length 1]
          omega
        split
        · simp only [hcon, parseFloatExpPart_formatIntChars, List.isEmpty_nil, hmant, hexp, ↓reduceIte]
        · rename_i hnd; exact absurd hr0 hnd

private theorem evalFloat_eq_evalScientificFloat (neg : Bool) (m : Nat) (e : Int) :
    (Model.evalFloat neg m e).toBits = (Internal.evalScientificFloat neg m e).toBits := rfl

private theorem decFold_append (acc : Nat) (xs ys : List Char) :
    (xs ++ ys).foldl decStep acc = ys.foldl decStep (xs.foldl decStep acc) :=
  List.foldl_append

private theorem afterDot_zero (neg : Bool) (intVal : Nat) :
    (match (['.', '0'] : List Char) with
      | '.' :: afterDot =>
        match afterDot with
        | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
        | c :: rest2 =>
          if Model.isDecDigit c = true then
            match Model.consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest2 with
            | Except.error k => Except.error k
            | Except.ok (mantissa, fracCount, afterFrac) =>
              match afterFrac with
              | 'e' :: afterE =>
                match Model.parseFloatExpPart afterE with
                | Except.error k => Except.error k
                | Except.ok (expVal, afterExp) =>
                  if afterExp.isEmpty = true then
                    Except.ok (Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                  else Except.error NumParseErrorKind.trailingChars
              | 'E' :: afterE =>
                match Model.parseFloatExpPart afterE with
                | Except.error k => Except.error k
                | Except.ok (expVal, afterExp) =>
                  if afterExp.isEmpty = true then
                    Except.ok (Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                  else Except.error NumParseErrorKind.trailingChars
              | [] => Except.ok (Model.evalFloat neg mantissa (-Int.ofNat fracCount))
              | _ :: _ => Except.error NumParseErrorKind.trailingChars
          else Except.error NumParseErrorKind.invalidSyntax
        | [] => Except.error NumParseErrorKind.invalidSyntax
      | 'e' :: afterE =>
        match Model.parseFloatExpPart afterE with
        | Except.error k => Except.error k
        | Except.ok (expVal, afterExp) =>
          if afterExp.isEmpty = true then Except.ok (Model.evalFloat neg intVal expVal)
          else Except.error NumParseErrorKind.trailingChars
      | 'E' :: afterE =>
        match Model.parseFloatExpPart afterE with
        | Except.error k => Except.error k
        | Except.ok (expVal, afterExp) =>
          if afterExp.isEmpty = true then Except.ok (Model.evalFloat neg intVal expVal)
          else Except.error NumParseErrorKind.trailingChars
      | _ => Except.error NumParseErrorKind.invalidSyntax) =
      Except.ok (Model.evalFloat neg (intVal * 10) (-1)) := by
  have h0 : ('0'.toNat - '0'.toNat) = 0 := by decide
  change Except.ok (Model.evalFloat neg (intVal * 10 + ('0'.toNat - '0'.toNat)) (-1)) =
    Except.ok (Model.evalFloat neg (intVal * 10) (-1))
  rw [h0, Nat.add_zero]

private theorem renderFloatChoice_spec (neg : Bool) (mant : Nat) (hm : 0 < mant) (exp10 : Int) :
    let (effMant, effExp, s) := Internal.renderFloatChoice neg mant exp10
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      Model.parseFloatModel s = Except.ok (Model.evalFloat neg effMant effExp) := by
  unfold Internal.renderFloatChoice
  dsimp only
  have hne := natToDecCharsPos_nonempty hm
  have hall := natToDecCharsPos_all_dec mant
  have hhd := natToDecCharsPos_head_ne_zero hm
  have hev := natToDecCharsPos_eval mant 0
  simp only [Nat.zero_mul, Nat.zero_add] at hev
  split
  · split
    · rename_i hexp
      let ds := Internal.natToDecCharsPos mant []
      let pad := exp10.toNat
      let pfx := if neg = true then ['-'] else []
      have hds_ne : ds ++ List.replicate pad '0' ≠ [] := by
        intro h; exact hne (List.append_eq_nil_iff.mp h).1
      have hds_all : ∀ c ∈ ds ++ List.replicate pad '0', Model.isDecDigit c = true := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · exact hall c h1
        · rw [(List.mem_replicate.mp h2).2]; decide
      have hds_hd : (ds ++ List.replicate pad '0').head? ≠ some '0' := by
        cases hds : Internal.natToDecCharsPos mant [] with
        | nil => exact absurd hds hne
        | cons a as =>
          have hds' : ds = a :: as := hds
          rw [hds']
          simp only [List.cons_append, List.head?_cons]
          intro h; apply hhd; rw [hds]; exact h
      have hnu : ∀ c ∈ pfx ++ ds ++ List.replicate pad '0' ++ ['.', '0'], c ≠ '_' := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · rcases List.mem_append.mp h1 with h1a | h1b
          · rcases List.mem_append.mp h1a with h1aa | h1ab
            · cases neg <;> simp [pfx] at h1aa; subst h1aa; decide
            · exact (decDigit_props (hall c h1ab)).1
          · rw [(List.mem_replicate.mp h1b).2]; decide
        · simp at h2; rcases h2 with rfl | rfl <;> decide
      have hhasDot : (pfx ++ ds ++ List.replicate pad '0' ++ ['.', '0']).contains '.' = true := by
        simp
      refine ⟨?_, Or.inl ?_, ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_eq_false_of_forall hnu
      · simp only [String.contains_char_eq, String.toList_ofList]
        exact hhasDot
      · unfold Model.parseFloatModel
        rw [String.toList_ofList]
        change Model.parseFloatModelChars (pfx ++ ds ++ List.replicate pad '0' ++ ['.', '0']) =
          Except.ok (Model.evalFloat neg (mant * 10 ^ (pad + 1)) (-1))
        cases hds' : Internal.natToDecCharsPos mant [] with
        | nil => exact absurd hds' hne
        | cons d0 ds0 =>
          have hd0 : Model.isDecDigit d0 = true := hall d0 (by rw [hds']; exact List.mem_cons_self)
          have hreassoc : pfx ++ ds ++ List.replicate pad '0' ++ ['.', '0'] =
              pfx ++ d0 :: ((ds0 ++ List.replicate pad '0') ++ ['.', '0']) := by
            change pfx ++ Internal.natToDecCharsPos mant [] ++ List.replicate pad '0' ++ ['.', '0'] = _
            rw [hds']; simp [List.append_assoc]
          rw [hreassoc, parseFloatModelChars_cons_decDigit neg d0 _ hd0]
          have hdot_nd : Model.isDecDigit '.' = false := by decide
          have hdot_nu : '.' ≠ '_' := by decide
          have hpint := parseFloatIntPart_append_dec (ds ++ List.replicate pad '0') hds_ne hds_all hds_hd
            ['.', '0'] (Or.inr ⟨'.', ['0'], rfl, hdot_nd, hdot_nu⟩)
          have hseq : d0 :: ((ds0 ++ List.replicate pad '0') ++ ['.', '0']) =
              (ds ++ List.replicate pad '0') ++ ['.', '0'] := by
            change d0 :: ((ds0 ++ List.replicate pad '0') ++ ['.', '0']) =
              (Internal.natToDecCharsPos mant [] ++ List.replicate pad '0') ++ ['.', '0']
            rw [hds']; simp [List.append_assoc]
          rw [hseq, hpint]
          dsimp only
          rw [afterDot_zero, decFold_append, hev, decFold_zeros, Nat.pow_succ, Nat.mul_assoc]
    · rename_i hexp
      let ds := Internal.natToDecCharsPos mant []
      let len := ds.length
      let k := (-exp10).toNat
      have hkpos : 0 < k := by
        dsimp only [k]
        cases exp10 with
        | ofNat n => exact absurd (Int.natCast_nonneg n) hexp
        | negSucc n => simp [Int.negSucc_eq]
      have hkeq : (-Int.ofNat k) = exp10 := by
        dsimp only [k]
        cases exp10 with
        | ofNat n => exact absurd (Int.natCast_nonneg n) hexp
        | negSucc n => simp [Int.negSucc_eq]
      split
      · rename_i hklt
        let splitIdx := len - k
        have hsp_pos : 0 < splitIdx := by dsimp only [splitIdx, len, ds, k]; omega
        have hsp_le : splitIdx ≤ len := by dsimp only [splitIdx, len, ds, k]; omega
        let ds1 := ds.take splitIdx
        let ds2 := ds.drop splitIdx
        have hds1_ne : ds1 ≠ [] := by
          intro h
          have hlen0 : ds1.length = 0 := by rw [h]; rfl
          change (ds.take splitIdx).length = 0 at hlen0
          rw [List.length_take, Nat.min_eq_left hsp_le] at hlen0
          omega
        have hds2_len : ds2.length = k := by
          simp [ds2, List.length_drop]
          dsimp only [splitIdx, len, ds, k] at *
          omega
        have hds2_ne : ds2 ≠ [] := by
          intro h; rw [h] at hds2_len; simp at hds2_len; omega
        have hds_split : ds1 ++ ds2 = ds := List.take_append_drop splitIdx ds
        have hds1_all : ∀ c ∈ ds1, Model.isDecDigit c = true := fun c hc => hall c (List.mem_of_mem_take hc)
        have hds2_all : ∀ c ∈ ds2, Model.isDecDigit c = true := fun c hc => hall c (List.mem_of_mem_drop hc)
        have hds1_hd : ds1.head? ≠ some '0' := by
          cases h1 : ds1 with
          | nil => exact absurd h1 hds1_ne
          | cons a as =>
            intro hh
            have hds_hd : ds.head? = some '0' := by
              rw [← hds_split, h1]; exact hh
            exact hhd hds_hd
        let pfx := if neg = true then ['-'] else []
        have hnu : ∀ c ∈ pfx ++ ds1 ++ ['.'] ++ ds2, c ≠ '_' := by
          intro c hc
          rcases List.mem_append.mp hc with h1 | h2
          · rcases List.mem_append.mp h1 with h1a | h1b
            · rcases List.mem_append.mp h1a with h1aa | h1ab
              · cases neg <;> simp [pfx] at h1aa; subst h1aa; decide
              · exact (decDigit_props (hds1_all c h1ab)).1
            · simp at h1b; subst h1b; decide
          · exact (decDigit_props (hds2_all c h2)).1
        have hhasDot : (pfx ++ ds1 ++ ['.'] ++ ds2).contains '.' = true := by
          simp
        refine ⟨?_, Or.inl ?_, ?_⟩
        · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
          exact list_contains_eq_false_of_forall hnu
        · simp only [String.contains_char_eq, String.toList_ofList]
          exact hhasDot
        · unfold Model.parseFloatModel
          rw [String.toList_ofList]
          cases h1 : ds1 with
          | nil => exact absurd h1 hds1_ne
          | cons d0 ds0 =>
            have hd0 : Model.isDecDigit d0 = true := hds1_all d0 (by rw [h1]; simp)
            have hreassoc : pfx ++ (d0 :: ds0) ++ ['.'] ++ ds2 = pfx ++ d0 :: (ds0 ++ '.' :: ds2) := by
              simp [List.append_assoc]
            have hreassoc2 : pfx ++ ds1 ++ ['.'] ++ ds2 = pfx ++ d0 :: (ds0 ++ '.' :: ds2) := by
              rw [h1]; exact hreassoc
            rw [hreassoc2, parseFloatModelChars_cons_decDigit neg d0 _ hd0]
            have hdot_nd : Model.isDecDigit '.' = false := by decide
            have hdot_nu : '.' ≠ '_' := by decide
            have hpint := parseFloatIntPart_append_dec ds1 hds1_ne hds1_all hds1_hd ('.' :: ds2)
              (Or.inr ⟨'.', ds2, rfl, hdot_nd, hdot_nu⟩)
            have hseq : d0 :: (ds0 ++ '.' :: ds2) = ds1 ++ '.' :: ds2 := by rw [h1]; simp
            rw [hseq, hpint]
            cases h2 : ds2 with
            | nil => exact absurd h2 hds2_ne
            | cons f0 frest =>
              have hf0 : Model.isDecDigit f0 = true := hds2_all f0 (by rw [h2]; simp)
              have hf0nu : f0 ≠ '_' := (decDigit_props hf0).1
              have hfrest : ∀ c ∈ frest, Model.isDecDigit c = true := fun c hc => hds2_all c (by rw [h2]; simp [hc])
              simp only []
              split
              · have hcon := consumeDecFloatDigits_append_dec frest hfrest [] (Or.inl rfl)
                  (ds1.foldl decStep 0 * 10 + (f0.toNat - '0'.toNat)) 1
                simp only [List.append_nil] at hcon
                rw [hcon]
                have hmant : frest.foldl decStep (ds1.foldl decStep 0 * 10 + (f0.toNat - '0'.toNat)) = mant := by
                  have h' : (ds1 ++ (f0 :: frest)).foldl decStep 0 = mant := by
                    rw [← h2, hds_split]; exact hev
                  rw [decFold_append, List.foldl_cons] at h'
                  exact h'
                have hexp' : -Int.ofNat (1 + frest.length) = exp10 := by
                  have hl : 1 + frest.length = k := by
                    rw [← hds2_len, h2]; simp [Nat.add_comm]
                  rw [hl, hkeq]
                simp only [hmant, hexp']
              · rename_i hnd; exact absurd hf0 hnd
      · rename_i hklt
        have hlen_eq : len = (Internal.natToDecCharsPos mant []).length := rfl
        rw [← hlen_eq] at hklt
        let zeros := List.replicate (k - len) '0'
        have hfrac_ne : zeros ++ ds ≠ [] := by
          intro h; exact hne (List.append_eq_nil_iff.mp h).2
        have hfrac_all : ∀ c ∈ zeros ++ ds, Model.isDecDigit c = true := by
          intro c hc
          rcases List.mem_append.mp hc with h1 | h2
          · rw [(List.mem_replicate.mp h1).2]; decide
          · exact hall c h2
        have hfrac_len : (zeros ++ ds).length = k := by
          simp [zeros, len, ds]; omega
        let pfx := if neg = true then ['-'] else []
        have hnu : ∀ c ∈ pfx ++ ['0', '.'] ++ zeros ++ ds, c ≠ '_' := by
          intro c hc
          rcases List.mem_append.mp hc with h1 | h2
          · rcases List.mem_append.mp h1 with h1a | h1b
            · rcases List.mem_append.mp h1a with h1aa | h1ab
              · cases neg <;> simp [pfx] at h1aa; subst h1aa; decide
              · simp at h1ab; rcases h1ab with rfl | rfl <;> decide
            · rw [(List.mem_replicate.mp h1b).2]; decide
          · exact (decDigit_props (hall c h2)).1
        have hhasDot : (pfx ++ ['0', '.'] ++ zeros ++ ds).contains '.' = true := by
          simp
        refine ⟨?_, Or.inl ?_, ?_⟩
        · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
          exact list_contains_eq_false_of_forall hnu
        · simp only [String.contains_char_eq, String.toList_ofList]
          exact hhasDot
        · unfold Model.parseFloatModel
          rw [String.toList_ofList]
          have hz_dec : Model.isDecDigit '0' = true := by decide
          have hreassoc : pfx ++ ['0', '.'] ++ zeros ++ ds = pfx ++ '0' :: ('.' :: (zeros ++ ds)) := by
            simp [List.append_assoc]
          rw [hreassoc, parseFloatModelChars_cons_decDigit neg '0' _ hz_dec]
          have hpint0 : Model.parseFloatIntPart ('0' :: '.' :: (zeros ++ ds)) =
              Except.ok (0, '.' :: (zeros ++ ds)) := by
            unfold Model.parseFloatIntPart
            have hd_nd : Model.isDecDigit '.' = false := by decide
            have hd_nu : ('.' == '_') = false := by decide
            simp [hd_nd, hd_nu]
          rw [hpint0]
          cases hf : zeros ++ ds with
          | nil => exact absurd hf hfrac_ne
          | cons f0 frest =>
            have hf0 : Model.isDecDigit f0 = true := hfrac_all f0 (by rw [hf]; simp)
            have hf0nu : f0 ≠ '_' := (decDigit_props hf0).1
            have hfrest : ∀ c ∈ frest, Model.isDecDigit c = true := fun c hc => hfrac_all c (by rw [hf]; simp [hc])
            simp only []
            split
            · have hcon := consumeDecFloatDigits_append_dec frest hfrest [] (Or.inl rfl)
                (0 * 10 + (f0.toNat - '0'.toNat)) 1
              simp only [List.append_nil] at hcon
              rw [hcon]
              have hmant : frest.foldl decStep (0 * 10 + (f0.toNat - '0'.toNat)) = mant := by
                have h' : (zeros ++ ds).foldl decStep 0 = mant := by
                  rw [decFold_append, decFold_zeros_zero]; exact hev
                rw [hf, List.foldl_cons] at h'
                exact h'
              have hexp' : -Int.ofNat (1 + frest.length) = exp10 := by
                have hl : 1 + frest.length = k := by
                  rw [← hfrac_len, hf]; simp [Nat.add_comm]
                rw [hl, hkeq]
              simp only [hmant, hexp']
            · rename_i hnd; exact absurd hf0 hnd
  · exact renderScientific_spec neg mant hm exp10

private theorem stripTrailingZeros_pos {mant : Nat} (hm : 0 < mant) (exp10 : Int) :
    0 < (Internal.stripTrailingZeros mant exp10).1 := by
  induction mant using Nat.strongRecOn generalizing exp10 with
  | ind mant ih =>
    rw [Internal.stripTrailingZeros.eq_def]
    have hnz : mant ≠ 0 := by omega
    simp only [hnz, ↓reduceDIte]
    by_cases hmod : mant % 10 = 0
    · have hbmod : (mant % 10 == 0) = true := beq_iff_eq.mpr hmod
      simp only [hbmod, ↓reduceIte]
      have hge10 : 10 ≤ mant := by omega
      have hdivpos : 0 < mant / 10 := by omega
      have hdivlt : mant / 10 < mant := Nat.div_lt_self hm (by decide)
      exact ih (mant / 10) hdivlt hdivpos (exp10 + 1)
    · have hbmod : (mant % 10 == 0) = false := beq_false_of_ne hmod
      simp only [hbmod, Bool.false_eq_true, ↓reduceIte]
      exact hm

private theorem checkFloatCandidate_spec {x : Float} {neg : Bool} {mant : Nat} {exp10 : Int} {s : String}
    (h : Internal.checkFloatCandidate x neg mant exp10 = some s) :
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
  unfold Internal.checkFloatCandidate at h
  by_cases hz : mant = 0
  · have hbz : (mant == 0) = true := beq_iff_eq.mpr hz
    simp [hbz] at h
  · have hbz : (mant == 0) = false := beq_false_of_ne hz
    simp only [hbz, Bool.false_eq_true, ↓reduceIte] at h
    have hmpos : 0 < mant := Nat.pos_of_ne_zero hz
    have hm'pos : 0 < (Internal.stripTrailingZeros mant exp10).1 := stripTrailingZeros_pos hmpos exp10
    cases hst : Internal.stripTrailingZeros mant exp10 with
    | mk m' e' =>
      rw [hst] at h hm'pos
      have hr := renderFloatChoice_spec neg m' hm'pos e'
      rcases hrc : Internal.renderFloatChoice neg m' e' with ⟨effMant, effExp, str⟩
      rw [hrc] at h hr
      simp only [] at h hr
      by_cases hbits : (Internal.evalScientificFloat neg effMant effExp).toBits = x.toBits
      · have hbbits : ((Internal.evalScientificFloat neg effMant effExp).toBits == x.toBits) = true :=
          beq_iff_eq.mpr hbits
        simp only [hbbits, ↓reduceIte] at h
        injection h with hs
        subst hs
        exact ⟨hr.1, hr.2.1, Model.evalFloat neg effMant effExp, hr.2.2, by
          rw [evalFloat_eq_evalScientificFloat]; exact hbits⟩
      · have hbbits : ((Internal.evalScientificFloat neg effMant effExp).toBits == x.toBits) = false :=
          beq_false_of_ne hbits
        simp [hbbits] at h

private theorem tryDigitsCount_spec {x : Float} {neg : Bool} {m : Nat} {e2 kEst : Int} {d : Nat} {s : String}
    (h : Internal.tryDigitsCount x neg m e2 kEst d = some s) :
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
  have htryOne : ∀ e10 q0,
      (match Internal.checkFloatCandidate x neg q0 e10 with
        | some s => some s
        | none =>
          match Internal.checkFloatCandidate x neg (q0 + 1) e10 with
          | some s => some s
          | none => if 1 < q0 then Internal.checkFloatCandidate x neg (q0 - 1) e10 else none) = some s →
      (!s.contains '_') = true ∧
        (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
        ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
    intro e10 q0 h0
    split at h0
    · injection h0 with hs; subst hs; rename_i hc; exact checkFloatCandidate_spec hc
    · split at h0
      · injection h0 with hs; subst hs; rename_i _ hc; exact checkFloatCandidate_spec hc
      · split at h0
        · exact checkFloatCandidate_spec h0
        · simp at h0
  unfold Internal.tryDigitsCount at h
  simp only [] at h
  split at h
  · injection h with hs; subst hs; rename_i h1
    exact htryOne (kEst - Int.ofNat d + 1) _ h1
  · exact htryOne (kEst - Int.ofNat d + 1 - 1) _ h

private theorem searchShortCandidate_spec {x : Float} {neg : Bool} {m : Nat} {e2 kEst : Int} {rem : Nat} {s : String}
    (h : Internal.searchShortCandidate x neg m e2 kEst rem = some s) :
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
  induction rem with
  | zero =>
    rw [Internal.searchShortCandidate.eq_1] at h
    simp at h
  | succ k ih =>
    rw [Internal.searchShortCandidate.eq_2] at h
    split at h
    · injection h with hs; subst hs; rename_i ht
      exact tryDigitsCount_spec ht
    · exact ih h

private theorem nat_log2_pow2_bounds (n : Nat) (hn : 0 < n) :
    2 ^ n.log2 ≤ n ∧ n < 2 ^ (n.log2 + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.log2_def]
    by_cases h2 : 2 ≤ n
    · simp only [h2, ↓reduceIte]
      have hdpos : 0 < n / 2 := by omega
      have hdlt : n / 2 < n := Nat.div_lt_self hn (by decide)
      obtain ⟨hlo, hhi⟩ := ih (n / 2) hdlt hdpos
      constructor
      · rw [Nat.pow_succ]; omega
      · rw [Nat.pow_succ]; omega
    · simp only [h2, ↓reduceIte]
      omega

private theorem nat_log2_eq_of_bounds {n k : Nat} (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1)) :
    n.log2 = k := by
  have hkpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hnpos : 0 < n := Nat.lt_of_lt_of_le hkpos hlo
  obtain ⟨hl, hr⟩ := nat_log2_pow2_bounds n hnpos
  have h1 : 2 ^ n.log2 < 2 ^ (k + 1) := Nat.lt_of_le_of_lt hl hhi
  have h2 : 2 ^ k < 2 ^ (n.log2 + 1) := Nat.lt_of_le_of_lt hlo hr
  have hlt1 : n.log2 < k + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h1
  have hlt2 : k < n.log2 + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
  omega

private theorem nat_log2_mul_pow2 (a s : Nat) (ha : 0 < a) :
    (a * 2 ^ s).log2 = a.log2 + s := by
  obtain ⟨hlo, hhi⟩ := nat_log2_pow2_bounds a ha
  apply nat_log2_eq_of_bounds
  · rw [Nat.pow_add]
    exact Nat.mul_le_mul_right (2 ^ s) hlo
  · rw [Nat.add_right_comm, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hhi (Nat.pow_pos (by decide))

private theorem nat_log2_mul_bounds (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    a.log2 + b.log2 ≤ (a * b).log2 ∧ (a * b).log2 ≤ a.log2 + b.log2 + 1 := by
  obtain ⟨halo, hahi⟩ := nat_log2_pow2_bounds a ha
  obtain ⟨hblo, hbhi⟩ := nat_log2_pow2_bounds b hb
  have hab : 0 < a * b := Nat.mul_pos ha hb
  obtain ⟨hlo, hhi⟩ := nat_log2_pow2_bounds (a * b) hab
  have hpow_lo : 2 ^ (a.log2 + b.log2) ≤ a * b := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul halo hblo
  have hpow_hi : a * b < 2 ^ (a.log2 + b.log2 + 2) := by
    have hmul : a * b < 2 ^ (a.log2 + 1) * 2 ^ (b.log2 + 1) :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right b (Nat.le_of_lt hahi))
        (Nat.mul_lt_mul_of_pos_left hbhi (Nat.pow_pos (by decide)))
    have hexp : 2 ^ (a.log2 + 1) * 2 ^ (b.log2 + 1) = 2 ^ (a.log2 + b.log2 + 2) := by
      rw [← Nat.pow_add]
      congr 1; omega
    exact hexp ▸ hmul
  have h1 : 2 ^ (a.log2 + b.log2) < 2 ^ ((a * b).log2 + 1) := Nat.lt_of_le_of_lt hpow_lo hhi
  have h2 : 2 ^ (a * b).log2 < 2 ^ (a.log2 + b.log2 + 2) := Nat.lt_of_le_of_lt hlo hpow_hi
  have hlt1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h1
  have hlt2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
  omega

private theorem extendedMantissa_shift_exact_mul_pow2 (m s : Nat) :
    (Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ s) .exact >>> s) =
      ⟨m, false, false⟩ := by
  induction s generalizing m with
  | zero =>
    simp [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
      HShiftRight.hShiftRight, Nat.repeat]
  | succ k ih =>
    have hm2 : m * 2 ^ (k + 1) = (m * 2) * 2 ^ k := by
      rw [Nat.pow_succ', ← Nat.mul_assoc]
    have hrep : ∀ em : Float.Model.UnpackedFloat.ExtendedMantissa,
        (em >>> (k + 1)) = Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne (em >>> k) := by
      intro em; rfl
    rw [hrep, hm2]
    have ihk := ih (m * 2)
    change Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne
      (Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy ((m * 2) * 2 ^ k) .exact >>> k) =
      ⟨m, false, false⟩
    rw [ihk]
    simp [Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne]

private theorem shiftRightOne_two_mul (m : Nat) :
    Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne ⟨2 * m, false, false⟩ = ⟨m, false, false⟩ := by
  simp [Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne]

private theorem shiftToTargetExponent_exact (m : Nat) (e2 : Int)
    (htarg : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent m e2) = e2) :
    Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 m e2 .exact =
      (⟨m, false, false⟩, e2) := by
  unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
  rw [htarg]
  dsimp only
  have hsh0 : (e2 - e2).toNat = 0 := by omega
  rw [hsh0]
  simp [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
    HShiftRight.hShiftRight, Nat.repeat]

private theorem roundWithAccuracy_binary64_pos_exact (m : Nat) (e2 : Int)
    (hvalid : (e2 = -1074 ∧ 0 < m ∧ m < 2 ^ 52) ∨ (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e2 ∧ e2 ≤ 971)) :
    (Float.Model.UnpackedFloat.roundWithAccuracy Float.Model.Format.binary64 .positive m e2 .exact) =
      .finite .positive m e2 (by rcases hvalid with ⟨_, hm, _⟩ | ⟨hm, _⟩ <;> omega) := by
  have hmpos : 0 < m := by rcases hvalid with ⟨_, hm, _⟩ | ⟨hm, _⟩ <;> omega
  have htarg : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent m e2) = e2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent
    have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
    have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
    rw [hmb, hmin]
    rcases hvalid with ⟨rfl, hm0, hm52⟩ | ⟨hm52, hm53, he_lo, he_hi⟩
    · have hloglt : m.log2 < 52 := by
        obtain ⟨hlo, _⟩ := nat_log2_pow2_bounds m hm0
        have hlt : 2 ^ m.log2 < 2 ^ 52 := Nat.lt_of_le_of_lt hlo hm52
        exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
      omega
    · have hlog : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
      omega
  unfold Float.Model.UnpackedFloat.roundWithAccuracy
  simp only [shiftToTargetExponent_exact m e2 htarg,
    Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
    Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
    Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]
  have hmne : m ≠ 0 := by omega
  simp only [hmne, ↓reduceDIte]

private theorem roundWithAccuracy_binary64_pos_double (m : Nat) (e2 : Int)
    (hm52 : 2 ^ 52 ≤ m) (hm53 : m < 2 ^ 53) (he_lo : -1073 ≤ e2) (he_hi : e2 ≤ 971) :
    Float.Model.UnpackedFloat.roundWithAccuracy Float.Model.Format.binary64 .positive (2 * m) (e2 - 1) .exact =
      .finite .positive m e2 (by omega) := by
  have hmpos : 0 < m := by omega
  have hlog : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
  have hlog2 : (2 * m).log2 = 53 := by
    have hpow : 2 * m = m * 2 ^ 1 := by omega
    rw [hpow, nat_log2_mul_pow2 m 1 hmpos, hlog]
  have htarg : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent (2 * m) (e2 - 1)) = e2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent
    have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
    have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
    rw [hmb, hmin, hlog2]
    omega
  have htarg2 : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent m e2) = e2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent
    have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
    have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
    rw [hmb, hmin, hlog]
    omega
  unfold Float.Model.UnpackedFloat.roundWithAccuracy
  have hsh1_step : Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 (2 * m) (e2 - 1) .exact =
      (⟨m, false, false⟩, e2) := by
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
    rw [htarg]
    dsimp only
    have hsh1 : (e2 - (e2 - 1)).toNat = 1 := by omega
    rw [hsh1]
    simp only [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
      HShiftRight.hShiftRight, Nat.repeat]
    rw [shiftRightOne_two_mul]
    exact Prod.ext rfl (by omega)
  rw [hsh1_step]
  dsimp only
  simp only [shiftToTargetExponent_exact m e2 htarg2,
    Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
    Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
    Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]
  have hmne : m ≠ 0 := by omega
  simp only [hmne, ↓reduceDIte]

private theorem packComponents_unpack_eq (b : BitVec 64) :
    Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64
      (Float.Model.UnpackedFloat.Sign.ofBitVec
        (Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64) b))
      (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b)
      (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b) = b := by
  let signVec := Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64) b
  have hsign : (Float.Model.UnpackedFloat.Sign.ofBitVec signVec).toBitVec = signVec := by
    unfold Float.Model.UnpackedFloat.Sign.ofBitVec
    split
    · rename_i h; rw [h]; rfl
    · rename_i h
      have h1 : signVec = 1#1 := by
        have hb : signVec.toNat < 2 ^ 1 := signVec.isLt
        have hb2 : signVec.toNat < 2 := Nat.lt_of_lt_of_eq hb (by decide)
        have hnz : signVec.toNat ≠ 0 := by
          intro hz; apply h; exact BitVec.eq_of_toNat_eq hz
        have hnat1 : signVec.toNat = (1#1 : BitVec 1).toNat := by
          change signVec.toNat = 1
          omega
        exact BitVec.eq_of_toNat_eq hnat1
      rw [h1]; rfl
  rw [Float.Model.UnpackedFloat.packComponents, hsign]
  ext i hi
  have hlen : 1 + Float.Model.Format.binary64.exponentBits + Float.Model.Format.binary64.mantissaBitsWithoutImplicit = 64 := rfl
  rw [hlen] at hi
  have hget : ∀ j (hj : j < 64), b.getLsbD j = b[j] := fun j hj => BitVec.getLsbD_eq_getElem hj
  simp only [signVec, Float.Model.UnpackedFloat.unpackSign,
    Float.Model.UnpackedFloat.unpackExponent, Float.Model.UnpackedFloat.unpackMantissa,
    Float.Model.Format.binary64]
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  by_cases h52 : i < 52
  · simp only [h52, ↓reduceDIte]
    rw [hget _ (by omega)]
    congr 1; omega
  · by_cases h63 : i < 63
    · have h11 : i - 52 < 11 := by omega
      simp only [h52, ↓reduceDIte, h11]
      rw [hget _ (by omega)]
      congr 1; omega
    · have h1 : i - 63 < 1 := by omega
      have hn11 : ¬(i - 52 < 11) := by omega
      simp only [h52, ↓reduceDIte, hn11]
      rw [hget _ (by omega)]
      congr 1; omega

private theorem unpackSign_packComponents
    {sign : Float.Model.UnpackedFloat.Sign}
    {exponent : BitVec 11}
    {mantissa : BitVec 52} :
    Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64)
        (Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 sign exponent mantissa) =
      sign.toBitVec := by
  ext i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp only [Float.Model.UnpackedFloat.unpackSign, Float.Model.UnpackedFloat.packComponents,
    Float.Model.Format.binary64, BitVec.getElem_extractLsb']
  have hget : ∀ (v : BitVec (1 + 11 + 52)) j (hj : j < 64), v.getLsbD j = v[j] :=
    fun v j hj => BitVec.getLsbD_eq_getElem hj
  rw [hget _ 63 (by omega)]
  rw [BitVec.getElem_append]
  split
  · omega
  · rw [BitVec.getElem_append]
    split
    · omega
    · rfl

private theorem unpack_finite_props (x : Float) (sign : Float.Model.UnpackedFloat.Sign)
    (m : Nat) (e2 : Int) (hm : 0 < m)
    (hun : x.toModel.unpack = .finite sign m e2 hm) :
    ((e2 = -1074 ∧ 0 < m ∧ m < 2 ^ 52) ∨ (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e2 ∧ e2 ≤ 971)) ∧
      (Float.Model.pack (.finite sign m e2 hm)).toBits = x.toModel.toBits := by
  let b : BitVec 64 := x.toModel.toBits.toBitVec
  have hun_def : Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 b = .finite sign m e2 hm := hun
  unfold Float.Model.UnpackedFloat.unpack at hun_def
  dsimp only at hun_def
  have hrepack : Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64
      (Float.Model.UnpackedFloat.Sign.ofBitVec (Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64) b))
      (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b)
      (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b) = b :=
    packComponents_unpack_eq b
  by_cases hexp1 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = -1#11
  · simp only [hexp1, ↓reduceIte] at hun_def
    split at hun_def <;> cases hun_def
  · simp only [hexp1, ↓reduceIte] at hun_def
    by_cases hexp0 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = 0#11
    · simp only [hexp0, ↓reduceIte] at hun_def
      by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
      · simp [hmant0] at hun_def
      · simp only [hmant0, ↓reduceDIte, Float.Model.UnpackedFloat.finite.injEq] at hun_def
        rcases hun_def with ⟨rfl, rfl, rfl⟩
        have hm52 : (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat < 2 ^ 52 :=
          (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).isLt
        have hmpos : 0 < (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat := by
          have : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b ≠ 0#52 := hmant0
          exact Nat.pos_of_ne_zero (fun hz => this (BitVec.eq_of_toNat_eq hz))
        have heq : (↑(0#11 : BitVec 11).toNat -
            (↑Float.Model.Format.binary64.exponentBias + ↑Float.Model.Format.binary64.mantissaBitsWithoutImplicit) + 1 : Int) = -1074 := rfl
        rw [heq]
        refine ⟨Or.inl ⟨rfl, hmpos, hm52⟩, ?_⟩
        apply congrArg UInt64.ofBitVec
        simp only [Float.Model.UnpackedFloat.pack]
        have hloglt : (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat.log2 < 52 := by
          obtain ⟨hlo, _⟩ := nat_log2_pow2_bounds _ hmpos
          exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt hlo hm52)
        have hbiased : ((-1074 : Int) + Float.Model.Format.binary64.exponentBias +
            Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat = 1 := rfl
        have hcond1 : ¬(2 ^ Float.Model.Format.binary64.exponentBits ≤ 1 + 1) := by decide
        have hcond2 : ¬((Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat.log2 + 1 =
            Float.Model.Format.binary64.mantissaBits) := by
          change ¬(_ + 1 = 53); omega
        simp only [hbiased, hcond1, ↓reduceIte, hcond2]
        have hmbv : BitVec.ofNat 52 (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat =
            Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b :=
          BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt hm52)
        rw [← hexp0, hmbv]
        exact hrepack
    · simp only [hexp0, ↓reduceIte, Float.Model.UnpackedFloat.finite.injEq] at hun_def
      rcases hun_def with ⟨rfl, rfl, rfl⟩
      have hexp_lt : (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat < 2047 := by
        have hle : (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat < 2048 :=
          (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).isLt
        have hne : (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat ≠ 2047 := by
          intro h; apply hexp1; exact BitVec.eq_of_toNat_eq h
        omega
      have hexp_pos : 0 < (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat := by
        have hne : (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat ≠ 0 := by
          intro h; apply hexp0; exact BitVec.eq_of_toNat_eq h
        omega
      have hm_val : (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat =
          2 ^ 52 + (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat := by
        rw [BitVec.toNat_append_eq_mul_add]; rfl
      have hm_lo : 2 ^ 52 ≤ (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat := by
        rw [hm_val]; omega
      have hm_hi : (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat < 2 ^ 53 := by
        have h52 : (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat < 2 ^ 52 :=
          (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).isLt
        rw [hm_val]; omega
      have he_val : (((Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat : Int) -
          (Float.Model.Format.binary64.exponentBias + Float.Model.Format.binary64.mantissaBitsWithoutImplicit)) =
          ((Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat : Int) - 1075 := rfl
      rw [he_val]
      refine ⟨Or.inr ⟨hm_lo, hm_hi, by omega, by omega⟩, ?_⟩
      apply congrArg UInt64.ofBitVec
      simp only [Float.Model.UnpackedFloat.pack]
      have hlog : (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat.log2 = 52 :=
        nat_log2_eq_of_bounds hm_lo hm_hi
      have hbiased : ((((Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat : Int) -
          1075) +
          Float.Model.Format.binary64.exponentBias + Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat =
          (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat := by
        have hbm : (Float.Model.Format.binary64.exponentBias +
            Float.Model.Format.binary64.mantissaBitsWithoutImplicit : Int) = 1075 := rfl
        rw [Int.add_assoc, hbm]; omega
      have hcond1 : ¬(2 ^ Float.Model.Format.binary64.exponentBits ≤
          (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat + 1) := by
        change ¬(2048 ≤ _ + 1); omega
      have hcond2 : (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat.log2 + 1 =
          Float.Model.Format.binary64.mantissaBits := by
        rw [hlog]; rfl
      simp only [hbiased, hcond1, ↓reduceIte, hcond2]
      have hebv : BitVec.ofNat 11 (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat =
          Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b :=
        BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).isLt)
      have hmbv : BitVec.ofNat 52 (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat =
          Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b := by
        apply BitVec.eq_of_toNat_eq
        have h52 := (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).isLt
        simp only [BitVec.toNat_ofNat, hm_val, Nat.add_mod_left, Nat.mod_eq_of_lt h52]
      rw [hebv, hmbv]
      exact hrepack

private theorem neg_pack_finite_pos (m : Nat) (e2 : Int) (hm : 0 < m)
    (hvalid : (e2 = -1074 ∧ 0 < m ∧ m < 2 ^ 52) ∨ (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e2 ∧ e2 ≤ 971)) :
    Float.Model.neg (Float.Model.pack (.finite .positive m e2 hm)) =
      Float.Model.pack (.finite .negative m e2 hm) := by
  have hunpack : (Float.Model.pack (.finite .positive m e2 hm)).unpack = .finite .positive m e2 hm := by
    unfold Float.Model.unpack Float.Model.pack Float.Model.UnpackedFloat.pack
    dsimp only
    have hbm : (Float.Model.Format.binary64.exponentBias +
        Float.Model.Format.binary64.mantissaBitsWithoutImplicit : Int) = 1075 := rfl
    have hbiased : (e2 + Float.Model.Format.binary64.exponentBias +
        Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat = (e2 + 1075).toNat := by
      rw [Int.add_assoc, hbm]
    rcases hvalid with ⟨rfl, hm0, hm52⟩ | ⟨hm52, hm53, he_lo, he_hi⟩
    · have hloglt : m.log2 < 52 := by
        obtain ⟨hlo, _⟩ := nat_log2_pow2_bounds m hm0
        exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt hlo hm52)
      have hbiased1 : ((-1074 : Int) + Float.Model.Format.binary64.exponentBias +
          Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat = 1 := rfl
      have hcond1 : ¬(2 ^ Float.Model.Format.binary64.exponentBits ≤ 1 + 1) := by decide
      have hcond2 : ¬(m.log2 + 1 = Float.Model.Format.binary64.mantissaBits) := by
        change ¬(m.log2 + 1 = 53); omega
      simp only [hbiased1, hcond1, ↓reduceIte, hcond2]
      unfold Float.Model.UnpackedFloat.unpack
      simp only [Float.Model.UnpackedFloat.unpackExponent_packComponents,
        Float.Model.UnpackedFloat.unpackMantissa_packComponents]
      have hsign : Float.Model.UnpackedFloat.Sign.ofBitVec
          (Float.Model.UnpackedFloat.unpackSign
            (Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 .positive 0#_ (BitVec.ofNat _ m))) =
          .positive := by
        rw [unpackSign_packComponents]; rfl
      have hexp1 : (0#11 : BitVec 11) ≠ -1#11 := by decide
      have hmant_ne : (BitVec.ofNat 52 m) ≠ 0#52 := by
        intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt hm52] at this; omega
      simp only [hsign, hexp1, ↓reduceIte, hmant_ne, ↓reduceDIte, Float.Model.UnpackedFloat.finite.injEq]
      refine ⟨trivial, Nat.mod_eq_of_lt hm52, rfl⟩
    · have hlog : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
      have hcond1 : ¬(2 ^ Float.Model.Format.binary64.exponentBits ≤ (e2 + 1075).toNat + 1) := by
        change ¬(2048 ≤ (e2 + 1075).toNat + 1); omega
      have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
      have hcond2 : m.log2 + 1 = Float.Model.Format.binary64.mantissaBits := by
        rw [hmb, hlog]
      simp only [hbiased, hcond1, ↓reduceIte, hcond2]
      unfold Float.Model.UnpackedFloat.unpack
      simp only [Float.Model.UnpackedFloat.unpackExponent_packComponents,
        Float.Model.UnpackedFloat.unpackMantissa_packComponents]
      have hsign : Float.Model.UnpackedFloat.Sign.ofBitVec
          (Float.Model.UnpackedFloat.unpackSign
            (Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 .positive
              (BitVec.ofNat _ (e2 + 1075).toNat) (BitVec.ofNat _ m))) = .positive := by
        rw [unpackSign_packComponents]; rfl
      have hlt2047 : (e2 + 1075).toNat < 2047 := by omega
      have hpos_e : 0 < (e2 + 1075).toNat := by omega
      have hexp_ne1 : BitVec.ofNat 11 (e2 + 1075).toNat ≠ -1#11 := by
        intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt (by omega : (e2 + 1075).toNat < 2048)] at this; omega
      have hexp_ne0 : BitVec.ofNat 11 (e2 + 1075).toNat ≠ 0#11 := by
        intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt (by omega : (e2 + 1075).toNat < 2048)] at this; omega
      simp only [hsign, hexp_ne1, ↓reduceIte, hexp_ne0, Float.Model.UnpackedFloat.finite.injEq]
      refine ⟨trivial, ?_, ?_⟩
      · have hlt52 : m - 2 ^ 52 < 2 ^ 52 :=
          Nat.sub_lt_left_of_lt_add hm52 (by rw [← Nat.two_mul]; exact hm53)
        have hsub52 : 2 ^ 52 + (m - 2 ^ 52) = m := Nat.add_sub_cancel' hm52
        have hmod52 : (BitVec.ofNat 52 m).toNat = m - 2 ^ 52 := by
          simp only [BitVec.toNat_ofNat]
          have hmod := Nat.add_mod_left (2 ^ 52) (m - 2 ^ 52)
          rw [hsub52] at hmod
          rw [hmod, Nat.mod_eq_of_lt hlt52]
        rw [BitVec.toNat_append_eq_mul_add, hmod52]
        have h1_val : (1#1 : BitVec 1).toNat * 2 ^ Float.Model.Format.binary64.mantissaBitsWithoutImplicit = 2 ^ 52 := rfl
        rw [h1_val]
        exact hsub52
      · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (e2 + 1075).toNat < 2048)]
        have hbm' : (Float.Model.Format.binary64.exponentBias : Int) + (52 : Nat) = 1075 := rfl
        rw [hbm']; omega
  unfold Float.Model.neg
  rw [hunpack]
  rfl

private theorem evalFloat_fallback_pos_bits (m : Nat) (e2 : Int) (hm : 0 < m)
    (hvalid : (e2 = -1074 ∧ 0 < m ∧ m < 2 ^ 52) ∨ (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e2 ∧ e2 ≤ 971)) :
    Float.Model.ofScientific (if 0 ≤ e2 then m <<< e2.toNat else m * 5 ^ (-e2).toNat) (if 0 ≤ e2 then 0 else e2) =
      Float.Model.pack (.finite .positive m e2 hm) := by
  unfold Float.Model.ofScientific
  congr 1
  by_cases he : 0 ≤ e2
  · cases e2 with
    | negSucc _ => exact absurd he (by omega)
    | ofNat n =>
      have hm52 : 2 ^ 52 ≤ m := by rcases hvalid with ⟨h0, _⟩ | ⟨h, _⟩; exact absurd h0 (by omega); exact h
      have hm53 : m < 2 ^ 53 := by rcases hvalid with ⟨h0, _⟩ | ⟨_, h, _⟩; exact absurd h0 (by omega); exact h
      have hehi : (Int.ofNat n) ≤ 971 := by rcases hvalid with ⟨h0, _⟩ | ⟨_, _, _, h⟩; exact absurd h0 (by omega); exact h
      have hnt : (Int.ofNat n).toNat = n := rfl
      simp only [he, ↓reduceIte, hnt]
      have hM : m <<< n = m * 2 ^ n := Nat.shiftLeft_eq m n
      have hMpos : 0 < m <<< n := by rw [hM]; exact Nat.mul_pos hm (Nat.pow_pos (by decide))
      have hMne : m <<< n ≠ 0 := by omega
      unfold Float.Model.UnpackedFloat.ofScientific
      dsimp only
      have hexpb : (2 ^ Float.Model.Format.binary64.exponentBits : Int) = 2048 := rfl
      have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
      have hno1 : ¬((0 : Int) > 2 ^ Float.Model.Format.binary64.exponentBits) := by rw [hexpb]; omega
      have hno2 : ¬((0 : Int) < -((2 ^ Float.Model.Format.binary64.exponentBits : Int) + (m <<< n).log2)) := by
        have hnn : (0 : Int) ≤ (m <<< n).log2 := Int.natCast_nonneg _
        rw [hexpb]; omega
      have hge0 : (0 : Int) ≤ 0 := Int.le_refl 0
      simp only [hMne, ↓reduceDIte, hno1, hno2, hge0, ↓reduceIte]
      unfold Float.Model.UnpackedFloat.mul
      dsimp only
      have hs_mul : (Float.Model.UnpackedFloat.Sign.positive * Float.Model.UnpackedFloat.Sign.positive) = .positive := rfl
      rw [hs_mul]
      have hz_nat : (0 : Int).toNat = 0 := rfl
      have hmul_val : ((m <<< n) <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ (0 : Int).toNat =
          m * 2 ^ (n + 53) := by
        rw [hz_nat, Nat.pow_zero, Nat.mul_one, hmb, hM, Nat.shiftLeft_eq, Nat.mul_assoc, ← Nat.pow_add]
      have hlogm : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
      have hlog_mul : (((m <<< n) <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ (0 : Int).toNat).log2 =
          52 + (n + 53) := by
        rw [hmul_val, nat_log2_mul_pow2 m (n + 53) hm, hlogm]
      have htarg : Float.Model.Format.binary64.targetExponent
          (Float.Model.totalExponent (((m <<< n) <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ (0 : Int).toNat)
            (-↑Float.Model.Format.binary64.mantissaBits + 0)) = Int.ofNat n := by
        unfold Float.Model.Format.targetExponent Float.Model.totalExponent
        have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
        rw [hlog_mul, hmb, hmin, Int.add_zero]
        omega
      have hsh1_step : Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64
          (((m <<< n) <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ (0 : Int).toNat)
          (-↑Float.Model.Format.binary64.mantissaBits + 0) .exact = (⟨m, false, false⟩, Int.ofNat n) := by
        unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
        rw [htarg]
        dsimp only
        have hsh : (Int.ofNat n - (-↑Float.Model.Format.binary64.mantissaBits + 0)).toNat = n + 53 := by
          rw [hmb]; omega
        rw [hsh, hmul_val, extendedMantissa_shift_exact_mul_pow2 m (n + 53)]
        have hexp : (-↑Float.Model.Format.binary64.mantissaBits + 0 : Int) + ↑(n + 53) = Int.ofNat n := by
          rw [hmb]; push_cast; omega
        rw [hexp]
      have htarg2 : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent m (Int.ofNat n)) = Int.ofNat n := by
        unfold Float.Model.Format.targetExponent Float.Model.totalExponent
        have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
        rw [hmb, hmin, hlogm]; omega
      unfold Float.Model.UnpackedFloat.roundWithAccuracy
      rw [hsh1_step]
      dsimp only
      simp only [shiftToTargetExponent_exact m (Int.ofNat n) htarg2,
        Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
        Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
        Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]
      have hmne : m ≠ 0 := by omega
      simp only [hmne, ↓reduceDIte]
  · cases e2 with
    | ofNat n => exact absurd (Int.natCast_nonneg n) he
    | negSucc e' =>
      simp only [he, ↓reduceIte]
      let k := (-Int.negSucc e').toNat
      have hk_def : k = e' + 1 := rfl
      have hk_eq : Int.negSucc e' = -Int.ofNat k := rfl
      have hk_pos : 1 ≤ k := by rw [hk_def]; omega
      have hk_le : k ≤ 1074 := by
        rw [hk_def]
        rcases hvalid with ⟨h0, _⟩ | ⟨_, _, he_lo, _⟩ <;> omega
      let M := m * 5 ^ k
      have h5pos : 0 < 5 ^ k := Nat.pow_pos (by decide)
      have hMpos : 0 < M := Nat.mul_pos hm h5pos
      have hMne : m * 5 ^ (-Int.negSucc e').toNat ≠ 0 := Nat.ne_of_gt hMpos
      unfold Float.Model.UnpackedFloat.ofScientific
      dsimp only
      have hexpb : (2 ^ Float.Model.Format.binary64.exponentBits : Int) = 2048 := rfl
      have hno1 : ¬(Int.negSucc e' > 2 ^ Float.Model.Format.binary64.exponentBits) := by rw [hexpb]; omega
      have hno2 : ¬(Int.negSucc e' < -(2 ^ 11 + ↑(m * 5 ^ (-Int.negSucc e').toNat).log2)) := by
        have hnn : (0 : Int) ≤ (m * 5 ^ (-Int.negSucc e').toNat).log2 := Int.natCast_nonneg _
        omega
      have hnotge : ¬(0 ≤ Int.negSucc e') := he
      simp only [hMne, ↓reduceDIte, hno1, hno2, hnotge, ↓reduceIte]
      unfold Float.Model.UnpackedFloat.div Float.Model.UnpackedFloat.divCore
      dsimp only
      have hsdiv : (Float.Model.UnpackedFloat.Sign.positive / Float.Model.UnpackedFloat.Sign.positive) = .positive := rfl
      rw [hsdiv]
      have h00 : (0 : Int) - 0 = 0 := rfl
      have h10_eq : 10 ^ k = 5 ^ k * 2 ^ k := by rw [← Nat.mul_pow]
      have hlog10 : (10 ^ k).log2 = (5 ^ k).log2 + k := by
        rw [h10_eq, nat_log2_mul_pow2 (5 ^ k) k h5pos]
      obtain ⟨hM_lo, hM_hi⟩ := nat_log2_mul_bounds m (5 ^ k) hm h5pos
      have hM_lo_i : (m.log2 : Int) + ((5 ^ k).log2 : Int) ≤ (M.log2 : Int) := by
        have h := Int.ofNat_le.mpr hM_lo
        push_cast at h; exact h
      have hM_hi_i : (M.log2 : Int) ≤ (m.log2 : Int) + ((5 ^ k).log2 : Int) + 1 := by
        have h := Int.ofNat_le.mpr hM_hi
        push_cast at h; exact h
      have hlog10_i : ((10 ^ k).log2 : Int) = ((5 ^ k).log2 : Int) + (k : Int) := by
        have h := congrArg (Int.ofNat) hlog10
        push_cast at h; exact h
      have hdiv_exact : ∀ s : Nat, k ≤ s →
          (M <<< s) / 10 ^ k = m * 2 ^ (s - k) ∧ (M <<< s) % 10 ^ k = 0 := by
        intro s hs
        have hpow : 2 ^ s = 2 ^ k * 2 ^ (s - k) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hmul : M <<< s = (m * 2 ^ (s - k)) * 10 ^ k := by
          rw [Nat.shiftLeft_eq]
          dsimp only [M]
          rw [hpow, h10_eq]
          calc
            m * 5 ^ k * (2 ^ k * 2 ^ (s - k))
                = m * (5 ^ k * (2 ^ k * 2 ^ (s - k))) := Nat.mul_assoc _ _ _
            _ = m * ((5 ^ k * 2 ^ k) * 2 ^ (s - k)) := by rw [Nat.mul_assoc (5 ^ k)]
            _ = m * (2 ^ (s - k) * (5 ^ k * 2 ^ k)) := by rw [Nat.mul_comm (5 ^ k * 2 ^ k)]
            _ = m * 2 ^ (s - k) * (5 ^ k * 2 ^ k) := (Nat.mul_assoc _ _ _).symm
        rw [hmul, Nat.mul_div_cancel _ (Nat.pow_pos (by decide : 0 < 10)), Nat.mul_mod_left]
        exact ⟨rfl, rfl⟩
      rcases hvalid with ⟨h1074, hm0, hm52⟩ | ⟨hm52, hm53, he_lo, he_hi⟩
      · have hk1074 : k = 1074 := by rw [hk_def]; omega
        have hk_i : (k : Int) = 1074 := by rw [hk1074]; rfl
        have hloglt : m.log2 < 52 := by
          obtain ⟨hlo, _⟩ := nat_log2_pow2_bounds m hm0
          exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt hlo hm52)
        have hloglt_i : (m.log2 : Int) < 52 := Int.ofNat_lt.mpr hloglt
        have htarg : Float.Model.Format.binary64.targetExponent
            (Float.Model.totalExponent M 0 - Float.Model.totalExponent (10 ^ k) 0) = -1074 := by
          unfold Float.Model.Format.targetExponent Float.Model.totalExponent
          have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
          have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
          rw [hmb, hmin]
          omega
        have hmin0 : min (0 : Int) (-1074) = -1074 := by omega
        rw [htarg, h00, hmin0]
        have hsh : ((0 : Int) - (-1074 : Int)).toNat = 1074 := rfl
        rw [hsh]
        obtain ⟨hq, hr⟩ := hdiv_exact 1074 (by omega)
        have hksub : 1074 - k = 0 := by omega
        rw [hq, hr, hksub, Nat.pow_zero, Nat.mul_one]
        have hacc : Float.Model.UnpackedFloat.accuracyOfFraction 0 (10 ^ k) = .exact := rfl
        rw [hacc]
        have he1074 : Int.negSucc e' = -1074 := h1074
        rw [he1074]
        exact roundWithAccuracy_binary64_pos_exact m (-1074) (Or.inl ⟨rfl, hm0, hm52⟩)
      · have hlogm : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
        have hlogm_i : (m.log2 : Int) = 52 := by rw [hlogm]; rfl
        have hdiff_bounds : (M.log2 : Int) - ((10 ^ k).log2 : Int) - 53 = Int.negSucc e' ∨
            (M.log2 : Int) - ((10 ^ k).log2 : Int) - 53 = Int.negSucc e' - 1 := by
          omega
        rcases hdiff_bounds with hdiff | hdiff
        · have htarg : Float.Model.Format.binary64.targetExponent
              (Float.Model.totalExponent M 0 - Float.Model.totalExponent (10 ^ k) 0) = Int.negSucc e' := by
            unfold Float.Model.Format.targetExponent Float.Model.totalExponent
            have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
            have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
            rw [hmb, hmin]; omega
          have hmin0 : min (0 : Int) (Int.negSucc e') = Int.negSucc e' := by omega
          rw [htarg, h00, hmin0]
          have hsh : ((0 : Int) - Int.negSucc e').toNat = k := by rw [hk_eq]; omega
          rw [hsh]
          obtain ⟨hq, hr⟩ := hdiv_exact k (by omega)
          rw [hq, hr, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
          have hacc : Float.Model.UnpackedFloat.accuracyOfFraction 0 (10 ^ k) = .exact := rfl
          rw [hacc]
          exact roundWithAccuracy_binary64_pos_exact m (Int.negSucc e') (Or.inr ⟨hm52, hm53, he_lo, he_hi⟩)
        · by_cases he1074 : Int.negSucc e' = -1074
          · have hk1074 : k = 1074 := by rw [hk_def]; omega
            have htarg : Float.Model.Format.binary64.targetExponent
                (Float.Model.totalExponent M 0 - Float.Model.totalExponent (10 ^ k) 0) = -1074 := by
              unfold Float.Model.Format.targetExponent Float.Model.totalExponent
              have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
              have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
              rw [hmb, hmin]; omega
            have hmin0 : min (0 : Int) (-1074) = -1074 := by omega
            rw [htarg, h00, hmin0]
            have hsh : ((0 : Int) - (-1074 : Int)).toNat = 1074 := rfl
            rw [hsh]
            obtain ⟨hq, hr⟩ := hdiv_exact 1074 (by omega)
            have hksub : 1074 - k = 0 := by omega
            rw [hq, hr, hksub, Nat.pow_zero, Nat.mul_one]
            have hacc : Float.Model.UnpackedFloat.accuracyOfFraction 0 (10 ^ k) = .exact := rfl
            rw [hacc]
            rw [he1074]
            exact roundWithAccuracy_binary64_pos_exact m (-1074)
              (Or.inr ⟨hm52, hm53, Int.le_refl (-1074), by decide⟩)
          · have he1073 : -1073 ≤ Int.negSucc e' := by omega
            have htarg : Float.Model.Format.binary64.targetExponent
                (Float.Model.totalExponent M 0 - Float.Model.totalExponent (10 ^ k) 0) = Int.negSucc e' - 1 := by
              unfold Float.Model.Format.targetExponent Float.Model.totalExponent
              have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
              have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
              rw [hmb, hmin]; omega
            have hmin0 : min (0 : Int) (Int.negSucc e' - 1) = Int.negSucc e' - 1 := by omega
            rw [htarg, h00, hmin0]
            have hsh : ((0 : Int) - (Int.negSucc e' - 1)).toNat = k + 1 := by rw [hk_eq]; omega
            rw [hsh]
            obtain ⟨hq, hr⟩ := hdiv_exact (k + 1) (by omega)
            rw [hq, hr]
            have hpow1 : k + 1 - k = 1 := by omega
            rw [hpow1, Nat.pow_one, Nat.mul_comm m 2]
            have hacc : Float.Model.UnpackedFloat.accuracyOfFraction 0 (10 ^ k) = .exact := rfl
            rw [hacc]
            exact roundWithAccuracy_binary64_pos_double m (Int.negSucc e') hm52 hm53 he1073 he_hi

private theorem fallback_toBits_eq (x : Float) (sign : Float.Model.UnpackedFloat.Sign)
    (m : Nat) (e2 : Int) (hm : 0 < m)
    (hun : x.toModel.unpack = .finite sign m e2 hm) :
    (Model.evalFloat (match sign with | .positive => false | .negative => true)
      (if 0 ≤ e2 then m <<< e2.toNat else m * 5 ^ (-e2).toNat)
      (if 0 ≤ e2 then 0 else e2)).toBits = x.toBits := by
  obtain ⟨hvalid, hpack_bits⟩ := unpack_finite_props x sign m e2 hm hun
  have hpos := evalFloat_fallback_pos_bits m e2 hm hvalid
  cases sign with
  | positive =>
    change (Float.ofModel (Float.Model.ofScientific _ _)).toBits = x.toBits
    rw [hpos]
    exact hpack_bits
  | negative =>
    change (Float.ofModel (Float.Model.neg (Float.Model.ofScientific _ _))).toBits = x.toBits
    rw [hpos, neg_pack_finite_pos m e2 hm hvalid]
    exact hpack_bits

private theorem zero_pos_toBits_eq (x : Float) (hun : x.toModel.unpack = .zero .positive) :
    (0.0 : Float).toBits = x.toBits := by
  let b : BitVec 64 := x.toModel.toBits.toBitVec
  change Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 b = .zero .positive at hun
  unfold Float.Model.UnpackedFloat.unpack at hun
  dsimp only at hun
  by_cases hexp1 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = -1#11
  · simp only [hexp1, ↓reduceIte] at hun
    split at hun <;> cases hun
  · simp only [hexp1, ↓reduceIte] at hun
    by_cases hexp0 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = 0#11
    · simp only [hexp0, ↓reduceIte] at hun
      by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
      · simp only [hmant0, ↓reduceDIte, Float.Model.UnpackedFloat.zero.injEq] at hun
        have hsign0 : Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64) b = 0#1 := by
          unfold Float.Model.UnpackedFloat.Sign.ofBitVec at hun
          split at hun
          · assumption
          · cases hun
        have hb0 : b = 0#64 := by
          ext i hi
          simp only [Float.Model.UnpackedFloat.unpackSign, Float.Model.UnpackedFloat.unpackExponent,
            Float.Model.UnpackedFloat.unpackMantissa, Float.Model.Format.binary64] at hsign0 hexp0 hmant0
          have h1 : b.getLsbD i = false := by
            by_cases hi52 : i < 52
            · have := congrArg (fun v : BitVec 52 => v.getLsbD i) hmant0
              simpa [BitVec.getLsbD_extractLsb', hi52] using this
            · by_cases hi63 : i < 63
              · have := congrArg (fun v : BitVec 11 => v.getLsbD (i - 52)) hexp0
                have hlt : i - 52 < 11 := by omega
                have hadd : 52 + (i - 52) = i := by omega
                simpa [BitVec.getLsbD_extractLsb', hlt, hadd] using this
              · have := congrArg (fun v : BitVec 1 => v.getLsbD (i - 63)) hsign0
                have hlt : i - 63 < 1 := by omega
                have hadd : 63 + (i - 63) = i := by omega
                simpa [BitVec.getLsbD_extractLsb', hlt, hadd] using this
          simpa [BitVec.getLsbD_eq_getElem, hi] using h1
        apply congrArg UInt64.ofBitVec
        exact hb0.symm
      · simp [hmant0] at hun
    · simp [hexp0] at hun

private theorem zero_neg_toBits_eq (x : Float) (hun : x.toModel.unpack = .zero .negative) :
    (-0.0 : Float).toBits = x.toBits := by
  let b : BitVec 64 := x.toModel.toBits.toBitVec
  change Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 b = .zero .negative at hun
  unfold Float.Model.UnpackedFloat.unpack at hun
  dsimp only at hun
  by_cases hexp1 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = -1#11
  · simp only [hexp1, ↓reduceIte] at hun
    split at hun <;> cases hun
  · simp only [hexp1, ↓reduceIte] at hun
    by_cases hexp0 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = 0#11
    · simp only [hexp0, ↓reduceIte] at hun
      by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
      · simp only [hmant0, ↓reduceDIte, Float.Model.UnpackedFloat.zero.injEq] at hun
        have hb0 : Float.Model.UnpackedFloat.packedZero Float.Model.Format.binary64 .negative = b := by
          unfold Float.Model.UnpackedFloat.packedZero
          have hz11 : (0 : BitVec Float.Model.Format.binary64.exponentBits) = 0#11 := rfl
          have hz52 : (0 : BitVec Float.Model.Format.binary64.mantissaBitsWithoutImplicit) = 0#52 := rfl
          rw [← hun, hz11, hz52, ← hexp0, ← hmant0]
          exact packComponents_unpack_eq b
        have hneg0 : (-0.0 : Float).toBits = UInt64.ofBitVec (Float.Model.UnpackedFloat.packedZero Float.Model.Format.binary64 .negative) := rfl
        rw [hneg0]
        exact congrArg UInt64.ofBitVec hb0
      · simp [hmant0] at hun
    · simp [hexp0] at hun

private theorem formatFloat_spec (x : Float) :
    Model.FloatFormatSpec x (Internal.formatFloat x) := by
  unfold Internal.formatFloat Model.FloatFormatSpec
  by_cases hnan : x.isNaN = true
  · simp only [hnan, ↓reduceIte]
  · simp only [hnan, Bool.false_eq_true, ↓reduceIte]
    by_cases hinf : (x == Float.inf) = true
    · simp only [hinf, ↓reduceIte]
    · simp only [hinf, Bool.false_eq_true, ↓reduceIte]
      by_cases hninf : (x == -Float.inf) = true
      · simp only [hninf, ↓reduceIte]
      · simp only [hninf, Bool.false_eq_true, ↓reduceIte]
        have hnotnan : x.toModel.unpack ≠ .notANumber := by
          intro h
          apply hnan
          change x.toModel.unpack.isNaN = true
          simp [h, Float.Model.UnpackedFloat.isNaN]
        have hnotinf : x.toModel.unpack ≠ .infinity .positive := by
          intro h
          apply hinf
          change (x.toModel.unpack.beq Float.inf.toModel.unpack) = true
          simp [h, Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare,
            show Float.inf.toModel.unpack = .infinity .positive from rfl, compare]
        have hnotninf : x.toModel.unpack ≠ .infinity .negative := by
          intro h
          apply hninf
          change (x.toModel.unpack.beq (-Float.inf).toModel.unpack) = true
          simp [h, Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare,
            show (-Float.inf).toModel.unpack = .infinity .negative from rfl, compare]
        split
        · rename_i hun; exact absurd hun hnotnan
        · rename_i hun; exact absurd hun hnotinf
        · rename_i hun; exact absurd hun hnotninf
        · rename_i hun
          refine ⟨by simp [String.contains_char_eq], Or.inl (by simp [String.contains_char_eq]), ?_⟩
          have hp : Model.parseFloatModel "0.0" = Except.ok (0.0 : Float) := rfl
          rw [hp]
          exact zero_pos_toBits_eq x hun
        · rename_i hun
          refine ⟨by simp [String.contains_char_eq], Or.inl (by simp [String.contains_char_eq]), ?_⟩
          have hp : Model.parseFloatModel "-0.0" = Except.ok (-0.0 : Float) := rfl
          rw [hp]
          exact zero_neg_toBits_eq x hun
        · rename_i sign m e2 hm hun
          cases sign <;>
          · split
            · rename_i s hsr
              obtain ⟨hnu, hsep, y, hy, hbits⟩ := searchShortCandidate_spec hsr
              refine ⟨hnu, hsep, ?_⟩
              rw [hy]
              exact hbits
            · by_cases he : 0 ≤ e2
              · simp only [he, ↓reduceIte]
                have hMpos : 0 < m <<< e2.toNat := by
                  rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hm (Nat.pow_pos (by decide))
                obtain ⟨hnu, hsep, hp⟩ := renderScientific_spec _ (m <<< e2.toNat) hMpos 0
                refine ⟨hnu, hsep, ?_⟩
                rw [hp]
                have hfb := fallback_toBits_eq x _ m e2 hm hun
                simp only [he, ↓reduceIte] at hfb
                exact hfb
              · simp only [he, ↓reduceIte]
                have hMpos : 0 < m * 5 ^ (-e2).toNat := Nat.mul_pos hm (Nat.pow_pos (by decide))
                obtain ⟨hnu, hsep, hp⟩ := renderScientific_spec _ (m * 5 ^ (-e2).toNat) hMpos e2
                refine ⟨hnu, hsep, ?_⟩
                rw [hp]
                have hfb := fallback_toBits_eq x _ m e2 hm hun
                simp only [he, ↓reduceIte] at hfb
                exact hfb

private theorem eq_inf_toBits {x : Float} (s : Float.Model.UnpackedFloat.Sign)
    (h : (x.toModel.unpack.beq (.infinity s)) = true) :
    (Float.ofModel (Float.Model.pack (.infinity s))).toBits = x.toBits := by
  have hu : x.toModel.unpack = .infinity s := by
    cases s <;> cases hu' : x.toModel.unpack with
    | infinity s' =>
      cases s' <;>
        simp [hu', Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare] at h <;> rfl
    | notANumber =>
      simp [hu', Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare] at h
    | zero s' =>
      simp [hu', Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare] at h
    | finite s' _ _ _ =>
      cases s' <;>
        simp [hu', Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare] at h
  let b : BitVec 64 := x.toModel.toBits.toBitVec
  change Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 b = .infinity s at hu
  unfold Float.Model.UnpackedFloat.unpack at hu
  dsimp only at hu
  by_cases hexp1 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = -1#11
  · simp only [hexp1, ↓reduceIte] at hu
    by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
    · simp only [hmant0, ↓reduceIte, Float.Model.UnpackedFloat.infinity.injEq] at hu
      have hpack : Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 s (-1#11) 0#52 = b := by
        rw [← hu, ← hexp1, ← hmant0]
        exact packComponents_unpack_eq b
      have hinf_bits : (Float.ofModel (Float.Model.pack (.infinity s))).toBits = UInt64.ofBitVec
          (Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 s (-1#11) 0#52) := by
        cases s <;> rfl
      rw [hinf_bits]
      exact congrArg UInt64.ofBitVec hpack
    · simp [hmant0] at hu
  · simp only [hexp1, ↓reduceIte] at hu
    by_cases hexp0 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = 0#11
    · simp only [hexp0, ↓reduceIte] at hu
      by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
      · simp [hmant0] at hu
      · simp [hmant0] at hu
    · simp [hexp0] at hu

private theorem formatFloat_roundTrip_one (x : Float) :
    Model.FloatFormatSpec x (Internal.formatFloat x) ∧
      match Internal.parseFloat (Internal.formatFloat x) with
      | .ok y => Model.FloatBitMatch x y ∧ Model.FloatEquiv x y
      | .error _ => False := by
  have hfmt := formatFloat_spec x
  refine ⟨hfmt, ?_⟩
  have hpf := (parseFloat_spec (Internal.formatFloat x)).1
  have hfmt' := hfmt
  unfold Model.FloatFormatSpec at hfmt'
  by_cases hnan : x.isNaN = true
  · simp only [hnan, ↓reduceIte] at hfmt'
    rw [hfmt'] at hpf ⊢
    have hp : Model.parseFloatModel "nan" = .ok Float.nan := rfl
    cases hd : Internal.parseFloat "nan" with
    | error e =>
      have heq : Model.parseFloatModel "nan" = .error e.kind := by rw [← hpf, hd]; rfl
      rw [hp] at heq; cases heq
    | ok y =>
      have heq : Model.parseFloatModel "nan" = .ok y := by rw [← hpf, hd]; rfl
      rw [hp] at heq
      rcases Except.ok.inj heq with rfl
      have hnan_y : Float.nan.isNaN = true := by decide
      exact ⟨by simp [Model.FloatBitMatch, hnan, hnan_y], Or.inl ⟨hnan, hnan_y⟩⟩
  · simp only [hnan, Bool.false_eq_true, ↓reduceIte] at hfmt'
    by_cases hinf : (x == Float.inf) = true
    · simp only [hinf, ↓reduceIte] at hfmt'
      rw [hfmt'] at hpf ⊢
      have hp : Model.parseFloatModel "inf" = .ok Float.inf := rfl
      cases hd : Internal.parseFloat "inf" with
      | error e =>
        have heq : Model.parseFloatModel "inf" = .error e.kind := by rw [← hpf, hd]; rfl
        rw [hp] at heq; cases heq
      | ok y =>
        have heq : Model.parseFloatModel "inf" = .ok y := by rw [← hpf, hd]; rfl
        rw [hp] at heq
        rcases Except.ok.inj heq with rfl
        have hx : Float.inf.toBits = x.toBits := by
          have hb := eq_inf_toBits .positive hinf
          change (Float.ofModel (Float.Model.pack (.infinity .positive))).toBits = x.toBits at hb
          exact hb
        exact ⟨by simp [Model.FloatBitMatch, hnan, hx], Or.inr hinf⟩
    · simp only [hinf, Bool.false_eq_true, ↓reduceIte] at hfmt'
      by_cases hninf : (x == -Float.inf) = true
      · simp only [hninf, ↓reduceIte] at hfmt'
        rw [hfmt'] at hpf ⊢
        have hp : Model.parseFloatModel "-inf" = .ok (-Float.inf) := rfl
        cases hd : Internal.parseFloat "-inf" with
        | error e =>
          have heq : Model.parseFloatModel "-inf" = .error e.kind := by rw [← hpf, hd]; rfl
          rw [hp] at heq; cases heq
        | ok y =>
          have heq : Model.parseFloatModel "-inf" = .ok y := by rw [← hpf, hd]; rfl
          rw [hp] at heq
          rcases Except.ok.inj heq with rfl
          have hx : (-Float.inf).toBits = x.toBits := by
            have hb := eq_inf_toBits .negative hninf
            change (Float.ofModel (Float.Model.pack (.infinity .negative))).toBits = x.toBits at hb
            exact hb
          exact ⟨by simp [Model.FloatBitMatch, hnan, hx], Or.inr hninf⟩
      · simp only [hninf, Bool.false_eq_true, ↓reduceIte] at hfmt'
        rcases hfmt' with ⟨_, _, hm⟩
        cases hd : Internal.parseFloat (Internal.formatFloat x) with
        | error e =>
          have heq : Model.parseFloatModel (Internal.formatFloat x) = .error e.kind := by
            rw [← hpf, hd]; rfl
          rw [heq] at hm
          exact False.elim hm
        | ok y =>
          have heq : Model.parseFloatModel (Internal.formatFloat x) = .ok y := by
            rw [← hpf, hd]; rfl
          rw [heq] at hm
          have hbm : Model.FloatBitMatch x y := by simp [Model.FloatBitMatch, hnan, hm]
          exact ⟨hbm, Model.floatEquiv_symm (Model.floatBitMatch_implies_floatEquiv hbm)⟩

/-- Proof of `test_numparse_formatFloat_specAndRoundTrip` for `defaultApi`. -/
theorem proof_numparse_formatFloat_specAndRoundTrip :
    AllPass (test_numparse_formatFloat_specAndRoundTrip defaultApi) := by
  intro x
  have h := formatFloat_roundTrip_one x
  dsimp [test_numparse_formatFloat_specAndRoundTrip, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  refine ⟨h.1, ?_⟩
  cases hpf : Internal.parseFloat (Internal.formatFloat x) with
  | error e =>
    have h2 := h.2
    rw [hpf] at h2
    exact False.elim h2
  | ok y =>
    have h2 := h.2
    rw [hpf] at h2
    exact ⟨h2, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_formatFloat_specAndRoundTrip`. -/
theorem reach_numparse_formatFloat_specAndRoundTrip :
    CanReach (test_numparse_formatFloat_specAndRoundTrip defaultApi) :=
  ⟨0.0, proof_numparse_formatFloat_specAndRoundTrip 0.0⟩

private def pubCheckFormatPreserves (xs : List Float) : AllPassRun Unit :=
  xs.forM fun x => do
    let s := defaultApi.formatFloat x
    NondetTest.assert (FloatFormatSpec x s)
    match defaultApi.parseFloat s with
    | .ok y => NondetTest.assert (FloatBitMatch x y)
    | .error _ => NondetTest.assert False

private theorem pubCheckFormatPreserves_all (xs : List Float) :
    pubCheckFormatPreserves xs (fun _ => True) := by
  induction xs with
  | nil => exact trivial
  | cons x xs ih =>
    have h := formatFloat_roundTrip_one x
    change ((NondetTest.assert (FloatFormatSpec x (Internal.formatFloat x)) : AllPassRun Unit)
      (fun _ => (match Internal.parseFloat (Internal.formatFloat x) with
        | .ok y => NondetTest.assert (FloatBitMatch x y)
        | .error _ => NondetTest.assert False : AllPassRun Unit)
        (fun _ => pubCheckFormatPreserves xs (fun _ => True))))
    refine ⟨h.1, ?_⟩
    cases hpf : Internal.parseFloat (Internal.formatFloat x) with
    | error e =>
      have h2 := h.2
      rw [hpf] at h2
      exact False.elim h2
    | ok y =>
      have h2 := h.2
      rw [hpf] at h2
      exact ⟨h2.1, ih⟩

/-- Proof of `test_numparse_float_formatPreservesSpecialsAndExtremes` for `defaultApi`. -/
theorem proof_numparse_float_formatPreservesSpecialsAndExtremes :
    AllPass (test_numparse_float_formatPreservesSpecialsAndExtremes defaultApi) :=
  pubCheckFormatPreserves_all _

/-- Non-vacuity `CanReach` witness for `test_numparse_float_formatPreservesSpecialsAndExtremes`. -/
theorem reach_numparse_float_formatPreservesSpecialsAndExtremes :
    CanReach (test_numparse_float_formatPreservesSpecialsAndExtremes defaultApi) :=
  proof_numparse_float_formatPreservesSpecialsAndExtremes

end LeanSwe.NumParse.Proofs
