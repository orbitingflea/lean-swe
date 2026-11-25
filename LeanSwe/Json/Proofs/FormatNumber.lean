import Lean.Data.Json.Basic
import LeanSwe.Json.Impl.Format
import LeanSwe.Json.Model
import LeanSwe.Json.Proofs.ScalarLex
import LeanSwe.Json.Proofs.FormatScalar

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- Allowed characters inside any `renderNumTape` with `validNumTape = true`. -/
def isNumRenderChar (c : Char) : Bool :=
  isAsciiDigit c || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

/-- Every valid `renderNumTape` is non-empty, free of `\n`/`\r`, and does not start with `"{"`. -/
theorem renderNumTape_char_props {nt : NumTape} (hv : validNumTape nt = true) :
    let out := renderNumTape nt
    !out.isEmpty = true ∧ !out.contains '\n' = true ∧ !out.contains '\r' = true ∧
      out.startsWith "{" = false := by
  simp only [validNumTape, Bool.and_eq_true] at hv
  rcases hv with ⟨hfrac, hexp⟩
  obtain ⟨hwNe, hwAll, _⟩ := repr_nat_props nt.whole
  have hDigSub : ∀ {l : List Char}, l.all isAsciiDigit = true → l.all isNumRenderChar = true := by
    intro l hl; rw [List.all_eq_true] at hl ⊢
    intro c hc; simp [isNumRenderChar, hl c hc]
  have hAllNum : (renderNumTape nt).toList.all isNumRenderChar = true := by
    unfold renderNumTape
    simp only [String.toList_append, List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨?_, hDigSub hwAll⟩, ?_⟩, ?_⟩
    · cases nt.minus <;> decide
    · cases hf : nt.fracDigits with
      | none => rfl
      | some f =>
        rw [hf] at hfrac; simp only [isNonEmptyDigits, Bool.and_eq_true] at hfrac
        simp [String.toList_append, show ".".toList = ['.'] from rfl, isNumRenderChar, hDigSub hfrac.2]
    · cases he : nt.exp with
      | none => rfl
      | some e =>
        rw [he] at hexp; simp only [isNonEmptyDigits, Bool.and_eq_true] at hexp
        rcases e with ⟨uE, sgnE, digsE⟩
        dsimp only at hexp ⊢
        cases uE <;> cases sgnE <;>
          (simp only [Bool.false_eq_true, ↓reduceIte, renderExpSign, String.toList_append, List.all_append, Bool.and_eq_true];
           exact ⟨⟨by decide, by decide⟩, hDigSub hexp.2⟩)
  have hHead : ∃ c0 tl, (renderNumTape nt).toList = c0 :: tl ∧ c0 ≠ '{' := by
    unfold renderNumTape; dsimp only
    cases hminus : nt.minus with
    | true =>
      exact ⟨'-', _, by simp only [↓reduceIte, show "-".toList = ['-'] from rfl,
        String.toList_append, List.cons_append, List.nil_append, List.append_assoc]; rfl, by decide⟩
    | false =>
      cases hw : nt.whole.repr.toList with
      | nil => exact absurd hw hwNe
      | cons d0 dtl =>
        rw [hw, List.all_cons, Bool.and_eq_true] at hwAll
        have hd0 : isAsciiDigit d0 = true := hwAll.1
        refine ⟨d0, _, by simp only [Bool.false_eq_true, ↓reduceIte, String.empty_append,
          String.toList_append, List.append_assoc, List.cons_append, hw]; rfl, ?_⟩
        rintro rfl; simp [isAsciiDigit] at hd0
  obtain ⟨c0, tl, hList, hc0Ne⟩ := hHead
  have hSafe : ∀ c ∈ (renderNumTape nt).toList, c ≠ '\n' ∧ c ≠ '\r' := by
    intro c hc
    have h1 := (List.all_eq_true.mp hAllNum) c hc
    refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [isNumRenderChar, isAsciiDigit] at h1)
  refine ⟨not_isEmpty_iff.mpr (by rw [hList]; simp),
    not_contains_char_iff.mpr (fun h => (hSafe '\n' h).1 rfl),
    not_contains_char_iff.mpr (fun h => (hSafe '\r' h).2 rfl),
    by rw [startsWith_openBrace_of_toList_cons hList, beq_false_of_ne hc0Ne]⟩

/-- Leading `'0'` characters leave `parseDecDigitsLoop 0` at `0`. -/
theorem parseDecDigitsLoop_leading_zeros (z : Nat) (raw : List Char) :
    parseDecDigitsLoop 0 (List.replicate z '0' ++ raw) = parseDecDigitsLoop 0 raw := by
  induction z with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, parseDecDigitsLoop_cons,
      Nat.zero_mul, Nat.zero_add, show ('0').toNat - 0x30 = 0 from rfl, ih]

/-- Exact RFC 8259 `renderNum` witness for `jsonNumberToString n`. -/
theorem jsonNumberToString_renderNum (n : Lean.JsonNumber) :
    ∃ nt : NumTape, renderNum n nt = some (jsonNumberToString n) := by
  rcases n with ⟨m, e⟩
  by_cases hm0 : m = 0
  · subst hm0
    refine ⟨{ minus := false, whole := 0, fracDigits := none, exp := none }, ?_⟩
    simp [jsonNumberToString, renderNum, validNumTape, numEquivBool_iff, numEquiv,
      evalNumTape, Lean.JsonNumber.fromInt, renderNumTape, show Nat.repr 0 = "0" from rfl]
  · have hmAbsPos : 0 < m.natAbs := Int.natAbs_pos.mpr hm0
    let neg := decide (m < 0)
    let sgn : Int := if neg then -1 else 1
    have hsgnMul : sgn * (m.natAbs : Int) = m := by
      dsimp [sgn, neg]
      by_cases hlt : m < 0
      · simp [hlt]; omega
      · simp [hlt]; omega
    cases e with
    | zero =>
      refine ⟨{ minus := neg, whole := m.natAbs, fracDigits := none, exp := none }, ?_⟩
      have hstr : jsonNumberToString ⟨m, 0⟩ = (if m < 0 then "-" else "") ++ m.natAbs.repr := by
        cases m with
        | ofNat k => cases k with | zero => exact absurd rfl hm0 | succ _ => rfl
        | negSucc _ => rfl
      rw [hstr]
      have heqv : numEquiv ⟨m, 0⟩ (evalNumTape ⟨neg, m.natAbs, none, none⟩) := by
        unfold numEquiv evalNumTape Lean.JsonNumber.fromInt
        simp only [Int.pow_zero, Int.mul_one]
        exact hsgnMul.symm
      have heqvB : numEquivBool ⟨m, 0⟩ (evalNumTape ⟨neg, m.natAbs, none, none⟩) = true :=
        (numEquivBool_iff _ _).mpr heqv
      simp [renderNum, validNumTape, heqvB, renderNumTape, neg]
    | succ ePred =>
      let ePos := ePred + 1
      let expRaw : Int := 9 + countDigits m.natAbs - (ePos : Int)
      let exp : Int := if expRaw < 0 then expRaw else 0
      let k := ePos - exp.natAbs
      let e' := 10 ^ k
      let whole := m.natAbs / e'
      let rem := m.natAbs % e'
      have hCountGe1 : 1 ≤ countDigits m.natAbs := (countDigitsAux_bounds m.natAbs 1).1
      have hkAddExp : k + exp.natAbs = ePos := by
        dsimp [k, exp, expRaw]
        by_cases hlt : (9 + (countDigits m.natAbs : Int) - (ePos : Int)) < 0
        · simp [hlt]; omega
        · simp [hlt]
      have hDivMod : whole * e' + rem = m.natAbs := by
        have := Nat.div_add_mod m.natAbs e'
        rw [Nat.mul_comm] at this; exact this
      have hUnfold : jsonNumberToString ⟨m, ePos⟩ =
          (let sign := if m < 0 then "-" else ""
           if rem == 0 && exp == 0 then sign ++ whole.repr
           else
             let right := formatFracStr k rem
             let expStr := if exp == 0 then "" else "e-" ++ exp.natAbs.repr
             sign ++ whole.repr ++ "." ++ right ++ expStr) := by
        cases m with
        | ofNat km => cases km with | zero => exact absurd rfl hm0 | succ _ => rfl
        | negSucc _ => rfl
      rw [hUnfold]
      dsimp only
      by_cases hRemExp0 : (rem == 0 && exp == 0) = true
      · simp only [hRemExp0, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at hRemExp0
        rcases hRemExp0 with ⟨hrem0, hexp0⟩
        have hkEq : k = ePos := by omega
        have hmAbsEq : m.natAbs = whole * (10 ^ ePos) := by
          rw [hrem0, Nat.add_zero] at hDivMod
          dsimp only [e'] at hDivMod
          rw [← hkEq]; exact hDivMod.symm
        refine ⟨{ minus := neg, whole := whole, fracDigits := none, exp := none }, ?_⟩
        have heqv : numEquiv ⟨m, ePos⟩ (evalNumTape ⟨neg, whole, none, none⟩) := by
          unfold numEquiv evalNumTape Lean.JsonNumber.fromInt
          simp only [Int.pow_zero, Int.mul_one]
          rw [← hsgnMul, hmAbsEq, Int.natCast_mul, Int.natCast_pow, Int.mul_assoc]
          rfl
        have heqvB : numEquivBool ⟨m, ePos⟩ (evalNumTape ⟨neg, whole, none, none⟩) = true :=
          (numEquivBool_iff _ _).mpr heqv
        unfold renderNum
        rw [heqvB]
        simp [validNumTape, renderNumTape, neg]
      · simp only [hRemExp0, Bool.false_eq_true, ↓reduceIte]
        have hremPos : 0 < rem := by
          by_cases hexp0 : exp = 0
          · simp [hexp0] at hRemExp0
            exact Nat.pos_of_ne_zero hRemExp0
          · have hltRaw : expRaw < 0 := by
              apply Decidable.byContradiction; intro hge; simp [exp, hge] at hexp0
            have hk9 : k = 9 + countDigits m.natAbs := by
              dsimp [k, exp, expRaw] at *; simp [hltRaw]; omega
            have hmLt : m.natAbs < e' := by
              have h1 := lt_pow10_countDigits m.natAbs
              have h2 : 10 ^ countDigits m.natAbs ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
              exact Nat.lt_of_lt_of_le h1 h2
            have hmod : rem = m.natAbs := Nat.mod_eq_of_lt hmLt
            omega
        have hremLt : rem < 10 ^ k := Nat.mod_lt _ (Nat.pow_pos (by decide))
        let raw := Nat.toDigits 10 rem
        have hrawLenLe : raw.length ≤ k := toDigits_length_le_of_lt_pow10 hremPos hremLt
        obtain ⟨_, hrawAll, hrawVal⟩ := toDigitsCore_props (rem + 1) rem [] (by omega) rfl
        have hrawEqCore : raw = Nat.toDigitsCore 10 (rem + 1) rem [] := rfl
        rw [← hrawEqCore] at hrawAll hrawVal
        simp only [parseDecDigitsLoop_nil] at hrawVal
        let padded := List.replicate (k - raw.length) '0' ++ raw
        have hpaddedLen : padded.length = k := by simp [padded]; omega
        have hpaddedAll : padded.all isAsciiDigit = true := by
          simp only [padded, List.all_append, Bool.and_eq_true, hrawAll, and_true]
          rw [List.all_eq_true]; intro x hx; rw [List.eq_of_mem_replicate hx]; rfl
        have hpaddedVal : parseDecDigitsLoop 0 padded = rem := by
          dsimp [padded]; rw [parseDecDigitsLoop_leading_zeros, hrawVal]
        obtain ⟨hTrimNe, hTrimAll, t, hpaddedSplit⟩ :=
          dropTrailingZeroChars_props hpaddedAll (by rw [hpaddedVal]; exact hremPos)
        let trimmed := dropTrailingZeroChars padded
        let right := String.ofList trimmed
        have hRightEq : formatFracStr k rem = right := rfl
        have hRightList : right.toList = trimmed := String.toList_ofList
        let d := trimmed.length
        have hdPlusT : d + t = k := by
          have := congrArg List.length hpaddedSplit
          rw [hpaddedLen, List.length_append, List.length_replicate] at this
          dsimp only [d, trimmed] at *; omega
        have hRemDecomp : rem = parseDecDigits right * (10 ^ t) := by
          rw [← hpaddedVal, hpaddedSplit, parseDecDigitsLoop_append,
            parseDecDigitsLoop_replicate_zero, parseDecDigits, hRightList]
        have hmAbsDecomp : m.natAbs = (whole * (10 ^ d) + parseDecDigits right) * (10 ^ t) := by
          calc m.natAbs = whole * (10 ^ k) + rem := hDivMod.symm
            _ = whole * (10 ^ (d + t)) + parseDecDigits right * (10 ^ t) := by rw [← hdPlusT, ← hRemDecomp]
            _ = whole * ((10 ^ d) * (10 ^ t)) + parseDecDigits right * (10 ^ t) := by rw [Nat.pow_add]
            _ = (whole * (10 ^ d) + parseDecDigits right) * (10 ^ t) := by rw [Nat.add_mul, Nat.mul_assoc]
        let expOpt : Option ExpTape :=
          if exp == 0 then none else some ⟨false, .minus, exp.natAbs.repr⟩
        let nt : NumTape := ⟨neg, whole, some right, expOpt⟩
        have hValNt : validNumTape nt = true := by
          have hTrimNe' : (!trimmed.isEmpty) = true := by
            dsimp only [trimmed]
            cases h : (dropTrailingZeroChars padded).isEmpty <;> simp [h] at hTrimNe ⊢
          have hTrimAll' : trimmed.all isAsciiDigit = true := hTrimAll
          dsimp only [nt, validNumTape, isNonEmptyDigits]
          rw [hRightList, hTrimNe', hTrimAll']
          simp only [Bool.and_self, Bool.true_and]
          by_cases hexp0 : exp == 0
          · simp [expOpt, hexp0]
          · obtain ⟨heNe, heAll, _⟩ := repr_nat_props exp.natAbs
            have heNeB : (!exp.natAbs.repr.toList.isEmpty) = true := by
              cases hl : exp.natAbs.repr.toList with | nil => exact absurd hl heNe | cons _ _ => rfl
            dsimp only [expOpt]; rw [ite_eq_right hexp0]; dsimp only [isNonEmptyDigits]; rw [heNeB, heAll]; rfl
        have hEvalNt : evalNumTape nt =
            ⟨sgn * ((whole * (10 ^ d) + parseDecDigits right : Nat) : Int), d + exp.natAbs⟩ := by
          obtain ⟨_, _, heParse⟩ := repr_nat_props exp.natAbs
          by_cases hexp0 : exp == 0
          · have hna0 : exp.natAbs = 0 := by rw [beq_iff_eq.mp hexp0]; rfl
            simp [nt, expOpt, hexp0, evalNumTape, hRightList, d, sgn, hna0]
          · dsimp only [nt, expOpt]; rw [ite_eq_right hexp0]
            simp only [evalNumTape, Lean.JsonNumber.shiftr, parseDecDigits, heParse, hRightList]
            rfl
        have hEqvNt : numEquiv ⟨m, ePos⟩ (evalNumTape nt) := by
          rw [hEvalNt]
          unfold numEquiv
          dsimp only
          have heSum : ePos = (d + exp.natAbs) + t := by omega
          have h10 : ((10 : Nat) : Int) = 10 := rfl
          rw [← hsgnMul, hmAbsDecomp, heSum, Int.natCast_mul, Int.natCast_pow, h10]
          simp only [Int.pow_add]
          ac_rfl
        have hEqvNtB : numEquivBool ⟨m, ePos⟩ (evalNumTape nt) = true :=
          (numEquivBool_iff _ _).mpr hEqvNt
        refine ⟨nt, ?_⟩
        unfold renderNum
        rw [hValNt, hEqvNtB]
        simp only [Bool.and_self, ↓reduceIte, Option.some.injEq]
        unfold renderNumTape
        by_cases hexp0 : exp == 0 <;> simp [nt, expOpt, hexp0, neg, renderExpSign, hRightEq, String.append_assoc]

/-- Full specification of `jsonNumberToString n`: non-empty, single-line, non-`{`, and witnessed by `renderNum`. -/
theorem jsonNumberToString_spec (n : Lean.JsonNumber) :
    let out := jsonNumberToString n
    !out.isEmpty = true ∧ !out.contains '\n' = true ∧ !out.contains '\r' = true ∧
      out.startsWith "{" = false ∧
      ∃ nt : NumTape, renderNum n nt = some out := by
  obtain ⟨nt, hRen⟩ := jsonNumberToString_renderNum n
  have hCopy := hRen
  simp only [renderNum, Bool.and_eq_true] at hCopy
  split at hCopy <;> simp at hCopy
  rename_i hc
  obtain ⟨h1, h2, h3, h4⟩ := renderNumTape_char_props hc.1
  rw [← hCopy]
  exact ⟨h1, h2, h3, h4, nt, by rw [hCopy]; exact hRen⟩

end LeanSwe.Json.Proofs
