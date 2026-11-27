import Core.NondetTest
import Core.Assumptions
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.NumParse`. -/

namespace LeanSwe.NumParse

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.NumParse.Model

example : parseIntModel "0xdead_BEEF" = .ok 0xdeadbeef := rfl

example : parseIntModel "+0x1" = .error .invalidSignForBase := rfl

example : parseIntModel "0_1" = .error .leadingZero := rfl

example : parseIntModel "0_" = .error .invalidUnderscore := rfl

example : parseInt64Model "0x8000_0000_0000_0000" = .error .overflow := rfl

example : parseInt64Model "-9223372036854775808" = .ok (Int64.ofInt int64MinInt) := rfl

example : (match parseFloatModel "0.0" with | .ok f => f.toBits == (0.0 : Float).toBits | .error _ => false) = true := by decide

example : (match parseFloatModel "-0.0" with | .ok f => f.toBits == (-0.0 : Float).toBits | .error _ => false) = true := by decide

example : (match parseFloatModel "1e05" with | .ok f => f.toBits == (evalFloat false 1 5).toBits | .error _ => false) = true := by decide

example : (match parseFloatModel "1e-00" with | .ok f => f.toBits == (1.0 : Float).toBits | .error _ => false) = true := by decide

example : (match parseFloatModel "inf" with | .ok f => f.toBits == Float.inf.toBits | .error _ => false) = true := by decide

example : (match parseFloatModel "-inf" with | .ok f => f.toBits == (-Float.inf).toBits | .error _ => false) = true := by decide

example : (match parseFloatModel "nan" with | .ok f => f.isNaN | .error _ => false) = true := by decide

example : parseFloatModel "Inf" = .error .invalidSyntax := rfl

example : parseFloatModel "42" = .error .invalidSyntax := rfl

example : parseFloatModel "01.5" = .error .leadingZero := rfl

example : parseFloatModel "-00e1" = .error .leadingZero := rfl

example : (match parseFloatModel "1e1000000000" with | .ok f => f.toBits == Float.inf.toBits | .error _ => false) = true := by decide

example : (match parseFloatModel "-1e-1000000000" with | .ok f => f.toBits == (-0.0 : Float).toBits | .error _ => false) = true := by decide

private def stubNumParseApi : NumParseApi :=
  { parseInt := fun _ => .error { kind := .emptyInput, message := "" }
  , parseInt64 := fun _ => .error { kind := .emptyInput, message := "" }
  , formatInt := fun _ => "0"
  , parseFloat := fun _ => .error { kind := .emptyInput, message := "" }
  , formatFloat := fun _ => "0.0"
  }

example : ¬ Core.AllPass (test_numparse_onError_returnsNonEmptyMessage stubNumParseApi) := by
  intro h
  have h0 := h ""
  simp [stubNumParseApi, bind, assert] at h0

private def buggyEmptyMsgApi : NumParseApi :=
  { stubNumParseApi with
    parseInt := fun _ => .error { kind := .emptyInput, message := "" } }

example : ¬ Core.AllPass (test_numparse_parseInt_matchesModel buggyEmptyMsgApi) := by
  intro h
  have h0 := h ""
  have hm : parseIntModel "" = .error .emptyInput := rfl
  simp [buggyEmptyMsgApi, hm, assert] at h0

private def buggyNegSignHexAcceptedApi : NumParseApi :=
  { stubNumParseApi with
    parseInt := fun s => if s == "-0x1" then .ok (-1) else .error { kind := .invalidSyntax, message := "bad" } }

example : ¬ Core.AllPass (test_numparse_parseInt_matchesModel buggyNegSignHexAcceptedApi) := by
  intro h
  have h0 := h "-0x1"
  have hm : parseIntModel "-0x1" = .error .invalidSignForBase := rfl
  simp [buggyNegSignHexAcceptedApi, hm, assert] at h0

private def buggyInt64WraparoundApi : NumParseApi :=
  { stubNumParseApi with
    parseInt64 := fun _ => .ok 0 }

example : ¬ Core.AllPass (test_numparse_parseInt64_matchesModel buggyInt64WraparoundApi) := by
  intro h
  have h0 := h "9223372036854775808"
  have hm : parseInt64Model "9223372036854775808" = .error .overflow := rfl
  simp [buggyInt64WraparoundApi, hm, assert] at h0

private def buggyFormatIntUnderscoreApi : NumParseApi :=
  { stubNumParseApi with
    formatInt := fun _ => "1_000"
    parseInt := fun _ => .ok 1000 }

example : ¬ Core.AllPass (test_numparse_formatInt_roundTrip buggyFormatIntUnderscoreApi) := by
  intro h
  have h0 := h 1000
  simp [buggyFormatIntUnderscoreApi, bind, assert] at h0

private def buggyExpLeadingZeroRejectedApi : NumParseApi :=
  { stubNumParseApi with
    parseFloat := fun s =>
      if s == "1e05" then .error { kind := .leadingZero, message := "leading zero" }
      else .error { kind := .invalidSyntax, message := "bad" } }

example : ¬ Core.AllPass (test_numparse_parseFloat_matchesModel buggyExpLeadingZeroRejectedApi) := by
  intro h
  have h0 := h "1e05"
  have hm : parseFloatModel "1e05" = .ok (evalFloat false 1 5) := rfl
  simp [buggyExpLeadingZeroRejectedApi, hm, assert] at h0

private def buggyFormatFloatUnderscoreApi : NumParseApi :=
  { stubNumParseApi with
    formatFloat := fun _ => "1_0.0"
    parseFloat := fun _ => .ok 10.0 }

example : ¬ Core.AllPass (test_numparse_formatFloat_specAndRoundTrip buggyFormatFloatUnderscoreApi) := by
  intro h
  have h0 := h 10.0
  simp [buggyFormatFloatUnderscoreApi, FloatFormatSpec, bind, assert] at h0

private def buggyFormatFloatSwallowsNegZeroApi : NumParseApi :=
  { stubNumParseApi with
    formatFloat := fun _ => "0.0"
    parseFloat := fun _ => .ok 0.0 }

example : ¬ Core.AllPass (test_numparse_formatFloat_specAndRoundTrip buggyFormatFloatSwallowsNegZeroApi) := by
  intro h
  have h0 := h (-0.0)
  have hp : parseFloatModel "0.0" = .ok (evalFloat false 0 (-1)) := rfl
  have hbits : (evalFloat false 0 (-1)).toBits ≠ (-0.0 : Float).toBits := by decide
  simp [buggyFormatFloatSwallowsNegZeroApi, FloatFormatSpec, hp, hbits, bind, assert] at h0

example : ¬ Core.AllPass (test_numparse_int_concreteBoundaries stubNumParseApi) := by
  intro h
  exact h.1

example : ¬ Core.AllPass (test_numparse_float_concreteSpecialsAndEdges stubNumParseApi) := by
  intro h
  exact h.1

example : ¬ Core.AllPass (test_numparse_float_formatPreservesSpecialsAndExtremes stubNumParseApi) := by
  intro h
  simp [Core.AllPass, test_numparse_float_formatPreservesSpecialsAndExtremes, stubNumParseApi, FloatFormatSpec,
    List.forM, bind, pure, assert] at h

end LeanSwe.NumParse
