import Init.Data.Float.Model
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model.Base

namespace LeanSwe.NumParse.Model

open Float.Model

/-- Pure binary64 `Float.Model` evaluation of `(-1)^neg * mantissa * 10^exp10` using IEEE-754 round-to-nearest-ties-to-even. -/
def evalFloatModel (neg : Bool) (mantissa : Nat) (exp10 : Int) : Float.Model :=
  let m := Float.Model.ofScientific mantissa exp10
  if neg then -m else m

/-- Pure binary64 `Float` evaluation of `(-1)^neg * mantissa * 10^exp10` using IEEE-754 round-to-nearest-ties-to-even. -/
def evalFloat (neg : Bool) (mantissa : Nat) (exp10 : Int) : Float :=
  Float.ofModel (evalFloatModel neg mantissa exp10)

/-- Evaluating zero significand with positive sign produces `+0.0`. -/
theorem evalFloat_zero (e : Int) : evalFloat false 0 e = (0.0 : Float) := by
  simp only [evalFloat, evalFloatModel, Bool.false_eq_true, ↓reduceIte, Float.Model.ofScientific,
    UnpackedFloat.ofScientific, ↓reduceDIte]
  decide

/-- Evaluating zero significand with negative sign produces `-0.0`. -/
theorem evalFloat_neg_zero (e : Int) : evalFloat true 0 e = (-0.0 : Float) := by
  simp only [evalFloat, evalFloatModel, ↓reduceIte, Float.Model.ofScientific,
    UnpackedFloat.ofScientific, ↓reduceDIte]
  decide

/-- Negating a positive `evalFloat` yields the corresponding negative `evalFloat`. -/
theorem evalFloat_neg (m : Nat) (e : Int) :
    evalFloat true m e = -(evalFloat false m e) := rfl

/-- Non-zero significands with `e > 2048` overflow to `+inf` (`Float.inf`). -/
theorem evalFloat_overflow_pos {m : Nat} {e : Int} (hm : m ≠ 0) (he : e > 2048) :
    evalFloat false m e = Float.inf := by
  have he' : e > (2 ^ Format.binary64.exponentBits : Int) := by
    have hexp : (2 ^ Format.binary64.exponentBits : Int) = 2048 := by decide
    omega
  simp only [evalFloat, evalFloatModel, Bool.false_eq_true, ↓reduceIte, Float.Model.ofScientific,
    UnpackedFloat.ofScientific, hm, ↓reduceDIte, he']
  rfl

/-- Non-zero significands with `e > 2048` and negative sign overflow to `-inf`. -/
theorem evalFloat_overflow_neg {m : Nat} {e : Int} (hm : m ≠ 0) (he : e > 2048) :
    evalFloat true m e = -Float.inf := by
  rw [evalFloat_neg, evalFloat_overflow_pos hm he]

/-- Extreme negative exponents `e < -(2048 + m.log2)` underflow to `+0.0`. -/
theorem evalFloat_underflow_pos {m : Nat} {e : Int} (he : e < -(2048 + (m.log2 : Int))) :
    evalFloat false m e = (0.0 : Float) := by
  by_cases hm : m = 0
  · subst hm; exact evalFloat_zero e
  · have hexp : (2 ^ Format.binary64.exponentBits : Int) = 2048 := by decide
    have hnot : ¬(e > (2 ^ Format.binary64.exponentBits : Int)) := by omega
    have he' : e < -((2 ^ Format.binary64.exponentBits : Int) + m.log2) := by omega
    simp only [evalFloat, evalFloatModel, Bool.false_eq_true, ↓reduceIte, Float.Model.ofScientific,
      UnpackedFloat.ofScientific, hm, ↓reduceDIte, hnot, he']
    decide

/-- Extreme negative exponents `e < -(2048 + m.log2)` with negative sign underflow to `-0.0`. -/
theorem evalFloat_underflow_neg {m : Nat} {e : Int} (he : e < -(2048 + (m.log2 : Int))) :
    evalFloat true m e = (-0.0 : Float) := by
  rw [evalFloat_neg, evalFloat_underflow_pos he]

/-- Scan decimal digits and underscore separators for a float part, returning `(value, digitCount, rest)`. -/
def consumeDecFloatDigits (acc count : Nat) :
    List Char → Except NumParseErrorKind (Nat × Nat × List Char)
  | [] => .ok (acc, count, [])
  | '_' :: c :: cs =>
    if isDecDigit c then
      consumeDecFloatDigits (acc * 10 + (c.toNat - '0'.toNat)) (count + 1) cs
    else
      .error .invalidUnderscore
  | '_' :: [] => .error .invalidUnderscore
  | c :: cs =>
    if isDecDigit c then
      consumeDecFloatDigits (acc * 10 + (c.toNat - '0'.toNat)) (count + 1) cs
    else
      .ok (acc, count, c :: cs)

/-- Parse the integer significand part of a TOML float literal, rejecting disallowed leading zeros. -/
def parseFloatIntPart : List Char → Except NumParseErrorKind (Nat × List Char)
  | [] => .error .invalidSyntax
  | '_' :: _ => .error .invalidUnderscore
  | '0' :: rest =>
    match rest with
    | c :: _ =>
      if isDecDigit c then .error .leadingZero
      else if c == '_' then
        match rest with
        | '_' :: c2 :: _ =>
          if isDecDigit c2 then .error .leadingZero else .error .invalidUnderscore
        | _ => .error .invalidUnderscore
      else .ok (0, rest)
    | [] => .ok (0, [])
  | c :: rest =>
    if isDecDigit c then
      match consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest with
      | .ok (m, _, rem) => .ok (m, rem)
      | .error k => .error k
    else
      .error .invalidSyntax

/-- Parse the signed exponent part of a TOML float literal (allowing leading zeros per TOML 1.0). -/
def parseFloatExpPart : List Char → Except NumParseErrorKind (Int × List Char)
  | cs =>
    let (expNeg, afterSign) :=
      match cs with
      | '+' :: rest => (false, rest)
      | '-' :: rest => (true, rest)
      | _ => (false, cs)
    match afterSign with
    | [] => .error .invalidSyntax
    | '_' :: _ => .error .invalidUnderscore
    | c :: rest =>
      if isDecDigit c then
        match consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest with
        | .ok (eMag, _, rem) => .ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
        | .error k => .error k
      else
        .error .invalidSyntax

/-- Pure mathematical binary64 float grammar and value specification over `List Char`. -/
def parseFloatModelChars : List Char → Except NumParseErrorKind Float
  | [] => .error .emptyInput
  | cs =>
    let (neg, body) :=
      match cs with
      | '+' :: rest => (false, rest)
      | '-' :: rest => (true, rest)
      | _ => (false, cs)
    match body with
    | 'i' :: 'n' :: 'f' :: rest =>
      match rest with
      | [] => .ok (if neg then -Float.inf else Float.inf)
      | _ :: _ => .error .trailingChars
    | 'n' :: 'a' :: 'n' :: rest =>
      match rest with
      | [] => .ok Float.nan
      | _ :: _ => .error .trailingChars
    | _ =>
      match parseFloatIntPart body with
      | .error k => .error k
      | .ok (intVal, afterInt) =>
        match afterInt with
        | '.' :: afterDot =>
          match afterDot with
          | '_' :: _ => .error .invalidUnderscore
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
                    if afterExp.isEmpty then
                      .ok (evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                    else
                      .error .trailingChars
                | 'E' :: afterE =>
                  match parseFloatExpPart afterE with
                  | .error k => .error k
                  | .ok (expVal, afterExp) =>
                    if afterExp.isEmpty then
                      .ok (evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                    else
                      .error .trailingChars
                | [] => .ok (evalFloat neg mantissa (-Int.ofNat fracCount))
                | _ :: _ => .error .trailingChars
            else
              .error .invalidSyntax
          | [] => .error .invalidSyntax
        | 'e' :: afterE =>
          match parseFloatExpPart afterE with
          | .error k => .error k
          | .ok (expVal, afterExp) =>
            if afterExp.isEmpty then .ok (evalFloat neg intVal expVal)
            else .error .trailingChars
        | 'E' :: afterE =>
          match parseFloatExpPart afterE with
          | .error k => .error k
          | .ok (expVal, afterExp) =>
            if afterExp.isEmpty then .ok (evalFloat neg intVal expVal)
            else .error .trailingChars
        | _ => .error .invalidSyntax

/-- Pure mathematical binary64 float grammar and value specification over `String`. -/
def parseFloatModel (s : String) : Except NumParseErrorKind Float :=
  parseFloatModelChars s.toList

/-- Exact float bit-pattern agreement for non-NaN values and `isNaN` agreement for `NaN`. -/
def FloatBitMatch (expected actual : Float) : Prop :=
  if expected.isNaN = true then actual.isNaN = true else actual.toBits = expected.toBits

/-- `FloatBitMatch` is reflexive. -/
theorem floatBitMatch_refl (x : Float) : FloatBitMatch x x := by
  unfold FloatBitMatch
  by_cases h : x.isNaN = true
  · simp only [h, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- `FloatBitMatch` implies `FloatEquiv`. -/
theorem floatBitMatch_implies_floatEquiv {x y : Float} (h : FloatBitMatch x y) :
    FloatEquiv y x := by
  unfold FloatBitMatch at h
  split at h
  · left; exact ⟨h, ‹_›⟩
  · have heq : y = x := by
      cases y with | ofModel my =>
      cases x with | ofModel mx =>
      cases my with | mk by_ vy_ =>
      cases mx with | mk bx_ vx_ =>
      simp only [Float.toBits] at h
      subst h
      rfl
    subst heq
    exact floatEquiv_refl y

/-- Pure specification relation for valid canonical float formatting output. -/
def FloatFormatSpec (x : Float) (s : String) : Prop :=
  if x.isNaN = true then
    s = "nan"
  else if (x == Float.inf) = true then
    s = "inf"
  else if (x == -Float.inf) = true then
    s = "-inf"
  else
    !(s.contains '_') ∧ (s.contains '.' ∨ s.contains 'e' ∨ s.contains 'E') ∧
      match parseFloatModel s with
      | .ok y => y.toBits = x.toBits
      | .error _ => False

/-- Allowed outcome relation for `NumParse.parseInt` against `parseIntModel`. -/
def allowedParseInt (s : String) (out : Except NumParseError Int) : Prop :=
  out.mapError NumParseError.kind = parseIntModel s ∧
    ∀ e, out = .error e → e.message ≠ ""

/-- Allowed outcome relation for `NumParse.parseInt64` against `parseInt64Model`. -/
def allowedParseInt64 (s : String) (out : Except NumParseError Int64) : Prop :=
  out.mapError NumParseError.kind = parseInt64Model s ∧
    ∀ e, out = .error e → e.message ≠ ""

/-- Allowed outcome relation for `NumParse.formatInt` against `parseIntModel`. -/
def allowedFormatInt (n : Int) (out : String) : Prop :=
  !out.contains '_' ∧
    out.toList.all (fun c => isDecDigit c || c == '-') = true ∧
    parseIntModel out = .ok n

/-- Allowed outcome relation for `NumParse.parseFloat` against `parseFloatModel`. -/
def allowedParseFloat (s : String) (out : Except NumParseError Float) : Prop :=
  out.mapError NumParseError.kind = parseFloatModel s ∧
    ∀ e, out = .error e → e.message ≠ ""

end LeanSwe.NumParse.Model
