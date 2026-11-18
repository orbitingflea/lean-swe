import Core.NondetTest
import Core.Assumptions
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model

namespace LeanSwe.NumParse

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.NumParse.Model

/-- Every error returned by `parseInt`, `parseInt64`, or `parseFloat` carries a non-empty diagnostic message. -/
def test_numparse_onError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : NumParseApi) : runner Unit := do
  let s ← nondet String
  match api.parseInt s with
  | .ok _ => NondetTest.assert True
  | .error e => NondetTest.assert (e.message ≠ "")
  match api.parseInt64 s with
  | .ok _ => NondetTest.assert True
  | .error e => NondetTest.assert (e.message ≠ "")
  match api.parseFloat s with
  | .ok _ => NondetTest.assert True
  | .error e => NondetTest.assert (e.message ≠ "")

/-- `api.parseInt` agrees with `parseIntModel` on every input string, with non-empty messages on error. -/
def test_numparse_parseInt_matchesModel
    {runner} [NondetTest runner] (api : NumParseApi) : runner Unit := do
  let s ← nondet String
  match api.parseInt s, parseIntModel s with
  | .ok actual, .ok expected => NondetTest.assert (actual = expected)
  | .error e, .error expectedKind => NondetTest.assert (e.kind = expectedKind ∧ e.message ≠ "")
  | _, _ => NondetTest.assert False

/-- `api.parseInt64` agrees with `parseInt64Model` on every input string, with non-empty messages on error. -/
def test_numparse_parseInt64_matchesModel
    {runner} [NondetTest runner] (api : NumParseApi) : runner Unit := do
  let s ← nondet String
  match api.parseInt64 s, parseInt64Model s with
  | .ok actual, .ok expected => NondetTest.assert (actual = expected)
  | .error e, .error expectedKind => NondetTest.assert (e.kind = expectedKind ∧ e.message ≠ "")
  | _, _ => NondetTest.assert False

/-- `api.formatInt` emits canonical underscore-free decimal text that round-trips through `parseInt` and respects `Int64` bounds. -/
def test_numparse_formatInt_roundTrip
    {runner} [NondetTest runner] (api : NumParseApi) : runner Unit := do
  let n ← nondet Int
  let s := api.formatInt n
  NondetTest.assert (!(s.contains '_'))
  NondetTest.assert (parseIntModel s = .ok n)
  NondetTest.assert (api.parseInt s = .ok n)
  if inInt64Range n then
    NondetTest.assert (api.parseInt64 s = .ok (Int64.ofInt n))
  else
    match api.parseInt64 s with
    | .error e => NondetTest.assert (e.kind = .overflow ∧ e.message ≠ "")
    | .ok _ => NondetTest.assert False

/-- `api.parseFloat` agrees with `parseFloatModel` up to `FloatBitMatch`, with non-empty messages on error. -/
def test_numparse_parseFloat_matchesModel
    {runner} [NondetTest runner] (api : NumParseApi) : runner Unit := do
  let s ← nondet String
  match api.parseFloat s, parseFloatModel s with
  | .ok actual, .ok expected => NondetTest.assert (FloatBitMatch expected actual)
  | .error e, .error expectedKind => NondetTest.assert (e.kind = expectedKind ∧ e.message ≠ "")
  | _, _ => NondetTest.assert False

/-- `api.formatFloat` satisfies `FloatFormatSpec` and round-trips through `api.parseFloat` preserving bits and `FloatEquiv`. -/
def test_numparse_formatFloat_specAndRoundTrip
    {runner} [NondetTest runner] (api : NumParseApi) : runner Unit := do
  let x ← nondet Float
  let s := api.formatFloat x
  NondetTest.assert (FloatFormatSpec x s)
  match api.parseFloat s with
  | .ok y => NondetTest.assert (FloatBitMatch x y ∧ FloatEquiv x y)
  | .error _ => NondetTest.assert False

private def checkIntOk {runner} [NondetTest runner]
    (api : NumParseApi) (cases : List (String × Int)) : runner Unit :=
  cases.forM fun (s, expected) =>
    match api.parseInt s with
    | .ok v => NondetTest.assert (v = expected)
    | .error _ => NondetTest.assert False

private def checkIntErr {runner} [NondetTest runner]
    (api : NumParseApi) (cases : List (String × NumParseErrorKind)) : runner Unit :=
  cases.forM fun (s, expected) =>
    match api.parseInt s with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = expected ∧ e.message ≠ "")

private def checkInt64Ok {runner} [NondetTest runner]
    (api : NumParseApi) (cases : List (String × Int64)) : runner Unit :=
  cases.forM fun (s, expected) =>
    match api.parseInt64 s with
    | .ok v => NondetTest.assert (v = expected)
    | .error _ => NondetTest.assert False

private def checkInt64Err {runner} [NondetTest runner]
    (api : NumParseApi) (cases : List (String × NumParseErrorKind)) : runner Unit :=
  cases.forM fun (s, expected) =>
    match api.parseInt64 s with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = expected ∧ e.message ≠ "")

private def checkFloatOkBits {runner} [NondetTest runner]
    (api : NumParseApi) (cases : List (String × Float)) : runner Unit :=
  cases.forM fun (s, expected) =>
    match api.parseFloat s with
    | .ok actual => NondetTest.assert (FloatBitMatch expected actual)
    | .error _ => NondetTest.assert False

private def checkFloatErr {runner} [NondetTest runner]
    (api : NumParseApi) (cases : List (String × NumParseErrorKind)) : runner Unit :=
  cases.forM fun (s, expected) =>
    match api.parseFloat s with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = expected ∧ e.message ≠ "")

/-- Concrete base prefixes, underscores, error-precedence, and 64-bit overflow boundaries for integer parsing and formatting. -/
def test_numparse_int_concreteBoundaries
    {runner} [NondetTest runner] (api : NumParseApi) : runner Unit := do
  checkIntOk api
    [ ("0", 0)
    , ("+0", 0)
    , ("-0", 0)
    , ("42", 42)
    , ("-1_000", -1000)
    , ("+1_2_3", 123)
    , ("0xdead_BEEF", 0xdeadbeef)
    , ("0X00_ff", 255)
    , ("0o7_5_5", 493)
    , ("0O007", 7)
    , ("0b1010_0101", 165)
    , ("0B0001", 1)
    , ("9223372036854775808", 9223372036854775808)
    , ("-9223372036854775809", -9223372036854775809)
    , ("0x8000_0000_0000_0000", 0x8000000000000000)
    , ("0xffff_ffff_ffff_ffff", 0xffffffffffffffff)
    ]
  checkIntErr api
    [ ("", .emptyInput)
    , ("+", .invalidSyntax)
    , ("-", .invalidSyntax)
    , ("0x", .invalidSyntax)
    , ("0X", .invalidSyntax)
    , ("0o", .invalidSyntax)
    , ("0O", .invalidSyntax)
    , ("0b", .invalidSyntax)
    , ("0B", .invalidSyntax)
    , ("abc", .invalidSyntax)
    , ("+0x1", .invalidSignForBase)
    , ("-0x1", .invalidSignForBase)
    , ("+0X1", .invalidSignForBase)
    , ("-0o7", .invalidSignForBase)
    , ("+0b1", .invalidSignForBase)
    , ("01", .leadingZero)
    , ("-01", .leadingZero)
    , ("00", .leadingZero)
    , ("0_1", .leadingZero)
    , ("_1", .invalidUnderscore)
    , ("1_", .invalidUnderscore)
    , ("1__2", .invalidUnderscore)
    , ("0x_1", .invalidUnderscore)
    , ("0x1_", .invalidUnderscore)
    , ("0x1__2", .invalidUnderscore)
    , ("0o_7", .invalidUnderscore)
    , ("0b_1", .invalidUnderscore)
    , ("12abc", .trailingChars)
    , ("0x1g", .trailingChars)
    , ("0o8", .invalidSyntax)
    , ("0b2", .invalidSyntax)
    , ("0o18", .trailingChars)
    , ("0b12", .trailingChars)
    , ("42 ", .trailingChars)
    ]
  checkInt64Ok api
    [ ("-9223372036854775808", Int64.ofInt int64MinInt)
    , ("9223372036854775807", Int64.ofInt int64MaxInt)
    , ("0x7fff_ffff_ffff_ffff", Int64.ofInt int64MaxInt)
    ]
  checkInt64Err api
    [ ("-9223372036854775809", .overflow)
    , ("9223372036854775808", .overflow)
    , ("0x8000_0000_0000_0000", .overflow)
    , ("0xffff_ffff_ffff_ffff", .overflow)
    ]
  [0, 1, -1, int64MinInt, int64MaxInt, 100000000000000000000].forM fun n =>
    NondetTest.assert (parseIntModel (api.formatInt n) = .ok n ∧ api.parseInt (api.formatInt n) = .ok n)

/-- Concrete float grammar, error-precedence, signed-zero, subnormal, overflow, and extreme-exponent boundaries. -/
def test_numparse_float_concreteSpecialsAndEdges
    {runner} [NondetTest runner] (api : NumParseApi) : runner Unit := do
  checkFloatOkBits api
    [ ("inf", Float.inf)
    , ("+inf", Float.inf)
    , ("-inf", -Float.inf)
    , ("nan", Float.nan)
    , ("+nan", Float.nan)
    , ("-nan", Float.nan)
    , ("0.0", 0.0)
    , ("+0.0", 0.0)
    , ("-0.0", -0.0)
    , ("1e05", evalFloat false 1 5)
    , ("1e-00", 1.0)
    , ("1e+01", 10.0)
    , ("1e400", Float.inf)
    , ("-1e400", -Float.inf)
    , ("1e-400", 0.0)
    , ("-1e-400", -0.0)
    , ("1e1000000000", Float.inf)
    , ("-1e1000000000", -Float.inf)
    , ("1e-1000000000", 0.0)
    , ("-1e-1000000000", -0.0)
    , ("5e-324", evalFloat false 5 (-324))
    , ("2.47e-324", evalFloat false 247 (-326))
    , ("2.5e-324", evalFloat false 25 (-325))
    , ("1e-323", evalFloat false 1 (-323))
    ]
  checkFloatErr api
    [ ("", .emptyInput)
    , ("Inf", .invalidSyntax)
    , ("INF", .invalidSyntax)
    , ("Infinity", .invalidSyntax)
    , ("-Infinity", .invalidSyntax)
    , ("NaN", .invalidSyntax)
    , ("NAN", .invalidSyntax)
    , ("42", .invalidSyntax)
    , ("-0", .invalidSyntax)
    , ("1_000", .invalidSyntax)
    , (".5", .invalidSyntax)
    , ("1.", .invalidSyntax)
    , ("1.5e", .invalidSyntax)
    , ("1.5e+", .invalidSyntax)
    , ("01.5", .leadingZero)
    , ("-00e1", .leadingZero)
    , ("0_1.5", .leadingZero)
    , ("1._5", .invalidUnderscore)
    , ("1.5_", .invalidUnderscore)
    , ("1.5e_", .invalidUnderscore)
    , ("1.5e_1", .invalidUnderscore)
    , ("1.5e1_", .invalidUnderscore)
    , ("infx", .trailingChars)
    , ("nanx", .trailingChars)
    , ("1.5x", .trailingChars)
    , ("1.5 ", .trailingChars)
    ]
  match api.parseFloat "0.0", api.parseFloat "-0.0" with
  | .ok p, .ok n =>
    NondetTest.assert (p.toBits = (0.0 : Float).toBits)
    NondetTest.assert (n.toBits = (-0.0 : Float).toBits)
    NondetTest.assert (n.toBits ≠ p.toBits)
    NondetTest.assert (FloatEquiv p n)
  | _, _ => NondetTest.assert False

/-- `api.formatFloat` emits compliant TOML literals and round-trips special, signed-zero, subnormal, and max-finite values. -/
def test_numparse_float_formatPreservesSpecialsAndExtremes
    {runner} [NondetTest runner] (api : NumParseApi) : runner Unit := do
  [Float.nan, Float.inf, -Float.inf, 0.0, -0.0, 1.0, -1.0,
    Float.ofBits 1, Float.ofBits 0x7fefffffffffffff].forM fun x => do
    let s := api.formatFloat x
    NondetTest.assert (FloatFormatSpec x s)
    match api.parseFloat s with
    | .ok y => NondetTest.assert (FloatBitMatch x y)
    | .error _ => NondetTest.assert False

/-- Declared error-coverage matrix for `LeanSwe.NumParse` fallible requests (`NumParseErrorKind`). -/
def errorCoverage : List (ErrorObligation NumParseErrorKind) :=
  [ { request := "LeanSwe.NumParse.parseInt"
      errorKind := .emptyInput
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_emptyInput" .real }
  , { request := "LeanSwe.NumParse.parseInt"
      errorKind := .invalidSyntax
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_invalidSyntax" .real }
  , { request := "LeanSwe.NumParse.parseInt"
      errorKind := .invalidSignForBase
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_invalidSignForBase" .real }
  , { request := "LeanSwe.NumParse.parseInt"
      errorKind := .leadingZero
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_leadingZero" .real }
  , { request := "LeanSwe.NumParse.parseInt"
      errorKind := .invalidUnderscore
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_invalidUnderscore" .real }
  , { request := "LeanSwe.NumParse.parseInt"
      errorKind := .overflow
      justification := .provedImpossible "LeanSwe.NumParse.Proofs.numparse_parseInt_never_overflow" }
  , { request := "LeanSwe.NumParse.parseInt"
      errorKind := .trailingChars
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_trailingChars" .real }
  , { request := "LeanSwe.NumParse.parseInt64"
      errorKind := .emptyInput
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_emptyInput" .real }
  , { request := "LeanSwe.NumParse.parseInt64"
      errorKind := .invalidSyntax
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_invalidSyntax" .real }
  , { request := "LeanSwe.NumParse.parseInt64"
      errorKind := .invalidSignForBase
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_invalidSignForBase" .real }
  , { request := "LeanSwe.NumParse.parseInt64"
      errorKind := .leadingZero
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_leadingZero" .real }
  , { request := "LeanSwe.NumParse.parseInt64"
      errorKind := .invalidUnderscore
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_invalidUnderscore" .real }
  , { request := "LeanSwe.NumParse.parseInt64"
      errorKind := .overflow
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_overflow" .real }
  , { request := "LeanSwe.NumParse.parseInt64"
      errorKind := .trailingChars
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_trailingChars" .real }
  , { request := "LeanSwe.NumParse.parseFloat"
      errorKind := .emptyInput
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_emptyInput" .real }
  , { request := "LeanSwe.NumParse.parseFloat"
      errorKind := .invalidSyntax
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_invalidSyntax" .real }
  , { request := "LeanSwe.NumParse.parseFloat"
      errorKind := .invalidSignForBase
      justification := .provedImpossible "LeanSwe.NumParse.Proofs.numparse_parseFloat_never_invalidSignForBase" }
  , { request := "LeanSwe.NumParse.parseFloat"
      errorKind := .leadingZero
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_leadingZero" .real }
  , { request := "LeanSwe.NumParse.parseFloat"
      errorKind := .invalidUnderscore
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_invalidUnderscore" .real }
  , { request := "LeanSwe.NumParse.parseFloat"
      errorKind := .overflow
      justification := .provedImpossible "LeanSwe.NumParse.Proofs.numparse_parseFloat_never_overflow" }
  , { request := "LeanSwe.NumParse.parseFloat"
      errorKind := .trailingChars
      justification := .tested "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_trailingChars" .real } ]

end LeanSwe.NumParse
