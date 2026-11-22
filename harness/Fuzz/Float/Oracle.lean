import LeanSwe.NumParse.Interface

/-!
Thin C99/POSIX IEEE-754 oracle bindings, pure IEEE-754 bit-pattern helpers,
and persistent Python 3 `float`/`repr`/`tomllib`/`fractions` co-process differential oracle for `Fuzz/Float/`.
-/

namespace Fuzz.Float

@[extern "leanswe_float_oracle_is_tonearest"]
private opaque rawCIsRoundToNearest : IO Bool

@[extern "leanswe_float_oracle_strtod"]
private opaque rawCStrtod (s : @& String) : USize × UInt64

@[extern "leanswe_float_oracle_snprintf17g"]
private opaque rawCSnprintf17g (rawBits : UInt64) : String

@[extern "leanswe_float_oracle_raw_double_from_bits"]
private opaque rawCRawDoubleFromBits (rawBits : UInt64) : Float

@[extern "leanswe_float_oracle_raw_f32_from_bits"]
private opaque rawCRawFloat32FromBits (rawBits : UInt32) : Float32

@[extern "leanswe_float_oracle_raw_bits_from_double"]
private opaque rawCRawBitsFromDouble (d : Float) : UInt64

@[extern "leanswe_float_oracle_raw_bits_from_f32"]
private opaque rawCRawBitsFromFloat32 (f : Float32) : UInt32

@[extern "leanswe_float_oracle_unop"]
private opaque rawCUnOp (op : UInt8) (aBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_trans1"]
private opaque rawCTrans1 (op : UInt8) (aBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_trans2"]
private opaque rawCTrans2 (op : UInt8) (aBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_trans3"]
private opaque rawCTrans3 (op : UInt8) (aBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_binop"]
private opaque rawCBinOp (op : UInt8) (aBits bBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_fma"]
private opaque rawCFma (aBits bBits cBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_cmp"]
private opaque rawCCmp (aBits bBits : UInt64) : UInt8

@[extern "leanswe_float_oracle_frexp"]
private opaque rawCFrexp (aBits : UInt64) : UInt64 × UInt32

@[extern "leanswe_float_oracle_ldexp"]
private opaque rawCLdexp (aBits : UInt64) (expBits : UInt32) : UInt64

@[extern "leanswe_float_oracle_f64_to_f32"]
private opaque rawCF64ToF32 (aBits : UInt64) : UInt32

@[extern "leanswe_float_oracle_f32_to_f64"]
private opaque rawCF32ToF64 (aBits : UInt32) : UInt64

@[extern "leanswe_float_oracle_minmax"]
private opaque rawCMinMax (isMax : UInt8) (aBits bBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_minmax_num"]
private opaque rawCMinMaxNum (isMax : UInt8) (aBits bBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_to_uint64"]
private opaque rawCToUInt64 (aBits maxVal : UInt64) : UInt64

@[extern "leanswe_float_oracle_to_int64"]
private opaque rawCToInt64 (aBits minBits maxBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_of_uint64"]
private opaque rawCOfUInt64 (u : UInt64) : UInt64

@[extern "leanswe_float_oracle_of_int64"]
private opaque rawCOfInt64 (iBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_f32_unop"]
private opaque rawCF32UnOp (op : UInt8) (aBits : UInt32) : UInt32

@[extern "leanswe_float_oracle_f32_binop"]
private opaque rawCF32BinOp (op : UInt8) (aBits bBits : UInt32) : UInt32

@[extern "leanswe_float_oracle_f32_fma"]
private opaque rawCF32Fma (aBits bBits cBits : UInt32) : UInt32

@[extern "leanswe_float_oracle_f32_cmp"]
private opaque rawCF32Cmp (aBits bBits : UInt32) : UInt8

@[extern "leanswe_float_oracle_f32_frexp"]
private opaque rawCF32Frexp (aBits : UInt32) : UInt32 × UInt32

@[extern "leanswe_float_oracle_f32_ldexp"]
private opaque rawCF32Ldexp (aBits : UInt32) (expBits : UInt32) : UInt32

@[extern "leanswe_float_oracle_f32_minmax"]
private opaque rawCF32MinMax (isMax : UInt8) (aBits bBits : UInt32) : UInt32

@[extern "leanswe_float_oracle_f32_minmax_num"]
private opaque rawCF32MinMaxNum (isMax : UInt8) (aBits bBits : UInt32) : UInt32

@[extern "leanswe_float_oracle_f32_to_uint64"]
private opaque rawCF32ToUInt64 (aBits : UInt32) (maxVal : UInt64) : UInt64

@[extern "leanswe_float_oracle_f32_to_int64"]
private opaque rawCF32ToInt64 (aBits : UInt32) (minBits maxBits : UInt64) : UInt64

@[extern "leanswe_float_oracle_f32_of_uint64"]
private opaque rawCF32OfUInt64 (u : UInt64) : UInt32

@[extern "leanswe_float_oracle_f32_of_int64"]
private opaque rawCF32OfInt64 (iBits : UInt64) : UInt32

/-- Verify that the host IEEE-754 rounding mode is `FE_TONEAREST`. -/
def cIsRoundToNearest : IO Bool :=
  rawCIsRoundToNearest

/-- Call C99 `strtod_l` in the `"C"` locale, returning `(consumedBytes, rawBinary64Bits)`. -/
def cStrtod (s : String) : USize × UInt64 :=
  rawCStrtod s

/-- Format raw binary64 `bits` via C `snprintf("%.17g")` in the `"C"` locale. -/
def cSnprintf17g (rawBits : UInt64) : String :=
  rawCSnprintf17g rawBits

/-- Inject arbitrary uncanonicalized binary64 `bits` directly into a Lean `Float` register. -/
def rawDoubleFromBits (rawBits : UInt64) : Float :=
  rawCRawDoubleFromBits rawBits

/-- Inject arbitrary uncanonicalized binary32 `bits` directly into a Lean `Float32` register. -/
def rawFloat32FromBits (rawBits : UInt32) : Float32 :=
  rawCRawFloat32FromBits rawBits

/-- Read raw uncanonicalized binary64 bits directly from a Lean `Float` register. -/
def rawBitsFromDouble (d : Float) : UInt64 :=
  rawCRawBitsFromDouble d

/-- Read raw uncanonicalized binary32 bits directly from a Lean `Float32` register. -/
def rawBitsFromFloat32 (f : Float32) : UInt32 :=
  rawCRawBitsFromFloat32 f

/-- Compute C unary double op (`0`: `-a`, `1`: `fabs`, `2`: `sqrt`, `3`: `ceil`, `4`: `floor`, `5`: `round`). -/
def cUnOp (op : UInt8) (aBits : UInt64) : UInt64 :=
  rawCUnOp op aBits

/-- Compute C unary transcendental group 1 (`0`: `sin`, `1`: `cos`, `2`: `tan`, `3`: `asin`, `4`: `acos`, `5`: `atan`, `6`: `sinh`). -/
def cTrans1 (op : UInt8) (aBits : UInt64) : UInt64 :=
  rawCTrans1 op aBits

/-- Compute C unary transcendental group 2 (`0`: `cosh`, `1`: `tanh`, `2`: `asinh`, `3`: `acosh`, `4`: `atanh`, `5`: `exp`, `6`: `exp2`). -/
def cTrans2 (op : UInt8) (aBits : UInt64) : UInt64 :=
  rawCTrans2 op aBits

/-- Compute C unary transcendental group 3 (`0`: `log`, `1`: `log2`, `2`: `log10`, `3`: `cbrt`). -/
def cTrans3 (op : UInt8) (aBits : UInt64) : UInt64 :=
  rawCTrans3 op aBits

/-- Compute C binary double op (`0`: `+`, `1`: `-`, `2`: `*`, `3`: `/`, `4`: `pow`, `5`: `atan2`) returning raw bits. -/
def cBinOp (op : UInt8) (aBits bBits : UInt64) : UInt64 :=
  rawCBinOp op aBits bBits

/-- Compute C99 `fma(a, b, c)` returning raw binary64 bits. -/
def cFma (aBits bBits cBits : UInt64) : UInt64 :=
  rawCFma aBits bBits cBits

/-- Compute C comparison/classification bitmask (`==`, `<`, `<=`, `isnan`, `isfinite`, `isinf`). -/
def cCmp (aBits bBits : UInt64) : UInt8 :=
  rawCCmp aBits bBits

/-- Compute C `frexp(a, &exp)` returning `(mantissaBits, expInt32)`. -/
def cFrexp (aBits : UInt64) : UInt64 × Int32 :=
  let (sig, expBits) := rawCFrexp aBits
  (sig, Int32.ofUInt32 expBits)

/-- Compute C `ldexp(a, exp)` returning raw binary64 bits. -/
def cLdexp (aBits : UInt64) (exp : Int32) : UInt64 :=
  rawCLdexp aBits exp.toUInt32

/-- Narrow binary64 `aBits` to binary32 raw bits via C `(float)`. -/
def cF64ToF32 (aBits : UInt64) : UInt32 :=
  rawCF64ToF32 aBits

/-- Widen binary32 `aBits` to binary64 raw bits via C `(double)`. -/
def cF32ToF64 (aBits : UInt32) : UInt64 :=
  rawCF32ToF64 aBits

/-- Compute IEEE-754-2019 `minimum` (`isMax=false`) or `maximum` (`isMax=true`) in C. -/
def cMinMax (isMax : Bool) (aBits bBits : UInt64) : UInt64 :=
  rawCMinMax (if isMax then 1 else 0) aBits bBits

/-- Compute IEEE-754-2019 `minimumNumber` (`isMax=false`) or `maximumNumber` (`isMax=true`) in C. -/
def cMinMaxNum (isMax : Bool) (aBits bBits : UInt64) : UInt64 :=
  rawCMinMaxNum (if isMax then 1 else 0) aBits bBits

/-- Convert binary64 `aBits` to clamped unsigned integer `[0, maxVal]` in C without UB. -/
def cToUInt64 (aBits maxVal : UInt64) : UInt64 :=
  rawCToUInt64 aBits maxVal

/-- Convert binary64 `aBits` to clamped signed integer `[minVal, maxVal]` in C without UB. -/
def cToInt64 (aBits : UInt64) (minVal maxVal : Int64) : Int64 :=
  Int64.ofUInt64 (rawCToInt64 aBits minVal.toUInt64 maxVal.toUInt64)

/-- Convert `UInt64` to binary64 bits via C `(double)`. -/
def cOfUInt64 (u : UInt64) : UInt64 :=
  rawCOfUInt64 u

/-- Convert `Int64` to binary64 bits via C `(double)`. -/
def cOfInt64 (i : Int64) : UInt64 :=
  rawCOfInt64 i.toUInt64

/-- Compute C unary float32 op (`0`: `-a`, `1`: `fabsf`, `2`: `sqrtf`, `3`: `ceilf`, `4`: `floorf`, `5`: `roundf`). -/
def cF32UnOp (op : UInt8) (aBits : UInt32) : UInt32 :=
  rawCF32UnOp op aBits

/-- Compute C binary float32 op (`0`: `+`, `1`: `-`, `2`: `*`, `3`: `/`, `4`: `powf`) returning raw bits. -/
def cF32BinOp (op : UInt8) (aBits bBits : UInt32) : UInt32 :=
  rawCF32BinOp op aBits bBits

/-- Compute C99 `fmaf(a, b, c)` returning raw binary32 bits. -/
def cF32Fma (aBits bBits cBits : UInt32) : UInt32 :=
  rawCF32Fma aBits bBits cBits

/-- Compute C float32 comparison/classification bitmask (`==`, `<`, `<=`, `isnan`, `isfinite`, `isinf`). -/
def cF32Cmp (aBits bBits : UInt32) : UInt8 :=
  rawCF32Cmp aBits bBits

/-- Compute C `frexpf(a, &exp)` returning `(mantissaBits, expInt32)`. -/
def cF32Frexp (aBits : UInt32) : UInt32 × Int32 :=
  let (sig, expBits) := rawCF32Frexp aBits
  (sig, Int32.ofUInt32 expBits)

/-- Compute C `ldexpf(a, exp)` returning raw binary32 bits. -/
def cF32Ldexp (aBits : UInt32) (exp : Int32) : UInt32 :=
  rawCF32Ldexp aBits exp.toUInt32

/-- Compute IEEE-754-2019 float32 `minimum` (`isMax=false`) or `maximum` (`isMax=true`) in C. -/
def cF32MinMax (isMax : Bool) (aBits bBits : UInt32) : UInt32 :=
  rawCF32MinMax (if isMax then 1 else 0) aBits bBits

/-- Compute IEEE-754-2019 float32 `minimumNumber` (`isMax=false`) or `maximumNumber` (`isMax=true`) in C. -/
def cF32MinMaxNum (isMax : Bool) (aBits bBits : UInt32) : UInt32 :=
  rawCF32MinMaxNum (if isMax then 1 else 0) aBits bBits

/-- Convert binary32 `aBits` to clamped unsigned integer `[0, maxVal]` in C without UB. -/
def cF32ToUInt64 (aBits : UInt32) (maxVal : UInt64) : UInt64 :=
  rawCF32ToUInt64 aBits maxVal

/-- Convert binary32 `aBits` to clamped signed integer `[minVal, maxVal]` in C without UB. -/
def cF32ToInt64 (aBits : UInt32) (minVal maxVal : Int64) : Int64 :=
  Int64.ofUInt64 (rawCF32ToInt64 aBits minVal.toUInt64 maxVal.toUInt64)

/-- Convert `UInt64` to binary32 bits via C `(float)`. -/
def cF32OfUInt64 (u : UInt64) : UInt32 :=
  rawCF32OfUInt64 u

/-- Convert `Int64` to binary32 bits via C `(float)`. -/
def cF32OfInt64 (i : Int64) : UInt32 :=
  rawCF32OfInt64 i.toUInt64

/-- Return `true` iff `b` encodes any IEEE-754 binary64 NaN (quiet or signaling, either sign). -/
def isRawNaNBits (b : UInt64) : Bool :=
  ((b &&& 0x7ff0000000000000) == 0x7ff0000000000000) &&
    ((b &&& 0x000fffffffffffff) != 0)

/-- Return `true` iff `b` encodes any IEEE-754 binary32 NaN. -/
def isRawNaNBits32 (b : UInt32) : Bool :=
  ((b &&& 0x7f800000) == 0x7f800000) && ((b &&& 0x007fffff) != 0)

/-- Canonicalize any raw binary32 NaN bit pattern to Lean's `0x7fc00000`. -/
def canonBits32 (b : UInt32) : UInt32 :=
  if isRawNaNBits32 b then 0x7fc00000 else b

/-- Return `true` iff `b` encodes a signaling binary64 NaN (quiet bit 51 cleared). -/
def isSignalingNaNBits (b : UInt64) : Bool :=
  isRawNaNBits b && ((b &&& 0x0008000000000000) == 0)

/-- Return `true` iff `b` encodes a signaling binary32 NaN (quiet bit 22 cleared). -/
def isSignalingNaNBits32 (b : UInt32) : Bool :=
  isRawNaNBits32 b && ((b &&& 0x00400000) == 0)

/-- Canonicalize any raw binary64 NaN bit pattern to Lean's `0x7ff8000000000000`. -/
def canonBits (b : UInt64) : UInt64 :=
  if isRawNaNBits b then 0x7ff8000000000000 else b

/-- Return `true` iff `b` encodes a non-zero IEEE-754 binary64 subnormal. -/
def isSubnormalBits (b : UInt64) : Bool :=
  let absBits := b &&& 0x7fffffffffffffff
  (absBits != 0) && (absBits < 0x0010000000000000)

/-- Remove all `'_'` separator characters from `s`. -/
def stripUnderscores (s : String) : String :=
  String.ofList (s.toList.filter (· != '_'))

/-- Return `true` iff `s` begins with an ASCII `isspace` character. -/
def hasLeadingAsciiSpace (s : String) : Bool :=
  match s.toList with
  | c :: _ =>
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'
  | [] => false

/-- Normalize C `snprintf` or Python `repr` float output into valid TOML 1.0 float syntax. -/
def normalizeCFormattedForToml (s : String) : String :=
  let low := s.toLower
  if low == "nan" || low == "-nan" || low == "+nan" then
    "nan"
  else if low == "inf" || low == "+inf" then
    "inf"
  else if low == "-inf" then
    "-inf"
  else if s.contains '.' || s.contains 'e' || s.contains 'E' then
    s
  else
    s ++ ".0"

private def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

private def hasDotWithoutFracDigit : List Char → Bool
  | [] => false
  | '.' :: [] => true
  | '.' :: 'e' :: _ => true
  | '.' :: 'E' :: _ => true
  | '.' :: c :: rest =>
    if isAsciiDigit c then hasDotWithoutFracDigit rest else true
  | _ :: rest => hasDotWithoutFracDigit rest

/-- Verify that a string accepted in full by C `strtod_l` legitimately violates TOML 1.0 float syntax. -/
def isAllowedStrtodOnlySyntax (s : String) : Bool :=
  let body := match s.toList with
    | '+' :: rest => rest
    | '-' :: rest => rest
    | cs => cs
  let bodyStr := String.ofList body
  let lowBody := bodyStr.toLower
  if lowBody.startsWith "0x" then
    true
  else if lowBody.startsWith "inf" || lowBody.startsWith "nan" then
    bodyStr != "inf" && bodyStr != "nan"
  else if !bodyStr.contains '.' && !bodyStr.contains 'e' && !bodyStr.contains 'E' then
    true
  else if bodyStr.startsWith "." || hasDotWithoutFracDigit body then
    true
  else
    match body with
    | '0' :: c :: _ => isAsciiDigit c
    | _ => false

/-- Return `true` iff `s` is safe for direct `"x = " ++ s` `tomllib.loads` and `LeanSwe.Toml.parse` comparison. -/
def isTomlCheckEligible (s : String) : Bool :=
  !s.isEmpty &&
  !s.startsWith " " &&
  !s.endsWith " " &&
  !s.startsWith "\t" &&
  !s.endsWith "\t" &&
  !s.contains '\n' &&
  !s.contains '#' &&
  !s.contains '\\' &&
  !s.contains '"' &&
  !s.contains '\'' &&
  !s.contains '[' &&
  !s.contains '{'

/-- One parse check entry queued for the persistent Python 3 differential oracle. -/
structure PyParseItem where
  /-- Raw input string passed to `NumParse.parseFloat`. -/
  rawInput : String
  /-- Input string with `'_'` stripped (for `float()`). -/
  cleanStr : String
  /-- Whether `NumParse.parseFloat` succeeded. -/
  expectedOk : Bool
  /-- Canonicalized expected binary64 bit pattern when `expectedOk` is `true`. -/
  expectedBits : UInt64
  /-- Whether to also run `tomllib.loads("x = " ++ rawInput)`. -/
  tomlCheck : Bool
  deriving Repr, Inhabited

/-- One formatting check entry queued for the persistent Python 3 differential oracle. -/
structure PyFormatItem where
  /-- Canonicalized binary64 bit pattern of the formatted float. -/
  bits : UInt64
  /-- String produced by `NumParse.formatFloat`. -/
  formatted : String
  deriving Repr, Inhabited

/-- One arbitrary-precision `Int -> Float` check queued for Python `float(int(s))`. -/
structure PyIntFloatItem where
  /-- Decimal representation of the `Nat` or `Int`. -/
  decStr : String
  /-- Expected canonical binary64 bits from Lean `Nat.toFloat`/`Int.toFloat`. -/
  expectedBits : UInt64
  deriving Repr, Inhabited

/-- One independent Python `fractions.Fraction` extern check (`ceil`, `floor`, `round`, `frExp`, `scaleB`). -/
structure PyExternItem where
  /-- `false` for `Float` (binary64), `true` for `Float32` (binary32). -/
  isFloat32 : Bool
  /-- Raw IEEE-754 bits (`UInt64` for binary64, zero-extended `UInt32` for binary32). -/
  bits : UInt64
  /-- Exponent passed to `scaleB`. -/
  scaleExp : Int32
  /-- Expected `ceil` canonical bits. -/
  ceilBits : UInt64
  /-- Expected `floor` canonical bits. -/
  floorBits : UInt64
  /-- Expected `round` canonical bits. -/
  roundBits : UInt64
  /-- Expected `frExp` significand canonical bits. -/
  frexpSigBits : UInt64
  /-- Expected `frExp` integer exponent (checked when finite). -/
  frexpExp : Int
  /-- Expected `scaleB` canonical bits. -/
  scaleBBits : UInt64
  deriving Repr, Inhabited

/-- Accumulated batch of Python 3 differential verification items for one episode. -/
structure PyOracleBatch where
  /-- Queued string parse checks. -/
  parses : Array PyParseItem := #[]
  /-- Queued formatted string checks. -/
  formats : Array PyFormatItem := #[]
  /-- Queued `UInt64` bit patterns for Python `repr()` → `NumParse.parseFloat` round-trip. -/
  reprBits : Array UInt64 := #[]
  /-- Queued `Int -> Float` checks against Python `float(int(s))`. -/
  intFloats : Array PyIntFloatItem := #[]
  /-- Queued independent `Fraction`-based `ceil`/`floor`/`round`/`frExp`/`scaleB` checks. -/
  externs : Array PyExternItem := #[]
  deriving Inhabited

/-- Return `true` iff `batch` has no queued checks. -/
def PyOracleBatch.isEmpty (b : PyOracleBatch) : Bool :=
  b.parses.isEmpty && b.formats.isEmpty && b.reprBits.isEmpty &&
    b.intFloats.isEmpty && b.externs.isEmpty

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def bytesToHex (bs : ByteArray) : String := Id.run do
  let mut out := ""
  for i in [0 : bs.size] do
    let b := bs[i]!.toNat
    out := out.push (hexDigit (b / 16))
    out := out.push (hexDigit (b % 16))
  return out

private def stringToHex (s : String) : String :=
  bytesToHex s.toUTF8

private def u64ToHex16 (u : UInt64) : String := Id.run do
  let mut out := ""
  for idx in List.range 16 do
    let shift := (15 - idx) * 4
    let nib := ((u >>> UInt64.ofNat shift) &&& 0xf).toNat
    out := out.push (hexDigit nib)
  return out

private def parseHexByte? (hi lo : Char) : Option UInt8 :=
  let val (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
    else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
    else none
  match val hi, val lo with
  | some h, some l => some (UInt8.ofNat (h * 16 + l))
  | _, _ => none

private def hexToString (hex : String) : Except String String := do
  let chars := hex.toList
  if chars.length % 2 != 0 then
    throw s!"PYTHON_ORACLE_BAD_HEX_LENGTH: {chars.length}"
  let rec loop : List Char → ByteArray → Except String ByteArray
    | [], acc => .ok acc
    | hi :: lo :: rest, acc =>
      match parseHexByte? hi lo with
      | some b => loop rest (acc.push b)
      | none => .error s!"PYTHON_ORACLE_BAD_HEX_CHAR: {hi}{lo}"
    | [_], _ => .error "PYTHON_ORACLE_ODD_HEX"
  let bytes ← loop chars ByteArray.empty
  match String.fromUTF8? bytes with
  | some s => .ok s
  | none => .error "PYTHON_ORACLE_INVALID_UTF8"

private def parseHexU64? (hex : String) : Option UInt64 :=
  let chars := hex.toList
  if chars.length != 16 then none
  else
    chars.foldlM (init := (0 : UInt64)) fun acc c =>
      let nib? :=
        if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
        else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
        else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
        else none
      nib?.map fun d => (acc <<< 4) ||| UInt64.ofNat d

private def pythonCoprocScript : String :=
  "from fractions import Fraction\n" ++
  "import math, struct, sys, tomllib\n" ++
  "sys.set_int_max_str_digits(0)\n" ++
  "def canon(v):\n" ++
  "    if math.isnan(v):\n" ++
  "        return 0x7ff8000000000000\n" ++
  "    return struct.unpack('>Q', struct.pack('>d', v))[0]\n" ++
  "def canon32(v):\n" ++
  "    if math.isnan(v):\n" ++
  "        return 0x7fc00000\n" ++
  "    try:\n" ++
  "        return struct.unpack('>I', struct.pack('>f', v))[0]\n" ++
  "    except OverflowError:\n" ++
  "        return 0x7f800000 if v >= 0 else 0xff800000\n" ++
  "def norm_repr(s):\n" ++
  "    low = s.lower()\n" ++
  "    if low in ('nan', '-nan', '+nan'):\n" ++
  "        return 'nan'\n" ++
  "    if low in ('inf', '+inf'):\n" ++
  "        return 'inf'\n" ++
  "    if low == '-inf':\n" ++
  "        return '-inf'\n" ++
  "    if '.' in s or 'e' in s or 'E' in s:\n" ++
  "        return s\n" ++
  "    return s + '.0'\n" ++
  "def check_extern(is_f32, bits, sc, e_ceil, e_floor, e_round, e_fsig, e_fexp, e_scale):\n" ++
  "    c_fn = canon32 if is_f32 else canon\n" ++
  "    d = struct.unpack('>f', struct.pack('>I', bits))[0] if is_f32 else struct.unpack('>d', struct.pack('>Q', bits))[0]\n" ++
  "    if not math.isfinite(d):\n" ++
  "        cb = c_fn(d)\n" ++
  "        for name, exp in (('ceil', e_ceil), ('floor', e_floor), ('round', e_round), ('frexp_sig', e_fsig), ('scaleb', e_scale)):\n" ++
  "            if cb != exp:\n" ++
  "                raise AssertionError(f'E nonfinite {name} mismatch: f32={is_f32} bits={bits:#x} py={cb:#x} lean={exp:#x}')\n" ++
  "        return\n" ++
  "    f = Fraction(d)\n" ++
  "    cv = math.ceil(f)\n" ++
  "    cf = math.copysign(0.0, d) if cv == 0 else float(cv)\n" ++
  "    if c_fn(cf) != e_ceil:\n" ++
  "        raise AssertionError(f'E ceil mismatch: f32={is_f32} bits={bits:#x} py={c_fn(cf):#x} lean={e_ceil:#x}')\n" ++
  "    fv = math.floor(f)\n" ++
  "    ff = math.copysign(0.0, d) if fv == 0 else float(fv)\n" ++
  "    if c_fn(ff) != e_floor:\n" ++
  "        raise AssertionError(f'E floor mismatch: f32={is_f32} bits={bits:#x} py={c_fn(ff):#x} lean={e_floor:#x}')\n" ++
  "    rv = math.floor(f + Fraction(1, 2)) if f >= 0 else -math.floor(-f + Fraction(1, 2))\n" ++
  "    rf = math.copysign(0.0, d) if rv == 0 else float(rv)\n" ++
  "    if c_fn(rf) != e_round:\n" ++
  "        raise AssertionError(f'E round mismatch: f32={is_f32} bits={bits:#x} py={c_fn(rf):#x} lean={e_round:#x}')\n" ++
  "    if d == 0.0:\n" ++
  "        sig_bits = c_fn(d)\n" ++
  "        ex = 0\n" ++
  "    else:\n" ++
  "        num, den = abs(d).as_integer_ratio()\n" ++
  "        ex = num.bit_length() - (den.bit_length() - 1)\n" ++
  "        sig_v = math.copysign(float(Fraction(num, 1 << num.bit_length())), d)\n" ++
  "        sig_bits = c_fn(sig_v)\n" ++
  "    if sig_bits != e_fsig or ex != e_fexp:\n" ++
  "        raise AssertionError(f'E frexp mismatch: f32={is_f32} bits={bits:#x} py=({sig_bits:#x},{ex}) lean=({e_fsig:#x},{e_fexp})')\n" ++
  "    if d == 0.0:\n" ++
  "        sb = c_fn(d)\n" ++
  "    elif sc > 3000:\n" ++
  "        sb = c_fn(math.copysign(float('inf'), d))\n" ++
  "    elif sc < -3000:\n" ++
  "        sb = c_fn(math.copysign(0.0, d))\n" ++
  "    else:\n" ++
  "        sf = f * (1 << sc) if sc >= 0 else f / (1 << (-sc))\n" ++
  "        try:\n" ++
  "            sv = float(sf)\n" ++
  "            if sv == 0.0:\n" ++
  "                sv = math.copysign(0.0, d)\n" ++
  "            sb = c_fn(sv)\n" ++
  "        except OverflowError:\n" ++
  "            sb = c_fn(math.copysign(float('inf'), d))\n" ++
  "    if sb != e_scale:\n" ++
  "        raise AssertionError(f'E scaleB mismatch: f32={is_f32} bits={bits:#x} sc={sc} py={sb:#x} lean={e_scale:#x}')\n" ++
  "out_lines = []\n" ++
  "batch_err = None\n" ++
  "for raw_line in sys.stdin:\n" ++
  "    line = raw_line.rstrip('\\r\\n')\n" ++
  "    if not line:\n" ++
  "        continue\n" ++
  "    if line == 'QUIT':\n" ++
  "        break\n" ++
  "    if line == 'END':\n" ++
  "        if batch_err is not None:\n" ++
  "            sys.stdout.write('ERR:' + batch_err + '\\n')\n" ++
  "        else:\n" ++
  "            if out_lines:\n" ++
  "                sys.stdout.write('\\n'.join(out_lines) + '\\n')\n" ++
  "            sys.stdout.write('OK\\n')\n" ++
  "        sys.stdout.flush()\n" ++
  "        out_lines = []\n" ++
  "        batch_err = None\n" ++
  "        continue\n" ++
  "    if batch_err is not None:\n" ++
  "        continue\n" ++
  "    try:\n" ++
  "        parts = line.split(' ')\n" ++
  "        tag = parts[0]\n" ++
  "        if tag == 'P':\n" ++
  "            toml_chk = int(parts[1])\n" ++
  "            exp_ok = int(parts[2])\n" ++
  "            exp_bits = int(parts[3], 16)\n" ++
  "            raw_s = bytes.fromhex(parts[4]).decode('utf-8')\n" ++
  "            clean_s = bytes.fromhex(parts[5]).decode('utf-8')\n" ++
  "            if exp_ok == 1:\n" ++
  "                got = canon(float(clean_s))\n" ++
  "                if got != exp_bits:\n" ++
  "                    raise AssertionError(f'P float mismatch: {clean_s[:80]!r} py={got:#018x} lean={exp_bits:#018x}')\n" ++
  "            if toml_chk == 1:\n" ++
  "                try:\n" ++
  "                    val = tomllib.loads('x = ' + raw_s)['x']\n" ++
  "                    is_flt = isinstance(val, float)\n" ++
  "                except tomllib.TOMLDecodeError:\n" ++
  "                    val = None\n" ++
  "                    is_flt = False\n" ++
  "                if exp_ok == 1:\n" ++
  "                    if not is_flt:\n" ++
  "                        raise AssertionError(f'P tomllib rejected valid float: {raw_s[:80]!r}')\n" ++
  "                    got_t = canon(val)\n" ++
  "                    if got_t != exp_bits:\n" ++
  "                        raise AssertionError(f'P tomllib bits mismatch: {raw_s[:80]!r} py={got_t:#018x} lean={exp_bits:#018x}')\n" ++
  "                elif is_flt:\n" ++
  "                    raise AssertionError(f'P tomllib accepted invalid float: {raw_s[:80]!r} -> {val!r}')\n" ++
  "        elif tag == 'F':\n" ++
  "            exp_bits = int(parts[1], 16)\n" ++
  "            fmt_s = bytes.fromhex(parts[2]).decode('utf-8')\n" ++
  "            got_f = canon(float(fmt_s))\n" ++
  "            if got_f != exp_bits:\n" ++
  "                raise AssertionError(f'F float mismatch: {fmt_s!r} py={got_f:#018x} lean={exp_bits:#018x}')\n" ++
  "            val = tomllib.loads('x = ' + fmt_s)['x']\n" ++
  "            if not isinstance(val, float) or canon(val) != exp_bits:\n" ++
  "                raise AssertionError(f'F tomllib mismatch: {fmt_s!r} -> {val!r}')\n" ++
  "        elif tag == 'R':\n" ++
  "            bits = int(parts[1], 16)\n" ++
  "            d = struct.unpack('>d', struct.pack('>Q', bits))[0]\n" ++
  "            out_lines.append('R ' + parts[1] + ' ' + norm_repr(repr(d)).encode('utf-8').hex())\n" ++
  "        elif tag == 'I':\n" ++
  "            exp_bits = int(parts[1], 16)\n" ++
  "            dec_s = bytes.fromhex(parts[2]).decode('utf-8')\n" ++
  "            n = int(dec_s)\n" ++
  "            try:\n" ++
  "                got_i = canon(float(n))\n" ++
  "            except OverflowError:\n" ++
  "                got_i = 0x7ff0000000000000 if n >= 0 else 0xfff0000000000000\n" ++
  "            if got_i != exp_bits:\n" ++
  "                raise AssertionError(f'I int->float mismatch: n={dec_s[:80]} py={got_i:#018x} lean={exp_bits:#018x}')\n" ++
  "        elif tag == 'E':\n" ++
  "            check_extern(\n" ++
  "                int(parts[1]), int(parts[2], 16),\n" ++
  "                int(bytes.fromhex(parts[3]).decode('utf-8')),\n" ++
  "                int(parts[4], 16), int(parts[5], 16), int(parts[6], 16),\n" ++
  "                int(parts[7], 16), int(bytes.fromhex(parts[8]).decode('utf-8')),\n" ++
  "                int(parts[9], 16))\n" ++
  "        else:\n" ++
  "            raise AssertionError(f'unknown tag {tag!r}')\n" ++
  "    except Exception as exc:\n" ++
  "        msg = str(exc).replace('\\n', ' ').strip()\n" ++
  "        batch_err = msg if msg else type(exc).__name__\n"

private def encodeBatchPayload (batch : PyOracleBatch) : String := Id.run do
  let total := batch.parses.size + batch.formats.size + batch.reprBits.size +
    batch.intFloats.size + batch.externs.size
  let mut lines : Array String := Array.mkEmpty (total + 1)
  for item in batch.parses do
    let tc := if item.tomlCheck then "1" else "0"
    let ok := if item.expectedOk then "1" else "0"
    lines := lines.push s!"P {tc} {ok} {u64ToHex16 item.expectedBits} {stringToHex item.rawInput} {stringToHex item.cleanStr}"
  for item in batch.formats do
    lines := lines.push s!"F {u64ToHex16 item.bits} {stringToHex item.formatted}"
  for b in batch.reprBits do
    lines := lines.push s!"R {u64ToHex16 b}"
  for item in batch.intFloats do
    lines := lines.push s!"I {u64ToHex16 item.expectedBits} {stringToHex item.decStr}"
  for item in batch.externs do
    let f32Tag := if item.isFloat32 then "1" else "0"
    lines := lines.push (s!"E {f32Tag} {u64ToHex16 item.bits} {stringToHex (toString item.scaleExp)} " ++
      s!"{u64ToHex16 item.ceilBits} {u64ToHex16 item.floorBits} {u64ToHex16 item.roundBits} " ++
      s!"{u64ToHex16 item.frexpSigBits} {stringToHex (toString item.frexpExp)} {u64ToHex16 item.scaleBBits}")
  lines := lines.push "END"
  return "\n".intercalate lines.toList ++ "\n"

private def drainPipeToDiscard (h : IO.FS.Handle) : IO Unit := do
  while true do
    let chunk ← h.read 8192
    if chunk.isEmpty then
      break

private def drainStderrLoop (h : IO.FS.Handle) (ref : IO.Ref String) : IO Unit := do
  while true do
    let chunk ← h.read 4096
    if chunk.isEmpty then
      break
    let text := match String.fromUTF8? chunk with
      | some s => s
      | none => s!"<non-utf8 {chunk.size}B>"
    ref.modify fun cur =>
      if cur.length < 16384 then cur ++ text else cur

/-- Persistent Python 3 co-process handle used to check every episode without clamping. -/
structure PyOracleClient where
  /-- Spawned `python3` child process. -/
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }
  /-- Captured bounded `stderr` output drained continuously on a background task. -/
  stderrRef : IO.Ref String
  /-- Background task continuously draining `child.stderr` to prevent >64 KiB pipe deadlocks. -/
  stderrTask : Task (Except IO.Error Unit)

/-- Spawn the persistent Python 3 differential oracle co-process in isolated mode (`-I`). -/
def startPyOracleClient : IO PyOracleClient := do
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-I", "-B", "-u", "-c", pythonCoprocScript]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let stderrRef ← IO.mkRef ""
  let stderrTask ← IO.asTask (drainStderrLoop child.stderr stderrRef)
  return { child, stderrRef, stderrTask }

/-- Flush one episode's `PyOracleBatch` to the persistent Python 3 co-process and verify all `repr()` round-trips. -/
def flushPyBatch (client : PyOracleClient) (batch : PyOracleBatch) : IO (Except String Unit) := do
  if batch.isEmpty then
    return .ok ()
  let payload := encodeBatchPayload batch
  try
    client.child.stdin.putStr payload
    client.child.stdin.flush
  catch e =>
    let stderr ← client.stderrRef.get
    return .error s!"PYTHON_ORACLE_EOF: write failed ({e}); stderr={stderr.trimAscii.toString}"
  let mut reprLines : Array (UInt64 × String) := Array.mkEmpty batch.reprBits.size
  let mut errMsg? : Option String := none
  while true do
    let rawLine ← client.child.stdout.getLine
    if rawLine.isEmpty then
      let stderr ← client.stderrRef.get
      errMsg? := some s!"PYTHON_ORACLE_EOF: {stderr.trimAscii.toString}"
      break
    let line := rawLine.trimAscii.toString
    if line == "OK" then
      break
    else if line.startsWith "ERR:" then
      let detail := (line.drop 4).toString
      if errMsg?.isNone then
        errMsg? := some s!"PYTHON_ORACLE_MISMATCH: {detail}"
      break
    else if line.startsWith "R " then
      match line.splitOn " " with
      | ["R", bitsHex, reprHex] =>
        match parseHexU64? bitsHex, hexToString reprHex with
        | some b, .ok s => reprLines := reprLines.push (b, s)
        | _, .error e =>
          if errMsg?.isNone then errMsg? := some e
        | none, _ =>
          if errMsg?.isNone then errMsg? := some s!"PYTHON_ORACLE_BAD_BITS_HEX: {bitsHex}"
      | _ =>
        if errMsg?.isNone then errMsg? := some s!"PYTHON_ORACLE_BAD_RESPONSE: {line}"
    else
      if errMsg?.isNone then errMsg? := some s!"PYTHON_ORACLE_UNEXPECTED_LINE: {line}"
  if let some err := errMsg? then
    return .error err
  if reprLines.size != batch.reprBits.size then
    return .error s!"PYTHON_ORACLE_LINE_COUNT_MISMATCH: expected {batch.reprBits.size}, got {reprLines.size}"
  for idx in [0 : reprLines.size] do
    let (bits, reprStr) := reprLines[idx]!
    let reqBits := batch.reprBits[idx]!
    if bits != reqBits then
      return .error s!"PYTHON_ORACLE_BITS_ECHO_MISMATCH idx={idx} echoed={u64ToHex16 bits} requested={u64ToHex16 reqBits}"
    match LeanSwe.NumParse.parseFloat reprStr with
    | .error err =>
      return .error s!"PYTHON_REPR_PARSE_FAILED bits={u64ToHex16 bits} repr='{reprStr}': {repr err}"
    | .ok parsed =>
      let expected := canonBits bits
      if parsed.toBits != expected then
        return .error s!"PYTHON_REPR_BITS_MISMATCH bits={u64ToHex16 bits} repr='{reprStr}' got={u64ToHex16 parsed.toBits} expected={u64ToHex16 expected}"
  return .ok ()

@[noinline]
private def closeChildStdin
    (child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }) :
    IO (IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }) := do
  let (h, c) ← child.takeStdin
  let _ := h
  return c

/-- Cleanly shut down the persistent Python 3 co-process and verify exit status `0`. -/
def closePyOracleClient (client : PyOracleClient) : IO Unit := do
  let { child, stderrRef, stderrTask } := client
  try
    child.stdin.putStr "QUIT\n"
    child.stdin.flush
  catch _ =>
    pure ()
  let child ← closeChildStdin child
  let stdoutTask ← IO.asTask (drainPipeToDiscard child.stdout)
  let exitCode ← child.wait
  let _ ← IO.ofExcept stdoutTask.get
  let _ ← IO.ofExcept stderrTask.get
  let stderr ← stderrRef.get
  if exitCode != 0 then
    throw (IO.userError s!"PYTHON_ORACLE_EXIT_NONZERO exit={exitCode}: {stderr.trimAscii.toString}")

/-- Best-effort quiet cleanup of the Python 3 co-process on error paths so primary errors are preserved. -/
def closePyOracleClientQuiet (client : PyOracleClient) : IO Unit := do
  let { child, stderrRef := _, stderrTask } := client
  try
    child.stdin.putStr "QUIT\n"
    child.stdin.flush
  catch _ =>
    pure ()
  try
    let child ← closeChildStdin child
    let stdoutTask ← IO.asTask (drainPipeToDiscard child.stdout)
    IO.sleep 10
    if (← child.tryWait).isNone then
      try child.kill catch _ => pure ()
    let _ ← child.wait
    let _ ← IO.ofExcept stdoutTask.get
    let _ ← IO.ofExcept stderrTask.get
  catch _ =>
    pure ()

end Fuzz.Float
