import Fuzz.Common.Coverage
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
import Fuzz.Float.Oracle
import Fuzz.Float.Gen
import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.Toml.Interface
import Lean.Data.Json.Basic

/-!
4-way differential fuzzer suite `Fuzz.Float.suite` verifying Lean runtime `Float` and
`LeanSwe.NumParse` / `LeanSwe.Toml` against pure `Float.Model`, C99 `strtod_l`/`snprintf`/`libm`,
and an unclamped persistent Python 3 `float`/`repr`/`tomllib` co-process.
-/

namespace Fuzz.Float

open Fuzz.Common

private def hex64 (u : UInt64) : String := Id.run do
  let mut out := "0x"
  for idx in List.range 16 do
    let shift := (15 - idx) * 4
    let nib := ((u >>> UInt64.ofNat shift) &&& 0xf).toNat
    let c := if nib < 10 then Char.ofNat ('0'.toNat + nib) else Char.ofNat ('a'.toNat + nib - 10)
    out := out.push c
  return out

private def hex32 (u : UInt32) : String := Id.run do
  let mut out := "0x"
  for idx in List.range 8 do
    let shift := (7 - idx) * 4
    let nib := ((u >>> UInt32.ofNat shift) &&& 0xf).toNat
    let c := if nib < 10 then Char.ofNat ('0'.toNat + nib) else Char.ofNat ('a'.toNat + nib - 10)
    out := out.push c
  return out

private def errorKindBucket : LeanSwe.NumParse.NumParseErrorKind → String
  | .emptyInput => "err.emptyInput"
  | .invalidSyntax => "err.invalidSyntax"
  | .invalidSignForBase => "err.invalidSignForBase"
  | .leadingZero => "err.leadingZero"
  | .invalidUnderscore => "err.invalidUnderscore"
  | .overflow => "err.overflow"
  | .trailingChars => "err.trailingChars"

private def isSpecialLiteral (sClean : String) : Bool :=
  sClean == "inf" || sClean == "+inf" || sClean == "-inf" ||
    sClean == "nan" || sClean == "+nan" || sClean == "-nan"

private def hasNonZeroMantissaDigit (sClean : String) : Bool := Id.run do
  for c in sClean.toList do
    if c == 'e' || c == 'E' then
      return false
    if '1' ≤ c && c ≤ '9' then
      return true
  return false

private def isMidpointLike (sClean : String) : Bool := Id.run do
  let mut sigDigits := 0
  let mut started := false
  for c in sClean.toList do
    if c == 'e' || c == 'E' then
      break
    if '1' ≤ c && c ≤ '9' then
      started := true
      sigDigits := sigDigits + 1
    else if c == '0' && started then
      sigDigits := sigDigits + 1
  return sigDigits >= 17

private def checkParseStr (s : String) : Except String (List CoverageBucket × Option PyParseItem) := do
  let resImpl := LeanSwe.NumParse.parseFloat s
  let resModel := LeanSwe.NumParse.Model.parseFloatModel s
  let mut bkts : List CoverageBucket := []
  let tomlEligible := isTomlCheckEligible s
  let mut expOk := false
  let mut expBits : UInt64 := 0
  match resImpl, resModel with
  | .ok actual, .ok expected =>
    expOk := true
    expBits := actual.toBits
    if actual.toBits != expected.toBits then
      throw s!"PARSE_BITS_MISMATCH s={repr s} impl={hex64 actual.toBits} model={hex64 expected.toBits}"
    if actual.isNaN != expected.isNaN then
      throw s!"PARSE_ISNAN_MISMATCH s={repr s} impl={actual.isNaN} model={expected.isNaN}"
    let sClean := stripUnderscores s
    if sClean.contains '\x00' then
      throw s!"PARSE_ACCEPTED_NUL s={repr s}"
    if hasLeadingAsciiSpace sClean then
      throw s!"PARSE_ACCEPTED_LEADING_SPACE s={repr s}"
    if sClean == "inf" || sClean == "+inf" then
      if actual.toBits != 0x7ff0000000000000 then
        throw s!"PARSE_POS_INF_BITS s={repr s} got={hex64 actual.toBits}"
      bkts := bucket "parseFloat" "ok.pos_inf" :: bkts
    else if sClean == "-inf" then
      if actual.toBits != 0xfff0000000000000 then
        throw s!"PARSE_NEG_INF_BITS s={repr s} got={hex64 actual.toBits}"
      bkts := bucket "parseFloat" "ok.neg_inf" :: bkts
    else if sClean == "nan" || sClean == "+nan" || sClean == "-nan" then
      if !actual.isNaN || actual.toBits != 0x7ff8000000000000 then
        throw s!"PARSE_NAN_BITS s={repr s} got={hex64 actual.toBits}"
      bkts := bucket "parseFloat" "ok.nan" :: bkts
    else
      let (consumed, rawCBits) := cStrtod sClean
      if consumed.toNat != sClean.utf8ByteSize then
        throw s!"C_STRTOD_SHORT_CONSUME s={repr sClean} consumed={consumed.toNat} bytes={sClean.utf8ByteSize}"
      let cCanon := canonBits rawCBits
      if actual.toBits != cCanon then
        throw s!"C_STRTOD_BITS_MISMATCH s={repr sClean} lean={hex64 actual.toBits} c={hex64 cCanon}"
      let bits := actual.toBits
      if bits == 0x0000000000000000 then
        bkts := bucket "parseFloat" "ok.pos_zero" :: bkts
        if hasNonZeroMantissaDigit sClean then
          bkts := bucket "parseFloat" "ok.underflow_zero" :: bkts
      else if bits == 0x8000000000000000 then
        bkts := bucket "parseFloat" "ok.neg_zero" :: bkts
        if hasNonZeroMantissaDigit sClean then
          bkts := bucket "parseFloat" "ok.underflow_zero" :: bkts
      else if bits == 0x7ff0000000000000 || bits == 0xfff0000000000000 then
        bkts := bucket "parseFloat" "ok.overflow_inf" :: bkts
      else if isSubnormalBits bits then
        bkts := bucket "parseFloat" "ok.subnormal" :: bkts
      else
        bkts := bucket "parseFloat" "ok.normal" :: bkts
    if s.contains '_' then
      bkts := bucket "parseFloat" "ok.underscore" :: bkts
    if !isSpecialLiteral sClean && isMidpointLike sClean then
      bkts := bucket "parseFloat" "ok.midpoint" :: bkts
    if tomlEligible then
      match LeanSwe.Toml.parse ("x = " ++ s) with
      | .error err =>
        throw s!"TOML_REJECTED_VALID_FLOAT s={repr s} err={repr err}"
      | .ok tbl =>
        match LeanSwe.Toml.getField (α := Float) tbl "x" with
        | .error err =>
          throw s!"TOML_DECODE_FLOAT_ERR s={repr s} err={repr err}"
        | .ok gotF =>
          if gotF.toBits != actual.toBits then
            throw s!"TOML_PARSE_BITS_MISMATCH s={repr s} toml={hex64 gotF.toBits} num={hex64 actual.toBits}"
          bkts := bucket "toml_parse" "ok.matched_float" :: bkts
  | .error e, .error expectedKind =>
    if e.kind != expectedKind then
      throw s!"PARSE_ERR_KIND_MISMATCH s={repr s} impl={repr e.kind} model={repr expectedKind}"
    if e.message.isEmpty then
      throw s!"PARSE_ERR_EMPTY_MSG s={repr s}"
    if !s.contains '_' && !s.contains '\x00' && !hasLeadingAsciiSpace s && !s.isEmpty then
      let (consumed, _) := cStrtod s
      if consumed.toNat == s.utf8ByteSize then
        if !isAllowedStrtodOnlySyntax s then
          throw s!"STRTOD_ACCEPTED_TOML_REJECTED s={repr s} err={repr e.kind}"
    if tomlEligible then
      if let .ok tbl := LeanSwe.Toml.parse ("x = " ++ s) then
        if let .ok gotF := LeanSwe.Toml.getField (α := Float) tbl "x" then
          throw s!"TOML_ACCEPTED_INVALID_FLOAT s={repr s} got={hex64 gotF.toBits}"
      bkts := bucket "toml_parse" "ok.rejected_nonfloat" :: bkts
    bkts := bucket "parseFloat" (errorKindBucket e.kind) :: bkts
  | .ok actual, .error expectedKind =>
    throw s!"PARSE_IMPL_OK_MODEL_ERR s={repr s} impl={hex64 actual.toBits} model={repr expectedKind}"
  | .error e, .ok expected =>
    throw s!"PARSE_IMPL_ERR_MODEL_OK s={repr s} impl={repr e.kind} model={hex64 expected.toBits}"
  let pyItem : PyParseItem := {
    rawInput := s
    cleanStr := stripUnderscores s
    expectedOk := expOk
    expectedBits := expBits
    tomlCheck := tomlEligible
  }
  return (bkts, some pyItem)

private def checkBitsCase (u : UInt64) : Except String (List CoverageBucket × PyFormatItem) := do
  let m := Float.Model.ofBits u
  let f := Float.ofBits u
  let fRaw := rawDoubleFromBits u
  let expBits := canonBits u
  if m.toBits != expBits then
    throw s!"MODEL_CANON_BITS_MISMATCH u={hex64 u} model={hex64 m.toBits} expected={hex64 expBits}"
  if f.toBits != expBits then
    throw s!"FLOAT_CANON_BITS_MISMATCH u={hex64 u} float={hex64 f.toBits} expected={hex64 expBits}"
  if fRaw.toBits != expBits then
    throw s!"RAW_DOUBLE_CANON_BITS_MISMATCH u={hex64 u} raw={hex64 fRaw.toBits} expected={hex64 expBits}"
  if f.isNaN != m.isNaN || f.isFinite != m.isFinite || f.isInf != m.isInf then
    throw s!"FLOAT_CLASS_MISMATCH u={hex64 u}"
  if fRaw.isNaN != m.isNaN || fRaw.isFinite != m.isFinite || fRaw.isInf != m.isInf then
    throw s!"RAW_FLOAT_CLASS_MISMATCH u={hex64 u}"
  let cmpMask := cCmp u 0
  let cIsNaN := (cmpMask &&& 8) != 0
  let cIsFin := (cmpMask &&& 16) != 0
  let cIsInf := (cmpMask &&& 32) != 0
  if cIsNaN != m.isNaN || cIsFin != m.isFinite || cIsInf != m.isInf then
    throw s!"C_CLASS_MISMATCH u={hex64 u}"
  let mut bkts : List CoverageBucket := []
  if !isRawNaNBits u then
    bkts := bucket "bits_abi" "ok.finite_or_inf" :: bkts
  else if u == 0x7ff8000000000000 then
    bkts := bucket "bits_abi" "ok.canonical_qnan" :: bkts
  else if isSignalingNaNBits u then
    bkts := bucket "bits_abi" "ok.snan_raw_ffi" :: bkts
  else
    bkts := bucket "bits_abi" "ok.noncanonical_qnan" :: bkts
  let s := LeanSwe.NumParse.formatFloat f
  let sRaw := LeanSwe.NumParse.formatFloat fRaw
  if s != sRaw then
    throw s!"FORMAT_RAW_MISMATCH u={hex64 u} s={repr s} sRaw={repr sRaw}"
  if m.isNaN then
    if s != "nan" then
      throw s!"FORMAT_NAN_CONTRACT u={hex64 u} s={repr s}"
    bkts := bucket "formatFloat" "ok.nan" :: bkts
  else if m.toBits == 0x7ff0000000000000 then
    if s != "inf" then
      throw s!"FORMAT_POS_INF_CONTRACT u={hex64 u} s={repr s}"
    bkts := bucket "formatFloat" "ok.pos_inf" :: bkts
  else if m.toBits == 0xfff0000000000000 then
    if s != "-inf" then
      throw s!"FORMAT_NEG_INF_CONTRACT u={hex64 u} s={repr s}"
    bkts := bucket "formatFloat" "ok.neg_inf" :: bkts
  else
    if s.contains '_' then
      throw s!"FORMAT_CONTAINS_UNDERSCORE u={hex64 u} s={repr s}"
    if !(s.contains '.' || s.contains 'e' || s.contains 'E') then
      throw s!"FORMAT_MISSING_FLOAT_MARKER u={hex64 u} s={repr s}"
    if s.length > 26 then
      throw s!"FORMAT_TOO_LONG u={hex64 u} len={s.length} s={repr s}"
    match LeanSwe.NumParse.parseFloat s with
    | .error err =>
      throw s!"FORMAT_ROUNDTRIP_PARSE_ERR u={hex64 u} s={repr s} err={repr err}"
    | .ok y =>
      if y.toBits != m.toBits then
        throw s!"FORMAT_ROUNDTRIP_BITS u={hex64 u} s={repr s} got={hex64 y.toBits} expected={hex64 m.toBits}"
    let (cConsumed, cRawBits) := cStrtod s
    if cConsumed.toNat != s.utf8ByteSize then
      throw s!"FORMAT_C_STRTOD_SHORT u={hex64 u} s={repr s} consumed={cConsumed.toNat}"
    if canonBits cRawBits != m.toBits then
      throw s!"FORMAT_C_STRTOD_BITS u={hex64 u} s={repr s} c={hex64 cRawBits} expected={hex64 m.toBits}"
    if m.toBits == 0x0000000000000000 then
      bkts := bucket "formatFloat" "ok.pos_zero" :: bkts
    else if m.toBits == 0x8000000000000000 then
      bkts := bucket "formatFloat" "ok.neg_zero" :: bkts
    else if isSubnormalBits m.toBits then
      bkts := bucket "formatFloat" "ok.subnormal" :: bkts
    else if s.contains 'e' || s.contains 'E' then
      bkts := bucket "formatFloat" "ok.normal_scientific" :: bkts
    else
      bkts := bucket "formatFloat" "ok.normal_decimal" :: bkts
  let cStr := cSnprintf17g m.toBits
  let normCStr := normalizeCFormattedForToml cStr
  match LeanSwe.NumParse.parseFloat normCStr with
  | .error err =>
    throw s!"SNPRINTF_ROUNDTRIP_ERR u={hex64 u} cStr={repr cStr} norm={repr normCStr} err={repr err}"
  | .ok z =>
    if z.toBits != m.toBits then
      throw s!"SNPRINTF_ROUNDTRIP_BITS u={hex64 u} norm={repr normCStr} got={hex64 z.toBits} expected={hex64 m.toBits}"
  let doc : LeanSwe.Toml.TomlTable := #[("v", LeanSwe.Toml.TomlValue.float f)]
  let tomlText := LeanSwe.Toml.format doc
  match LeanSwe.Toml.parse tomlText with
  | .error err =>
    throw s!"TOML_PARSE_ERR u={hex64 u} text={repr tomlText} err={repr err}"
  | .ok tbl =>
    match LeanSwe.Toml.getField (α := Float) tbl "v" with
    | .error err =>
      throw s!"TOML_DECODE_ERR u={hex64 u} text={repr tomlText} err={repr err}"
    | .ok decoded =>
      if decoded.toBits != m.toBits then
        throw s!"TOML_BITS_MISMATCH u={hex64 u} text={repr tomlText} got={hex64 decoded.toBits} expected={hex64 m.toBits}"
  bkts := bucket "toml_roundtrip" "ok.float_bits" :: bkts
  return (bkts, { bits := m.toBits, formatted := s })

private def checkSame4 (tag : String) (a b c d : UInt64) : Except String Unit := do
  if a != b || a != c || a != d then
    throw s!"{tag}: runtime={hex64 a} raw={hex64 b} model={hex64 c} c={hex64 d}"

private def checkBinOpCase (ua ub : UInt64) : Except String (List CoverageBucket) := do
  let fa := Float.ofBits ua
  let fb := Float.ofBits ub
  let faRaw := rawDoubleFromBits ua
  let fbRaw := rawDoubleFromBits ub
  let ma := Float.Model.ofBits ua
  let mb := Float.Model.ofBits ub
  checkSame4 s!"ADD({hex64 ua},{hex64 ub})" (fa + fb).toBits (faRaw + fbRaw).toBits (ma + mb).toBits (canonBits (cBinOp 0 ua ub))
  checkSame4 s!"SUB({hex64 ua},{hex64 ub})" (fa - fb).toBits (faRaw - fbRaw).toBits (ma - mb).toBits (canonBits (cBinOp 1 ua ub))
  checkSame4 s!"MUL({hex64 ua},{hex64 ub})" (fa * fb).toBits (faRaw * fbRaw).toBits (ma * mb).toBits (canonBits (cBinOp 2 ua ub))
  checkSame4 s!"DIV({hex64 ua},{hex64 ub})" (fa / fb).toBits (faRaw / fbRaw).toBits (ma / mb).toBits (canonBits (cBinOp 3 ua ub))
  checkSame4 s!"MIN({hex64 ua},{hex64 ub})"
    (Float.minimum fa fb).toBits (Float.minimum faRaw fbRaw).toBits (ma.minimum mb).toBits (canonBits (cMinMax false ua ub))
  checkSame4 s!"MIN_NUM({hex64 ua},{hex64 ub})"
    (Float.minimumNumber fa fb).toBits (Float.minimumNumber faRaw fbRaw).toBits (ma.minimumNumber mb).toBits (canonBits (cMinMaxNum false ua ub))
  checkSame4 s!"MAX({hex64 ua},{hex64 ub})"
    (Float.maximum fa fb).toBits (Float.maximum faRaw fbRaw).toBits (ma.maximum mb).toBits (canonBits (cMinMax true ua ub))
  checkSame4 s!"MAX_NUM({hex64 ua},{hex64 ub})"
    (Float.maximumNumber fa fb).toBits (Float.maximumNumber faRaw fbRaw).toBits (ma.maximumNumber mb).toBits (canonBits (cMinMaxNum true ua ub))
  let mask := cCmp ua ub
  let cBeq := (mask &&& 1) != 0
  let cLt := (mask &&& 2) != 0
  let cLe := (mask &&& 4) != 0
  if (fa == fb) != (ma == mb) || (faRaw == fbRaw) != (ma == mb) || cBeq != (ma == mb) then
    throw s!"BEQ_MISMATCH({hex64 ua},{hex64 ub})"
  if (fa < fb) != (ma < mb) || (faRaw < fbRaw) != (ma < mb) || cLt != (ma < mb) then
    throw s!"LT_MISMATCH({hex64 ua},{hex64 ub})"
  if (fa <= fb) != (ma <= mb) || (faRaw <= fbRaw) != (ma <= mb) || cLe != (ma <= mb) then
    throw s!"LE_MISMATCH({hex64 ua},{hex64 ub})"
  if decide (fa = fb) != decide (ma = mb) || decide (faRaw = fbRaw) != decide (ma = mb) then
    throw s!"DEC_EQ_MISMATCH({hex64 ua},{hex64 ub})"
  let mut bkts : List CoverageBucket := []
  let sumBits := (ma + mb).toBits
  if ma.isFinite && mb.isFinite && (ma + mb).isFinite then
    bkts := bucket "arith" "add.finite" :: bkts
  if isSubnormalBits sumBits then
    bkts := bucket "arith" "add.subnormal" :: bkts
  if !ma.isFinite || !mb.isFinite || !(ma + mb).isFinite then
    bkts := bucket "arith" "add.special" :: bkts
  if ma.isFinite && mb.isFinite && (ma == mb) && (ma - mb) == Float.Model.ofBits 0 then
    bkts := bucket "arith" "sub.cancel_zero" :: bkts
  if ma.isFinite && mb.isFinite && (ma * mb).isInf then
    bkts := bucket "arith" "mul.overflow" :: bkts
  if ma.isFinite && mb.isFinite && !(ma == Float.Model.ofBits 0) && !(mb == Float.Model.ofBits 0) && (ma * mb) == Float.Model.ofBits 0 then
    bkts := bucket "arith" "mul.underflow" :: bkts
  if ma.isFinite && mb == Float.Model.ofBits 0 then
    bkts := bucket "arith" "div.by_zero" :: bkts
  if ma.isFinite && mb.isFinite && !(mb == Float.Model.ofBits 0) && (ma / mb).isFinite then
    bkts := bucket "arith" "div.inexact" :: bkts
  if ma == Float.Model.ofBits 0 && mb == Float.Model.ofBits 0 then
    bkts := bucket "minmax_cmp" "minmax.signed_zero" :: bkts
  if ma.isNaN || mb.isNaN then
    bkts := bucket "minmax_cmp" "minmax.nan_prop" :: bkts
    bkts := bucket "minmax_cmp" "cmp.unordered_nan" :: bkts
  else
    bkts := bucket "minmax_cmp" "cmp.ordered" :: bkts
  if (ma.isNaN && !mb.isNaN) || (!ma.isNaN && mb.isNaN) then
    bkts := bucket "minmax_cmp" "minmax.number_ignore_nan" :: bkts
  return bkts

private def checkFmaCase (ua ub uc : UInt64) : Except String (List CoverageBucket) := do
  let fa := Float.ofBits ua
  let fb := Float.ofBits ub
  let fc := Float.ofBits uc
  let faRaw := rawDoubleFromBits ua
  let fbRaw := rawDoubleFromBits ub
  let fcRaw := rawDoubleFromBits uc
  let ma := Float.Model.ofBits ua
  let mb := Float.Model.ofBits ub
  let mc := Float.Model.ofBits uc
  let mf := Float.Model.fma ma mb mc
  checkSame4 s!"FMA({hex64 ua},{hex64 ub},{hex64 uc})"
    (Float.fma fa fb fc).toBits (Float.fma faRaw fbRaw fcRaw).toBits mf.toBits (canonBits (cFma ua ub uc))
  let mut bkts : List CoverageBucket := []
  if ma.isFinite && mb.isFinite && mc.isFinite && mf.isFinite then
    bkts := bucket "arith" "fma.single_round" :: bkts
  if ma.isFinite && mb.isFinite && mc.isFinite && mf == Float.Model.ofBits 0 then
    bkts := bucket "arith" "fma.underflow_sign" :: bkts
  return bkts

private def checkIntConvCase (u : UInt64) : Except String (List CoverageBucket × Array PyIntFloatItem) := do
  let f := Float.ofBits u
  let fRaw := rawDoubleFromBits u
  let m := Float.Model.ofBits u
  checkSame4 s!"NEG({hex64 u})" (-f).toBits (-fRaw).toBits (-m).toBits (canonBits (cUnOp 0 u))
  checkSame4 s!"ABS({hex64 u})" f.abs.toBits fRaw.abs.toBits m.abs.toBits (canonBits (cUnOp 1 u))
  checkSame4 s!"SQRT({hex64 u})" f.sqrt.toBits fRaw.sqrt.toBits m.sqrt.toBits (canonBits (cUnOp 2 u))
  let cU8 := (cToUInt64 u 255).toUInt8
  let cU16 := (cToUInt64 u 65535).toUInt16
  let cU32 := (cToUInt64 u 0xffffffff).toUInt32
  let cU64 := cToUInt64 u 0xffffffffffffffff
  let cUSz := USize.ofNat (cToUInt64 u (UInt64.ofNat (USize.size - 1))).toNat
  if f.toUInt8 != m.toUInt8 || fRaw.toUInt8 != m.toUInt8 || cU8 != m.toUInt8 then
    throw s!"TO_UINT8_MISMATCH u={hex64 u}"
  if f.toUInt16 != m.toUInt16 || fRaw.toUInt16 != m.toUInt16 || cU16 != m.toUInt16 then
    throw s!"TO_UINT16_MISMATCH u={hex64 u}"
  if f.toUInt32 != m.toUInt32 || fRaw.toUInt32 != m.toUInt32 || cU32 != m.toUInt32 then
    throw s!"TO_UINT32_MISMATCH u={hex64 u}"
  if f.toUInt64 != m.toUInt64 || fRaw.toUInt64 != m.toUInt64 || cU64 != m.toUInt64 then
    throw s!"TO_UINT64_MISMATCH u={hex64 u}"
  if f.toUSize != m.toUSize || fRaw.toUSize != m.toUSize || cUSz != m.toUSize then
    throw s!"TO_USIZE_MISMATCH u={hex64 u}"
  let cI8 := (cToInt64 u (Int64.ofInt (-128)) (Int64.ofInt 127)).toInt8
  let cI16 := (cToInt64 u (Int64.ofInt (-32768)) (Int64.ofInt 32767)).toInt16
  let cI32 := (cToInt64 u (Int64.ofInt (-2147483648)) (Int64.ofInt 2147483647)).toInt32
  let cI64 := cToInt64 u Int64.minValue Int64.maxValue
  let iszMin := Int64.ofInt (-Int.ofNat (USize.size / 2))
  let iszMax := Int64.ofInt (Int.ofNat (USize.size / 2 - 1))
  let cISz := (cToInt64 u iszMin iszMax).toISize
  if f.toInt8 != m.toInt8 || fRaw.toInt8 != m.toInt8 || cI8 != m.toInt8 then
    throw s!"TO_INT8_MISMATCH u={hex64 u}"
  if f.toInt16 != m.toInt16 || fRaw.toInt16 != m.toInt16 || cI16 != m.toInt16 then
    throw s!"TO_INT16_MISMATCH u={hex64 u}"
  if f.toInt32 != m.toInt32 || fRaw.toInt32 != m.toInt32 || cI32 != m.toInt32 then
    throw s!"TO_INT32_MISMATCH u={hex64 u}"
  if f.toInt64 != m.toInt64 || fRaw.toInt64 != m.toInt64 || cI64 != m.toInt64 then
    throw s!"TO_INT64_MISMATCH u={hex64 u}"
  if f.toISize != m.toISize || fRaw.toISize != m.toISize || cISz != m.toISize then
    throw s!"TO_ISIZE_MISMATCH u={hex64 u}"
  let u8 := u.toUInt8
  let u16 := u.toUInt16
  let u32 := u.toUInt32
  let usz := u.toUSize
  if u8.toFloat.toBits != (Float.Model.ofUInt8 u8).toBits || u8.toFloat.toBits != cOfUInt64 u8.toUInt64 then
    throw s!"OF_UINT8_MISMATCH u={hex64 u}"
  if u16.toFloat.toBits != (Float.Model.ofUInt16 u16).toBits || u16.toFloat.toBits != cOfUInt64 u16.toUInt64 then
    throw s!"OF_UINT16_MISMATCH u={hex64 u}"
  if u32.toFloat.toBits != (Float.Model.ofUInt32 u32).toBits || u32.toFloat.toBits != cOfUInt64 u32.toUInt64 then
    throw s!"OF_UINT32_MISMATCH u={hex64 u}"
  if u.toFloat.toBits != (Float.Model.ofUInt64 u).toBits || u.toFloat.toBits != cOfUInt64 u then
    throw s!"OF_UINT64_MISMATCH u={hex64 u}"
  if usz.toFloat.toBits != (Float.Model.ofUSize usz).toBits || usz.toFloat.toBits != cOfUInt64 usz.toUInt64 then
    throw s!"OF_USIZE_MISMATCH u={hex64 u}"
  let i8 := u8.toInt8
  let i16 := u16.toInt16
  let i32 := u32.toInt32
  let i64 := u.toInt64
  let isz := usz.toISize
  if i8.toFloat.toBits != (Float.Model.ofInt8 i8).toBits || i8.toFloat.toBits != cOfInt64 i8.toInt64 then
    throw s!"OF_INT8_MISMATCH u={hex64 u}"
  if i16.toFloat.toBits != (Float.Model.ofInt16 i16).toBits || i16.toFloat.toBits != cOfInt64 i16.toInt64 then
    throw s!"OF_INT16_MISMATCH u={hex64 u}"
  if i32.toFloat.toBits != (Float.Model.ofInt32 i32).toBits || i32.toFloat.toBits != cOfInt64 i32.toInt64 then
    throw s!"OF_INT32_MISMATCH u={hex64 u}"
  if i64.toFloat.toBits != (Float.Model.ofInt64 i64).toBits || i64.toFloat.toBits != cOfInt64 i64 then
    throw s!"OF_INT64_MISMATCH u={hex64 u}"
  if isz.toFloat.toBits != (Float.Model.ofISize isz).toBits || isz.toFloat.toBits != cOfInt64 isz.toInt64 then
    throw s!"OF_ISIZE_MISMATCH u={hex64 u}"
  let smallNat := (u &&& (((1 : UInt64) <<< 53) - 1)).toNat
  let smallNatF := Nat.toFloat smallNat
  if smallNatF.toBits != (Float.Model.ofNat smallNat).toBits || smallNatF.toBits != cOfUInt64 (UInt64.ofNat smallNat) then
    throw s!"OF_SMALL_NAT_MISMATCH smallNat={smallNat}"
  let smallInt := if (u >>> 63) == 1 then -Int.ofNat smallNat else Int.ofNat smallNat
  let smallIntF := Int.toFloat smallInt
  if smallIntF.toBits != (Float.Model.ofInt smallInt).toBits then
    throw s!"OF_SMALL_INT_MISMATCH smallInt={smallInt}"
  let bigShift := (u % 1025).toNat
  let tieBit := if (u >>> 62) &&& 1 == 1 && bigShift >= 54 then (1 <<< (bigShift - 54)) else 0
  let bigNat := ((1 <<< 53) + (u &&& 0x1fff).toNat) + (if bigShift > 53 then (1 <<< bigShift) else 0) + tieBit
  let bigNatF := Nat.toFloat bigNat
  if bigNatF.toBits != (Float.Model.ofNat bigNat).toBits then
    throw s!"OF_NAT_MISMATCH bigNat={bigNat}"
  let bigInt := if (u >>> 63) == 1 then -Int.ofNat bigNat else Int.ofNat bigNat
  let bigIntF := Int.toFloat bigInt
  if bigIntF.toBits != (Float.Model.ofInt bigInt).toBits then
    throw s!"OF_INT_MISMATCH bigInt={bigInt}"
  let pyInts : Array PyIntFloatItem := #[
    { decStr := toString smallNat, expectedBits := smallNatF.toBits },
    { decStr := toString smallInt, expectedBits := smallIntF.toBits },
    { decStr := toString bigNat, expectedBits := bigNatF.toBits },
    { decStr := toString bigInt, expectedBits := bigIntF.toBits }
  ]
  let mut bkts : List CoverageBucket := [bucket "int_conv" "from_int.exact_and_round"]
  let zero := Float.Model.ofBits 0
  if m.isFinite && !(m < zero) then
    bkts := bucket "arith" "sqrt.finite" :: bkts
  if m < zero then
    bkts := bucket "arith" "sqrt.neg_nan" :: bkts
  if m.isFinite && !(m < zero) && m < Float.Model.ofNat 256 then
    bkts := bucket "int_conv" "to_uint.in_range" :: bkts
  if m.isNaN || m < zero || !(m < Float.Model.ofNat (1 <<< 64)) then
    bkts := bucket "int_conv" "to_uint.clamped" :: bkts
  if m.isFinite && !(m < Float.Model.ofInt (-128)) && m < Float.Model.ofInt 128 then
    bkts := bucket "int_conv" "to_int.in_range" :: bkts
  if m.isNaN || m < Float.Model.ofInt (-(1 <<< 63)) || !(m < Float.Model.ofInt (1 <<< 63)) then
    bkts := bucket "int_conv" "to_int.clamped" :: bkts
  return (bkts, pyInts)

private def checkSciCase (m : Nat) (negExp : Bool) (e : Nat) : Except String (List CoverageBucket × PyParseItem) := do
  let f : Float := OfScientific.ofScientific m negExp e
  let modelExp : Int := if negExp then -Int.ofNat e else Int.ofNat e
  let modF := Float.Model.ofScientific m modelExp
  if f.toBits != modF.toBits then
    throw s!"OF_SCIENTIFIC_MODEL_MISMATCH m={m} neg={negExp} e={e} rt={hex64 f.toBits} model={hex64 modF.toBits}"
  let sciStr := s!"{m}e{if negExp then "-" else ""}{e}"
  let (consumed, cRaw) := cStrtod sciStr
  if consumed.toNat != sciStr.utf8ByteSize then
    throw s!"OF_SCIENTIFIC_C_STRTOD_SHORT s={sciStr}"
  if f.toBits != canonBits cRaw then
    throw s!"OF_SCIENTIFIC_C_MISMATCH s={sciStr} rt={hex64 f.toBits} c={hex64 (canonBits cRaw)}"
  if negExp then
    let jn : Lean.JsonNumber := ⟨Int.ofNat m, e⟩
    if jn.toFloat.toBits != modF.toBits then
      throw s!"JSON_NUM_TO_FLOAT_MISMATCH m={m} e={e} got={hex64 jn.toFloat.toBits} exp={hex64 modF.toBits}"
    if m > 0 then
      let jnNeg : Lean.JsonNumber := ⟨-Int.ofNat m, e⟩
      let negExpBits := (-modF).toBits
      if jnNeg.toFloat.toBits != negExpBits then
        throw s!"JSON_NUM_NEG_TO_FLOAT_MISMATCH m={m} e={e} got={hex64 jnNeg.toFloat.toBits} exp={hex64 negExpBits}"
  let pyItem : PyParseItem := {
    rawInput := sciStr
    cleanStr := sciStr
    expectedOk := true
    expectedBits := f.toBits
    tomlCheck := true
  }
  let bkt :=
    if m < (1 <<< 53) && e <= 22 then
      if negExp then bucket "ofScientific" "ok.fast_div"
      else bucket "ofScientific" "ok.fast_mul"
    else
      bucket "ofScientific" "ok.model_slow"
  return ([bkt], pyItem)

/--
Verify deterministic `Float` runtime externs (`frExp`, `scaleB` on `Int32`, `ceil`, `floor`,
`round`, `Float.toFloat32` / `Float32.toFloat`, and `FloatArray` unboxing/boxing).

Note: `Float.scaleB` is bounded to `Int32` (`[-2147483648, 2147483647]`) because upstream
Lean `v4.36.0-rc2` `lean_float_scaleb` in `libleanrt` corrupts `-0.0`, `±Inf`, and `NaN` to
`+0.0` for non-scalar `Int` exponents (`|i| > 2^31 - 1`).
-/
private def checkExternCase (u : UInt64) (u32 : UInt32) (scaleExp : Int32) :
    Except String (List CoverageBucket) := do
  let f := Float.ofBits u
  let fRaw := rawDoubleFromBits u
  let m := Float.Model.ofBits u
  let expBits := canonBits u
  checkSame4 s!"CEIL({hex64 u})" f.ceil.toBits fRaw.ceil.toBits (canonBits (cUnOp 3 u)) (canonBits (cUnOp 3 expBits))
  checkSame4 s!"FLOOR({hex64 u})" f.floor.toBits fRaw.floor.toBits (canonBits (cUnOp 4 u)) (canonBits (cUnOp 4 expBits))
  checkSame4 s!"ROUND({hex64 u})" f.round.toBits fRaw.round.toBits (canonBits (cUnOp 5 u)) (canonBits (cUnOp 5 expBits))
  let scaleInt := scaleExp.toInt
  let cScaled := canonBits (cLdexp u scaleExp)
  let fScaled := Float.scaleB f scaleInt
  let fRawScaled := Float.scaleB fRaw scaleInt
  if fScaled.toBits != cScaled || fRawScaled.toBits != cScaled then
    throw s!"SCALEB_MISMATCH u={hex64 u} exp={scaleInt} rt={hex64 fScaled.toBits} raw={hex64 fRawScaled.toBits} c={hex64 cScaled}"
  let mut bkts : List CoverageBucket := [
    bucket "extern" "round.ceil_floor_round",
    bucket "extern" "scaleB.int32"
  ]
  if m.isFinite then
    let (sigF, expF) := f.frExp
    let (sigRaw, expRaw) := fRaw.frExp
    let (cSig, cExp) := cFrexp u
    if sigF.toBits != cSig || sigRaw.toBits != cSig || expF != cExp.toInt || expRaw != cExp.toInt then
      throw s!"FREXP_MISMATCH u={hex64 u} rt=({hex64 sigF.toBits},{expF}) raw=({hex64 sigRaw.toBits},{expRaw}) c=({hex64 cSig},{cExp.toInt})"
    bkts := bucket "extern" "frExp.finite" :: bkts
  let f32 := f.toFloat32
  let f32Raw := fRaw.toFloat32
  let cF32 := canonBits32 (cF64ToF32 u)
  if f32.toBits != cF32 || f32Raw.toBits != cF32 then
    throw s!"TO_FLOAT32_MISMATCH u={hex64 u} rt={hex32 f32.toBits} raw={hex32 f32Raw.toBits} c={hex32 cF32}"
  let f32In := Float32.ofBits u32
  let f32InRaw := rawFloat32FromBits u32
  if f32In.toBits != canonBits32 u32 || f32InRaw.toBits != canonBits32 u32 then
    throw s!"FLOAT32_BITS_MISMATCH u32={hex32 u32}"
  let backF64 := f32In.toFloat
  let backF64Raw := f32InRaw.toFloat
  let cBackF64 := canonBits (cF32ToF64 u32)
  if backF64.toBits != cBackF64 || backF64Raw.toBits != cBackF64 then
    throw s!"FLOAT32_TO_FLOAT_MISMATCH u32={hex32 u32} rt={hex64 backF64.toBits} raw={hex64 backF64Raw.toBits} c={hex64 cBackF64}"
  bkts := bucket "extern" "float32.cast" :: bkts
  if u32 == 0x7f800000 || u32 == 0xff800000 || (isRawNaNBits32 u32 && ((u32 &&& 0x00400000) == 0)) then
    bkts := bucket "extern" "float32.inf_snan" :: bkts
  let negF := -f
  let arr := ((FloatArray.emptyWithCapacity 3).push f).push fRaw |>.push negF
  if arr.size != 3 then
    throw s!"FLOAT_ARRAY_SIZE_MISMATCH size={arr.size}"
  if (arr.get! 0).toBits != expBits || (arr.get! 1).toBits != expBits || (arr.get! 2).toBits != (-m).toBits then
    throw s!"FLOAT_ARRAY_GET_MISMATCH u={hex64 u}"
  let arr2 := arr.set! 1 negF
  if (arr2.get! 1).toBits != (-m).toBits then
    throw s!"FLOAT_ARRAY_SET_MISMATCH u={hex64 u}"
  bkts := bucket "extern" "floatArray.box" :: bkts
  return bkts

private def checkCase (c : FloatFuzzCase) : Except String (List CoverageBucket × PyOracleBatch) := do
  match c with
  | .parseStr s =>
    let (bkts, pyItem?) ← checkParseStr s
    let parses := match pyItem? with | some it => #[it] | none => #[]
    return (bkts, { parses })
  | .checkBits u =>
    let (bkts, fmtItem) ← checkBitsCase u
    return (bkts, { formats := #[fmtItem], reprBits := #[u] })
  | .checkBinOp ua ub =>
    let bkts ← checkBinOpCase ua ub
    return (bkts, {})
  | .checkFma ua ub uc =>
    let bkts ← checkFmaCase ua ub uc
    return (bkts, {})
  | .checkIntConv u =>
    let (bkts, pyInts) ← checkIntConvCase u
    return (bkts, { intFloats := pyInts })
  | .checkSci m negExp e =>
    let (bkts, pyItem) ← checkSciCase m negExp e
    return (bkts, { parses := #[pyItem] })
  | .checkExtern u u32 scaleExp =>
    let bkts ← checkExternCase u u32 scaleExp
    return (bkts, {})

private def appendBatch (a b : PyOracleBatch) : PyOracleBatch :=
  { parses := a.parses ++ b.parses
    formats := a.formats ++ b.formats
    reprBits := a.reprBits ++ b.reprBits
    intFloats := a.intFloats ++ b.intFloats }

private def checkEpisodeWithPy (client : PyOracleClient) (trace : Array FloatFuzzCase) :
    IO (Except String (List CoverageBucket)) := do
  let mut bkts : List CoverageBucket := []
  let mut batch : PyOracleBatch := {}
  for c in trace do
    match checkCase c with
    | .error err => return .error err
    | .ok (bs, cBatch) =>
      bkts := bs ++ bkts
      batch := appendBatch batch cBatch
  match ← flushPyBatch client batch with
  | .error err => return .error err
  | .ok () => return .ok bkts

private def requiredBuckets : Array CoverageBucket := #[
  bucket "parseFloat" "ok.pos_zero",
  bucket "parseFloat" "ok.neg_zero",
  bucket "parseFloat" "ok.subnormal",
  bucket "parseFloat" "ok.normal",
  bucket "parseFloat" "ok.pos_inf",
  bucket "parseFloat" "ok.neg_inf",
  bucket "parseFloat" "ok.nan",
  bucket "parseFloat" "ok.overflow_inf",
  bucket "parseFloat" "ok.underflow_zero",
  bucket "parseFloat" "ok.midpoint",
  bucket "parseFloat" "ok.underscore",
  bucket "parseFloat" "err.emptyInput",
  bucket "parseFloat" "err.invalidSyntax",
  bucket "parseFloat" "err.leadingZero",
  bucket "parseFloat" "err.invalidUnderscore",
  bucket "parseFloat" "err.trailingChars",
  bucket "toml_parse" "ok.matched_float",
  bucket "toml_parse" "ok.rejected_nonfloat",
  bucket "formatFloat" "ok.pos_zero",
  bucket "formatFloat" "ok.neg_zero",
  bucket "formatFloat" "ok.subnormal",
  bucket "formatFloat" "ok.normal_decimal",
  bucket "formatFloat" "ok.normal_scientific",
  bucket "formatFloat" "ok.pos_inf",
  bucket "formatFloat" "ok.neg_inf",
  bucket "formatFloat" "ok.nan",
  bucket "bits_abi" "ok.finite_or_inf",
  bucket "bits_abi" "ok.canonical_qnan",
  bucket "bits_abi" "ok.noncanonical_qnan",
  bucket "bits_abi" "ok.snan_raw_ffi",
  bucket "ofScientific" "ok.fast_mul",
  bucket "ofScientific" "ok.fast_div",
  bucket "ofScientific" "ok.model_slow",
  bucket "arith" "add.finite",
  bucket "arith" "add.subnormal",
  bucket "arith" "add.special",
  bucket "arith" "sub.cancel_zero",
  bucket "arith" "mul.overflow",
  bucket "arith" "mul.underflow",
  bucket "arith" "div.by_zero",
  bucket "arith" "div.inexact",
  bucket "arith" "fma.single_round",
  bucket "arith" "fma.underflow_sign",
  bucket "arith" "sqrt.finite",
  bucket "arith" "sqrt.neg_nan",
  bucket "minmax_cmp" "minmax.signed_zero",
  bucket "minmax_cmp" "minmax.nan_prop",
  bucket "minmax_cmp" "minmax.number_ignore_nan",
  bucket "minmax_cmp" "cmp.ordered",
  bucket "minmax_cmp" "cmp.unordered_nan",
  bucket "int_conv" "to_uint.in_range",
  bucket "int_conv" "to_uint.clamped",
  bucket "int_conv" "to_int.in_range",
  bucket "int_conv" "to_int.clamped",
  bucket "int_conv" "from_int.exact_and_round",
  bucket "extern" "frExp.finite",
  bucket "extern" "scaleB.int32",
  bucket "extern" "round.ceil_floor_round",
  bucket "extern" "float32.cast",
  bucket "extern" "float32.inf_snan",
  bucket "extern" "floatArray.box",
  bucket "toml_roundtrip" "ok.float_bits",
  bucket "python_oracle" "ok.batch_verified"
]

private def shrinkU64 (u : UInt64) : List UInt64 :=
  let raw : List UInt64 := [
    0,
    1,
    0x0010000000000000,
    0x3ff0000000000000,
    0x7ff0000000000000,
    0x7ff0000000000001,
    0x7ff8000000000000,
    0x8000000000000000,
    u &&& 0x7fffffffffffffff,
    u &&& 0xfff0000000000000,
    u &&& 0xffffffffffff0000,
    u &&& 0xffffffffffffff00
  ]
  (raw.filter (fun c => c < u)).eraseDups

private def shrinkU32 (u : UInt32) : List UInt32 :=
  let raw : List UInt32 := [
    0,
    1,
    0x00800000,
    0x3f800000,
    0x7f800000,
    0x7f800001,
    0x7fc00000,
    0x80000000,
    u &&& 0x7fffffff,
    u &&& 0xfff80000
  ]
  (raw.filter (fun c => c < u)).eraseDups

private def shrinkInt32 (x : Int32) : List Int32 :=
  let raw : List Int32 := [0, 1, -1, 2, -2, x / 2]
  (raw.filter (fun c => c.toInt.natAbs < x.toInt.natAbs)).eraseDups

private def shrinkDigitsList (ds : List Char) : List (List Char) := Id.run do
  let mut cands : List (List Char) := []
  if ds.length > 1 then
    cands := cands ++ [ds.take (max 1 (ds.length / 2))]
    cands := cands ++ [ds.drop (ds.length / 2)]
  let arr := ds.toArray
  let limit := min arr.size 16
  for i in List.range limit do
    if arr.size > 1 then
      let dropped := (arr.extract 0 i ++ arr.extract (i + 1) arr.size).toList
      cands := cands ++ [dropped]
    let c := arr[i]!
    if c > '0' then
      cands := cands ++ [(arr.set! i '0').toList]
    if c > '1' then
      cands := cands ++ [(arr.set! i '1').toList]
  return cands

private def splitFirstExp? (s : String) : Option (String × Char × String) :=
  match s.splitOn "e" with
  | sig :: rest@(_ :: _) => some (sig, 'e', "e".intercalate rest)
  | _ =>
    match s.splitOn "E" with
    | sig :: rest@(_ :: _) => some (sig, 'E', "E".intercalate rest)
    | _ => none

private def shrinkString (s : String) : List String := Id.run do
  let mut cands : List String := []
  let noUnder := stripUnderscores s
  if noUnder != s then
    cands := cands ++ [noUnder]
  if let some (sig, sep, expStr) := splitFirstExp? s then
    let (signStr, body) :=
      if sig.startsWith "-" then ("-", (sig.toList.drop 1))
      else if sig.startsWith "+" then ("+", (sig.toList.drop 1))
      else ("", sig.toList)
    let bodyStr := String.ofList body
    match bodyStr.splitOn "." with
    | [intPart, fracPart] =>
      let intChars := intPart.toList
      if !intChars.isEmpty then
        cands := cands ++ [s!"{signStr}{intPart}{sep}{expStr}"]
      for intCand in shrinkDigitsList intChars do
        cands := cands ++ [s!"{signStr}{String.ofList intCand}.{fracPart}{sep}{expStr}"]
      for fracCand in shrinkDigitsList fracPart.toList do
        cands := cands ++ [s!"{signStr}{intPart}.{String.ofList fracCand}{sep}{expStr}"]
    | _ =>
      for sigCand in shrinkDigitsList body do
        cands := cands ++ [s!"{signStr}{String.ofList sigCand}{sep}{expStr}"]
    let (expSign, expDigits) :=
      if expStr.startsWith "-" then ("-", expStr.toList.drop 1)
      else if expStr.startsWith "+" then ("+", expStr.toList.drop 1)
      else ("", expStr.toList)
    for expCand in shrinkDigitsList expDigits do
      cands := cands ++ [s!"{sig}{sep}{expSign}{String.ofList expCand}"]
  let arr := s.toList.toArray
  if arr.size > 1 then
    cands := cands ++ [String.ofList (arr.extract 0 (arr.size / 2)).toList]
    cands := cands ++ [String.ofList (arr.extract (arr.size / 2) arr.size).toList]
  let limit := min arr.size 32
  for i in List.range limit do
    let deleted := (arr.extract 0 i ++ arr.extract (i + 1) arr.size).toList
    cands := cands ++ [String.ofList deleted]
  return (cands.filter (fun c => c.length < s.length || (c.length == s.length && c < s))).eraseDups

private def shrinkNat (n : Nat) : List Nat :=
  if n == 0 then []
  else if n == 1 then [0]
  else [0, 1, n / 2, n - 1]

private def shrinkFloatCase : FloatFuzzCase → List FloatFuzzCase
  | .parseStr s => (shrinkString s).map .parseStr
  | .checkBits u => (shrinkU64 u).map .checkBits
  | .checkBinOp ua ub =>
    (shrinkU64 ua).map (fun a => .checkBinOp a ub) ++
      (shrinkU64 ub).map (fun b => .checkBinOp ua b)
  | .checkFma ua ub uc =>
    (shrinkU64 ua).map (fun a => .checkFma a ub uc) ++
      (shrinkU64 ub).map (fun b => .checkFma ua b uc) ++
      (shrinkU64 uc).map (fun c => .checkFma ua ub c)
  | .checkIntConv u => (shrinkU64 u).map .checkIntConv
  | .checkSci m negExp e =>
    (shrinkNat m).map (fun m' => .checkSci m' negExp e) ++
      (if negExp then [.checkSci m false e] else []) ++
      (shrinkNat e).map (fun e' => .checkSci m negExp e')
  | .checkExtern u u32 sc =>
    (shrinkU64 u).map (fun u' => .checkExtern u' u32 sc) ++
      (shrinkU32 u32).map (fun u32' => .checkExtern u u32' sc) ++
      (shrinkInt32 sc).map (fun sc' => .checkExtern u u32 sc')

private def shrinkToFixedPoint (fails : Array FloatFuzzCase → IO Bool) (trace : Array FloatFuzzCase) :
    IO (Array FloatFuzzCase) := do
  let mut cur ← shrinkTrace fails trace
  for _ in List.range 64 do
    let nxt ← shrinkElements shrinkFloatCase fails cur
    if nxt == cur then
      break
    cur := nxt
  return cur

private def runTraceChecked (client : PyOracleClient) (tracker : CoverageTracker)
    (trace : Array FloatFuzzCase) : IO CoverageTracker := do
  match ← checkEpisodeWithPy client trace with
  | .ok bkts =>
    let mut tr := tracker
    for b in bkts do
      tr := tr.record b.op b.bucket
    return tr
  | .error err =>
    if err.startsWith "PYTHON_ORACLE_EOF" then
      throw (IO.userError s!"FLOAT_FUZZ_MISMATCH err={err} trace_size={trace.size}")
    let fails (cand : Array FloatFuzzCase) : IO Bool := do
      match ← checkEpisodeWithPy client cand with
      | .ok _ => return false
      | .error e =>
        if e.startsWith "PYTHON_ORACLE_EOF" then
          throw (IO.userError e)
        return true
    let shrunk ← shrinkToFixedPoint fails trace
    let shrunkErr := match ← checkEpisodeWithPy client shrunk with
      | .error e => e
      | .ok _ => err
    throw (IO.userError s!"FLOAT_FUZZ_MISMATCH err={shrunkErr} original_err={err} shrunk={repr shrunk}")

private def runFloatSuite (steps : Nat) (seedVal : UInt64) (isSmoke : Bool) : IO Unit := do
  let client ← startPyOracleClient
  try
    let mut smokeTracker := CoverageTracker.empty
    let epSize := 24
    let mut idx := 0
    while idx < smokeCases.size do
      let stop := min smokeCases.size (idx + epSize)
      smokeTracker ← runTraceChecked client smokeTracker (smokeCases.extract idx stop)
      idx := stop
    let mut randTracker := CoverageTracker.empty
    let mut rng := Rng.seed seedVal
    let mut done := 0
    while done < steps do
      let (epLenRaw, r1) := rng.nextRange 16 32
      rng := r1
      let epLen := min epLenRaw (steps - done)
      let mut trace : Array FloatFuzzCase := Array.mkEmpty epLen
      for _ in List.range epLen do
        let (c, rN) := genFloatFuzzCase rng
        rng := rN
        trace := trace.push c
      randTracker ← runTraceChecked client randTracker trace
      done := done + epLen
    randTracker := randTracker.record "python_oracle" "ok.batch_verified"
    smokeTracker := smokeTracker.record "python_oracle" "ok.batch_verified"
    let reportTracker :=
      if isSmoke then
        smokeTracker.merge randTracker
      else
        randTracker
    if isSmoke || steps >= 5000 then
      assertCoverage "float" reportTracker requiredBuckets
    IO.println (reportTracker.formatReport "float")
    IO.println s!"FUZZ_SUMMARY suite=float steps={steps} seed={seedVal}"
    closePyOracleClient client
  catch e =>
    closePyOracleClientQuiet client
    throw e

private def hasNonZeroBeforeExp (s : String) : Bool := Id.run do
  for c in s.toList do
    if c == 'e' || c == 'E' then
      return false
    if '1' ≤ c && c ≤ '9' then
      return true
  return false

private def runFloatSelfTestShrink (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  let mut rng := Rng.seed (seedVal ^^^ 0x243f6a8885a308d3)
  let isParseBugItem : FloatFuzzCase → Bool
    | .parseStr s =>
      match LeanSwe.NumParse.parseFloat s with
      | .ok f => f.toBits == 0x8000000000000000 && hasNonZeroBeforeExp s
      | .error _ => false
    | _ => false
  let mut trace1 : Array FloatFuzzCase := Array.mkEmpty 21
  for _ in List.range 20 do
    let (c, r1) := genFloatFuzzCase rng
    rng := r1
    if !isParseBugItem c then
      trace1 := trace1.push c
  let (idx1, r2) := rng.nextRange 0 trace1.size
  rng := r2
  let badParse := FloatFuzzCase.parseStr "-123_456.789_012e-450"
  let injected1 := (trace1.extract 0 idx1).push badParse ++ trace1.extract idx1 trace1.size
  let failsParseBug (cand : Array FloatFuzzCase) : IO Bool := pure (cand.any isParseBugItem)
  let shrunk1 ← shrinkToFixedPoint failsParseBug injected1
  unless ← failsParseBug shrunk1 do
    throw (IO.userError "FLOAT_SHRINK_SELFTEST_1: shrunk trace no longer triggers failure")
  if shrunk1.size != 1 then
    throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_1: expected size 1, got {shrunk1.size}")
  match shrunk1[0]! with
  | .parseStr s =>
    if s.length > 9 then
      throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_1: shrunk string too long ({s.length}): {repr s}")
    IO.println s!"FLOAT_SHRINK_SELFTEST_1_OK: shrunk={repr s}"
  | other =>
    throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_1: unexpected variant {repr other}")
  let isSnanBugItem : FloatFuzzCase → Bool
    | .checkBinOp ua ub => isSignalingNaNBits ua || isSignalingNaNBits ub
    | _ => false
  let mut trace2 : Array FloatFuzzCase := Array.mkEmpty 21
  for _ in List.range 20 do
    let (c, rN) := genFloatFuzzCase rng
    rng := rN
    if !isSnanBugItem c then
      trace2 := trace2.push c
  let (idx2, r3) := rng.nextRange 0 trace2.size
  rng := r3
  let badBin := FloatFuzzCase.checkBinOp 0xfff0deadbeef1234 0x4029000000000000
  let injected2 := (trace2.extract 0 idx2).push badBin ++ trace2.extract idx2 trace2.size
  let failsSnanBug (cand : Array FloatFuzzCase) : IO Bool := pure (cand.any isSnanBugItem)
  let shrunk2 ← shrinkToFixedPoint failsSnanBug injected2
  unless ← failsSnanBug shrunk2 do
    throw (IO.userError "FLOAT_SHRINK_SELFTEST_2: shrunk trace no longer triggers failure")
  if shrunk2 != #[.checkBinOp 0x7ff0000000000001 0] then
    throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_2: unexpected shrunk={repr shrunk2}")
  IO.println s!"FLOAT_SHRINK_SELFTEST_2_OK: shrunk={repr shrunk2}"
  let client ← startPyOracleClient
  try
    let mut trace3 : Array FloatFuzzCase := Array.mkEmpty 12
    for _ in List.range 10 do
      trace3 := trace3.push (.parseStr "1.5")
    let (idx3, _) := rng.nextRange 0 10
    let injected3 := (trace3.extract 0 idx3).push (.parseStr "123_456.789") ++ trace3.extract idx3 trace3.size
    let failsPyBug (cand : Array FloatFuzzCase) : IO Bool := do
      let mut items : Array PyParseItem := #[]
      for c in cand do
        if let .parseStr s := c then
          let parsed? := (LeanSwe.NumParse.parseFloat s).toOption
          items := items.push {
            rawInput := s
            cleanStr := stripUnderscores s
            expectedOk := parsed?.isSome
            expectedBits := if s.contains '9' then 0 else parsed?.map (·.toBits) |>.getD 0
            tomlCheck := false
          }
      match ← flushPyBatch client { parses := items } with
      | .ok () => return false
      | .error e =>
        if e.startsWith "PYTHON_ORACLE_EOF" then
          throw (IO.userError e)
        return true
    let shrunk3 ← shrinkToFixedPoint failsPyBug injected3
    unless ← failsPyBug shrunk3 do
      throw (IO.userError "FLOAT_SHRINK_SELFTEST_3: Python oracle shrunk trace no longer triggers failure")
    if shrunk3.size != 1 then
      throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_3: expected size 1, got {shrunk3.size}")
    match shrunk3[0]! with
    | .parseStr s =>
      if s.length > 4 || !s.contains '9' then
        throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_3: unexpected shrunk={repr shrunk3}")
      IO.println s!"FLOAT_SHRINK_SELFTEST_3_OK: shrunk={repr shrunk3}"
    | _ =>
      throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_3: unexpected variant {repr shrunk3}")
    closePyOracleClient client
  catch e =>
    closePyOracleClientQuiet client
    throw e

/-- 4-way differential fuzzing suite for `Float` runtime, `NumParse`, `Toml`, `Float.Model`, C99, and Python 3. -/
def suite : FuzzSuite := {
  name := "float"
  description := "4-way differential fuzzer for Float runtime, NumParse, Toml, Float.Model, C99 strtod_l/libm, and Python 3"
  runSmoke := fun cfg =>
    runFloatSuite 400 cfg.seed true
  runFuzz := fun cfg =>
    runFloatSuite cfg.steps cfg.seed false
  selfTestShrink := runFloatSelfTestShrink
}

end Fuzz.Float
