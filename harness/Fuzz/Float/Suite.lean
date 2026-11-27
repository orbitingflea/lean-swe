import Fuzz.Common.Coverage
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
import Fuzz.Float.Oracle
import Fuzz.Float.Gen
import LeanSwe.NumParse.Interface
import LeanSweProofs.NumParse.Model
import LeanSwe.Toml.Interface
import Lean.Data.Json.Basic

/-!
4-way differential fuzzer suite `Fuzz.Float.suite` verifying Lean runtime `Float` / `Float32` and
`LeanSwe.NumParse` / `LeanSwe.Toml` against pure `Float.Model` / `Float32.Model`,
C99 `strtod_l`/`snprintf`/`libm`, and an unclamped persistent Python 3 `float`/`repr`/`tomllib`/`fractions` co-process.
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

private def numParseErrKindCtor : LeanSwe.NumParse.NumParseErrorKind → String
  | .emptyInput => "LeanSwe.NumParse.NumParseErrorKind.emptyInput"
  | .invalidSyntax => "LeanSwe.NumParse.NumParseErrorKind.invalidSyntax"
  | .invalidSignForBase => "LeanSwe.NumParse.NumParseErrorKind.invalidSignForBase"
  | .leadingZero => "LeanSwe.NumParse.NumParseErrorKind.leadingZero"
  | .invalidUnderscore => "LeanSwe.NumParse.NumParseErrorKind.invalidUnderscore"
  | .overflow => "LeanSwe.NumParse.NumParseErrorKind.overflow"
  | .trailingChars => "LeanSwe.NumParse.NumParseErrorKind.trailingChars"

private def tomlErrKindCtor : LeanSwe.Toml.TomlErrorKind → String
  | .parseError => "LeanSwe.Toml.TomlErrorKind.parseError"
  | .duplicateKey => "LeanSwe.Toml.TomlErrorKind.duplicateKey"
  | .redefinedTable => "LeanSwe.Toml.TomlErrorKind.redefinedTable"
  | .immutableInlineTable => "LeanSwe.Toml.TomlErrorKind.immutableInlineTable"
  | .invalidUtf8OrControl => "LeanSwe.Toml.TomlErrorKind.invalidUtf8OrControl"
  | .numericOverflow => "LeanSwe.Toml.TomlErrorKind.numericOverflow"
  | .missingField => "LeanSwe.Toml.TomlErrorKind.missingField"
  | .typeMismatch => "LeanSwe.Toml.TomlErrorKind.typeMismatch"
  | .decodeError => "LeanSwe.Toml.TomlErrorKind.decodeError"

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
  let mut lastNonZeroPos := 0
  let mut started := false
  for c in sClean.toList do
    if c == 'e' || c == 'E' then
      break
    if '1' ≤ c && c ≤ '9' then
      started := true
      sigDigits := sigDigits + 1
      lastNonZeroPos := sigDigits
    else if c == '0' && started then
      sigDigits := sigDigits + 1
  return lastNonZeroPos >= 17

private def checkParseStr (s : String) :
    Except String (List CoverageBucket × List (String × String) × Option PyParseItem) := do
  let resImpl := LeanSwe.NumParse.parseFloat s
  let resModel := LeanSwe.NumParse.Model.parseFloatModel s
  let mut bkts : List CoverageBucket := []
  let mut errHits : List (String × String) := []
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
    errHits := ("LeanSwe.NumParse.parseFloat", numParseErrKindCtor e.kind) :: errHits
    if !s.contains '_' && !s.contains '\x00' && !hasLeadingAsciiSpace s && !s.isEmpty then
      let (consumed, _) := cStrtod s
      if consumed.toNat == s.utf8ByteSize then
        if !isAllowedStrtodOnlySyntax s then
          throw s!"STRTOD_ACCEPTED_TOML_REJECTED s={repr s} err={repr e.kind}"
    if tomlEligible then
      match LeanSwe.Toml.parse ("x = " ++ s) with
      | .error te =>
        errHits := ("LeanSwe.Toml.parse", tomlErrKindCtor te.kind) :: errHits
      | .ok tbl =>
        match LeanSwe.Toml.getField (α := Float) tbl "x" with
        | .ok gotF =>
          throw s!"TOML_ACCEPTED_INVALID_FLOAT s={repr s} got={hex64 gotF.toBits}"
        | .error ge =>
          errHits := ("LeanSwe.Toml.getField", tomlErrKindCtor ge.kind) :: errHits
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
  return (bkts, errHits, some pyItem)

private def checkTomlRoundTripField (tbl : LeanSwe.Toml.TomlTable) (key : String) (expectedBits : UInt64)
    (tomlText : String) : Except String Unit := do
  match LeanSwe.Toml.getField (α := Float) tbl key with
  | .error err =>
    throw s!"TOML_DECODE_ERR key={key} text={repr tomlText} err={repr err}"
  | .ok decoded =>
    if decoded.toBits != expectedBits then
      throw s!"TOML_BITS_MISMATCH key={key} text={repr tomlText} got={hex64 decoded.toBits} expected={hex64 expectedBits}"

private def checkBitsCase (u : UInt64) : Except String (List CoverageBucket × PyFormatItem) := do
  let m := Float.Model.ofBits u
  let f := Float.ofBits u
  let fRaw := rawDoubleFromBits u
  let expBits := canonBits u
  if rawBitsFromDouble fRaw != u then
    throw s!"RAW_BITS_ROUNDTRIP_MISMATCH u={hex64 u} got={hex64 (rawBitsFromDouble fRaw)}"
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
  let cStr := cSnprintf17g u
  let normCStr := normalizeCFormattedForToml cStr
  match LeanSwe.NumParse.parseFloat normCStr with
  | .error err =>
    throw s!"SNPRINTF_ROUNDTRIP_ERR u={hex64 u} cStr={repr cStr} norm={repr normCStr} err={repr err}"
  | .ok z =>
    if z.toBits != m.toBits then
      throw s!"SNPRINTF_ROUNDTRIP_BITS u={hex64 u} norm={repr normCStr} got={hex64 z.toBits} expected={hex64 m.toBits}"
  let negExpBits := (-m).toBits
  if (u &&& 0x3) == 0 then
    let doc : LeanSwe.Toml.TomlTable := #[
      ("v", LeanSwe.Toml.TomlValue.float fRaw),
      ("arr", LeanSwe.Toml.TomlValue.array #[LeanSwe.Toml.TomlValue.float fRaw, LeanSwe.Toml.TomlValue.float (-f)]),
      ("sec", LeanSwe.Toml.TomlValue.table #[
        ("nested", LeanSwe.Toml.TomlValue.float fRaw),
        ("inline", LeanSwe.Toml.TomlValue.table #[("x", LeanSwe.Toml.TomlValue.float f)])
      ]),
      ("items", LeanSwe.Toml.TomlValue.array #[
        LeanSwe.Toml.TomlValue.table #[("a", LeanSwe.Toml.TomlValue.float fRaw)],
        LeanSwe.Toml.TomlValue.table #[("a", LeanSwe.Toml.TomlValue.float (-f))]
      ])
    ]
    let tomlText := LeanSwe.Toml.format doc
    match LeanSwe.Toml.parse tomlText with
    | .error err =>
      throw s!"TOML_PARSE_ERR u={hex64 u} text={repr tomlText} err={repr err}"
    | .ok tbl =>
      checkTomlRoundTripField tbl "v" m.toBits tomlText
      match LeanSwe.Toml.getPath (α := Float) tbl ["sec", "nested"] with
      | .error err => throw s!"TOML_PATH_ERR u={hex64 u} err={repr err}"
      | .ok gotN =>
        if gotN.toBits != m.toBits then
          throw s!"TOML_NESTED_BITS_MISMATCH u={hex64 u} got={hex64 gotN.toBits} expected={hex64 m.toBits}"
      match LeanSwe.Toml.getPath (α := Float) tbl ["sec", "inline", "x"] with
      | .error err => throw s!"TOML_INLINE_ERR u={hex64 u} err={repr err}"
      | .ok gotI =>
        if gotI.toBits != m.toBits then
          throw s!"TOML_INLINE_BITS_MISMATCH u={hex64 u} got={hex64 gotI.toBits} expected={hex64 m.toBits}"
      match LeanSwe.Toml.getField (α := Array Float) tbl "arr" with
      | .error err => throw s!"TOML_ARR_ERR u={hex64 u} err={repr err}"
      | .ok arrOut =>
        if arrOut.size != 2 || arrOut[0]!.toBits != m.toBits || arrOut[1]!.toBits != negExpBits then
          throw s!"TOML_ARR_BITS_MISMATCH u={hex64 u}"
      match LeanSwe.Toml.getField (α := Array LeanSwe.Toml.TomlTable) tbl "items" with
      | .error err => throw s!"TOML_AOT_ERR u={hex64 u} err={repr err}"
      | .ok aot =>
        if aot.size != 2 then
          throw s!"TOML_AOT_SIZE_MISMATCH u={hex64 u}"
        checkTomlRoundTripField aot[0]! "a" m.toBits tomlText
        checkTomlRoundTripField aot[1]! "a" negExpBits tomlText
  else
    let doc : LeanSwe.Toml.TomlTable := #[("v", LeanSwe.Toml.TomlValue.float f)]
    let tomlText := LeanSwe.Toml.format doc
    match LeanSwe.Toml.parse tomlText with
    | .error err =>
      throw s!"TOML_PARSE_ERR u={hex64 u} text={repr tomlText} err={repr err}"
    | .ok tbl =>
      checkTomlRoundTripField tbl "v" m.toBits tomlText
  bkts := bucket "toml_roundtrip" "ok.float_bits" :: bkts
  return (bkts, { bits := m.toBits, formatted := s })

private def checkSame4 (tag : String) (a b c d : UInt64) : Except String Unit := do
  if a != b || a != c || a != d then
    throw s!"{tag}: runtime={hex64 a} raw={hex64 b} model={hex64 c} c={hex64 d}"

private def checkSame4F32 (tag : String) (a b c d : UInt32) : Except String Unit := do
  if a != b || a != c || a != d then
    throw s!"{tag}: runtime={hex32 a} raw={hex32 b} model={hex32 c} c={hex32 d}"

private def checkRawNotSignaling (tag : String) (f : Float) : Except String Unit := do
  let raw := rawBitsFromDouble f
  if isSignalingNaNBits raw then
    throw s!"{tag}: unquieted signaling NaN raw={hex64 raw}"

private def checkRawNotSignaling32 (tag : String) (f : Float32) : Except String Unit := do
  let raw := rawBitsFromFloat32 f
  if isSignalingNaNBits32 raw then
    throw s!"{tag}: unquieted signaling Float32 NaN raw={hex32 raw}"

/--
Check raw uncanonicalized `Float` `minimum`/`maximum`/`minimumNumber`/`maximumNumber` results.
Guards ONLY the known upstream Lean `v4.36.0-rc2` / Clang 23 `__builtin_elementwise_*` bug
where a NaN output from a signaling NaN operand remains unquieted.
-/
private def checkRawMinMax (tag : String) (res : Float) (mRes : Float.Model) (ua ub : UInt64) : Except String Unit := do
  let raw := rawBitsFromDouble res
  if mRes.isNaN then
    if !isSignalingNaNBits ua && !isSignalingNaNBits ub then
      if isSignalingNaNBits raw then
        throw s!"{tag}: unexpected signaling NaN raw={hex64 raw}"
  else
    if raw != mRes.toBits then
      throw s!"{tag}_RAW_NON_NAN: raw={hex64 raw} expected={hex64 mRes.toBits}"

/-- Narrow guard equivalent to `checkRawMinMax` for `Float32`. -/
private def checkRawMinMax32 (tag : String) (res : Float32) (mRes : Float32.Model) (ua ub : UInt32) : Except String Unit := do
  let raw := rawBitsFromFloat32 res
  if mRes.isNaN then
    if !isSignalingNaNBits32 ua && !isSignalingNaNBits32 ub then
      if isSignalingNaNBits32 raw then
        throw s!"{tag}: unexpected signaling Float32 NaN raw={hex32 raw}"
  else
    if raw != mRes.toBits then
      throw s!"{tag}_RAW_NON_NAN: raw={hex32 raw} expected={hex32 mRes.toBits}"

private def isPowSnanCongruenceCase (ua ub : UInt64) : Bool :=
  let ma := Float.Model.ofBits ua
  let mb := Float.Model.ofBits ub
  (isSignalingNaNBits ua && (mb == Float.Model.ofBits 0)) ||
    (ma == Float.Model.ofBits 0x3ff0000000000000 && isSignalingNaNBits ub)

private def isPow32SnanCongruenceCase (ua ub : UInt32) : Bool :=
  let ma := Float32.Model.ofBits ua
  let mb := Float32.Model.ofBits ub
  (isSignalingNaNBits32 ua && (mb == Float32.Model.ofBits 0)) ||
    (ma == Float32.Model.ofBits 0x3f800000 && isSignalingNaNBits32 ub)

private def checkBinOpCase (ua ub : UInt64) : Except String (List CoverageBucket) := do
  let fa := Float.ofBits ua
  let fb := Float.ofBits ub
  let faRaw := rawDoubleFromBits ua
  let fbRaw := rawDoubleFromBits ub
  let ma := Float.Model.ofBits ua
  let mb := Float.Model.ofBits ub
  let addRaw := faRaw + fbRaw
  let subRaw := faRaw - fbRaw
  let mulRaw := faRaw * fbRaw
  let divRaw := faRaw / fbRaw
  checkSame4 s!"ADD({hex64 ua},{hex64 ub})" (fa + fb).toBits addRaw.toBits (ma + mb).toBits (canonBits (cBinOp 0 ua ub))
  checkSame4 s!"SUB({hex64 ua},{hex64 ub})" (fa - fb).toBits subRaw.toBits (ma - mb).toBits (canonBits (cBinOp 1 ua ub))
  checkSame4 s!"MUL({hex64 ua},{hex64 ub})" (fa * fb).toBits mulRaw.toBits (ma * mb).toBits (canonBits (cBinOp 2 ua ub))
  checkSame4 s!"DIV({hex64 ua},{hex64 ub})" (fa / fb).toBits divRaw.toBits (ma / mb).toBits (canonBits (cBinOp 3 ua ub))
  checkRawNotSignaling s!"ADD_RAW({hex64 ua},{hex64 ub})" addRaw
  checkRawNotSignaling s!"SUB_RAW({hex64 ua},{hex64 ub})" subRaw
  checkRawNotSignaling s!"MUL_RAW({hex64 ua},{hex64 ub})" mulRaw
  checkRawNotSignaling s!"DIV_RAW({hex64 ua},{hex64 ub})" divRaw
  let minRaw := Float.minimum faRaw fbRaw
  let minNumRaw := Float.minimumNumber faRaw fbRaw
  let maxRaw := Float.maximum faRaw fbRaw
  let maxNumRaw := Float.maximumNumber faRaw fbRaw
  checkSame4 s!"MIN({hex64 ua},{hex64 ub})"
    (Float.minimum fa fb).toBits minRaw.toBits (ma.minimum mb).toBits (canonBits (cMinMax false ua ub))
  checkSame4 s!"MIN_NUM({hex64 ua},{hex64 ub})"
    (Float.minimumNumber fa fb).toBits minNumRaw.toBits (ma.minimumNumber mb).toBits (canonBits (cMinMaxNum false ua ub))
  checkSame4 s!"MAX({hex64 ua},{hex64 ub})"
    (Float.maximum fa fb).toBits maxRaw.toBits (ma.maximum mb).toBits (canonBits (cMinMax true ua ub))
  checkSame4 s!"MAX_NUM({hex64 ua},{hex64 ub})"
    (Float.maximumNumber fa fb).toBits maxNumRaw.toBits (ma.maximumNumber mb).toBits (canonBits (cMinMaxNum true ua ub))
  checkRawMinMax s!"MIN({hex64 ua},{hex64 ub})" minRaw (ma.minimum mb) ua ub
  checkRawMinMax s!"MIN_NUM({hex64 ua},{hex64 ub})" minNumRaw (ma.minimumNumber mb) ua ub
  checkRawMinMax s!"MAX({hex64 ua},{hex64 ub})" maxRaw (ma.maximum mb) ua ub
  checkRawMinMax s!"MAX_NUM({hex64 ua},{hex64 ub})" maxNumRaw (ma.maximumNumber mb) ua ub
  let powCanonC := canonBits (cBinOp 4 (canonBits ua) (canonBits ub))
  let powRt := Float.pow fa fb
  let powRaw := Float.pow faRaw fbRaw
  if powRt.toBits != powCanonC then
    throw s!"POW_CANON({hex64 ua},{hex64 ub}): rt={hex64 powRt.toBits} c={hex64 powCanonC}"
  if !isPowSnanCongruenceCase ua ub then
    if powRaw.toBits != powCanonC then
      throw s!"POW_RAW({hex64 ua},{hex64 ub}): raw={hex64 powRaw.toBits} c={hex64 powCanonC}"
  checkRawNotSignaling s!"POW_RAW_SNAN({hex64 ua},{hex64 ub})" powRaw
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
  if ma.isFinite && mb.isFinite && !(mb == Float.Model.ofBits 0) && (ma / mb).isFinite && (((ma / mb) * mb).toBits != ma.toBits) then
    bkts := bucket "arith" "div.inexact" :: bkts
  if (ma.toBits == 0x0000000000000000 && mb.toBits == 0x8000000000000000) ||
      (ma.toBits == 0x8000000000000000 && mb.toBits == 0x0000000000000000) then
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
  let fmaRaw := Float.fma faRaw fbRaw fcRaw
  checkSame4 s!"FMA({hex64 ua},{hex64 ub},{hex64 uc})"
    (Float.fma fa fb fc).toBits fmaRaw.toBits mf.toBits (canonBits (cFma ua ub uc))
  checkRawNotSignaling s!"FMA_RAW({hex64 ua},{hex64 ub},{hex64 uc})" fmaRaw
  let mut bkts : List CoverageBucket := []
  if ma.isFinite && mb.isFinite && mc.isFinite && mf.toBits != (ma * mb + mc).toBits then
    bkts := bucket "arith" "fma.single_round" :: bkts
  if ma.isFinite && mb.isFinite && mc.isFinite && !(ma == Float.Model.ofBits 0) &&
      !(mb == Float.Model.ofBits 0) && mf == Float.Model.ofBits 0 then
    bkts := bucket "arith" "fma.underflow_sign" :: bkts
  return bkts

private def checkIntConvCase (u : UInt64) : Except String (List CoverageBucket × Array PyIntFloatItem) := do
  let f := Float.ofBits u
  let fRaw := rawDoubleFromBits u
  let m := Float.Model.ofBits u
  let sqrtRaw := fRaw.sqrt
  checkSame4 s!"NEG({hex64 u})" (-f).toBits (-fRaw).toBits (-m).toBits (canonBits (cUnOp 0 u))
  checkSame4 s!"ABS({hex64 u})" f.abs.toBits fRaw.abs.toBits m.abs.toBits (canonBits (cUnOp 1 u))
  checkSame4 s!"SQRT({hex64 u})" f.sqrt.toBits sqrtRaw.toBits m.sqrt.toBits (canonBits (cUnOp 2 u))
  checkRawNotSignaling s!"SQRT_RAW({hex64 u})" sqrtRaw
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
  let bigNat :=
    if (u &&& 0x1f) == 0x1f then
      ((1 <<< 54) - 1) <<< 970
    else if bigShift >= 54 then
      let mantBits := (u &&& 0x000fffffffffffff).toNat <<< (bigShift - 52)
      let tieBit := if ((u >>> 62) &&& 1) == 1 then (1 <<< (bigShift - 53)) else 0
      let stickyBit := if ((u >>> 61) &&& 1) == 1 && bigShift >= 55 then 1 else 0
      (1 <<< bigShift) + mantBits + tieBit + stickyBit
    else
      (1 <<< 53) + (u &&& 0x1fff).toNat
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
  let mut bkts : List CoverageBucket := []
  if bigShift >= 54 && (bigNat % (1 <<< (bigShift - 52)) != 0) then
    bkts := bucket "int_conv" "from_int.exact_and_round" :: bkts
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
  let f32 : Float32 := OfScientific.ofScientific m negExp e
  let modF32 := Float32.Model.ofScientific m modelExp
  if f32.toBits != modF32.toBits then
    throw s!"OF_SCIENTIFIC_F32_MODEL_MISMATCH m={m} neg={negExp} e={e} rt={hex32 f32.toBits} model={hex32 modF32.toBits}"
  let sciStr := s!"{m}e{if negExp then "-" else ""}{e}"
  match LeanSwe.NumParse.parseFloat sciStr with
  | .error err =>
    throw s!"OF_SCIENTIFIC_NUMPARSE_ERR s={sciStr} err={repr err}"
  | .ok parsedF =>
    if parsedF.toBits != f.toBits then
      throw s!"OF_SCIENTIFIC_NUMPARSE_MISMATCH s={sciStr} parsed={hex64 parsedF.toBits} rt={hex64 f.toBits}"
  match LeanSwe.Toml.parse ("x = " ++ sciStr) with
  | .error err =>
    throw s!"OF_SCIENTIFIC_TOML_ERR s={sciStr} err={repr err}"
  | .ok tbl =>
    checkTomlRoundTripField tbl "x" f.toBits ("x = " ++ sciStr)
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

private def checkFloatTranscendental (tag : String) (f fRaw : Float) (fn : Float → Float) (cBits : UInt64) :
    Except String Unit := do
  let r1 := fn f
  let r2 := fn fRaw
  if r1.toBits != cBits || r2.toBits != cBits then
    throw s!"{tag}: rt={hex64 r1.toBits} raw={hex64 r2.toBits} c={hex64 cBits}"
  checkRawNotSignaling s!"{tag}_RAW" r2

private def checkFloat32Full (u : UInt64) (u32 : UInt32) (scaleExp : Int32) :
    Except String (List CoverageBucket × PyExternItem) := do
  let u32b : UInt32 := u.toUInt32 ^^^ 0x9e3779b9
  let u32c : UInt32 := (u >>> 32).toUInt32
  let fa := Float32.ofBits u32
  let fb := Float32.ofBits u32b
  let fc := Float32.ofBits u32c
  let faRaw := rawFloat32FromBits u32
  let fbRaw := rawFloat32FromBits u32b
  let fcRaw := rawFloat32FromBits u32c
  let ma := Float32.Model.ofBits u32
  let mb := Float32.Model.ofBits u32b
  let mc := Float32.Model.ofBits u32c
  if rawBitsFromFloat32 faRaw != u32 then
    throw s!"F32_RAW_ROUNDTRIP u32={hex32 u32}"
  let addR := faRaw + fbRaw
  let subR := faRaw - fbRaw
  let mulR := faRaw * fbRaw
  let divR := faRaw / fbRaw
  let fmaR := Float32.fma faRaw fbRaw fcRaw
  let sqrtR := faRaw.sqrt
  checkSame4F32 s!"F32_ADD({hex32 u32},{hex32 u32b})" (fa + fb).toBits addR.toBits (ma + mb).toBits (canonBits32 (cF32BinOp 0 u32 u32b))
  checkSame4F32 s!"F32_SUB({hex32 u32},{hex32 u32b})" (fa - fb).toBits subR.toBits (ma - mb).toBits (canonBits32 (cF32BinOp 1 u32 u32b))
  checkSame4F32 s!"F32_MUL({hex32 u32},{hex32 u32b})" (fa * fb).toBits mulR.toBits (ma * mb).toBits (canonBits32 (cF32BinOp 2 u32 u32b))
  checkSame4F32 s!"F32_DIV({hex32 u32},{hex32 u32b})" (fa / fb).toBits divR.toBits (ma / mb).toBits (canonBits32 (cF32BinOp 3 u32 u32b))
  checkSame4F32 s!"F32_FMA({hex32 u32},{hex32 u32b},{hex32 u32c})"
    (Float32.fma fa fb fc).toBits fmaR.toBits (Float32.Model.fma ma mb mc).toBits (canonBits32 (cF32Fma u32 u32b u32c))
  checkSame4F32 s!"F32_NEG({hex32 u32})" (-fa).toBits (-faRaw).toBits (-ma).toBits (canonBits32 (cF32UnOp 0 u32))
  checkSame4F32 s!"F32_ABS({hex32 u32})" fa.abs.toBits faRaw.abs.toBits ma.abs.toBits (canonBits32 (cF32UnOp 1 u32))
  checkSame4F32 s!"F32_SQRT({hex32 u32})" fa.sqrt.toBits sqrtR.toBits ma.sqrt.toBits (canonBits32 (cF32UnOp 2 u32))
  checkRawNotSignaling32 "F32_ADD_RAW" addR
  checkRawNotSignaling32 "F32_SUB_RAW" subR
  checkRawNotSignaling32 "F32_MUL_RAW" mulR
  checkRawNotSignaling32 "F32_DIV_RAW" divR
  checkRawNotSignaling32 "F32_FMA_RAW" fmaR
  checkRawNotSignaling32 "F32_SQRT_RAW" sqrtR
  let minR := Float32.minimum faRaw fbRaw
  let minNumR := Float32.minimumNumber faRaw fbRaw
  let maxR := Float32.maximum faRaw fbRaw
  let maxNumR := Float32.maximumNumber faRaw fbRaw
  checkSame4F32 s!"F32_MIN({hex32 u32},{hex32 u32b})" (Float32.minimum fa fb).toBits minR.toBits (ma.minimum mb).toBits (canonBits32 (cF32MinMax false u32 u32b))
  checkSame4F32 s!"F32_MIN_NUM({hex32 u32},{hex32 u32b})" (Float32.minimumNumber fa fb).toBits minNumR.toBits (ma.minimumNumber mb).toBits (canonBits32 (cF32MinMaxNum false u32 u32b))
  checkSame4F32 s!"F32_MAX({hex32 u32},{hex32 u32b})" (Float32.maximum fa fb).toBits maxR.toBits (ma.maximum mb).toBits (canonBits32 (cF32MinMax true u32 u32b))
  checkSame4F32 s!"F32_MAX_NUM({hex32 u32},{hex32 u32b})" (Float32.maximumNumber fa fb).toBits maxNumR.toBits (ma.maximumNumber mb).toBits (canonBits32 (cF32MinMaxNum true u32 u32b))
  checkRawMinMax32 s!"F32_MIN({hex32 u32},{hex32 u32b})" minR (ma.minimum mb) u32 u32b
  checkRawMinMax32 s!"F32_MIN_NUM({hex32 u32},{hex32 u32b})" minNumR (ma.minimumNumber mb) u32 u32b
  checkRawMinMax32 s!"F32_MAX({hex32 u32},{hex32 u32b})" maxR (ma.maximum mb) u32 u32b
  checkRawMinMax32 s!"F32_MAX_NUM({hex32 u32},{hex32 u32b})" maxNumR (ma.maximumNumber mb) u32 u32b
  let pow32CanonC := canonBits32 (cF32BinOp 4 (canonBits32 u32) (canonBits32 u32b))
  let pow32Rt := Float32.pow fa fb
  let pow32Raw := Float32.pow faRaw fbRaw
  if pow32Rt.toBits != pow32CanonC then
    throw s!"F32_POW_CANON({hex32 u32},{hex32 u32b}): rt={hex32 pow32Rt.toBits} c={hex32 pow32CanonC}"
  if !isPow32SnanCongruenceCase u32 u32b then
    if pow32Raw.toBits != pow32CanonC then
      throw s!"F32_POW_RAW({hex32 u32},{hex32 u32b}): raw={hex32 pow32Raw.toBits} c={hex32 pow32CanonC}"
  checkRawNotSignaling32 s!"F32_POW_RAW_SNAN({hex32 u32},{hex32 u32b})" pow32Raw
  let mask32 := cF32Cmp u32 u32b
  if (fa == fb) != (ma == mb) || (faRaw == fbRaw) != (ma == mb) || ((mask32 &&& 1) != 0) != (ma == mb) then
    throw s!"F32_BEQ_MISMATCH({hex32 u32},{hex32 u32b})"
  if (fa < fb) != (ma < mb) || (faRaw < fbRaw) != (ma < mb) || ((mask32 &&& 2) != 0) != (ma < mb) then
    throw s!"F32_LT_MISMATCH({hex32 u32},{hex32 u32b})"
  if (fa <= fb) != (ma <= mb) || (faRaw <= fbRaw) != (ma <= mb) || ((mask32 &&& 4) != 0) != (ma <= mb) then
    throw s!"F32_LE_MISMATCH({hex32 u32},{hex32 u32b})"
  if decide (fa = fb) != decide (ma = mb) || decide (faRaw = fbRaw) != decide (ma = mb) then
    throw s!"F32_DEC_EQ_MISMATCH({hex32 u32},{hex32 u32b})"
  if fa.isNaN != ma.isNaN || fa.isFinite != ma.isFinite || fa.isInf != ma.isInf then
    throw s!"F32_CLASS_MISMATCH({hex32 u32})"
  if fa.toUInt8 != ma.toUInt8 || faRaw.toUInt8 != ma.toUInt8 || (cF32ToUInt64 u32 255).toUInt8 != ma.toUInt8 then
    throw s!"F32_TO_UINT8_MISMATCH({hex32 u32})"
  if fa.toUInt16 != ma.toUInt16 || faRaw.toUInt16 != ma.toUInt16 || (cF32ToUInt64 u32 65535).toUInt16 != ma.toUInt16 then
    throw s!"F32_TO_UINT16_MISMATCH({hex32 u32})"
  if fa.toUInt32 != ma.toUInt32 || faRaw.toUInt32 != ma.toUInt32 || (cF32ToUInt64 u32 0xffffffff).toUInt32 != ma.toUInt32 then
    throw s!"F32_TO_UINT32_MISMATCH({hex32 u32})"
  if fa.toUInt64 != ma.toUInt64 || faRaw.toUInt64 != ma.toUInt64 || cF32ToUInt64 u32 0xffffffffffffffff != ma.toUInt64 then
    throw s!"F32_TO_UINT64_MISMATCH({hex32 u32})"
  if fa.toInt8 != ma.toInt8 || faRaw.toInt8 != ma.toInt8 || (cF32ToInt64 u32 (Int64.ofInt (-128)) (Int64.ofInt 127)).toInt8 != ma.toInt8 then
    throw s!"F32_TO_INT8_MISMATCH({hex32 u32})"
  if fa.toInt16 != ma.toInt16 || faRaw.toInt16 != ma.toInt16 || (cF32ToInt64 u32 (Int64.ofInt (-32768)) (Int64.ofInt 32767)).toInt16 != ma.toInt16 then
    throw s!"F32_TO_INT16_MISMATCH({hex32 u32})"
  if fa.toInt32 != ma.toInt32 || faRaw.toInt32 != ma.toInt32 || (cF32ToInt64 u32 (Int64.ofInt (-2147483648)) (Int64.ofInt 2147483647)).toInt32 != ma.toInt32 then
    throw s!"F32_TO_INT32_MISMATCH({hex32 u32})"
  if fa.toInt64 != ma.toInt64 || faRaw.toInt64 != ma.toInt64 || cF32ToInt64 u32 Int64.minValue Int64.maxValue != ma.toInt64 then
    throw s!"F32_TO_INT64_MISMATCH({hex32 u32})"
  let i64 := u.toInt64
  if u.toFloat32.toBits != (Float32.Model.ofUInt64 u).toBits || u.toFloat32.toBits != cF32OfUInt64 u then
    throw s!"F32_OF_UINT64_MISMATCH({hex64 u})"
  if i64.toFloat32.toBits != (Float32.Model.ofInt64 i64).toBits || i64.toFloat32.toBits != cF32OfInt64 i64 then
    throw s!"F32_OF_INT64_MISMATCH({hex64 u})"
  let smallNat := (u &&& 0xffffffff).toNat
  let smallInt := if (u >>> 63) == 1 then -Int.ofNat smallNat else Int.ofNat smallNat
  if (Nat.toFloat32 smallNat).toBits != (Float32.Model.ofNat smallNat).toBits then
    throw s!"F32_OF_NAT_MISMATCH({smallNat})"
  if (Int.toFloat32 smallInt).toBits != (Float32.Model.ofInt smallInt).toBits then
    throw s!"F32_OF_INT_MISMATCH({smallInt})"
  let ceilR := faRaw.ceil
  let floorR := faRaw.floor
  let roundR := faRaw.round
  checkSame4F32 s!"F32_CEIL({hex32 u32})" fa.ceil.toBits ceilR.toBits (canonBits32 (cF32UnOp 3 u32)) (canonBits32 (cF32UnOp 3 (canonBits32 u32)))
  checkSame4F32 s!"F32_FLOOR({hex32 u32})" fa.floor.toBits floorR.toBits (canonBits32 (cF32UnOp 4 u32)) (canonBits32 (cF32UnOp 4 (canonBits32 u32)))
  checkSame4F32 s!"F32_ROUND({hex32 u32})" fa.round.toBits roundR.toBits (canonBits32 (cF32UnOp 5 u32)) (canonBits32 (cF32UnOp 5 (canonBits32 u32)))
  checkRawNotSignaling32 "F32_CEIL_RAW" ceilR
  checkRawNotSignaling32 "F32_FLOOR_RAW" floorR
  checkRawNotSignaling32 "F32_ROUND_RAW" roundR
  let scaleInt := scaleExp.toInt
  let cScaled32 := canonBits32 (cF32Ldexp u32 scaleExp)
  let fScaled32 := Float32.scaleB fa scaleInt
  let fRawScaled32 := Float32.scaleB faRaw scaleInt
  if fScaled32.toBits != cScaled32 || fRawScaled32.toBits != cScaled32 then
    throw s!"F32_SCALEB_MISMATCH u32={hex32 u32} exp={scaleInt}"
  let (sig32, exp32) := fa.frExp
  let (sig32Raw, exp32Raw) := faRaw.frExp
  let (cSig32, cExp32) := cF32Frexp u32
  if ma.isFinite then
    if sig32.toBits != cSig32 || sig32Raw.toBits != cSig32 || exp32 != cExp32.toInt || exp32Raw != cExp32.toInt then
      throw s!"F32_FREXP_MISMATCH u32={hex32 u32}"
  else
    if sig32.toBits != canonBits32 u32 || sig32Raw.toBits != canonBits32 u32 then
      throw s!"F32_FREXP_NONFINITE_MISMATCH u32={hex32 u32}"
  let str32 := Float32.toString fa
  if str32.isEmpty || str32 != Float32.toString faRaw then
    throw s!"F32_TO_STRING_MISMATCH u32={hex32 u32}"
  let pyExt : PyExternItem := {
    isFloat32 := true
    bits := UInt64.ofNat (canonBits32 u32).toNat
    scaleExp := scaleExp
    ceilBits := UInt64.ofNat fa.ceil.toBits.toNat
    floorBits := UInt64.ofNat fa.floor.toBits.toNat
    roundBits := UInt64.ofNat fa.round.toBits.toNat
    frexpSigBits := UInt64.ofNat sig32.toBits.toNat
    frexpExp := exp32
    scaleBBits := UInt64.ofNat fScaled32.toBits.toNat
  }
  let mut bkts : List CoverageBucket := []
  if ma.isFinite then
    bkts := bucket "extern" "float32.ops" :: bkts
  if u32 == 0x7f800000 || u32 == 0xff800000 || isSignalingNaNBits32 u32 then
    bkts := bucket "extern" "float32.inf_snan" :: bkts
  return (bkts, pyExt)

/--
Verify deterministic `Float` and `Float32` runtime externs (`frExp`, `scaleB` on `Int32`, `ceil`, `floor`,
`round`, `Float.toFloat32` / `Float32.toFloat`, `Float32` full ops, transcendentals, and `FloatArray` unboxing/boxing).

Note: `Float.scaleB` / `Float32.scaleB` are bounded to `Int32` (`[-2147483648, 2147483647]`) because upstream
Lean `v4.36.0-rc2` `lean_float_scaleb` / `lean_float32_scaleb` in `libleanrt` fail outside `Int32`:
`i = -2147483648` (`-2^31`) works via the scalar path, whereas for `i <= -2147483649 || i >= 2147483648`
non-scalar exponents corrupt `-0.0`, `±Inf`, and `NaN` to `+0.0`, and `i <= -2147483649` also corrupts all
negative finite numbers to `+0.0`.
Note also: `Lean.JsonNumber.fromFloat?` in Lean `v4.36.0-rc2` routes through `Float.toString` (`%f`, 6 decimals),
which truncates values `< 1e-6`, loses `-0.0` sign, and expands `DBL_MAX` to 316 bytes.
-/
private def checkExternCase (u : UInt64) (u32 : UInt32) (scaleExp : Int32) :
    Except String (List CoverageBucket × Array PyExternItem) := do
  let f := Float.ofBits u
  let fRaw := rawDoubleFromBits u
  let m := Float.Model.ofBits u
  let expBits := canonBits u
  let ceilRaw := fRaw.ceil
  let floorRaw := fRaw.floor
  let roundRaw := fRaw.round
  checkSame4 s!"CEIL({hex64 u})" f.ceil.toBits ceilRaw.toBits (canonBits (cUnOp 3 u)) (canonBits (cUnOp 3 expBits))
  checkSame4 s!"FLOOR({hex64 u})" f.floor.toBits floorRaw.toBits (canonBits (cUnOp 4 u)) (canonBits (cUnOp 4 expBits))
  checkSame4 s!"ROUND({hex64 u})" f.round.toBits roundRaw.toBits (canonBits (cUnOp 5 u)) (canonBits (cUnOp 5 expBits))
  checkRawNotSignaling "CEIL_RAW" ceilRaw
  checkRawNotSignaling "FLOOR_RAW" floorRaw
  checkRawNotSignaling "ROUND_RAW" roundRaw
  let scaleInt := scaleExp.toInt
  let cScaled := canonBits (cLdexp u scaleExp)
  let fScaled := Float.scaleB f scaleInt
  let fRawScaled := Float.scaleB fRaw scaleInt
  if fScaled.toBits != cScaled || fRawScaled.toBits != cScaled then
    throw s!"SCALEB_MISMATCH u={hex64 u} exp={scaleInt} rt={hex64 fScaled.toBits} raw={hex64 fRawScaled.toBits} c={hex64 cScaled}"
  let mut bkts : List CoverageBucket := []
  if m.isFinite && f.ceil.toBits != f.floor.toBits then
    bkts := bucket "extern" "round.ceil_floor_round" :: bkts
  if m.isFinite && scaleExp != 0 then
    bkts := bucket "extern" "scaleB.int32" :: bkts
  let (sigF, expF) := f.frExp
  let (sigRaw, expRaw) := fRaw.frExp
  let (cSig, cExp) := cFrexp u
  if m.isFinite then
    if sigF.toBits != cSig || sigRaw.toBits != cSig || expF != cExp.toInt || expRaw != cExp.toInt then
      throw s!"FREXP_MISMATCH u={hex64 u} rt=({hex64 sigF.toBits},{expF}) raw=({hex64 sigRaw.toBits},{expRaw}) c=({hex64 cSig},{cExp.toInt})"
    bkts := bucket "extern" "frExp.finite" :: bkts
  else
    if sigF.toBits != expBits || sigRaw.toBits != expBits then
      throw s!"FREXP_NONFINITE_MISMATCH u={hex64 u} rt={hex64 sigF.toBits} raw={hex64 sigRaw.toBits} exp={hex64 expBits}"
    bkts := bucket "extern" "frExp.nonfinite" :: bkts
  checkFloatTranscendental s!"SIN({hex64 u})" f fRaw Float.sin (canonBits (cTrans1 0 expBits))
  checkFloatTranscendental s!"COS({hex64 u})" f fRaw Float.cos (canonBits (cTrans1 1 expBits))
  checkFloatTranscendental s!"TAN({hex64 u})" f fRaw Float.tan (canonBits (cTrans1 2 expBits))
  checkFloatTranscendental s!"ASIN({hex64 u})" f fRaw Float.asin (canonBits (cTrans1 3 expBits))
  checkFloatTranscendental s!"ACOS({hex64 u})" f fRaw Float.acos (canonBits (cTrans1 4 expBits))
  checkFloatTranscendental s!"ATAN({hex64 u})" f fRaw Float.atan (canonBits (cTrans1 5 expBits))
  checkFloatTranscendental s!"SINH({hex64 u})" f fRaw Float.sinh (canonBits (cTrans1 6 expBits))
  checkFloatTranscendental s!"COSH({hex64 u})" f fRaw Float.cosh (canonBits (cTrans2 0 expBits))
  checkFloatTranscendental s!"TANH({hex64 u})" f fRaw Float.tanh (canonBits (cTrans2 1 expBits))
  checkFloatTranscendental s!"ASINH({hex64 u})" f fRaw Float.asinh (canonBits (cTrans2 2 expBits))
  checkFloatTranscendental s!"ACOSH({hex64 u})" f fRaw Float.acosh (canonBits (cTrans2 3 expBits))
  checkFloatTranscendental s!"ATANH({hex64 u})" f fRaw Float.atanh (canonBits (cTrans2 4 expBits))
  checkFloatTranscendental s!"EXP({hex64 u})" f fRaw Float.exp (canonBits (cTrans2 5 expBits))
  checkFloatTranscendental s!"EXP2({hex64 u})" f fRaw Float.exp2 (canonBits (cTrans2 6 expBits))
  checkFloatTranscendental s!"LOG({hex64 u})" f fRaw Float.log (canonBits (cTrans3 0 expBits))
  checkFloatTranscendental s!"LOG2({hex64 u})" f fRaw Float.log2 (canonBits (cTrans3 1 expBits))
  checkFloatTranscendental s!"LOG10({hex64 u})" f fRaw Float.log10 (canonBits (cTrans3 2 expBits))
  checkFloatTranscendental s!"CBRT({hex64 u})" f fRaw Float.cbrt (canonBits (cTrans3 3 expBits))
  let f2 := rawDoubleFromBits (cF32ToF64 u32)
  let atan2C := canonBits (cBinOp 5 expBits (canonBits (cF32ToF64 u32)))
  if (Float.atan2 f f2).toBits != atan2C || (Float.atan2 fRaw f2).toBits != atan2C then
    throw s!"ATAN2({hex64 u},{hex32 u32})"
  let fStr := Float.toString f
  if fStr.isEmpty || fStr != Float.toString fRaw then
    throw s!"FLOAT_TO_STRING_MISMATCH u={hex64 u}"
  let f32 := f.toFloat32
  let f32Raw := fRaw.toFloat32
  let cF32 := canonBits32 (cF64ToF32 u)
  if f32.toBits != cF32 || f32Raw.toBits != cF32 then
    throw s!"TO_FLOAT32_MISMATCH u={hex64 u} rt={hex32 f32.toBits} raw={hex32 f32Raw.toBits} c={hex32 cF32}"
  checkRawNotSignaling32 "TO_FLOAT32_RAW" f32Raw
  let f32In := Float32.ofBits u32
  let f32InRaw := rawFloat32FromBits u32
  if f32In.toBits != canonBits32 u32 || f32InRaw.toBits != canonBits32 u32 then
    throw s!"FLOAT32_BITS_MISMATCH u32={hex32 u32}"
  let backF64 := f32In.toFloat
  let backF64Raw := f32InRaw.toFloat
  let cBackF64 := canonBits (cF32ToF64 u32)
  if backF64.toBits != cBackF64 || backF64Raw.toBits != cBackF64 then
    throw s!"FLOAT32_TO_FLOAT_MISMATCH u32={hex32 u32} rt={hex64 backF64.toBits} raw={hex64 backF64Raw.toBits} c={hex64 cBackF64}"
  checkRawNotSignaling "FLOAT32_TO_FLOAT_RAW" backF64Raw
  if !(Float32.ofBits u32).isNaN then
    bkts := bucket "extern" "float32.cast" :: bkts
  let (f32Bkts, pyExt32) ← checkFloat32Full u u32 scaleExp
  bkts := f32Bkts ++ bkts
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
  let pyExt64 : PyExternItem := {
    isFloat32 := false
    bits := expBits
    scaleExp := scaleExp
    ceilBits := f.ceil.toBits
    floorBits := f.floor.toBits
    roundBits := f.round.toBits
    frexpSigBits := sigF.toBits
    frexpExp := expF
    scaleBBits := fScaled.toBits
  }
  return (bkts, #[pyExt64, pyExt32])

private def checkCase (c : FloatFuzzCase) :
    Except String (List CoverageBucket × List (String × String) × PyOracleBatch) := do
  match c with
  | .parseStr s =>
    let (bkts, errHits, pyItem?) ← checkParseStr s
    let parses := match pyItem? with | some it => #[it] | none => #[]
    return (bkts, errHits, { parses })
  | .checkBits u =>
    let (bkts, fmtItem) ← checkBitsCase u
    return (bkts, [], { formats := #[fmtItem], reprBits := #[u] })
  | .checkBinOp ua ub =>
    let bkts ← checkBinOpCase ua ub
    return (bkts, [], {})
  | .checkFma ua ub uc =>
    let bkts ← checkFmaCase ua ub uc
    return (bkts, [], {})
  | .checkIntConv u =>
    let (bkts, pyInts) ← checkIntConvCase u
    return (bkts, [], { intFloats := pyInts })
  | .checkSci m negExp e =>
    let (bkts, pyItem) ← checkSciCase m negExp e
    return (bkts, [], { parses := #[pyItem] })
  | .checkExtern u u32 scaleExp =>
    let (bkts, pyExts) ← checkExternCase u u32 scaleExp
    return (bkts, [], { externs := pyExts })

private def appendBatch (a b : PyOracleBatch) : PyOracleBatch :=
  { parses := a.parses ++ b.parses
    formats := a.formats ++ b.formats
    reprBits := a.reprBits ++ b.reprBits
    intFloats := a.intFloats ++ b.intFloats
    externs := a.externs ++ b.externs }

private def checkEpisodeWithPy (client : PyOracleClient) (trace : Array FloatFuzzCase)
    (emitErrHits : Bool := false) :
    IO (Except String (List CoverageBucket)) := do
  let mut bkts : List CoverageBucket := []
  let mut errHits : List (String × String) := []
  let mut batch : PyOracleBatch := {}
  for c in trace do
    match checkCase c with
    | .error err => return .error err
    | .ok (bs, eh, cBatch) =>
      bkts := bs ++ bkts
      errHits := eh ++ errHits
      batch := appendBatch batch cBatch
  if batch.isEmpty then
    if emitErrHits then
      for (op, kind) in errHits do
        Fuzz.Common.logErrHit op kind "real"
    return .ok bkts
  match ← flushPyBatch client batch with
  | .error err => return .error err
  | .ok () =>
    if emitErrHits then
      for (op, kind) in errHits do
        Fuzz.Common.logErrHit op kind "real"
    bkts := bucket "python_oracle" "ok.batch_verified" :: bkts
    if !batch.externs.isEmpty then
      bkts := bucket "python_oracle" "ok.extern_fraction" :: bkts
    return .ok bkts

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
  bucket "extern" "frExp.nonfinite",
  bucket "extern" "scaleB.int32",
  bucket "extern" "round.ceil_floor_round",
  bucket "extern" "float32.cast",
  bucket "extern" "float32.ops",
  bucket "extern" "float32.inf_snan",
  bucket "extern" "floatArray.box",
  bucket "toml_roundtrip" "ok.float_bits",
  bucket "python_oracle" "ok.batch_verified",
  bucket "python_oracle" "ok.extern_fraction"
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
  let limit := min arr.size 64
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

private def shrinkMantissaBody (signStr suffixStr : String) (body : List Char) : List String := Id.run do
  let mut cands : List String := []
  let bodyStr := String.ofList body
  match bodyStr.splitOn "." with
  | [intPart, fracPart] =>
    let intChars := intPart.toList
    if !intChars.isEmpty then
      cands := cands ++ [s!"{signStr}{intPart}{suffixStr}"]
    for intCand in shrinkDigitsList intChars do
      cands := cands ++ [s!"{signStr}{String.ofList intCand}.{fracPart}{suffixStr}"]
    for fracCand in shrinkDigitsList fracPart.toList do
      cands := cands ++ [s!"{signStr}{intPart}.{String.ofList fracCand}{suffixStr}"]
  | _ =>
    for sigCand in shrinkDigitsList body do
      cands := cands ++ [s!"{signStr}{String.ofList sigCand}{suffixStr}"]
  return cands

private def shrinkStringLocal (s : String) : List String := Id.run do
  if s.length > 1024 then
    return []
  let mut cands : List String := []
  let noUnder := stripUnderscores s
  if noUnder != s then
    cands := cands ++ [noUnder]
  if let some (sig, sep, expStr) := splitFirstExp? s then
    let (signStr, body) :=
      if sig.startsWith "-" then ("-", sig.toList.drop 1)
      else if sig.startsWith "+" then ("+", sig.toList.drop 1)
      else ("", sig.toList)
    cands := cands ++ shrinkMantissaBody signStr s!"{sep}{expStr}" body
    let (expSign, expDigits) :=
      if expStr.startsWith "-" then ("-", expStr.toList.drop 1)
      else if expStr.startsWith "+" then ("+", expStr.toList.drop 1)
      else ("", expStr.toList)
    for expCand in shrinkDigitsList expDigits do
      cands := cands ++ [s!"{sig}{sep}{expSign}{String.ofList expCand}"]
  else
    let (signStr, body) :=
      if s.startsWith "-" then ("-", s.toList.drop 1)
      else if s.startsWith "+" then ("+", s.toList.drop 1)
      else ("", s.toList)
    cands := cands ++ shrinkMantissaBody signStr "" body
  let arr := s.toList.toArray
  if arr.size > 1 then
    cands := cands ++ [String.ofList (arr.extract 0 (arr.size / 2)).toList]
    cands := cands ++ [String.ofList (arr.extract (arr.size / 2) arr.size).toList]
  for i in List.range arr.size do
    let deleted := (arr.extract 0 i ++ arr.extract (i + 1) arr.size).toList
    cands := cands ++ [String.ofList deleted]
  return (cands.filter (fun c => c.length < s.length || (c.length == s.length && c < s))).eraseDups

private def shrinkStringDdmin (failsStr : String → IO Bool) (s : String) : IO String := do
  let mut cur := s.toList.toArray
  if cur.isEmpty then
    return s
  if ← failsStr "" then
    return ""
  let mut chunk := max 1 (cur.size / 2)
  let mut probes := 0
  let maxLargeProbes := 256
  while chunk >= 1 && cur.size > 1 do
    if cur.size > 512 && probes >= maxLargeProbes then
      break
    let mut improved := false
    let mut start := 0
    while start < cur.size && cur.size > 1 do
      if cur.size > 512 && probes >= maxLargeProbes then
        break
      let stop := min cur.size (start + chunk)
      let candArr := cur.extract 0 start ++ cur.extract stop cur.size
      let candStr := String.ofList candArr.toList
      probes := probes + 1
      if ← failsStr candStr then
        cur := candArr
        improved := true
      else
        start := start + chunk
    if !improved then
      if chunk == 1 then
        break
      chunk := max 1 (chunk / 2)
  let mut out := String.ofList cur.toList
  if out.length <= 1024 then
    for _ in List.range 32 do
      let mut replaced := false
      for cand in shrinkStringLocal out do
        if ← failsStr cand then
          out := cand
          replaced := true
          break
      if !replaced then
        break
  return out

private def binaryShrinkNat (failsNat : Nat → IO Bool) (n : Nat) : IO Nat := do
  if n == 0 then
    return 0
  if ← failsNat 0 then
    return 0
  if n == 1 then
    return 1
  if ← failsNat 1 then
    return 1
  let mut lo : Nat := 1
  let mut hi : Nat := n
  while lo + 1 < hi do
    let mid := lo + (hi - lo) / 2
    if ← failsNat mid then
      hi := mid
    else
      lo := mid
  return hi

private def shrinkFloatCase : FloatFuzzCase → List FloatFuzzCase
  | .parseStr s => (shrinkStringLocal s).map .parseStr
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
    (if negExp then [.checkSci m false e] else []) ++
      (if m > 0 then [.checkSci 0 negExp e] else []) ++
      (if e > 0 then [.checkSci m negExp 0] else [])
  | .checkExtern u u32 sc =>
    (shrinkU64 u).map (fun u' => .checkExtern u' u32 sc) ++
      (shrinkU32 u32).map (fun u32' => .checkExtern u u32' sc) ++
      (shrinkInt32 sc).map (fun sc' => .checkExtern u u32 sc')

private def shrinkSpecialAt (fails : Array FloatFuzzCase → IO Bool) (cur : Array FloatFuzzCase) (idx : Nat) :
    IO (Array FloatFuzzCase) := do
  match cur[idx]? with
  | some (.parseStr s) =>
    let s' ← shrinkStringDdmin (fun cand => fails (cur.setIfInBounds idx (.parseStr cand))) s
    return cur.setIfInBounds idx (.parseStr s')
  | some (.checkSci m negExp e) =>
    let neg' ←
      if negExp && (← fails (cur.setIfInBounds idx (.checkSci m false e))) then pure false
      else pure negExp
    let m' ← binaryShrinkNat (fun mCand => fails (cur.setIfInBounds idx (.checkSci mCand neg' e))) m
    let e' ← binaryShrinkNat (fun eCand => fails (cur.setIfInBounds idx (.checkSci m' neg' eCand))) e
    return cur.setIfInBounds idx (.checkSci m' neg' e')
  | _ => return cur

private def shrinkToFixedPoint (fails : Array FloatFuzzCase → IO Bool) (trace : Array FloatFuzzCase) :
    IO (Array FloatFuzzCase) := do
  let mut cur ← shrinkTrace fails trace
  for _ in List.range 16 do
    let prev := cur
    for idx in List.range cur.size do
      cur ← shrinkSpecialAt fails cur idx
    cur ← shrinkElements shrinkFloatCase fails cur
    cur ← shrinkTrace fails cur
    if cur == prev then
      break
  return cur

private def errorClassTag (err : String) : String := Id.run do
  let pyPrefix := "PYTHON_ORACLE_MISMATCH: "
  if err.startsWith pyPrefix then
    let rest := (err.drop pyPrefix.length).toString
    let tagPart := (rest.splitOn ":").headD rest
    return pyPrefix ++ tagPart
  let mut out := ""
  for c in err.toList do
    if c == '(' || c == ' ' || c == '=' || c == ':' then
      break
    out := out.push c
  return out

private def runTraceChecked (client : PyOracleClient) (tracker : CoverageTracker)
    (trace : Array FloatFuzzCase) : IO CoverageTracker := do
  match ← checkEpisodeWithPy client trace true with
  | .ok bkts =>
    let mut tr := tracker
    for b in bkts do
      tr := tr.record b.op b.bucket
    return tr
  | .error err =>
    if err.startsWith "PYTHON_ORACLE_EOF" then
      throw (IO.userError s!"FLOAT_FUZZ_MISMATCH err={err} trace_size={trace.size} trace={repr trace}")
    let origTag := errorClassTag err
    let fails (cand : Array FloatFuzzCase) : IO Bool := do
      match ← checkEpisodeWithPy client cand false with
      | .ok _ => return false
      | .error e =>
        if e.startsWith "PYTHON_ORACLE_EOF" then
          throw (IO.userError s!"FLOAT_FUZZ_MISMATCH err={e} original_err={err} trace_size={trace.size} trace={repr trace}")
        return errorClassTag e == origTag
    let shrunk ← shrinkToFixedPoint fails trace
    let shrunkErr := match ← checkEpisodeWithPy client shrunk false with
      | .error e => e
      | .ok _ => err
    throw (IO.userError s!"FLOAT_FUZZ_MISMATCH err={shrunkErr} original_err={err} shrunk={repr shrunk}")

private def verifyRoundToNearest : IO Unit := do
  unless ← cIsRoundToNearest do
    throw (IO.userError "FENV_ROUNDING_MODE_NOT_TONEAREST")

private def runFloatSuite (steps : Nat) (seedVal : UInt64) (isSmoke : Bool) : IO Unit := do
  verifyRoundToNearest
  let client ← startPyOracleClient
  try
    let mut smokeTracker := CoverageTracker.empty
    if isSmoke then
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
    let reportTracker :=
      if isSmoke then
        smokeTracker.merge randTracker
      else
        randTracker
    assertCoverage "float" reportTracker requiredBuckets
    verifyRoundToNearest
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
  verifyRoundToNearest
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
  let bigStr := "1." ++ String.ofList (List.replicate 300000 '0') ++ "x"
  let failsBigStr (cand : Array FloatFuzzCase) : IO Bool := pure (cand.any fun
    | FloatFuzzCase.parseStr s => s.length >= 200000 && s.endsWith "x"
    | _ => false)
  let shrunkBig : Array FloatFuzzCase ← shrinkToFixedPoint failsBigStr #[FloatFuzzCase.checkBits 0, .parseStr bigStr, .checkBits 1]
  match shrunkBig[0]? with
  | some (FloatFuzzCase.parseStr s) =>
    if shrunkBig.size != 1 || s.length > 205000 || !s.endsWith "x" then
      throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_BIGSTR: unexpected len={s.length} size={shrunkBig.size}")
    IO.println s!"FLOAT_SHRINK_SELFTEST_BIGSTR_OK: len={s.length}"
  | other =>
    throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_BIGSTR: unexpected {repr other}")
  let failsBigSci (cand : Array FloatFuzzCase) : IO Bool := pure (cand.any fun
    | .checkSci m _ e => m >= (1 <<< 53) && e >= 2049
    | _ => false)
  let shrunkSci ← shrinkToFixedPoint failsBigSci #[.checkBits 0, .checkSci 0xdeadbeefcafebabe true 12048]
  if shrunkSci != #[.checkSci (1 <<< 53) false 2049] then
    throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_SCI: unexpected {repr shrunkSci}")
  IO.println s!"FLOAT_SHRINK_SELFTEST_SCI_OK: shrunk={repr shrunkSci}"
  let snanProbe := rawDoubleFromBits 0x7ff0000000000001
  let minSnanRaw := rawBitsFromDouble (Float.minimum (-1.0) snanProbe)
  let powSnanDiff := (Float.pow 1.0 snanProbe).toBits != (Float.pow 1.0 Float.nan).toBits
  let snan32Probe := rawFloat32FromBits 0x7f800001
  let pow32SnanDiff := (Float32.pow 1.0 snan32Probe).toBits != (Float32.pow 1.0 Float32.nan).toBits
  IO.println s!"FLOAT_UPSTREAM_PROBE_OK: min_snan_raw={hex64 minSnanRaw} pow_snan_div={powSnanDiff} pow32_snan_div={pow32SnanDiff}"
  let client ← startPyOracleClient
  try
    let mut trace3 : Array FloatFuzzCase := Array.mkEmpty 12
    for _ in List.range 10 do
      trace3 := trace3.push (.parseStr "1.5")
    let (idx3, _) := rng.nextRange 0 10
    let injected3 := (trace3.extract 0 idx3).push (.parseStr "123_456.789") ++ trace3.extract idx3 trace3.size
    let buildPyParses (cand : Array FloatFuzzCase) : PyOracleBatch := Id.run do
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
      return { parses := items }
    let origErr ← match ← flushPyBatch client (buildPyParses injected3) with
      | .ok () => throw (IO.userError "FLOAT_SHRINK_SELFTEST_3: initial parse trace did not fail")
      | .error e => pure e
    let origTag := errorClassTag origErr
    let failsPyBug (cand : Array FloatFuzzCase) : IO Bool := do
      match ← flushPyBatch client (buildPyParses cand) with
      | .ok () => return false
      | .error e =>
        if e.startsWith "PYTHON_ORACLE_EOF" then
          throw (IO.userError e)
        return errorClassTag e == origTag
    let shrunk3 ← shrinkToFixedPoint failsPyBug injected3
    unless ← failsPyBug shrunk3 do
      throw (IO.userError "FLOAT_SHRINK_SELFTEST_3: Python oracle shrunk trace no longer triggers failure")
    if shrunk3.size != 1 then
      throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_3: expected size 1, got {shrunk3.size}")
    match shrunk3[0]! with
    | .parseStr s =>
      if s.length > 4 || !s.contains '9' then
        throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_3: unexpected shrunk={repr shrunk3}")
      IO.println s!"FLOAT_SHRINK_SELFTEST_3_OK: parse_shrunk={repr shrunk3} tag={origTag}"
    | _ =>
      throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_3: unexpected variant {repr shrunk3}")
    let buildExternBatch (cand : Array FloatFuzzCase) : Except String PyOracleBatch := do
      let mut exts : Array PyExternItem := #[]
      for c in cand do
        if let .checkExtern u u32 sc := c then
          let (_, itemArr) ← checkExternCase u u32 sc
          for item in itemArr do
            let tweaked :=
              if !item.isFloat32 && u != 0 then
                { item with ceilBits := 0 }
              else
                item
            exts := exts.push tweaked
      return { externs := exts }
    let injectedExt : Array FloatFuzzCase := #[
      .checkExtern 0 0 0,
      .checkExtern 0x4029000000000000 0x41200000 7,
      .checkExtern 0 0x3f800000 1
    ]
    let origExtErr ← match buildExternBatch injectedExt with
      | .error e => throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_3: buildExternBatch failed: {e}")
      | .ok batch =>
        match ← flushPyBatch client batch with
        | .ok () => throw (IO.userError "FLOAT_SHRINK_SELFTEST_3: initial extern trace did not fail")
        | .error e => pure e
    let origExtTag := errorClassTag origExtErr
    if origExtTag != "PYTHON_ORACLE_MISMATCH: E ceil mismatch" then
      throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_3: unexpected extern tag={repr origExtTag} err={origExtErr}")
    let failsExternBug (cand : Array FloatFuzzCase) : IO Bool := do
      match buildExternBatch cand with
      | .error _ => return false
      | .ok batch =>
        match ← flushPyBatch client batch with
        | .ok () => return false
        | .error e =>
          if e.startsWith "PYTHON_ORACLE_EOF" then
            throw (IO.userError e)
          return errorClassTag e == origExtTag
    let shrunkExt ← shrinkToFixedPoint failsExternBug injectedExt
    unless ← failsExternBug shrunkExt do
      throw (IO.userError "FLOAT_SHRINK_SELFTEST_3: extern shrunk trace no longer triggers failure")
    if shrunkExt != #[.checkExtern 1 0 0] then
      throw (IO.userError s!"FLOAT_SHRINK_SELFTEST_3: unexpected extern shrunk={repr shrunkExt}")
    IO.println s!"FLOAT_SHRINK_SELFTEST_3_EXTERN_OK: shrunk={repr shrunkExt} tag={origExtTag}"
    closePyOracleClient client
  catch e =>
    closePyOracleClientQuiet client
    throw e

/-- 4-way differential fuzzing suite for `Float` runtime, `Float32`, `NumParse`, `Toml`, `Float.Model`, C99, and Python 3. -/
def suite : FuzzSuite := {
  name := "float"
  description := "4-way differential fuzzer for Float/Float32 runtime, NumParse, Toml, Float.Model, C99 strtod_l/libm, and Python 3"
  runSmoke := fun cfg => do
    Fuzz.Common.recordSuiteSteps 400
    runFloatSuite 400 cfg.seed true
  runFuzz := fun cfg => do
    Fuzz.Common.recordSuiteSteps cfg.steps
    runFloatSuite cfg.steps cfg.seed false
  selfTestShrink := runFloatSelfTestShrink
}

end Fuzz.Float
