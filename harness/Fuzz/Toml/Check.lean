import Fuzz.Common.Coverage
import Fuzz.Common.Suite
import Fuzz.Toml.Oracle
import Fuzz.Toml.Gen
import LeanSwe.Toml.Interface
import LeanSweProofs.Toml.Model
import LeanSweProofs.NumParse.Model

namespace Fuzz.Toml

open Fuzz.Common
open LeanSwe.Toml

/-- Fixed required non-vacuous coverage buckets for `Fuzz.Toml.suite`. -/
def requiredBuckets : Array CoverageBucket := #[
  bucket "parse" "ok.key_bare",
  bucket "parse" "ok.key_basic",
  bucket "parse" "ok.key_literal",
  bucket "parse" "ok.key_dotted",
  bucket "parse" "ok.str_basic",
  bucket "parse" "ok.str_escape",
  bucket "parse" "ok.str_literal",
  bucket "parse" "ok.str_multiline_basic",
  bucket "parse" "ok.str_line_trim",
  bucket "parse" "ok.str_multiline_literal",
  bucket "parse" "ok.int_dec",
  bucket "parse" "ok.int_hex",
  bucket "parse" "ok.int_oct",
  bucket "parse" "ok.int_bin",
  bucket "parse" "ok.int_underscore",
  bucket "parse" "ok.float_frac",
  bucket "parse" "ok.float_exp",
  bucket "parse" "ok.float_special",
  bucket "parse" "ok.bool_true",
  bucket "parse" "ok.bool_false",
  bucket "parse" "ok.offset_datetime",
  bucket "parse" "ok.local_datetime",
  bucket "parse" "ok.local_date",
  bucket "parse" "ok.local_time",
  bucket "parse" "ok.datetime_frac",
  bucket "parse" "ok.year_zero",
  bucket "parse" "ok.inline_table_empty",
  bucket "parse" "ok.inline_table_nonempty",
  bucket "parse" "ok.array_empty",
  bucket "parse" "ok.array_nested_trailing",
  bucket "parse" "ok.table_header",
  bucket "parse" "ok.aot_header",
  bucket "parse" "ok.comments_blank_lines",
  bucket "parse" "ok.crlf",
  bucket "parse" "ok.no_trailing_newline",
  bucket "parse" "ok.deep_nested",
  bucket "parse" "err.parseError",
  bucket "parse" "err.duplicateKey",
  bucket "parse" "err.redefinedTable",
  bucket "parse" "err.immutableInlineTable",
  bucket "parse" "err.invalidUtf8OrControl",
  bucket "parse" "err.numericOverflow",
  bucket "parse" "err.duplicate_key",
  bucket "parse" "err.redefined_table",
  bucket "parse" "err.immutable_inline_table",
  bucket "parse" "err.control_or_bare_cr",
  bucket "parse" "err.bad_escape_or_surrogate",
  bucket "parse" "err.unclosed_string_or_bracket",
  bucket "parse" "err.leading_zero_or_bad_num",
  bucket "parse" "err.invalid_datetime",
  bucket "parse" "err.inline_table_syntax",
  bucket "parse" "err.trailing_garbage",
  bucket "format" "ok.empty",
  bucket "format" "ok.roundtrip",
  bucket "python_tomllib" "ok.parse_parity",
  bucket "python_tomllib" "ok.format_parity",
  bucket "python_tomllib" "ok.int64_overflow_divergence",
  bucket "python_tomllib" "ok.year_zero_divergence",
  bucket "encode_decode" "ok.roundtrip",
  bucket "decode" "err.decodeError",
  bucket "getTable" "ok",
  bucket "getTable" "err.typeMismatch",
  bucket "getArray" "ok",
  bucket "getArray" "err.typeMismatch",
  bucket "getField" "ok",
  bucket "getField" "err.missingField",
  bucket "getField" "err.decodeError",
  bucket "getOptField" "ok.some",
  bucket "getOptField" "ok.none_absent",
  bucket "getOptField" "err.decodeError",
  bucket "getPath" "ok",
  bucket "getPath" "err.missingField",
  bucket "getPath" "err.typeMismatch",
  bucket "getPath" "err.decodeError"
]

private def tomlErrorKindShort : TomlErrorKind → String
  | .parseError => "parseError"
  | .duplicateKey => "duplicateKey"
  | .redefinedTable => "redefinedTable"
  | .immutableInlineTable => "immutableInlineTable"
  | .invalidUtf8OrControl => "invalidUtf8OrControl"
  | .numericOverflow => "numericOverflow"
  | .missingField => "missingField"
  | .typeMismatch => "typeMismatch"
  | .decodeError => "decodeError"

private def tomlErrorKindCtor (k : TomlErrorKind) : String :=
  "LeanSwe.Toml.TomlErrorKind." ++ tomlErrorKindShort k

private def isAllowedParseErrKind : TomlErrorKind → Bool
  | .parseError | .duplicateKey | .redefinedTable
  | .immutableInlineTable | .invalidUtf8OrControl | .numericOverflow => true
  | .missingField | .typeMismatch | .decodeError => false

private def emitLiveErrHit (emit : Bool) (qualOp : String) (e : TomlError) : IO Unit := do
  if emit then
    Fuzz.Common.logErrHit qualOp (tomlErrorKindCtor e.kind) "real"

private def verifyErrShape (opLabel : String) (e : TomlError) (expKind : TomlErrorKind)
    (expPath : Option String) : Except String Unit := do
  if e.kind != expKind then
    throw s!"{opLabel}_ERR_KIND_MISMATCH: got={reprStr e.kind} expected={reprStr expKind}"
  if e.path != expPath then
    throw s!"{opLabel}_ERR_PATH_MISMATCH: got={reprStr e.path} expected={reprStr expPath}"
  if e.message.isEmpty then
    throw s!"{opLabel}_EMPTY_ERR_MSG"

/-- Verify a year-`0000` accepted TOML document by checking both:
1. Python `tomllib.loads` rejects `raw` with `Invalid date or datetime`, and
2. Rewriting value-position `0000-MM-DD` tokens to leap year `2000-MM-DD` succeeds in `parseFn`
   and in Python `tomllib.loads` with exact AST parity modulo `0 -> 2000`. -/
def verifyAndQueueYearZero (parseFn : String → Except TomlError TomlTable)
    (raw : String) (parsed : TomlTable) (labelPfx : String) (batch : PyOracleBatch) :
    Except String PyOracleBatch := do
  let rewrittenRaw := rewriteYearZeroTokensTo2000 raw
  if rewrittenRaw == raw then
    throw s!"YEAR_ZERO_REWRITE_NOOP:{labelPfx}: raw={reprStr (raw.take 80).toString}"
  let expected2000 := mapYearZeroTo2000Table parsed
  match parseFn rewrittenRaw with
  | .error e =>
    throw s!"YEAR_ZERO_REWRITE_PARSE_ERR:{labelPfx}: err={reprStr e} raw={reprStr (rewrittenRaw.take 80).toString}"
  | .ok parsed2000 =>
    if hasYearZeroTable parsed2000 then
      throw s!"YEAR_ZERO_REWRITE_STILL_HAS_YEAR0:{labelPfx}"
    if encodeCanonTomlModel parsed2000 != encodeCanonTomlModel expected2000 then
      throw s!"YEAR_ZERO_REWRITE_MODEL_MISMATCH:{labelPfx}"
    let pyTlv2000 := encodeCanonTomlPy parsed2000
    if pyTlv2000 != encodeCanonTomlPy expected2000 then
      throw s!"YEAR_ZERO_REWRITE_PY_BITS_MISMATCH:{labelPfx}"
    let nextParses := batch.parses
      |>.push {
        rawBytes := raw.toUTF8
        mode := .yearZero
        expectedPyTlv := ByteArray.empty
        label := s!"{labelPfx}:origYearZero"
      }
      |>.push {
        rawBytes := rewrittenRaw.toUTF8
        mode := .ok
        expectedPyTlv := pyTlv2000
        label := s!"{labelPfx}:rewritten2000"
      }
    return { batch with parses := nextParses }

private def checkValidRenderCase (doc : TomlTable) (raw : String) (tags : List String)
    (batch : PyOracleBatch) : Except String (List CoverageBucket × PyOracleBatch) := do
  let mut bkts : List CoverageBucket := []
  let mut nextBatch := batch
  for tg in tags do
    bkts := bucket "parse" s!"ok.{tg}" :: bkts
  if !Model.wellFormedTableBool doc then
    throw "VALID_RENDER_DOC_NOT_WF"
  match LeanSwe.Toml.parse raw with
  | .error e =>
    throw s!"VALID_RENDER_PARSE_ERR: err={reprStr e} raw={reprStr (raw.take 80).toString}"
  | .ok parsed =>
    if !Model.wellFormedTableBool parsed then
      throw "VALID_RENDER_PARSED_NOT_WF"
    let expModelTlv := encodeCanonTomlModel doc
    let gotModelTlv := encodeCanonTomlModel parsed
    if gotModelTlv != expModelTlv then
      throw s!"VALID_RENDER_MODEL_EQUIV_MISMATCH: raw={reprStr (raw.take 80).toString}"
    let pyTlv := encodeCanonTomlPy parsed
    let formatted := LeanSwe.Toml.format parsed
    if parsed.isEmpty then
      if formatted != "" then
        throw s!"FORMAT_EMPTY_CONTRACT_VIOLATION: got={reprStr formatted}"
      bkts := bucket "format" "ok.empty" :: bkts
    else
      if !formatted.endsWith "\n" || formatted.contains '\r' then
        throw s!"FORMAT_NONEMPTY_CONTRACT_VIOLATION: got={reprStr (formatted.take 80).toString}"
      match LeanSwe.Toml.parse formatted with
      | .error fe =>
        throw s!"FORMAT_ROUNDTRIP_PARSE_ERR: err={reprStr fe}"
      | .ok reparsed =>
        if !Model.wellFormedTableBool reparsed then
          throw "FORMAT_ROUNDTRIP_NOT_WF"
        if encodeCanonTomlModel reparsed != gotModelTlv then
          throw "FORMAT_ROUNDTRIP_MODEL_MISMATCH"
        if encodeCanonTomlPy reparsed != pyTlv then
          throw "FORMAT_ROUNDTRIP_PY_BITS_MISMATCH"
        if LeanSwe.Toml.format reparsed != formatted then
          throw "FORMAT_IDEMPOTENCE_MISMATCH"
      bkts := bucket "format" "ok.roundtrip" :: bkts
    if hasYearZeroTable parsed then
      nextBatch ← verifyAndQueueYearZero LeanSwe.Toml.parse raw parsed "validYearZero" nextBatch
      nextBatch ← verifyAndQueueYearZero LeanSwe.Toml.parse formatted parsed "formatYearZero" nextBatch
      bkts := bucket "python_tomllib" "ok.year_zero_divergence" :: bkts
    else
      nextBatch := {
        parses := nextBatch.parses.push {
          rawBytes := raw.toUTF8
          mode := .ok
          expectedPyTlv := pyTlv
          label := "validRender"
        }
        formats := nextBatch.formats.push {
          rendered := formatted
          expectedPyTlv := pyTlv
          label := "formatRender"
        }
      }
      bkts := bucket "python_tomllib" "ok.parse_parity" ::
        bucket "python_tomllib" "ok.format_parity" :: bkts
    return (bkts, nextBatch)

private def checkInt64OverflowCase (raw : String) (strictValidToml : Bool) (emitErr : Bool)
    (batch : PyOracleBatch) : IO (Except String (List CoverageBucket × PyOracleBatch)) := do
  match LeanSwe.Toml.parse raw with
  | .ok _ =>
    return .error s!"INT64_OVERFLOW_UNEXPECTED_OK: raw={reprStr (raw.take 80).toString}"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.parse" e
    if e.kind != .numericOverflow then
      return .error s!"INT64_OVERFLOW_WRONG_ERR_KIND: got={reprStr e.kind} raw={reprStr (raw.take 80).toString}"
    if e.message.isEmpty then
      return .error "INT64_OVERFLOW_EMPTY_MSG"
    let mode := if strictValidToml then PyParseMode.errOverflowStrict else .errOverflowAny
    let nextBatch := { batch with
      parses := batch.parses.push {
        rawBytes := raw.toUTF8
        mode := mode
        expectedPyTlv := ByteArray.empty
        label := "int64Overflow"
      }
    }
    let bkts := [
      bucket "parse" "err.numericOverflow",
      bucket "python_tomllib" "ok.int64_overflow_divergence"
    ]
    return .ok (bkts, nextBatch)

private def checkMalformedStrCase (raw : String) (tag : String) (emitErr : Bool)
    (batch : PyOracleBatch) : IO (Except String (List CoverageBucket × PyOracleBatch)) := do
  let mut bkts : List CoverageBucket := []
  match LeanSwe.Toml.parse raw with
  | .ok parsed =>
    if !Model.wellFormedTableBool parsed then
      return .error "MALFORMED_ACCEPT_NOT_WF"
    if hasYearZeroTable parsed then
      match verifyAndQueueYearZero LeanSwe.Toml.parse raw parsed s!"malformedYearZero:{tag}" batch with
      | .error yzErr => return .error yzErr
      | .ok nextBatch =>
        return .ok ([bucket "python_tomllib" "ok.year_zero_divergence"], nextBatch)
    else
      let pyTlv := encodeCanonTomlPy parsed
      let nextBatch := { batch with
        parses := batch.parses.push {
          rawBytes := raw.toUTF8
          mode := .ok
          expectedPyTlv := pyTlv
          label := s!"malformedAccept:{tag}"
        }
      }
      return .ok ([bucket "python_tomllib" "ok.parse_parity"], nextBatch)
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.parse" e
    if !isAllowedParseErrKind e.kind then
      return .error s!"PARSE_DISALLOWED_ERR_KIND: got={reprStr e.kind}"
    if e.message.isEmpty then
      return .error "PARSE_EMPTY_ERR_MSG"
    bkts := bucket "parse" s!"err.{tomlErrorKindShort e.kind}" :: bkts
    if !tag.isEmpty then
      bkts := bucket "parse" s!"err.{tag}" :: bkts
    let pyMode := if e.kind == .numericOverflow then PyParseMode.errOverflowAny else .errSyntax
    let nextBatch := { batch with
      parses := batch.parses.push {
        rawBytes := raw.toUTF8
        mode := pyMode
        expectedPyTlv := ByteArray.empty
        label := s!"malformedReject:{tag}"
      }
    }
    let pyBkt :=
      if e.kind == .numericOverflow then bucket "python_tomllib" "ok.int64_overflow_divergence"
      else bucket "python_tomllib" "ok.parse_parity"
    bkts := pyBkt :: bkts
    return .ok (bkts, nextBatch)

private def checkEncodeDecodeEq {α : Type} [ToToml α] [FromToml α] [BEq α]
    (label : String) (val : α) : Except String Unit := do
  let enc := LeanSwe.Toml.encode val
  if enc != Model.encodeModel val then
    throw s!"ENCODE_MODEL_MISMATCH:{label}"
  match LeanSwe.Toml.decode (α := α) enc with
  | .error e => throw s!"ENCODE_DECODE_ERR:{label}:{reprStr e}"
  | .ok dec =>
    if dec != val then
      throw s!"ENCODE_DECODE_VAL_MISMATCH:{label}"
  let wrapped : TomlTable := #[("v", enc)]
  if Model.wellFormedTableBool wrapped then
    let fmt := LeanSwe.Toml.format wrapped
    match LeanSwe.Toml.parse fmt with
    | .error e => throw s!"ENCODE_FORMAT_PARSE_ERR:{label}:{reprStr e}"
    | .ok parsed =>
      match LeanSwe.Toml.getField (α := α) parsed "v" with
      | .error e => throw s!"ENCODE_FORMAT_GETFIELD_ERR:{label}:{reprStr e}"
      | .ok dec2 =>
        if dec2 != val then
          throw s!"ENCODE_FORMAT_ROUNDTRIP_MISMATCH:{label}"

mutual
  private def tomlValueBitwiseEq : TomlValue → TomlValue → Bool
    | .bool a, .bool b => a == b
    | .int a, .int b => a == b
    | .float a, .float b => (a.isNaN && b.isNaN) || (!a.isNaN && !b.isNaN && a.toBits == b.toBits)
    | .string a, .string b => a == b
    | .offsetDateTime a, .offsetDateTime b => a == b
    | .localDateTime a, .localDateTime b => a == b
    | .localDate a, .localDate b => a == b
    | .localTime a, .localTime b => a == b
    | .array xs, .array ys => tomlListBitwiseEq xs.toList ys.toList
    | .table xs, .table ys => tomlEntriesBitwiseEq xs.toList ys.toList
    | _, _ => false
  termination_by a _ => sizeOf a
  decreasing_by
    · exact Nat.lt_trans (Model.sizeOf_toList_lt_array _) (by simp +arith)
    · exact Nat.lt_trans (Model.sizeOf_toList_lt_array _) (by simp +arith)

  private def tomlListBitwiseEq : List TomlValue → List TomlValue → Bool
    | [], [] => true
    | x :: xs, y :: ys => tomlValueBitwiseEq x y && tomlListBitwiseEq xs ys
    | _, _ => false
  termination_by xs _ => sizeOf xs
  decreasing_by all_goals simp +arith

  private def tomlEntriesBitwiseEq : List (String × TomlValue) → List (String × TomlValue) → Bool
    | [], [] => true
    | (kx, vx) :: xs, (ky, vy) :: ys =>
      kx == ky && tomlValueBitwiseEq vx vy && tomlEntriesBitwiseEq xs ys
    | _, _ => false
  termination_by xs _ => sizeOf xs
  decreasing_by all_goals simp +arith
end

private def checkEncodeDecodeFloat (f : Float) : Except String Unit := do
  let enc := LeanSwe.Toml.encode f
  if !tomlValueBitwiseEq enc (Model.encodeModel f) then
    throw "ENCODE_MODEL_MISMATCH:Float"
  match LeanSwe.Toml.decode (α := Float) enc with
  | .error e => throw s!"ENCODE_DECODE_ERR:Float:{reprStr e}"
  | .ok g =>
    let ok := if f.isNaN then g.isNaN else g.toBits == f.toBits
    if !ok then
      throw "ENCODE_DECODE_BITS_MISMATCH:Float"
  let wrapped : TomlTable := #[("f", enc)]
  let fmt := LeanSwe.Toml.format wrapped
  match LeanSwe.Toml.parse fmt with
  | .error e => throw s!"ENCODE_FORMAT_PARSE_ERR:Float:{reprStr e}"
  | .ok parsed =>
    match LeanSwe.Toml.getField (α := Float) parsed "f" with
    | .error e => throw s!"ENCODE_FORMAT_GETFIELD_ERR:Float:{reprStr e}"
    | .ok g2 =>
      let ok2 := if f.isNaN then g2.isNaN else g2.toBits == f.toBits
      if !ok2 then
        throw "ENCODE_FORMAT_BITS_MISMATCH:Float"

private def checkEncodeDecodeTable (doc : TomlTable) : Except String Unit := do
  let enc := LeanSwe.Toml.encode doc
  if !tomlValueBitwiseEq enc (Model.encodeModel doc) then
    throw "ENCODE_MODEL_MISMATCH:TomlTable"
  match LeanSwe.Toml.decode (α := TomlTable) enc with
  | .error e => throw s!"ENCODE_DECODE_ERR:TomlTable:{reprStr e}"
  | .ok dec =>
    if !tomlEntriesBitwiseEq dec.toList doc.toList then
      throw "ENCODE_DECODE_VAL_MISMATCH:TomlTable"
  if Model.wellFormedTableBool doc then
    let fmt := LeanSwe.Toml.format doc
    match LeanSwe.Toml.parse fmt with
    | .error e => throw s!"ENCODE_FORMAT_PARSE_ERR:TomlTable:{reprStr e}"
    | .ok parsed =>
      if !tomlTableEquivBool parsed doc then
        throw "ENCODE_FORMAT_EQUIV_MISMATCH:TomlTable"
      if encodeCanonTomlPy parsed != encodeCanonTomlPy doc then
        throw "ENCODE_FORMAT_PY_BITS_MISMATCH:TomlTable"

private def checkCodecAndAccessorsCase (doc : TomlTable) (b : Bool) (i64 : Int64) (f : Float)
    (s : String) (odt : TomlOffsetDateTime) (ldt : Std.Time.PlainDateTime)
    (ld : Std.Time.PlainDate) (lt : Std.Time.PlainTime) (xs : Array Int64)
    (k1 k2 : String) (pathKeys : List String) (emitErr : Bool) :
    IO (Except String (List CoverageBucket)) := do
  let mut bkts : List CoverageBucket := []
  if let .error err := do
      checkEncodeDecodeEq "Bool" b
      checkEncodeDecodeEq "Int64" i64
      checkEncodeDecodeFloat f
      checkEncodeDecodeEq "String" s
      checkEncodeDecodeEq "OffsetDateTime" odt
      checkEncodeDecodeEq "LocalDateTime" ldt
      checkEncodeDecodeEq "LocalDate" ld
      checkEncodeDecodeEq "LocalTime" lt
      checkEncodeDecodeEq "ArrayInt64" xs
      checkEncodeDecodeTable doc
      match LeanSwe.Toml.decode (α := Int) (.int i64) with
      | .ok gotI =>
        if gotI != i64.toInt then throw "DECODE_INT_MISMATCH"
      | .error e => throw s!"DECODE_INT_ERR:{reprStr e}"
      let nonNeg := if i64.toInt ≥ 0 then i64 else 42
      match LeanSwe.Toml.decode (α := Nat) (.int nonNeg) with
      | .ok gotN =>
        if gotN != nonNeg.toInt.toNat then throw "DECODE_NAT_MISMATCH"
      | .error e => throw s!"DECODE_NAT_ERR:{reprStr e}" then
    return .error err
  bkts := bucket "encode_decode" "ok.roundtrip" :: bkts

  for badVal in #[TomlValue.string ("not_int_" ++ s), TomlValue.int (-1)] do
    match LeanSwe.Toml.decode (α := Nat) badVal with
    | .ok v => return .error s!"DECODE_NAT_UNEXPECTED_OK:{v}"
    | .error e =>
      emitLiveErrHit emitErr "LeanSwe.Toml.decode" e
      if let .error se := verifyErrShape "DECODE" e .decodeError none then return .error se
      bkts := bucket "decode" "err.decodeError" :: bkts

  let distinctK2 := if k1 == k2 then k1 ++ "_missing" else k2
  let testTab : TomlTable := #[
    (k1, .int i64),
    ("str_" ++ k1, .string ("txt_" ++ s))
  ]
  match LeanSwe.Toml.getTable (.table testTab) with
  | .ok gotT =>
    if gotT != testTab then return .error "GETTABLE_OK_MISMATCH"
    bkts := bucket "getTable" "ok" :: bkts
  | .error e => return .error s!"GETTABLE_UNEXPECTED_ERR:{reprStr e}"
  match LeanSwe.Toml.getTable (.int i64) with
  | .ok _ => return .error "GETTABLE_NON_TABLE_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.getTable" e
    if let .error se := verifyErrShape "GETTABLE" e .typeMismatch none then return .error se
    bkts := bucket "getTable" "err.typeMismatch" :: bkts

  let encodedArr := LeanSwe.Toml.encode xs
  match LeanSwe.Toml.getArray encodedArr with
  | .ok gotArr =>
    if gotArr.size != xs.size then return .error "GETARRAY_SIZE_MISMATCH"
    bkts := bucket "getArray" "ok" :: bkts
  | .error e => return .error s!"GETARRAY_UNEXPECTED_ERR:{reprStr e}"
  match LeanSwe.Toml.getArray (.table testTab) with
  | .ok _ => return .error "GETARRAY_NON_ARRAY_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.getArray" e
    if let .error se := verifyErrShape "GETARRAY" e .typeMismatch none then return .error se
    bkts := bucket "getArray" "err.typeMismatch" :: bkts

  match LeanSwe.Toml.getField (α := Int64) testTab k1 with
  | .ok gotI =>
    if gotI != i64 then return .error "GETFIELD_OK_MISMATCH"
    bkts := bucket "getField" "ok" :: bkts
  | .error e => return .error s!"GETFIELD_OK_ERR:{reprStr e}"
  match LeanSwe.Toml.getField (α := Int64) testTab distinctK2 with
  | .ok _ => return .error "GETFIELD_MISSING_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.getField" e
    if let .error se := verifyErrShape "GETFIELD_MISSING" e .missingField (some distinctK2) then return .error se
    bkts := bucket "getField" "err.missingField" :: bkts
  match LeanSwe.Toml.getField (α := Int64) testTab ("str_" ++ k1) with
  | .ok _ => return .error "GETFIELD_DECODE_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.getField" e
    if let .error se := verifyErrShape "GETFIELD_DECODE" e .decodeError (some ("str_" ++ k1)) then return .error se
    bkts := bucket "getField" "err.decodeError" :: bkts

  match LeanSwe.Toml.getOptField (α := Int64) testTab k1 with
  | .ok (some gotI) =>
    if gotI != i64 then return .error "GETOPTFIELD_SOME_MISMATCH"
    bkts := bucket "getOptField" "ok.some" :: bkts
  | other => return .error s!"GETOPTFIELD_SOME_ERR:{reprStr other}"
  match LeanSwe.Toml.getOptField (α := Int64) testTab distinctK2 with
  | .ok none => bkts := bucket "getOptField" "ok.none_absent" :: bkts
  | other => return .error s!"GETOPTFIELD_NONE_ERR:{reprStr other}"
  match LeanSwe.Toml.getOptField (α := Int64) testTab ("str_" ++ k1) with
  | .ok _ => return .error "GETOPTFIELD_DECODE_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.getOptField" e
    if let .error se := verifyErrShape "GETOPTFIELD_DECODE" e .decodeError (some ("str_" ++ k1)) then return .error se
    bkts := bucket "getOptField" "err.decodeError" :: bkts

  match LeanSwe.Toml.getPath (α := TomlTable) testTab [] with
  | .ok rootT =>
    if rootT != testTab then return .error "GETPATH_EMPTY_MISMATCH"
  | .error e => return .error s!"GETPATH_EMPTY_ERR:{reprStr e}"
  match LeanSwe.Toml.getPath (α := Int64) testTab [] with
  | .ok _ => return .error "GETPATH_EMPTY_DECODE_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.getPath" e
    if let .error se := verifyErrShape "GETPATH_EMPTY_DECODE" e .decodeError none then return .error se

  let effKeys := if pathKeys.isEmpty then [k1, "leaf"] else pathKeys
  let nestedGood := effKeys.foldr (fun seg inner => TomlValue.table #[(seg, inner)]) (.int i64)
  let nestedBadLeaf := effKeys.foldr (fun seg inner => TomlValue.table #[(seg, inner)]) (.bool b)
  let goodRoot ← match nestedGood with
    | .table t => pure t
    | _ => return .error "INTERNAL_NESTED_GOOD"
  let badRoot ← match nestedBadLeaf with
    | .table t => pure t
    | _ => return .error "INTERNAL_NESTED_BAD"
  match LeanSwe.Toml.getPath (α := Int64) goodRoot effKeys with
  | .ok gotI =>
    if gotI != i64 then return .error "GETPATH_OK_MISMATCH"
    bkts := bucket "getPath" "ok" :: bkts
  | .error e => return .error s!"GETPATH_OK_ERR:{reprStr e}"
  let fullPath := String.intercalate "." effKeys
  match LeanSwe.Toml.getPath (α := Int64) badRoot effKeys with
  | .ok _ => return .error "GETPATH_DECODE_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.getPath" e
    if let .error se := verifyErrShape "GETPATH_DECODE" e .decodeError (some fullPath) then return .error se
    bkts := bucket "getPath" "err.decodeError" :: bkts
  let nonTblInterm : TomlTable := #[(k1, .bool b)]
  match LeanSwe.Toml.getPath (α := Int64) nonTblInterm [k1, distinctK2] with
  | .ok _ => return .error "GETPATH_TYPEMISMATCH_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.getPath" e
    if let .error se := verifyErrShape "GETPATH_TYPEMISMATCH" e .typeMismatch (some k1) then return .error se
    bkts := bucket "getPath" "err.typeMismatch" :: bkts
  let nestedEmptyLeaf := effKeys.foldr (fun seg inner => TomlValue.table #[(seg, inner)]) (.table #[])
  let emptyLeafRoot ← match nestedEmptyLeaf with
    | .table t => pure t
    | _ => return .error "INTERNAL_NESTED_EMPTY"
  let missKeys := effKeys ++ [distinctK2]
  match LeanSwe.Toml.getPath (α := Int64) emptyLeafRoot missKeys with
  | .ok _ => return .error "GETPATH_MISSING_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Toml.getPath" e
    let expMissPath := String.intercalate "." missKeys
    if let .error se := verifyErrShape "GETPATH_MISSING" e .missingField (some expMissPath) then return .error se
    bkts := bucket "getPath" "err.missingField" :: bkts
  return .ok bkts

/-- Execute an episode of `TomlFuzzCase` items against `LeanSwe.Toml`, `Model`, and `PyOracleClient`. -/
def checkEpisodeWithPy (client : PyOracleClient) (trace : Array TomlFuzzCase)
    (emitErrHits : Bool := true) : IO (Except String (List CoverageBucket)) := do
  let mut allBkts : List CoverageBucket := []
  let mut batch : PyOracleBatch := {}
  for item in trace do
    match item with
    | .validRender doc raw tags =>
      match checkValidRenderCase doc raw tags batch with
      | .error err => return .error err
      | .ok (bkts, batch') =>
        allBkts := bkts ++ allBkts
        batch := batch'
    | .malformedStr raw tag =>
      match ← checkMalformedStrCase raw tag emitErrHits batch with
      | .error err => return .error err
      | .ok (bkts, batch') =>
        allBkts := bkts ++ allBkts
        batch := batch'
    | .int64Overflow raw strict =>
      match ← checkInt64OverflowCase raw strict emitErrHits batch with
      | .error err => return .error err
      | .ok (bkts, batch') =>
        allBkts := bkts ++ allBkts
        batch := batch'
    | .codecAndAccessors doc b i64 f s odt ldt ld lt xs k1 k2 pks =>
      match ← checkCodecAndAccessorsCase doc b i64 f s odt ldt ld lt xs k1 k2 pks emitErrHits with
      | .error err => return .error err
      | .ok bkts =>
        allBkts := bkts ++ allBkts
  if let .error pyErr ← flushPyBatch client batch then
    return .error pyErr
  return .ok allBkts

end Fuzz.Toml
