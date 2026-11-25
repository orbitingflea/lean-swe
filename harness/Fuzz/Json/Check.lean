import Fuzz.Common.Coverage
import Fuzz.Common.Suite
import Fuzz.Json.Oracle
import Fuzz.Json.Gen
import LeanSwe.Json.Interface
import LeanSwe.Json.Impl
import LeanSwe.Json.Model

namespace Fuzz.Json

open Fuzz.Common
open LeanSwe.Json

/-- Fixed required non-vacuous coverage buckets for `Fuzz.Json.suite`. -/
def requiredBuckets : Array CoverageBucket := #[
  bucket "parse" "ok.null",
  bucket "parse" "ok.bool_true",
  bucket "parse" "ok.bool_false",
  bucket "parse" "ok.num_int",
  bucket "parse" "ok.num_frac",
  bucket "parse" "ok.num_exp",
  bucket "parse" "ok.num_neg_zero",
  bucket "parse" "ok.num_big",
  bucket "parse" "ok.str_ascii",
  bucket "parse" "ok.str_unicode",
  bucket "parse" "ok.arr_empty",
  bucket "parse" "ok.arr_nonempty",
  bucket "parse" "ok.obj_empty",
  bucket "parse" "ok.obj_nonempty",
  bucket "parse" "ok.deep_nested",
  bucket "parse" "ok.short_escape",
  bucket "parse" "ok.unicode_hex",
  bucket "parse" "ok.surrogate_pair",
  bucket "parse" "ok.whitespace",
  bucket "parse" "ok.limit_boundary",
  bucket "parse" "err.parseError",
  bucket "parse" "err.duplicate_key",
  bucket "parse" "err.lone_high_surrogate",
  bucket "parse" "err.lone_low_surrogate",
  bucket "parse" "err.bad_surrogate_pair",
  bucket "parse" "err.control_char",
  bucket "parse" "err.bad_escape",
  bucket "parse" "err.bad_number",
  bucket "parse" "err.nonfinite_constant",
  bucket "parse" "err.limit_exceeded",
  bucket "parse" "err.container_syntax",
  bucket "parse" "err.trailing_tokens",
  bucket "parse" "err.invalid_utf8",
  bucket "compress" "ok.roundtrip",
  bucket "pretty" "ok.flat",
  bucket "pretty" "ok.multiline",
  bucket "python_loads" "ok.parity",
  bucket "python_dumps" "ok.roundtrip",
  bucket "encode_decode" "ok.roundtrip",
  bucket "decode" "err.decodeError",
  bucket "getObject" "ok",
  bucket "getObject" "err.typeMismatch",
  bucket "getArray" "ok",
  bucket "getArray" "err.typeMismatch",
  bucket "getField" "ok",
  bucket "getField" "err.missingField",
  bucket "getField" "err.typeMismatch",
  bucket "getField" "err.decodeError",
  bucket "getOptField" "ok.some",
  bucket "getOptField" "ok.none_absent",
  bucket "getOptField" "ok.none_null",
  bucket "getOptField" "err.typeMismatch",
  bucket "getOptField" "err.decodeError",
  bucket "getPath" "ok",
  bucket "getPath" "err.missingField",
  bucket "getPath" "err.typeMismatch",
  bucket "getPath" "err.decodeError"
]

private def jsonErrorKindCtor : JsonErrorKind → String
  | .parseError => "LeanSwe.Json.JsonErrorKind.parseError"
  | .missingField => "LeanSwe.Json.JsonErrorKind.missingField"
  | .typeMismatch => "LeanSwe.Json.JsonErrorKind.typeMismatch"
  | .decodeError => "LeanSwe.Json.JsonErrorKind.decodeError"

private def emitLiveErrHit (emit : Bool) (qualOp : String) (e : JsonError) : IO Unit := do
  if emit then
    Fuzz.Common.logErrHit qualOp (jsonErrorKindCtor e.kind) "real"

private def verifyErrShape (opLabel : String) (e : JsonError) (expKind : JsonErrorKind)
    (expPath : Option String) : Except String Unit := do
  if e.kind != expKind then
    throw s!"{opLabel}_ERR_KIND_MISMATCH: got={reprStr e.kind} expected={reprStr expKind}"
  if e.path != expPath then
    throw s!"{opLabel}_ERR_PATH_MISMATCH: got={reprStr e.path} expected={reprStr expPath}"
  if e.message.isEmpty then
    throw s!"{opLabel}_EMPTY_ERR_MSG"

private def checkValidRenderCase (doc : Lean.Json) (raw : String) (prettyWidth : Nat)
    (dumpsFlags : UInt8) (tags : List String) (_emitErr : Bool) (batch : PyOracleBatch) :
    IO (Except String (List CoverageBucket × PyOracleBatch)) := do
  let mut bkts : List CoverageBucket := []
  let mut nextBatch := batch
  for tg in tags do
    bkts := bucket "parse" s!"ok.{tg}" :: bkts
  match LeanSwe.Json.parse raw with
  | .error e =>
    return .error s!"VALID_RENDER_PARSE_ERR: err={reprStr e} raw={reprStr (raw.take 80).toString}"
  | .ok parsed =>
    if !Model.wellFormedJsonBool parsed then
      return .error "VALID_RENDER_PARSED_NOT_WF"
    let expTlv := encodeCanonJson doc
    let gotTlv := encodeCanonJson parsed
    if gotTlv != expTlv then
      return .error s!"VALID_RENDER_EQUIV_MISMATCH: raw={reprStr (raw.take 80).toString}"
    nextBatch := { nextBatch with
      parses := nextBatch.parses.push {
        rawBytes := raw.toUTF8
        expectedOk := true
        expectedCanonTlv := expTlv
        label := "validRender"
      }
    }
    bkts := bucket "python_loads" "ok.parity" :: bkts
    let comp := LeanSwe.Json.compress parsed
    if comp.isEmpty || comp.contains '\n' || comp.contains '\r' then
      return .error s!"COMPRESS_CONTRACT_VIOLATION: comp={reprStr (comp.take 80).toString}"
    match LeanSwe.Json.parse comp with
    | .error ce =>
      return .error s!"COMPRESS_ROUNDTRIP_PARSE_ERR: err={reprStr ce}"
    | .ok vc =>
      if !Model.wellFormedJsonBool vc || encodeCanonJson vc != expTlv then
        return .error "COMPRESS_ROUNDTRIP_EQUIV_MISMATCH"
      if LeanSwe.Json.compress vc != comp then
        return .error "COMPRESS_IDEMPOTENCE_MISMATCH"
    bkts := bucket "compress" "ok.roundtrip" :: bkts
    nextBatch := { nextBatch with
      renders := nextBatch.renders.push {
        kindTag := "compress"
        rendered := comp
        expectedCanonTlv := expTlv
      }
    }
    let flat := Model.flatPretty parsed
    let pret := LeanSwe.Json.pretty parsed prettyWidth
    if pret.isEmpty then
      return .error "PRETTY_EMPTY_OUTPUT"
    if flat.length ≤ prettyWidth && pret != flat then
      return .error s!"PRETTY_FLAT_MISMATCH: width={prettyWidth} flatLen={flat.length}"
    if pret.contains '\n' then
      bkts := bucket "pretty" "ok.multiline" :: bkts
    else
      bkts := bucket "pretty" "ok.flat" :: bkts
    let pretTight := LeanSwe.Json.pretty parsed 0
    if pretTight.contains '\n' then
      bkts := bucket "pretty" "ok.multiline" :: bkts
    let pretWide := LeanSwe.Json.pretty parsed (flat.length + 4)
    if pretWide != flat then
      return .error "PRETTY_WIDE_FLAT_MISMATCH"
    bkts := bucket "pretty" "ok.flat" :: bkts
    match LeanSwe.Json.parse pret, LeanSwe.Json.parse pretTight with
    | .ok vp, .ok vt =>
      if !Model.wellFormedJsonBool vp || encodeCanonJson vp != expTlv then
        return .error "PRETTY_ROUNDTRIP_EQUIV_MISMATCH"
      if !Model.wellFormedJsonBool vt || encodeCanonJson vt != expTlv then
        return .error "PRETTY_TIGHT_ROUNDTRIP_EQUIV_MISMATCH"
    | .error pe, _ =>
      return .error s!"PRETTY_ROUNDTRIP_PARSE_ERR: err={reprStr pe}"
    | _, .error te =>
      return .error s!"PRETTY_TIGHT_PARSE_ERR: err={reprStr te}"
    nextBatch := { nextBatch with
      renders := nextBatch.renders.push {
        kindTag := "pretty"
        rendered := pret
        expectedCanonTlv := expTlv
      }
    }
    if isDumpsEligibleJson parsed then
      nextBatch := { nextBatch with
        dumps := nextBatch.dumps.push {
          modeFlags := dumpsFlags
          origVal := parsed
          expectedCanonTlv := expTlv
        }
      }
      bkts := bucket "python_dumps" "ok.roundtrip" :: bkts
    return .ok (bkts, nextBatch)

private def checkMalformedStrCase (raw : String) (tag : String) (emitErr : Bool)
    (batch : PyOracleBatch) : IO (Except String (List CoverageBucket × PyOracleBatch)) := do
  let mut bkts : List CoverageBucket := []
  match LeanSwe.Json.parse raw with
  | .ok parsed =>
    let tlv := encodeCanonJson parsed
    let nextBatch := { batch with
      parses := batch.parses.push {
        rawBytes := raw.toUTF8
        expectedOk := true
        expectedCanonTlv := tlv
        label := s!"malformedAccept:{tag}"
      }
    }
    bkts := bucket "python_loads" "ok.parity" :: bkts
    return .ok (bkts, nextBatch)
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.parse" e
    if let .error shapeErr := verifyErrShape "PARSE" e .parseError none then
      return .error shapeErr
    bkts := bucket "parse" "err.parseError" :: bkts
    if !tag.isEmpty then
      bkts := bucket "parse" s!"err.{tag}" :: bkts
    let nextBatch := { batch with
      parses := batch.parses.push {
        rawBytes := raw.toUTF8
        expectedOk := false
        expectedCanonTlv := ByteArray.empty
        label := s!"malformedReject:{tag}"
      }
    }
    bkts := bucket "python_loads" "ok.parity" :: bkts
    return .ok (bkts, nextBatch)

private def checkInvalidUtf8Case (rawBytes : ByteArray) (tag : String)
    (batch : PyOracleBatch) : Except String (List CoverageBucket × PyOracleBatch) := do
  let res := Internal.parseWantValue rawBytes 0 (Nat.zero_le _) []
  match res with
  | .ok parsed =>
    let tlv := encodeCanonJson parsed
    let nextBatch := { batch with
      parses := batch.parses.push {
        rawBytes := rawBytes
        expectedOk := true
        expectedCanonTlv := tlv
        label := s!"utf8Accept:{tag}"
      }
    }
    return ([bucket "python_loads" "ok.parity"], nextBatch)
  | .error msg =>
    if msg.isEmpty then
      throw "INVALID_UTF8_EMPTY_ERR_MSG"
    let nextBatch := { batch with
      parses := batch.parses.push {
        rawBytes := rawBytes
        expectedOk := false
        expectedCanonTlv := ByteArray.empty
        label := s!"utf8Reject:{tag}"
      }
    }
    return ([bucket "parse" "err.invalid_utf8", bucket "python_loads" "ok.parity"], nextBatch)

private def checkEncodeDecodeOne {α : Type} [Lean.ToJson α] [Lean.FromJson α] [BEq α]
    (label : String) (val : α) : Except String Unit := do
  let enc := LeanSwe.Json.encode val
  if enc != Model.encodeModel val then
    throw s!"ENCODE_MODEL_MISMATCH:{label}"
  match LeanSwe.Json.decode (α := α) enc with
  | .error e => throw s!"ENCODE_DECODE_ROUNDTRIP_ERR:{label}:{reprStr e}"
  | .ok dec =>
    if dec != val then
      throw s!"ENCODE_DECODE_ROUNDTRIP_VAL:{label}"
  let comp := LeanSwe.Json.compress enc
  match LeanSwe.Json.parse comp with
  | .error e => throw s!"ENCODE_COMPRESS_PARSE_ERR:{label}:{reprStr e}"
  | .ok parsed =>
    match LeanSwe.Json.decode (α := α) parsed with
    | .error e => throw s!"ENCODE_COMPRESS_DECODE_ERR:{label}:{reprStr e}"
    | .ok dec2 =>
      if dec2 != val then
        throw s!"ENCODE_COMPRESS_DECODE_VAL:{label}"

private def checkEncodeDecodeJson (doc : Lean.Json) : Except String Unit := do
  let enc := LeanSwe.Json.encode doc
  if enc != Model.encodeModel doc then
    throw "ENCODE_MODEL_MISMATCH:Json"
  match LeanSwe.Json.decode (α := Lean.Json) enc with
  | .error e => throw s!"ENCODE_DECODE_ROUNDTRIP_ERR:Json:{reprStr e}"
  | .ok dec =>
    if dec != doc then
      throw "ENCODE_DECODE_ROUNDTRIP_VAL:Json"
  let comp := LeanSwe.Json.compress enc
  match LeanSwe.Json.parse comp with
  | .error e => throw s!"ENCODE_COMPRESS_PARSE_ERR:Json:{reprStr e}"
  | .ok parsed =>
    match LeanSwe.Json.decode (α := Lean.Json) parsed with
    | .error e => throw s!"ENCODE_COMPRESS_DECODE_ERR:Json:{reprStr e}"
    | .ok dec2 =>
      if !jsonEquivBool dec2 doc then
        throw "ENCODE_COMPRESS_DECODE_EQUIV:Json"

private def checkCodecAndAccessorsCase (doc : Lean.Json) (b : Bool) (n : Nat) (i : Int)
    (s : String) (optVal : Option Int) (arrVals : Array String) (k1 k2 : String)
    (pathKeys : List String) (emitErr : Bool) : IO (Except String (List CoverageBucket)) := do
  let mut bkts : List CoverageBucket := []
  if let .error err := do
      checkEncodeDecodeOne "Bool" b
      checkEncodeDecodeOne "Nat" n
      checkEncodeDecodeOne "Int" i
      checkEncodeDecodeOne "String" s
      checkEncodeDecodeOne "OptionInt" optVal
      checkEncodeDecodeOne "ArrayString" arrVals
      checkEncodeDecodeJson doc then
    return .error err
  bkts := bucket "encode_decode" "ok.roundtrip" :: bkts

  let badNatJson : Lean.Json := .str ("not_a_nat_" ++ s)
  match LeanSwe.Json.decode (α := Nat) badNatJson with
  | .ok v => return .error s!"DECODE_UNEXPECTED_OK:{v}"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.decode" e
    if let .error se := verifyErrShape "DECODE" e .decodeError none then return .error se
    bkts := bucket "decode" "err.decodeError" :: bkts

  match doc, LeanSwe.Json.getObject doc with
  | .obj kvs, .ok got =>
    if got != kvs then return .error "GETOBJECT_OK_MISMATCH"
    bkts := bucket "getObject" "ok" :: bkts
  | .obj _, .error e => return .error s!"GETOBJECT_UNEXPECTED_ERR:{reprStr e}"
  | _, .ok _ => return .error "GETOBJECT_NONOBJ_UNEXPECTED_OK"
  | _, .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getObject" e
    if let .error se := verifyErrShape "GETOBJECT" e .typeMismatch none then return .error se
    bkts := bucket "getObject" "err.typeMismatch" :: bkts

  match doc, LeanSwe.Json.getArray doc with
  | .arr xs, .ok got =>
    if got != xs then return .error "GETARRAY_OK_MISMATCH"
    bkts := bucket "getArray" "ok" :: bkts
  | .arr _, .error e => return .error s!"GETARRAY_UNEXPECTED_ERR:{reprStr e}"
  | _, .ok _ => return .error "GETARRAY_NONARR_UNEXPECTED_OK"
  | _, .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getArray" e
    if let .error se := verifyErrShape "GETARRAY" e .typeMismatch none then return .error se
    bkts := bucket "getArray" "err.typeMismatch" :: bkts

  let distinctK2 := if k1 == k2 then k1 ++ "_missing" else k2
  let testObj := Lean.Json.mkObj [
    (k1, Lean.toJson n),
    ("str_" ++ k1, Lean.toJson ("txt_" ++ s)),
    ("null_" ++ k1, .null)
  ]
  match LeanSwe.Json.getObject testObj with
  | .ok _ => bkts := bucket "getObject" "ok" :: bkts
  | .error e => return .error s!"TEST_GETOBJECT_ERR:{reprStr e}"
  match LeanSwe.Json.getArray (.arr #[Lean.toJson s]) with
  | .ok arr =>
    if arr.size != 1 then return .error "TEST_GETARRAY_SIZE"
    bkts := bucket "getArray" "ok" :: bkts
  | .error e => return .error s!"TEST_GETARRAY_ERR:{reprStr e}"
  match LeanSwe.Json.getObject (.arr #[]) with
  | .ok _ => return .error "GETOBJECT_ARR_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getObject" e
    if let .error se := verifyErrShape "GETOBJECT_ARR" e .typeMismatch none then return .error se
    bkts := bucket "getObject" "err.typeMismatch" :: bkts
  match LeanSwe.Json.getArray testObj with
  | .ok _ => return .error "GETARRAY_OBJ_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getArray" e
    if let .error se := verifyErrShape "GETARRAY_OBJ" e .typeMismatch none then return .error se
    bkts := bucket "getArray" "err.typeMismatch" :: bkts

  match LeanSwe.Json.getField (α := Nat) testObj k1 with
  | .ok gotN =>
    if gotN != n then return .error "GETFIELD_OK_MISMATCH"
    bkts := bucket "getField" "ok" :: bkts
  | .error e => return .error s!"GETFIELD_OK_ERR:{reprStr e}"
  match LeanSwe.Json.getField (α := Nat) testObj distinctK2 with
  | .ok _ => return .error "GETFIELD_MISSING_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getField" e
    if let .error se := verifyErrShape "GETFIELD_MISSING" e .missingField (some distinctK2) then return .error se
    bkts := bucket "getField" "err.missingField" :: bkts
  match LeanSwe.Json.getField (α := Nat) testObj ("str_" ++ k1) with
  | .ok _ => return .error "GETFIELD_DECODE_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getField" e
    if let .error se := verifyErrShape "GETFIELD_DECODE" e .decodeError (some ("str_" ++ k1)) then return .error se
    bkts := bucket "getField" "err.decodeError" :: bkts
  match LeanSwe.Json.getField (α := Nat) (.bool b) k1 with
  | .ok _ => return .error "GETFIELD_NONOBJ_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getField" e
    if let .error se := verifyErrShape "GETFIELD_NONOBJ" e .typeMismatch none then return .error se
    bkts := bucket "getField" "err.typeMismatch" :: bkts

  match LeanSwe.Json.getOptField (α := Nat) testObj k1 with
  | .ok (some gotN) =>
    if gotN != n then return .error "GETOPTFIELD_SOME_MISMATCH"
    bkts := bucket "getOptField" "ok.some" :: bkts
  | other => return .error s!"GETOPTFIELD_SOME_ERR:{reprStr other}"
  match LeanSwe.Json.getOptField (α := Nat) testObj distinctK2 with
  | .ok none => bkts := bucket "getOptField" "ok.none_absent" :: bkts
  | other => return .error s!"GETOPTFIELD_ABSENT_ERR:{reprStr other}"
  match LeanSwe.Json.getOptField (α := Nat) testObj ("null_" ++ k1) with
  | .ok none => bkts := bucket "getOptField" "ok.none_null" :: bkts
  | other => return .error s!"GETOPTFIELD_NULL_ERR:{reprStr other}"
  match LeanSwe.Json.getOptField (α := Nat) testObj ("str_" ++ k1) with
  | .ok _ => return .error "GETOPTFIELD_DECODE_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getOptField" e
    if let .error se := verifyErrShape "GETOPTFIELD_DECODE" e .decodeError (some ("str_" ++ k1)) then return .error se
    bkts := bucket "getOptField" "err.decodeError" :: bkts
  match LeanSwe.Json.getOptField (α := Nat) (.arr #[]) k1 with
  | .ok _ => return .error "GETOPTFIELD_NONOBJ_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getOptField" e
    if let .error se := verifyErrShape "GETOPTFIELD_NONOBJ" e .typeMismatch none then return .error se
    bkts := bucket "getOptField" "err.typeMismatch" :: bkts

  let effKeys := if pathKeys.isEmpty then [k1, "leaf"] else pathKeys
  let nestedGood := effKeys.foldr (fun seg inner => Lean.Json.mkObj [(seg, inner)]) (Lean.toJson i)
  let nestedBadLeaf := effKeys.foldr (fun seg inner => Lean.Json.mkObj [(seg, inner)]) (.bool b)
  match LeanSwe.Json.getPath (α := Int) nestedGood effKeys with
  | .ok gotI =>
    if gotI != i then return .error "GETPATH_OK_MISMATCH"
    bkts := bucket "getPath" "ok" :: bkts
  | .error e => return .error s!"GETPATH_OK_ERR:{reprStr e}"
  let fullPath := String.intercalate "." effKeys
  match LeanSwe.Json.getPath (α := Nat) nestedBadLeaf effKeys with
  | .ok _ => return .error "GETPATH_DECODE_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getPath" e
    if let .error se := verifyErrShape "GETPATH_DECODE" e .decodeError (some fullPath) then return .error se
    bkts := bucket "getPath" "err.decodeError" :: bkts
  let missKeys := effKeys ++ [distinctK2]
  let nonObjIntermediate := Lean.Json.mkObj [(k1, .null)]
  match LeanSwe.Json.getPath (α := Int) nonObjIntermediate [k1, distinctK2] with
  | .ok _ => return .error "GETPATH_TYPEMISMATCH_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getPath" e
    if let .error se := verifyErrShape "GETPATH_TYPEMISMATCH" e .typeMismatch (some k1) then return .error se
    bkts := bucket "getPath" "err.typeMismatch" :: bkts
  let nestedEmptyLeaf := effKeys.foldr (fun seg inner => Lean.Json.mkObj [(seg, inner)]) (Lean.Json.mkObj [])
  match LeanSwe.Json.getPath (α := Int) nestedEmptyLeaf missKeys with
  | .ok _ => return .error "GETPATH_MISSING_OK"
  | .error e =>
    emitLiveErrHit emitErr "LeanSwe.Json.getPath" e
    let expMissPath := String.intercalate "." missKeys
    if let .error se := verifyErrShape "GETPATH_MISSING" e .missingField (some expMissPath) then return .error se
    bkts := bucket "getPath" "err.missingField" :: bkts
  return .ok bkts

/-- Execute an episode of `JsonFuzzCase` items against `LeanSwe.Json`, `Model`, and `PyOracleClient`. -/
def checkEpisodeWithPy (client : PyOracleClient) (trace : Array JsonFuzzCase)
    (emitErrHits : Bool := true) : IO (Except String (List CoverageBucket)) := do
  let mut allBkts : List CoverageBucket := []
  let mut batch : PyOracleBatch := {}
  for item in trace do
    match item with
    | .validRender doc raw pw df tags =>
      match ← checkValidRenderCase doc raw pw df tags emitErrHits batch with
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
    | .invalidUtf8 bs tag =>
      match checkInvalidUtf8Case bs tag batch with
      | .error err => return .error err
      | .ok (bkts, batch') =>
        allBkts := bkts ++ allBkts
        batch := batch'
    | .codecAndAccessors doc b n i s opt xs k1 k2 pks =>
      match ← checkCodecAndAccessorsCase doc b n i s opt xs k1 k2 pks emitErrHits with
      | .error err => return .error err
      | .ok bkts =>
        allBkts := bkts ++ allBkts
  if let .error pyErr ← flushPyBatch client batch LeanSwe.Json.parse then
    return .error pyErr
  return .ok allBkts

end Fuzz.Json
