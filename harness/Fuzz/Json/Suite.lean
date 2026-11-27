import Fuzz.Common.Coverage
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
import Fuzz.Json.Oracle
import Fuzz.Json.Gen
import Fuzz.Json.Corpus
import Fuzz.Json.Check
import LeanSwe.Json.Interface
import LeanSweProofs.Json.Model

namespace Fuzz.Json

open Fuzz.Common
open LeanSwe.Json

private def shrinkStringLocal (s : String) : List String := Id.run do
  let cs := s.toList.toArray
  let n := cs.size
  if n == 0 then
    return []
  let mut out : Array String := #[""]
  if s != "0" && n > 1 then
    out := out.push "0"
  let half := n / 2
  if half > 0 && half < n then
    out := out.push (String.ofList (cs.extract 0 half).toList)
    out := out.push (String.ofList (cs.extract half n).toList)
  let cap := min n 24
  for idx in [0 : cap] do
    out := out.push (String.ofList ((cs.extract 0 idx).toList ++ (cs.extract (idx + 1) n).toList))
  return out.toList.eraseDups.filter (·.utf8ByteSize < s.utf8ByteSize)

private def shrinkBytesLocal (bs : ByteArray) : List ByteArray := Id.run do
  let n := bs.size
  if n == 0 then
    return []
  let mut out : Array ByteArray := #[ByteArray.empty]
  let half := n / 2
  if half > 0 && half < n then
    out := out.push (bs.extract 0 half)
    out := out.push (bs.extract half n)
  let cap := min n 24
  for idx in [0 : cap] do
    out := out.push (bs.extract 0 idx ++ bs.extract (idx + 1) n)
  return out.toList.eraseDups.filter (·.size < n)

private partial def shrinkJsonVal : Lean.Json → List Lean.Json
  | .null => []
  | .bool true => [.null, .bool false]
  | .bool false => [.null]
  | .num n =>
    if n.mantissa == 0 && n.exponent == 0 then [.null]
    else [.null, .num ⟨0, 0⟩]
  | .str s =>
    .null :: (shrinkStringLocal s).map .str
  | .arr xs =>
    if xs.isEmpty then [.null]
    else
      let subElems := xs.toList
      let smallerArrs :=
        if xs.size > 1 then
          [.arr (xs.extract 0 (xs.size / 2)), .arr (xs.extract (xs.size / 2) xs.size)]
        else []
      [.null, .arr #[]] ++ subElems ++ smallerArrs
  | .obj kvs =>
    let entries := Model.objEntries kvs
    match entries with
    | [] => [.null]
    | [(k, v)] =>
      [.null, .obj ∅, v] ++ (shrinkJsonVal v).map (fun v' => Lean.Json.mkObj [(k, v')])
    | _ =>
      let half := entries.length / 2
      [.null, .obj ∅, Lean.Json.mkObj (entries.take half), Lean.Json.mkObj (entries.drop half)]

private def shrinkJsonCase : JsonFuzzCase → List JsonFuzzCase
  | .validRender doc raw pw df tags =>
    let docCands := (shrinkJsonVal doc).map fun d' =>
      .validRender d' (LeanSwe.Json.compress d') pw df []
    let widthCands := if pw > 0 then [.validRender doc raw 0 df tags] else []
    let flagCands := if df != 0 then [.validRender doc raw pw 0 tags] else []
    docCands ++ widthCands ++ flagCands
  | .malformedStr raw tag =>
    (shrinkStringLocal raw).map fun r' => .malformedStr r' tag
  | .invalidUtf8 bs tag =>
    (shrinkBytesLocal bs).map fun b' => .invalidUtf8 b' tag
  | .codecAndAccessors doc b n i s opt xs k1 k2 pks =>
    let docCands := (shrinkJsonVal doc).map fun d' =>
      .codecAndAccessors d' b n i s opt xs k1 k2 pks
    let strCands := (shrinkStringLocal s).map fun s' =>
      .codecAndAccessors doc b n i s' opt xs k1 k2 pks
    let natCands := if n > 0 then [.codecAndAccessors doc b 0 i s opt xs k1 k2 pks] else []
    let intCands := if i != 0 then [.codecAndAccessors doc b n 0 s opt xs k1 k2 pks] else []
    let pathCands := if !pks.isEmpty then [.codecAndAccessors doc b n i s opt xs k1 k2 []] else []
    docCands ++ strCands ++ natCands ++ intCands ++ pathCands

private def shrinkStringDdmin (fails : String → IO Bool) (initial : String) : IO String := do
  if initial.isEmpty then
    return initial
  let reduced ← shrinkTrace (fun arr => fails (String.ofList arr.toList)) initial.toList.toArray true
  return String.ofList reduced.toList

private def shrinkSpecialAt (fails : Array JsonFuzzCase → IO Bool) (cur : Array JsonFuzzCase)
    (idx : Nat) : IO (Array JsonFuzzCase) := do
  match cur[idx]? with
  | some (.malformedStr raw tag) =>
    let raw' ← shrinkStringDdmin (fun cand => fails (cur.setIfInBounds idx (.malformedStr cand tag))) raw
    return cur.setIfInBounds idx (.malformedStr raw' tag)
  | _ => return cur

private def shrinkToFixedPoint (fails : Array JsonFuzzCase → IO Bool) (trace : Array JsonFuzzCase) :
    IO (Array JsonFuzzCase) := do
  let mut cur ← shrinkTrace fails trace
  for _ in [0 : 12] do
    let prev := cur
    for idx in [0 : cur.size] do
      cur ← shrinkSpecialAt fails cur idx
    cur ← shrinkElements shrinkJsonCase fails cur
    cur ← shrinkTrace fails cur
    if cur == prev then
      break
  return cur

private def errorClassTag (err : String) : String := Id.run do
  let pyPrefix := "PYTHON_ORACLE_MISMATCH: "
  if err.startsWith pyPrefix then
    let rest := (err.drop pyPrefix.length).toString
    let tagPart := (rest.splitOn ":").headD rest
    let bracketBase := (tagPart.splitOn "[").headD tagPart
    return pyPrefix ++ bracketBase
  let mut out := ""
  for c in err.toList do
    if c == '(' || c == ' ' || c == '=' || c == ':' then
      break
    out := out.push c
  return out

private def runTraceChecked (client : PyOracleClient) (tracker : CoverageTracker)
    (trace : Array JsonFuzzCase) : IO CoverageTracker := do
  match ← checkEpisodeWithPy client trace true with
  | .ok bkts =>
    let mut tr := tracker
    for b in bkts do
      tr := tr.record b.op b.bucket
    return tr
  | .error err =>
    if err.startsWith "PYTHON_ORACLE_EOF" then
      throw (IO.userError s!"JSON_FUZZ_MISMATCH err={err} trace_size={trace.size} trace={reprStr trace}")
    let origTag := errorClassTag err
    let fails (cand : Array JsonFuzzCase) : IO Bool := do
      match ← checkEpisodeWithPy client cand false with
      | .ok _ => return false
      | .error e =>
        if e.startsWith "PYTHON_ORACLE_EOF" then
          throw (IO.userError s!"JSON_FUZZ_MISMATCH err={e} original_err={err} trace_size={trace.size}")
        return errorClassTag e == origTag
    let shrunk ← shrinkToFixedPoint fails trace
    let shrunkErr := match ← checkEpisodeWithPy client shrunk false with
      | .error e => e
      | .ok _ => err
    throw (IO.userError s!"JSON_FUZZ_MISMATCH err={shrunkErr} original_err={err} shrunk={reprStr shrunk}")

private def runJsonSuite (steps : Nat) (seedVal : UInt64) (isSmoke : Bool) : IO Unit := do
  let client ← startPyOracleClient
  try
    let mut smokeTracker := CoverageTracker.empty
    let mut executedSteps : Nat := 0
    if isSmoke then
      let epSize := 24
      let mut idx := 0
      while idx < smokeCases.size do
        let stop := min smokeCases.size (idx + epSize)
        smokeTracker ← runTraceChecked client smokeTracker (smokeCases.extract idx stop)
        idx := stop
      executedSteps := executedSteps + smokeCases.size
    let mut randTracker := CoverageTracker.empty
    let mut rng := Rng.seed seedVal
    let mut done := 0
    while done < steps do
      let (epLenRaw, r1) := rng.nextRange 16 32
      rng := r1
      let epLen := min epLenRaw (steps - done)
      let mut trace : Array JsonFuzzCase := Array.mkEmpty epLen
      for _ in [0 : epLen] do
        let (c, rN) := genJsonFuzzCase rng
        rng := rN
        trace := trace.push c
      randTracker ← runTraceChecked client randTracker trace
      done := done + epLen
    executedSteps := executedSteps + done
    Fuzz.Common.recordSuiteSteps executedSteps
    let reportTracker :=
      if isSmoke then
        smokeTracker.merge randTracker
      else
        randTracker
    assertCoverage "json" reportTracker requiredBuckets
    IO.println (reportTracker.formatReport "json")
    IO.println s!"FUZZ_SUMMARY suite=json steps={executedSteps} seed={seedVal}"
    closePyOracleClient client
  catch e =>
    closePyOracleClientQuiet client
    throw e

private def runJsonSelfTestShrink (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  let mut rng := Rng.seed (seedVal ^^^ 0x9e3779b97f4a7c15)
  let isSyntheticDupFault : JsonFuzzCase → Bool
    | .malformedStr s _ =>
      (s.splitOn "\"dup\"").length ≥ 3
    | _ => false
  let mut trace1 : Array JsonFuzzCase := Array.mkEmpty 17
  for _ in [0 : 16] do
    let (c, r1) := genJsonFuzzCase rng
    rng := r1
    if !isSyntheticDupFault c then
      trace1 := trace1.push c
  let (idx1, r2) := rng.nextRange 0 trace1.size
  rng := r2
  let badItem := JsonFuzzCase.malformedStr "{\"noise\":123456,\"dup\":1,\"extra\":\"abcdef\",\"dup\":2}" "duplicate_key"
  let injected1 := (trace1.extract 0 idx1).push badItem ++ trace1.extract idx1 trace1.size
  let failsDup (cand : Array JsonFuzzCase) : IO Bool := pure (cand.any isSyntheticDupFault)
  let shrunk1 ← shrinkToFixedPoint failsDup injected1
  unless ← failsDup shrunk1 do
    throw (IO.userError "JSON_SHRINK_SELFTEST_1: shrunk trace lost failure")
  if shrunk1.size != 1 then
    throw (IO.userError s!"JSON_SHRINK_SELFTEST_1: expected size 1, got {shrunk1.size}")
  match shrunk1[0]! with
  | .malformedStr s _ =>
    if s.length > 14 then
      throw (IO.userError s!"JSON_SHRINK_SELFTEST_1: shrunk string too long ({s.length}): {reprStr s}")
    IO.println s!"JSON_SHRINK_SELFTEST_1_OK: shrunk={reprStr s}"
  | other =>
    throw (IO.userError s!"JSON_SHRINK_SELFTEST_1: unexpected variant {reprStr other}")

  let client ← startPyOracleClient
  try
    let goodDoc := Lean.Json.mkObj [("ok", .num ⟨1, 0⟩)]
    let badDoc := Lean.Json.mkObj [
      ("a", .arr #[.str "padding_one", .str "padding_two"]),
      ("b", .num ⟨999, 0⟩)
    ]
    let injected2 : Array JsonFuzzCase := #[
      .validRender goodDoc "{\"ok\":1}" 80 0 [],
      .validRender badDoc (LeanSwe.Json.compress badDoc) 80 0 [],
      .validRender .null "null" 80 0 []
    ]
    let buildSpoofBatch (cand : Array JsonFuzzCase) : PyOracleBatch := Id.run do
      let mut items : Array PyParseCheck := #[]
      for c in cand do
        if let .validRender d raw _ _ _ := c then
          let spoofTlv :=
            if ((LeanSwe.Json.compress d).splitOn "999").length > 1 then
              encodeCanonJson .null
            else
              encodeCanonJson d
          items := items.push {
            rawBytes := raw.toUTF8
            expectedOk := true
            expectedCanonTlv := spoofTlv
            label := "selftest"
          }
      return { parses := items }
    let origErr ← match ← flushPyBatch client (buildSpoofBatch injected2) LeanSwe.Json.parse with
      | .ok () => throw (IO.userError "JSON_SHRINK_SELFTEST_2: spoofed batch unexpectedly passed")
      | .error e => pure e
    let origTag := errorClassTag origErr
    let failsPySpoof (cand : Array JsonFuzzCase) : IO Bool := do
      match ← flushPyBatch client (buildSpoofBatch cand) LeanSwe.Json.parse with
      | .ok () => return false
      | .error e =>
        if e.startsWith "PYTHON_ORACLE_EOF" then
          throw (IO.userError e)
        return errorClassTag e == origTag
    let shrunk2 ← shrinkToFixedPoint failsPySpoof injected2
    unless ← failsPySpoof shrunk2 do
      throw (IO.userError "JSON_SHRINK_SELFTEST_2: shrunk Python mismatch trace lost failure")
    if shrunk2.size != 1 then
      throw (IO.userError s!"JSON_SHRINK_SELFTEST_2: expected size 1, got {shrunk2.size}")
    IO.println s!"JSON_SHRINK_SELFTEST_2_OK: shrunk={reprStr shrunk2} tag={origTag}"
    closePyOracleClient client
  catch e =>
    closePyOracleClientQuiet client
    throw e

/-- Differential fuzzing suite for `LeanSwe.Json` against `LeanSwe.Json.Model` and Python 3 `json`. -/
def suite : FuzzSuite := {
  name := "json"
  description := "Differential fuzzer for LeanSwe.Json RFC 8259 parse/compress/pretty/encode/decode/accessors against Model.render and Python 3 json.loads/json.dumps"
  runSmoke := fun cfg =>
    runJsonSuite 400 cfg.seed true
  runFuzz := fun cfg =>
    runJsonSuite cfg.steps cfg.seed false
  selfTestShrink := runJsonSelfTestShrink
}

end Fuzz.Json
