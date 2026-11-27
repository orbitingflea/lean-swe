import Fuzz.Common.Coverage
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
import Fuzz.Toml.Oracle
import Fuzz.Toml.Gen
import Fuzz.Toml.Corpus
import Fuzz.Toml.Check
import LeanSwe.Toml.Interface
import LeanSweProofs.Toml.Model

namespace Fuzz.Toml

open Fuzz.Common
open LeanSwe.Toml

private def shrinkStringLocal (s : String) : List String := Id.run do
  let cs := s.toList.toArray
  let n := cs.size
  if n == 0 then
    return []
  let mut out : Array String := #[""]
  let half := n / 2
  if half > 0 && half < n then
    out := out.push (String.ofList (cs.extract 0 half).toList)
    out := out.push (String.ofList (cs.extract half n).toList)
  let cap := min n 24
  for idx in [0 : cap] do
    out := out.push (String.ofList ((cs.extract 0 idx).toList ++ (cs.extract (idx + 1) n).toList))
  return out.toList.eraseDups.filter (·.utf8ByteSize < s.utf8ByteSize)

private def shrinkTomlValue : Nat → TomlValue → List TomlValue
  | 0, _ => []
  | _ + 1, .bool true => [.bool false]
  | _ + 1, .bool false => []
  | _ + 1, .int n => if n == 0 then [] else [.int 0]
  | _ + 1, .float f => if f.toBits == (0.0 : Float).toBits then [] else [.float 0.0]
  | _ + 1, .string s => (shrinkStringLocal s).map .string
  | _ + 1, .offsetDateTime _ => [.int 0]
  | _ + 1, .localDateTime _ => [.int 0]
  | _ + 1, .localDate _ => [.int 0]
  | _ + 1, .localTime _ => [.int 0]
  | _ + 1, .array xs =>
    if xs.isEmpty then [.int 0]
    else
      let halves :=
        if xs.size > 1 then
          [.array (xs.extract 0 (xs.size / 2)), .array (xs.extract (xs.size / 2) xs.size)]
        else []
      [.int 0, .array #[]] ++ xs.toList ++ halves
  | fuel + 1, .table entries =>
    if entries.isEmpty then [.int 0]
    else if entries.size == 1 then
      let (k, v) := entries[0]!
      [.int 0, .table #[], v] ++ (shrinkTomlValue fuel v).map (fun v' => .table #[(k, v')])
    else
      let half := entries.size / 2
      [.int 0, .table #[], .table (entries.extract 0 half), .table (entries.extract half entries.size)]

private def shrinkTomlTable (doc : TomlTable) : List TomlTable :=
  if doc.isEmpty then []
  else if doc.size == 1 then
    let (k, v) := doc[0]!
    #[] :: (shrinkTomlValue 6 v).map (fun v' => #[(k, v')])
  else
    let half := doc.size / 2
    #[#[], doc.extract 0 half, doc.extract half doc.size].toList

private def shrinkTomlCase : TomlFuzzCase → List TomlFuzzCase
  | .validRender doc _ _ =>
    (shrinkTomlTable doc).filter Model.wellFormedTableBool |>.map fun d' =>
      .validRender d' (LeanSwe.Toml.format d') []
  | .malformedStr raw tag =>
    (shrinkStringLocal raw).map fun r' => .malformedStr r' tag
  | .int64Overflow raw strict =>
    if raw == "i=9223372036854775808" then []
    else [.int64Overflow "i=9223372036854775808" strict] ++
      (shrinkStringLocal raw).map (fun r' => .int64Overflow r' false)
  | .codecAndAccessors doc b i64 f s odt ldt ld lt xs k1 k2 pks =>
    let docCands := (shrinkTomlTable doc).map fun d' =>
      .codecAndAccessors d' b i64 f s odt ldt ld lt xs k1 k2 pks
    let strCands := (shrinkStringLocal s).map fun s' =>
      .codecAndAccessors doc b i64 f s' odt ldt ld lt xs k1 k2 pks
    let intCands := if i64 != 0 then [.codecAndAccessors doc b 0 f s odt ldt ld lt xs k1 k2 pks] else []
    let pathCands := if !pks.isEmpty then [.codecAndAccessors doc b i64 f s odt ldt ld lt xs k1 k2 []] else []
    docCands ++ strCands ++ intCands ++ pathCands

private def shrinkStringDdmin (fails : String → IO Bool) (initial : String) : IO String := do
  if initial.isEmpty then
    return initial
  let reduced ← shrinkTrace (fun arr => fails (String.ofList arr.toList)) initial.toList.toArray true
  return String.ofList reduced.toList

private def shrinkSpecialAt (fails : Array TomlFuzzCase → IO Bool) (cur : Array TomlFuzzCase)
    (idx : Nat) : IO (Array TomlFuzzCase) := do
  match cur[idx]? with
  | some (.malformedStr raw tag) =>
    let raw' ← shrinkStringDdmin (fun cand => fails (cur.setIfInBounds idx (.malformedStr cand tag))) raw
    return cur.setIfInBounds idx (.malformedStr raw' tag)
  | _ => return cur

private def shrinkToFixedPoint (fails : Array TomlFuzzCase → IO Bool) (trace : Array TomlFuzzCase) :
    IO (Array TomlFuzzCase) := do
  let mut cur ← shrinkTrace fails trace
  for _ in [0 : 12] do
    let prev := cur
    for idx in [0 : cur.size] do
      cur ← shrinkSpecialAt fails cur idx
    cur ← shrinkElements shrinkTomlCase fails cur
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
    (trace : Array TomlFuzzCase) : IO CoverageTracker := do
  match ← checkEpisodeWithPy client trace true with
  | .ok bkts =>
    let mut tr := tracker
    for b in bkts do
      tr := tr.record b.op b.bucket
    return tr
  | .error err =>
    if err.startsWith "PYTHON_ORACLE_EOF" then
      throw (IO.userError s!"TOML_FUZZ_MISMATCH err={err} trace_size={trace.size} trace={reprStr trace}")
    let origTag := errorClassTag err
    let fails (cand : Array TomlFuzzCase) : IO Bool := do
      match ← checkEpisodeWithPy client cand false with
      | .ok _ => return false
      | .error e =>
        if e.startsWith "PYTHON_ORACLE_EOF" then
          throw (IO.userError s!"TOML_FUZZ_MISMATCH err={e} original_err={err} trace_size={trace.size}")
        return errorClassTag e == origTag
    let shrunk ← shrinkToFixedPoint fails trace
    let shrunkErr := match ← checkEpisodeWithPy client shrunk false with
      | .error e => e
      | .ok _ => err
    throw (IO.userError s!"TOML_FUZZ_MISMATCH err={shrunkErr} original_err={err} shrunk={reprStr shrunk}")

private def runTomlSuite (steps : Nat) (seedVal : UInt64) (isSmoke : Bool) : IO Unit := do
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
      let mut trace : Array TomlFuzzCase := Array.mkEmpty epLen
      for _ in [0 : epLen] do
        let (c, rN) := genTomlFuzzCase rng
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
    assertCoverage "toml" reportTracker requiredBuckets
    IO.println (reportTracker.formatReport "toml")
    IO.println s!"FUZZ_SUMMARY suite=toml steps={executedSteps} seed={seedVal}"
    closePyOracleClient client
  catch e =>
    closePyOracleClientQuiet client
    throw e

private def runTomlSelfTestShrink (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  let mut rng := Rng.seed (seedVal ^^^ 0x9e3779b97f4a7c15)
  let isSyntheticDupFault : TomlFuzzCase → Bool
    | .malformedStr s _ =>
      (s.splitOn "dup").length ≥ 3
    | _ => false
  let mut trace1 : Array TomlFuzzCase := Array.mkEmpty 17
  for _ in [0 : 16] do
    let (c, r1) := genTomlFuzzCase rng
    rng := r1
    if !isSyntheticDupFault c then
      trace1 := trace1.push c
  let (idx1, r2) := rng.nextRange 0 trace1.size
  let _ := r2
  let badItem := TomlFuzzCase.malformedStr "noise = 123456\ndup = 1\nextra = \"abcdef\"\ndup = 2\n" "duplicate_key"
  let injected1 := (trace1.extract 0 idx1).push badItem ++ trace1.extract idx1 trace1.size
  let failsDup (cand : Array TomlFuzzCase) : IO Bool := pure (cand.any isSyntheticDupFault)
  let shrunk1 ← shrinkToFixedPoint failsDup injected1
  unless ← failsDup shrunk1 do
    throw (IO.userError "TOML_SHRINK_SELFTEST_1: shrunk trace lost failure")
  if shrunk1.size != 1 then
    throw (IO.userError s!"TOML_SHRINK_SELFTEST_1: expected size 1, got {shrunk1.size}")
  match shrunk1[0]! with
  | .malformedStr s _ =>
    if s.length > 10 then
      throw (IO.userError s!"TOML_SHRINK_SELFTEST_1: shrunk string too long ({s.length}): {reprStr s}")
    IO.println s!"TOML_SHRINK_SELFTEST_1_OK: shrunk={reprStr s}"
  | other =>
    throw (IO.userError s!"TOML_SHRINK_SELFTEST_1: unexpected variant {reprStr other}")

  let client ← startPyOracleClient
  try
    let goodDoc : TomlTable := #[("ok", .int 1)]
    let badDoc : TomlTable := #[
      ("a", .array #[.string "padding_one", .string "padding_two"]),
      ("b", .int 999)
    ]
    let injected2 : Array TomlFuzzCase := #[
      .validRender goodDoc "ok = 1\n" [],
      .validRender badDoc (LeanSwe.Toml.format badDoc) [],
      .validRender #[] "" []
    ]
    let buildSpoofBatch (cand : Array TomlFuzzCase) : PyOracleBatch := Id.run do
      let mut items : Array PyParseCheck := #[]
      for c in cand do
        if let .validRender d raw _ := c then
          let spoofTlv :=
            if ((LeanSwe.Toml.format d).splitOn "999").length > 1 then
              encodeCanonTomlPy #[]
            else
              encodeCanonTomlPy d
          items := items.push {
            rawBytes := raw.toUTF8
            mode := .ok
            expectedPyTlv := spoofTlv
            label := "selftest"
          }
      return { parses := items }
    let origErr ← match ← flushPyBatch client (buildSpoofBatch injected2) with
      | .ok () => throw (IO.userError "TOML_SHRINK_SELFTEST_2: spoofed batch unexpectedly passed")
      | .error e => pure e
    let origTag := errorClassTag origErr
    let failsPySpoof (cand : Array TomlFuzzCase) : IO Bool := do
      match ← flushPyBatch client (buildSpoofBatch cand) with
      | .ok () => return false
      | .error e =>
        if e.startsWith "PYTHON_ORACLE_EOF" then
          throw (IO.userError e)
        return errorClassTag e == origTag
    let shrunk2 ← shrinkToFixedPoint failsPySpoof injected2
    unless ← failsPySpoof shrunk2 do
      throw (IO.userError "TOML_SHRINK_SELFTEST_2: shrunk Python mismatch trace lost failure")
    if shrunk2.size != 1 then
      throw (IO.userError s!"TOML_SHRINK_SELFTEST_2: expected size 1, got {shrunk2.size}")
    IO.println s!"TOML_SHRINK_SELFTEST_2_OK: shrunk={reprStr shrunk2} tag={origTag}"

    let badYear0Raw := "d = 0000-02-30\n"
    let fakeYear0Date := Std.Time.PlainDate.ofYearMonthDayClip (Std.Time.Year.Offset.ofInt 0) 2 29
    let fakeYear2000Date := Std.Time.PlainDate.ofYearMonthDayClip (Std.Time.Year.Offset.ofInt 2000) 2 29
    let fakeDoc0 : TomlTable := #[("d", .localDate fakeYear0Date)]
    let fakeDoc2000 : TomlTable := #[("d", .localDate fakeYear2000Date)]
    let buggyParseYear0Only (inp : String) : Except TomlError TomlTable :=
      if inp == badYear0Raw then .ok fakeDoc0 else LeanSwe.Toml.parse inp
    match verifyAndQueueYearZero buggyParseYear0Only badYear0Raw fakeDoc0 "selftestYear0Asym" {} with
    | .ok _ =>
      throw (IO.userError "TOML_YEAR0_SELFTEST_ASYM: invalid 0000-02-30 unexpectedly passed Lean rewrite check")
    | .error asymErr =>
      unless asymErr.startsWith "YEAR_ZERO_REWRITE_PARSE_ERR:" do
        throw (IO.userError s!"TOML_YEAR0_SELFTEST_ASYM: unexpected error {asymErr}")
    let buggyParseBoth (inp : String) : Except TomlError TomlTable :=
      if inp == badYear0Raw then .ok fakeDoc0
      else if inp == "d = 2000-02-30\n" then .ok fakeDoc2000
      else LeanSwe.Toml.parse inp
    let symBatch ← match verifyAndQueueYearZero buggyParseBoth badYear0Raw fakeDoc0 "selftestYear0Sym" {} with
      | .ok b => pure b
      | .error e => throw (IO.userError s!"TOML_YEAR0_SELFTEST_SYM_SETUP: {e}")
    match ← flushPyBatch client symBatch with
    | .ok () =>
      throw (IO.userError "TOML_YEAR0_SELFTEST_SYM: invalid 0000-02-30 unexpectedly passed Python oracle")
    | .error pyRejErr =>
      unless (pyRejErr.splitOn "P_LEAN_OK_PY_ERR[selftestYear0Sym:rewritten2000]").length > 1 do
        throw (IO.userError s!"TOML_YEAR0_SELFTEST_SYM: unexpected Python error {pyRejErr}")
    let wrongDay0 := Std.Time.PlainDate.ofYearMonthDayClip (Std.Time.Year.Offset.ofInt 0) 2 28
    let wrongDay2000 := Std.Time.PlainDate.ofYearMonthDayClip (Std.Time.Year.Offset.ofInt 2000) 2 28
    let buggyParseWrongDay (inp : String) : Except TomlError TomlTable :=
      if inp == "d = 0000-02-29\n" then .ok #[("d", .localDate wrongDay0)]
      else if inp == "d = 2000-02-29\n" then .ok #[("d", .localDate wrongDay2000)]
      else LeanSwe.Toml.parse inp
    let astBatch ← match verifyAndQueueYearZero buggyParseWrongDay "d = 0000-02-29\n"
        #[("d", .localDate wrongDay0)] "selftestYear0Ast" {} with
      | .ok b => pure b
      | .error e => throw (IO.userError s!"TOML_YEAR0_SELFTEST_AST_SETUP: {e}")
    match ← flushPyBatch client astBatch with
    | .ok () =>
      throw (IO.userError "TOML_YEAR0_SELFTEST_AST: wrong year-0000 day unexpectedly passed Python oracle")
    | .error astErr =>
      unless (astErr.splitOn "P_AST_MISMATCH[selftestYear0Ast:rewritten2000]").length > 1 do
        throw (IO.userError s!"TOML_YEAR0_SELFTEST_AST: unexpected Python error {astErr}")
    IO.println "TOML_YEAR0_ORACLE_SELFTEST_OK"
    closePyOracleClient client
  catch e =>
    closePyOracleClientQuiet client
    throw e

/-- Differential fuzzing suite for `LeanSwe.Toml` against `LeanSwe.Toml.Model` and Python 3 `tomllib`. -/
def suite : FuzzSuite := {
  name := "toml"
  description := "Differential fuzzer for LeanSwe.Toml 1.0 parse/format/encode/decode/accessors against Model.render and Python 3 tomllib"
  runSmoke := fun cfg =>
    runTomlSuite 400 cfg.seed true
  runFuzz := fun cfg =>
    runTomlSuite cfg.steps cfg.seed false
  selfTestShrink := runTomlSelfTestShrink
}

end Fuzz.Toml
