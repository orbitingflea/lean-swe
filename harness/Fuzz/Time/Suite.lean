import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Coverage
import Fuzz.Common.Suite
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.Time.Types
import LeanSwe.Time.Model
import LeanSwe.Time.Interface

namespace Fuzz.Time

open Fuzz.Common
open LeanSwe.Time

private def exceptEq {ε α : Type} [BEq ε] [BEq α] : Except ε α → Except ε α → Bool
  | .ok a, .ok b => a == b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

private def durOfNs (ns : Int) : Std.Time.Duration :=
  Std.Time.Duration.ofNanoseconds (Std.Time.Nanosecond.Offset.ofInt ns)

private def tsOfNs (ns : Int) : Std.Time.Timestamp :=
  Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch (Std.Time.Nanosecond.Offset.ofInt ns)

private def dateOfDay (day : Int) : Std.Time.PlainDate :=
  Std.Time.PlainDate.ofEpochDay (Std.Time.Day.Offset.ofInt day)

private inductive TimeOp where
  | nowWall
  | nowMono
  | sleepMs (ms : Nat)
  | sleepDur (ns : Int)
  | measureAct (act : Model.StepAction)
  | pureElapsed (startMono stopMono : Nat)
  | pureDeadline (startMono : Nat) (limitNs : Int)
  | pureExpired (nowMono deadlineMono : Nat)
  | pureFormatTs (ns : Int)
  | pureDateRoundTrip (epochDay : Int)
  | pureParseIso (raw : String)
  | pureParseDate (raw : String)
  deriving BEq, DecidableEq

private def reprTimeOp : TimeOp → String
  | .nowWall => "nowWall"
  | .nowMono => "nowMono"
  | .sleepMs ms => s!"sleepMs({ms})"
  | .sleepDur ns => s!"sleepDur({ns})"
  | .measureAct act => s!"measureAct({repr act})"
  | .pureElapsed a b => s!"pureElapsed({a}, {b})"
  | .pureDeadline s l => s!"pureDeadline({s}, {l})"
  | .pureExpired n d => s!"pureExpired({n}, {d})"
  | .pureFormatTs ns => s!"pureFormatTs({ns})"
  | .pureDateRoundTrip d => s!"pureDateRoundTrip({d})"
  | .pureParseIso s => s!"pureParseIso({repr s})"
  | .pureParseDate s => s!"pureParseDate({repr s})"

private structure TimeRunState where
  model : Model.TimeModelState
  tracker : CoverageTracker := CoverageTracker.empty
  steps : Nat := 0
  posSleeps : Nat := 0

private def requiredBuckets : Array CoverageBucket := #[
  bucket "nowTimestamp" "ok",
  bucket "monoNanosNow" "ok",
  bucket "sleepMs" "zero",
  bucket "sleepMs" "pos",
  bucket "sleepDuration" "neg",
  bucket "sleepDuration" "zero",
  bucket "sleepDuration" "pos.subms",
  bucket "sleepDuration" "pos.ms",
  bucket "measure" "pureNat",
  bucket "measure" "sleepMsNat",
  bucket "measure" "sleepDurationNat",
  bucket "measure" "readMono",
  bucket "measure" "readWallNat",
  bucket "measure" "seq",
  bucket "elapsedDuration" "le",
  bucket "elapsedDuration" "gt",
  bucket "deadlineNanos" "nonneg",
  bucket "deadlineNanos" "neg",
  bucket "isMonoExpired" "true",
  bucket "isMonoExpired" "false",
  bucket "formatUtcIso8601" "epoch",
  bucket "formatUtcIso8601" "pos",
  bucket "formatUtcIso8601" "neg",
  bucket "formatUtcIso8601" "preEpochSubsec",
  bucket "formatUtcIso8601" "yearGt9999",
  bucket "dateRoundTrip" "epoch",
  bucket "dateRoundTrip" "leapDay",
  bucket "dateRoundTrip" "negYear",
  bucket "dateRoundTrip" "normal",
  bucket "parseUtcIso8601" "ok.z",
  bucket "parseUtcIso8601" "ok.zLower",
  bucket "parseUtcIso8601" "ok.frac",
  bucket "parseUtcIso8601" "ok.offsetPos",
  bucket "parseUtcIso8601" "ok.offsetNeg",
  bucket "parseUtcIso8601" "ok.offsetSec",
  bucket "parseUtcIso8601" "ok.negYear",
  bucket "parseUtcIso8601" "err.invalidFormat",
  bucket "parseUtcDate" "ok.pos",
  bucket "parseUtcDate" "ok.leap",
  bucket "parseUtcDate" "ok.neg",
  bucket "parseUtcDate" "err.invalidFormat",
  bucket "mkTimeOps.scripted" "eintrRetry1",
  bucket "mkTimeOps.scripted" "eintrRetryMax"
]

private def initRunState : IO TimeRunState := do
  let ts ← nowTimestamp
  let wallNs := ts.toNanosecondsSinceUnixEpoch.val
  let monoNs ← monoNanosNow
  unless Model.isValidTimestampNanos wallNs do
    throw (IO.userError s!"TIME_INIT_INVALID_WALL: {wallNs}")
  unless Model.isValidMonoNanos monoNs do
    throw (IO.userError s!"TIME_INIT_INVALID_MONO: {monoNs}")
  return { model := { wallNanos := wallNs, monoNanos := monoNs } }

private def actionMinSleepNanos : Model.StepAction → Nat
  | .pureNat _ => 0
  | .sleepMsNat ms _ => ms * 1000000
  | .sleepDurationNat d _ => Model.sleepNanosLowerBound d
  | .readMono => 0
  | .readWallNat _ => 0
  | .seq a b => actionMinSleepNanos a + actionMinSleepNanos b

private def actionExpectedVal? : Model.StepAction → Option Nat
  | .pureNat v => some v
  | .sleepMsNat _ v => some v
  | .sleepDurationNat _ v => some v
  | .readMono => none
  | .readWallNat v => some v
  | .seq _ b => actionExpectedVal? b

private def actionBucketName : Model.StepAction → String
  | .pureNat _ => "pureNat"
  | .sleepMsNat _ _ => "sleepMsNat"
  | .sleepDurationNat _ _ => "sleepDurationNat"
  | .readMono => "readMono"
  | .readWallNat _ => "readWallNat"
  | .seq _ _ => "seq"

private def execIoAction (wallRef : IO.Ref Int) : Model.StepAction → IO Nat
  | .pureNat v => pure v
  | .sleepMsNat ms v => do
    sleepMs ms
    pure v
  | .sleepDurationNat d v => do
    sleepDuration d
    pure v
  | .readMono => monoNanosNow
  | .readWallNat v => do
    let ts ← nowTimestamp
    let ns := ts.toNanosecondsSinceUnixEpoch.val
    let prev ← wallRef.get
    unless Model.isValidTimestampNanos ns && prev ≤ ns do
      throw (IO.userError s!"TIME_WALL_REGRESSED_IN_MEASURE: prev={prev} cur={ns}")
    wallRef.set ns
    pure v
  | .seq a b => do
    let _ ← execIoAction wallRef a
    execIoAction wallRef b

private def classifyIsoOkBucket (raw : String) : String :=
  if raw.startsWith "-" then "ok.negYear"
  else if raw.endsWith "z" then "ok.zLower"
  else if raw.endsWith "Z" then
    if raw.toList.contains '.' then "ok.frac" else "ok.z"
  else
    let afterT := match raw.splitOn "T" with
      | [_, rhs] => rhs
      | _ => match raw.splitOn "t" with
        | [_, rhs] => rhs
        | _ => raw
    let hasPlus := afterT.toList.contains '+'
    let hasMinus := afterT.toList.contains '-'
    let colonCount := (afterT.toList.filter (· == ':')).length
    if colonCount >= 4 then "ok.offsetSec"
    else if hasPlus then "ok.offsetPos"
    else if hasMinus then "ok.offsetNeg"
    else "ok.z"

private def execTimeOp (st : TimeRunState) (op : TimeOp) (emitCov : Bool := true) : IO TimeRunState := do
  let mut st := { st with steps := st.steps + 1 }
  match op with
  | .nowWall =>
    let ts ← nowTimestamp
    let ns := ts.toNanosecondsSinceUnixEpoch.val
    unless Model.isValidTimestampNanos ns do
      throw (IO.userError s!"TIME_WALL_OUT_OF_BOUNDS: {ns}")
    unless st.model.wallNanos ≤ ns do
      throw (IO.userError s!"TIME_WALL_NON_MONOTONIC: prev={st.model.wallNanos} cur={ns}")
    let iso := formatUtcIso8601 ts
    unless iso == Model.formatUtcIso8601 ts do
      throw (IO.userError s!"TIME_WALL_FORMAT_MISMATCH: {repr iso}")
    unless exceptEq (parseUtcIso8601 iso) (.ok ts) do
      throw (IO.userError s!"TIME_WALL_ROUNDTRIP_MISMATCH: {repr iso}")
    st := { st with
      model := { st.model with wallNanos := ns }
      tracker := st.tracker.record "nowTimestamp" "ok" }
  | .nowMono =>
    let ns ← monoNanosNow
    unless Model.isValidMonoNanos ns do
      throw (IO.userError s!"TIME_MONO_OUT_OF_BOUNDS: {ns}")
    unless st.model.monoNanos ≤ ns do
      throw (IO.userError s!"TIME_MONO_NON_MONOTONIC: prev={st.model.monoNanos} cur={ns}")
    st := { st with
      model := { st.model with monoNanos := ns }
      tracker := st.tracker.record "monoNanosNow" "ok" }
  | .sleepMs ms =>
    let monoBefore ← monoNanosNow
    unless Model.isValidMonoNanos monoBefore && st.model.monoNanos ≤ monoBefore do
      throw (IO.userError s!"TIME_SLEEPMS_PRE_MONO: prev={st.model.monoNanos} before={monoBefore}")
    sleepMs ms
    let monoAfter ← monoNanosNow
    let lower := min Model.maxMonoNanos (monoBefore + ms * 1000000)
    unless Model.isValidMonoNanos monoAfter && lower ≤ monoAfter do
      throw (IO.userError s!"TIME_SLEEPMS_SHORT: ms={ms} before={monoBefore} after={monoAfter} lower={lower}")
    st := { st with
      model := { st.model with monoNanos := monoAfter }
      posSleeps := st.posSleeps + (if ms > 0 then 1 else 0)
      tracker := st.tracker.record "sleepMs" (if ms == 0 then "zero" else "pos") }
  | .sleepDur ns =>
    let d := durOfNs ns
    let monoBefore ← monoNanosNow
    unless Model.isValidMonoNanos monoBefore && st.model.monoNanos ≤ monoBefore do
      throw (IO.userError s!"TIME_SLEEPDUR_PRE_MONO: prev={st.model.monoNanos} before={monoBefore}")
    sleepDuration d
    let monoAfter ← monoNanosNow
    let lower := min Model.maxMonoNanos (monoBefore + Model.sleepNanosLowerBound d)
    unless Model.isValidMonoNanos monoAfter && lower ≤ monoAfter do
      throw (IO.userError s!"TIME_SLEEPDUR_SHORT: ns={ns} before={monoBefore} after={monoAfter} lower={lower}")
    let b :=
      if ns < 0 then "neg"
      else if ns == 0 then "zero"
      else if ns < 1000000 then "pos.subms"
      else "pos.ms"
    st := { st with
      model := { st.model with monoNanos := monoAfter }
      posSleeps := st.posSleeps + (if ns > 0 then 1 else 0)
      tracker := st.tracker.record "sleepDuration" b }
  | .measureAct act =>
    let monoBefore ← monoNanosNow
    unless Model.isValidMonoNanos monoBefore && st.model.monoNanos ≤ monoBefore do
      throw (IO.userError s!"TIME_MEASURE_PRE_MONO: prev={st.model.monoNanos} before={monoBefore}")
    let wallRef ← IO.mkRef st.model.wallNanos
    let (val, elapsed) ← measure (execIoAction wallRef act)
    let monoAfter ← monoNanosNow
    let wallAfter ← wallRef.get
    unless Model.isValidMonoNanos monoAfter && monoBefore ≤ monoAfter do
      throw (IO.userError s!"TIME_MEASURE_POST_MONO: before={monoBefore} after={monoAfter}")
    let elapsedNs := elapsed.toNanoseconds.val
    let minSleep := actionMinSleepNanos act
    unless 0 ≤ elapsedNs && elapsedNs ≤ Int.ofNat (monoAfter - monoBefore) do
      throw (IO.userError s!"TIME_MEASURE_ELAPSED_BOUNDS: elapsed={elapsedNs} outer={monoAfter - monoBefore}")
    unless Int.ofNat minSleep ≤ elapsedNs do
      throw (IO.userError s!"TIME_MEASURE_SHORT_SLEEP: elapsed={elapsedNs} minSleep={minSleep}")
    unless elapsed == Model.elapsedDuration monoBefore (monoBefore + elapsedNs.toNat) do
      throw (IO.userError s!"TIME_MEASURE_ELAPSED_EQ: elapsed={repr elapsed}")
    match actionExpectedVal? act with
    | some expectedVal =>
      unless val == expectedVal do
        throw (IO.userError s!"TIME_MEASURE_VAL: got={val} expected={expectedVal}")
    | none =>
      unless monoBefore ≤ val && val ≤ monoAfter do
        throw (IO.userError s!"TIME_MEASURE_MONO_VAL: val={val} range=[{monoBefore}, {monoAfter}]")
    st := { st with
      model := { wallNanos := wallAfter, monoNanos := monoAfter }
      posSleeps := st.posSleeps + (if minSleep > 0 then 1 else 0)
      tracker := st.tracker.record "measure" (actionBucketName act) }
  | .pureElapsed a b =>
    let actual := elapsedDuration a b
    let expected := Model.elapsedDuration a b
    unless actual == expected do
      throw (IO.userError s!"TIME_ELAPSED_MISMATCH: a={a} b={b} actual={repr actual} expected={repr expected}")
    st := { st with tracker := st.tracker.record "elapsedDuration" (if a ≤ b then "le" else "gt") }
  | .pureDeadline startMono limitNs =>
    let d := durOfNs limitNs
    let actual := deadlineNanos startMono d
    let expected := Model.deadlineNanos startMono d
    unless actual == expected do
      throw (IO.userError s!"TIME_DEADLINE_MISMATCH: start={startMono} limit={limitNs} actual={actual} expected={expected}")
    st := { st with tracker := st.tracker.record "deadlineNanos" (if limitNs ≥ 0 then "nonneg" else "neg") }
  | .pureExpired nowMono deadlineMono =>
    let actual := isMonoExpired nowMono deadlineMono
    let expected := Model.isMonoExpired nowMono deadlineMono
    unless actual == expected do
      throw (IO.userError s!"TIME_EXPIRED_MISMATCH: now={nowMono} dl={deadlineMono} actual={actual} expected={expected}")
    st := { st with tracker := st.tracker.record "isMonoExpired" (if actual then "true" else "false") }
  | .pureFormatTs ns =>
    let ts := tsOfNs ns
    let iso := formatUtcIso8601 ts
    let isoM := Model.formatUtcIso8601 ts
    let cmp := formatUtcCompact ts
    let cmpM := Model.formatUtcCompact ts
    let dt := utcDateOfTimestamp ts
    let dtM := Model.utcDateOfTimestamp ts
    unless iso == isoM do
      throw (IO.userError s!"TIME_FORMAT_ISO_MISMATCH: ns={ns} actual={repr iso} expected={repr isoM}")
    unless cmp == cmpM do
      throw (IO.userError s!"TIME_FORMAT_COMPACT_MISMATCH: ns={ns} actual={repr cmp} expected={repr cmpM}")
    unless dt == dtM do
      throw (IO.userError s!"TIME_UTCDATE_MISMATCH: ns={ns} actual={repr dt} expected={repr dtM}")
    let yr := dt.year.toInt
    if -9999 ≤ yr && yr ≤ 9999 then
      unless exceptEq (parseUtcIso8601 iso) (.ok ts) do
        throw (IO.userError s!"TIME_ISO_ROUNDTRIP_MISMATCH: ns={ns} iso={repr iso}")
    let b :=
      if ns == 0 then "epoch"
      else if yr > 9999 then "yearGt9999"
      else if -1000000000 < ns && ns < 0 then "preEpochSubsec"
      else if ns > 0 then "pos"
      else "neg"
    st := { st with tracker := st.tracker.record "formatUtcIso8601" b }
  | .pureDateRoundTrip epochDay =>
    let d := dateOfDay epochDay
    let s := formatUtcDate d
    let sM := Model.formatUtcDate d
    let ts := timestampOfUtcDate d
    let tsM := Model.timestampOfUtcDate d
    unless s == sM do
      throw (IO.userError s!"TIME_FORMAT_DATE_MISMATCH: day={epochDay} actual={repr s} expected={repr sM}")
    unless ts == tsM do
      throw (IO.userError s!"TIME_TS_OF_DATE_MISMATCH: day={epochDay} actual={repr ts} expected={repr tsM}")
    unless utcDateOfTimestamp ts == d do
      throw (IO.userError s!"TIME_DATE_TS_ROUNDTRIP: day={epochDay}")
    let prevTs := tsOfNs (ts.toNanosecondsSinceUnixEpoch.val - 1)
    unless (utcDateOfTimestamp prevTs).toEpochDay.val == epochDay - 1 do
      throw (IO.userError s!"TIME_DATE_MIDNIGHT_MINUS_1NS: day={epochDay}")
    let yr := d.year.toInt
    if -9999 ≤ yr && yr ≤ 9999 then
      unless exceptEq (parseUtcDate s) (.ok d) do
        throw (IO.userError s!"TIME_DATE_PARSE_ROUNDTRIP: day={epochDay} s={repr s}")
    let b :=
      if epochDay == 0 then "epoch"
      else if d.month.val.toNat == 2 && d.day.val.toNat == 29 then "leapDay"
      else if yr < 0 then "negYear"
      else "normal"
    st := { st with tracker := st.tracker.record "dateRoundTrip" b }
  | .pureParseIso raw =>
    let actual := parseUtcIso8601 raw
    let expected := Model.parseUtcIso8601 raw
    unless exceptEq actual expected do
      throw (IO.userError s!"TIME_PARSE_ISO_MISMATCH: raw={repr raw} actual={repr actual} expected={repr expected}")
    match actual with
    | .ok _ =>
      st := { st with tracker := st.tracker.record "parseUtcIso8601" (classifyIsoOkBucket raw) }
    | .error e =>
      if e.message.isEmpty then
        throw (IO.userError s!"TIME_PARSE_ISO_EMPTY_MSG: raw={repr raw} err={repr e}")
      if emitCov then
        logErrHit "LeanSwe.Time.parseUtcIso8601" "LeanSwe.Time.TimeErrorKind.invalidFormat" "real"
      st := { st with tracker := st.tracker.record "parseUtcIso8601" "err.invalidFormat" }
  | .pureParseDate raw =>
    let actual := parseUtcDate raw
    let expected := Model.parseUtcDate raw
    unless exceptEq actual expected do
      throw (IO.userError s!"TIME_PARSE_DATE_MISMATCH: raw={repr raw} actual={repr actual} expected={repr expected}")
    match actual with
    | .ok d =>
      let b :=
        if d.year.toInt < 0 then "ok.neg"
        else if d.month.val.toNat == 2 && d.day.val.toNat == 29 then "ok.leap"
        else "ok.pos"
      st := { st with tracker := st.tracker.record "parseUtcDate" b }
    | .error e =>
      if e.message.isEmpty then
        throw (IO.userError s!"TIME_PARSE_DATE_EMPTY_MSG: raw={repr raw} err={repr e}")
      if emitCov then
        logErrHit "LeanSwe.Time.parseUtcDate" "LeanSwe.Time.TimeErrorKind.invalidFormat" "real"
      st := { st with tracker := st.tracker.record "parseUtcDate" "err.invalidFormat" }
  return st

private def curatedCorpus : Array TimeOp := #[
  .nowWall,
  .nowMono,
  .sleepMs 0,
  .sleepMs 1,
  .sleepDur (-5000000000),
  .sleepDur (-1),
  .sleepDur 0,
  .sleepDur 1,
  .sleepDur 500000,
  .sleepDur 1500000,
  .measureAct (.pureNat 42),
  .measureAct (.sleepMsNat 1 7),
  .measureAct (.sleepDurationNat (durOfNs 1000000) 9),
  .measureAct .readMono,
  .measureAct (.readWallNat 13),
  .measureAct (.seq (.readWallNat 1) (.seq .readMono (.pureNat 99))),
  .pureElapsed 100 100,
  .pureElapsed 100 250,
  .pureElapsed 300 250,
  .pureDeadline 1000 0,
  .pureDeadline 1000 5000000,
  .pureDeadline 1000 (-5000000),
  .pureExpired 100 100,
  .pureExpired 101 100,
  .pureExpired 99 100,
  .pureFormatTs 0,
  .pureFormatTs 1,
  .pureFormatTs (-1),
  .pureFormatTs (-999999999),
  .pureFormatTs (-86400000000000),
  .pureFormatTs 1700000000123456789,
  .pureFormatTs 315569520000000000000,
  .pureDateRoundTrip 0,
  .pureDateRoundTrip (-1),
  .pureDateRoundTrip 19782,
  .pureDateRoundTrip (-719528),
  .pureDateRoundTrip (-720000),
  .pureDateRoundTrip 11016,
  .pureParseIso "1970-01-01T00:00:00Z",
  .pureParseIso "1970-01-01t00:00:00z",
  .pureParseIso "2024-02-29T23:59:59.5Z",
  .pureParseIso "2024-02-29T23:59:59.123456789Z",
  .pureParseIso "2024-06-15T12:34:56+05:30",
  .pureParseIso "2024-06-15T12:34:56-07:00",
  .pureParseIso "2024-06-15T12:34:56+01:02:03",
  .pureParseIso "-0001-12-31T23:59:59.999999999Z",
  .pureParseIso "",
  .pureParseIso "2024-02-29",
  .pureParseIso "2023-02-29T00:00:00Z",
  .pureParseIso "2024-01-01 00:00:00Z",
  .pureParseIso "2024-01-01T24:00:00Z",
  .pureParseIso "2024-01-01T00:60:00Z",
  .pureParseIso "2024-01-01T00:00:60Z",
  .pureParseIso "2024-01-01T00:00:00.Z",
  .pureParseIso "2024-01-01T00:00:00.1234567890Z",
  .pureParseIso "2024-01-01T00:00:00",
  .pureParseIso "2024-01-01T00:00:00+24:00",
  .pureParseIso "2024-01-01T00:00:00+00:60",
  .pureParseIso "2024-01-01T00:00:00+00:00:60",
  .pureParseIso "2024-01-01T00:00:00+00:00x",
  .pureParseIso "-0000-01-01T00:00:00Z",
  .pureParseDate "1970-01-01",
  .pureParseDate "2000-02-29",
  .pureParseDate "2024-02-29",
  .pureParseDate "-0001-01-01",
  .pureParseDate "",
  .pureParseDate "2024-02-30",
  .pureParseDate "1900-02-29",
  .pureParseDate "2024-00-10",
  .pureParseDate "2024-13-10",
  .pureParseDate "2024-01-00",
  .pureParseDate "2024-01-32",
  .pureParseDate "2024/01/01",
  .pureParseDate "2024-01/01",
  .pureParseDate "-0000-01-01",
  .pureParseDate "2024-01-01x"
]

private def genRandomTimeString (r : Rng) (maxLen : Nat) : String × Rng := Id.run do
  let (len, r1) := r.nextRange 0 maxLen
  let mut cur := r1
  let mut cs : List Char := []
  let alphabet : Array Char :=
    #['0','1','2','3','4','5','6','7','8','9','-','T','t',':','.','Z','z','+',' ','/','x']
  for _ in [:len] do
    let (ch, nxt) := cur.choose alphabet '0'
    cur := nxt
    cs := ch :: cs
  return (String.ofList cs.reverse, cur)

private def genRandomOp (r : Rng) (allowPosSleep : Bool) : TimeOp × Rng :=
  let (tag, r1) := r.nextNat 12
  match tag with
  | 0 => (.nowWall, r1)
  | 1 => (.nowMono, r1)
  | 2 =>
    if allowPosSleep then
      let (ms, r2) := r1.nextRange 0 2
      (.sleepMs ms, r2)
    else
      (.sleepMs 0, r1)
  | 3 =>
    let (mode, r2) := r1.nextNat 4
    match mode with
    | 0 =>
      let (k, r3) := r2.nextRange 1 5000000
      (.sleepDur (-(Int.ofNat k)), r3)
    | 1 => (.sleepDur 0, r2)
    | 2 =>
      if allowPosSleep then
        let (k, r3) := r2.nextRange 1 999999
        (.sleepDur (Int.ofNat k), r3)
      else
        (.sleepDur 0, r2)
    | _ =>
      if allowPosSleep then
        let (k, r3) := r2.nextRange 1000000 2000000
        (.sleepDur (Int.ofNat k), r3)
      else
        (.sleepDur (-1), r2)
  | 4 =>
    let (kind, r2) := r1.nextNat 6
    let (v, r3) := r2.nextRange 0 1000
    match kind with
    | 0 => (.measureAct (.pureNat v), r3)
    | 1 =>
      let ms := if allowPosSleep then 1 else 0
      (.measureAct (.sleepMsNat ms v), r3)
    | 2 =>
      let ns : Int := if allowPosSleep then 1000000 else 0
      (.measureAct (.sleepDurationNat (durOfNs ns) v), r3)
    | 3 => (.measureAct .readMono, r3)
    | 4 => (.measureAct (.readWallNat v), r3)
    | _ => (.measureAct (.seq .readMono (.readWallNat v)), r3)
  | 5 =>
    let (a, r2) := r1.nextRange 0 1000000000
    let (b, r3) := r2.nextRange 0 1000000000
    (.pureElapsed a b, r3)
  | 6 =>
    let (s, r2) := r1.nextRange 0 1000000000
    let (l, r3) := r2.nextIntRange (-500000000) 500000000
    (.pureDeadline s l, r3)
  | 7 =>
    let (n, r2) := r1.nextRange 0 1000000000
    let (d, r3) := r2.nextRange 0 1000000000
    (.pureExpired n d, r3)
  | 8 =>
    let (ns, r2) := r1.nextIntRange (-300000000000000000000) 300000000000000000000
    (.pureFormatTs ns, r2)
  | 9 =>
    let (day, r2) := r1.nextIntRange (-4300000) 2900000
    (.pureDateRoundTrip day, r2)
  | 10 =>
    let (valid, r2) := r1.nextBool
    if valid then
      let (ns, r3) := r2.nextIntRange (-62167219200000000000) 253402300799999999999
      (.pureParseIso (Model.formatUtcIso8601 (tsOfNs ns)), r3)
    else
      let (s, r3) := genRandomTimeString r2 36
      (.pureParseIso s, r3)
  | _ =>
    let (valid, r2) := r1.nextBool
    if valid then
      let (day, r3) := r2.nextIntRange (-719528) 2932896
      (.pureParseDate (Model.formatUtcDate (dateOfDay day)), r3)
    else
      let (s, r3) := genRandomTimeString r2 16
      (.pureParseDate s, r3)

private def runTrace (ops : Array TimeOp) (st0 : TimeRunState) (emitCov : Bool := true) :
    IO TimeRunState := do
  let mut st := st0
  for op in ops do
    st ← execTimeOp st op emitCov
  return st

private def runScriptedSleepEintrChecks (st : TimeRunState) : IO TimeRunState := do
  let checkRetries (eintrCount : Nat) : IO Unit := do
    let callsRef ← IO.mkRef 0
    let startTs : LeanSwe.LinuxSyscall.TimeRand.Timespec := { sec := 10, nsec := 500000000 }
    let expectedTarget : LeanSwe.LinuxSyscall.TimeRand.Timespec := { sec := 10, nsec := 505000000 }
    let ops : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM IO := {
      clock_gettime := fun clk =>
        match clk with
        | .monotonic => pure (.ok startTs)
        | .realtime => pure (.ok startTs)
      clock_nanosleep := fun clk abstime reqTs => do
        unless clk == .monotonic && abstime == true && reqTs == expectedTarget do
          throw (IO.userError s!"TIME_SCRIPT_SLEEP_ARGS: clk={repr clk} abs={abstime} req={repr reqTs}")
        let c ← callsRef.get
        callsRef.set (c + 1)
        if c < eintrCount then
          pure (.error LeanSwe.LinuxSyscall.Errno.EINTR)
        else
          pure (.ok ())
      getrandom := fun _ _ => pure (.error LeanSwe.LinuxSyscall.Errno.EINVAL)
    }
    (mkTimeOps ops).sleep 5
    let totalCalls ← callsRef.get
    unless totalCalls == eintrCount + 1 do
      throw (IO.userError s!"TIME_SCRIPT_SLEEP_CALLS: eintr={eintrCount} got={totalCalls}")
  checkRetries 1
  checkRetries MAX_EINTR_RETRIES
  let tr := (st.tracker.record "mkTimeOps.scripted" "eintrRetry1").record "mkTimeOps.scripted" "eintrRetryMax"
  return { st with tracker := tr, steps := st.steps + 2 }

private def runSmokeImpl (cfg : FuzzConfig) : IO Unit := do
  let mut st ← initRunState
  st ← runTrace curatedCorpus st true
  st ← runScriptedSleepEintrChecks st
  let mut rng := Rng.seed (cfg.seed ^^^ 0x517cc1b727220a95)
  for _ in [:256] do
    let (op, r') := genRandomOp rng (st.posSleeps < 8)
    rng := r'
    st ← execTimeOp st op true
  recordSuiteSteps st.steps
  IO.println (st.tracker.formatReport "time")
  assertCoverage "time" st.tracker requiredBuckets
  IO.println s!"TIME_SMOKE_OK steps={st.steps} pos_sleeps={st.posSleeps}"

private def runFuzzImpl (cfg : FuzzConfig) : IO Unit := do
  let mut st ← initRunState
  st ← runTrace curatedCorpus st true
  st ← runScriptedSleepEintrChecks st
  let mut rng := Rng.seed (cfg.seed ^^^ 0x6a09e667f3bcc908)
  for _ in [:cfg.steps] do
    let (op, r') := genRandomOp rng (st.posSleeps < 20)
    rng := r'
    st ← execTimeOp st op true
  recordSuiteSteps st.steps
  IO.println (st.tracker.formatReport "time")
  assertCoverage "time" st.tracker requiredBuckets
  IO.println s!"TIME_FUZZ_OK steps={st.steps} pos_sleeps={st.posSleeps} seed={cfg.seed}"

private def selfTestShrinkImpl (seedVal : UInt64) : IO Unit := do
  let mut rng := Rng.seed (seedVal ^^^ 0xbb67ae8584caa73b)
  let mut trace1 : Array TimeOp := Array.mkEmpty 24
  for _ in [:24] do
    let (op, r') := genRandomOp rng false
    rng := r'
    trace1 := trace1.push op
  let fault1 : TimeOp := .pureParseIso "INJECTED-TIME-SINGLE-FAULT-0001"
  let (idx1, r2) := rng.nextNat trace1.size
  rng := r2
  trace1 := trace1.set! idx1 fault1
  let fails1 (xs : Array TimeOp) : IO Bool := do
    let st0 ← initRunState
    let _ ← runTrace xs st0 false
    return xs.any (· == fault1)
  match ← verifyShrinker fails1 trace1 1 with
  | .error msg => throw (IO.userError s!"TIME_SHRINK_SINGLE_FAILED: {msg}")
  | .ok shrunk =>
    unless shrunk == #[fault1] do
      let shown := shrunk.toList.map reprTimeOp
      throw (IO.userError s!"TIME_SHRINK_SINGLE_MISMATCH: {shown}")
  let mut trace2 : Array TimeOp := Array.mkEmpty 24
  for _ in [:24] do
    let (op, r') := genRandomOp rng false
    rng := r'
    trace2 := trace2.push op
  let faultA : TimeOp := .pureParseDate "INJECTED-TIME-PAIR-A"
  let faultB : TimeOp := .pureParseDate "INJECTED-TIME-PAIR-B"
  let (idxA, r3) := rng.nextRange 0 11
  let (idxB, _) := r3.nextRange 12 23
  trace2 := trace2.set! idxA faultA
  trace2 := trace2.set! idxB faultB
  let fails2 (xs : Array TimeOp) : IO Bool := do
    let st0 ← initRunState
    let _ ← runTrace xs st0 false
    let mut sawA := false
    for x in xs do
      if x == faultA then sawA := true
      else if x == faultB && sawA then return true
    return false
  match ← verifyShrinker fails2 trace2 2 with
  | .error msg => throw (IO.userError s!"TIME_SHRINK_PAIR_FAILED: {msg}")
  | .ok shrunk =>
    unless shrunk == #[faultA, faultB] do
      let shown := shrunk.toList.map reprTimeOp
      throw (IO.userError s!"TIME_SHRINK_PAIR_MISMATCH: {shown}")

/-- Differential fuzz suite for `LeanSwe.Time` covering real OS clocks, sleep bounds, `measure`, and pure calendar/ISO-8601 equivalence. -/
def suite : FuzzSuite := {
  name := "time"
  description := "Real OS wall/monotonic clocks, sleep bounds, measure consistency, and ISO-8601/date differential fuzzing"
  runSmoke := runSmokeImpl
  runFuzz := runFuzzImpl
  selfTestShrink := selfTestShrinkImpl
}

end Fuzz.Time
