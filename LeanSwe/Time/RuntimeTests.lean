import Core.Assumptions
import LeanSwe.LinuxSyscall.TimeRand.RuntimeTests
import LeanSwe.Time.Interface

namespace LeanSwe.Time.RuntimeTests

open Std.Time

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except TimeError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertOkEq {α : Type} [BEq α] [Repr α]
    (actual : Except TimeError α) (expected : α) (msg : String) : IO Unit := do
  let v ← assertOk actual msg
  if !(v == expected) then
    throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr v}, expected {repr expected})")

private def assertErrInvalidFormat {α : Type} [Repr α]
    (res : Except TimeError α) (msg : String) : IO Unit := do
  match res with
  | .ok v => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected invalidFormat error, got {repr v})")
  | .error e =>
    if e.kind != .invalidFormat || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e})")

private def testUtcFormattingAndParsing : IO Unit := do
  let samples : Array Timestamp := #[
    Timestamp.ofSecondsSinceUnixEpoch 0,
    Timestamp.ofNanosecondsSinceUnixEpoch 1700000000123456789,
    Timestamp.ofNanosecondsSinceUnixEpoch (-1),
    Timestamp.ofSecondsSinceUnixEpoch (-62167219200),
    Timestamp.ofNanosecondsSinceUnixEpoch 253402300799999999999,
    Timestamp.ofSecondsSinceUnixEpoch 1709164800
  ]
  for ts in samples do
    let s := formatUtcIso8601 ts
    assertOkEq (parseUtcIso8601 s) ts s!"ISO 8601 round-trip failed for {s}"
    let compact := formatUtcCompact ts
    assertTrue (compact.length == 16 && compact.endsWith "Z")
      s!"compact UTC stamp malformed: {compact}"

  assertOkEq (parseUtcIso8601 "2026-11-14T18:15:00Z")
    (Timestamp.ofSecondsSinceUnixEpoch 1794680100) "second-precision Z parse"
  assertOkEq (parseUtcIso8601 "2026-11-14T20:15:00+02:00")
    (Timestamp.ofSecondsSinceUnixEpoch 1794680100) "positive offset normalization"
  assertOkEq (parseUtcIso8601 "2026-11-14T12:45:00-05:30")
    (Timestamp.ofSecondsSinceUnixEpoch 1794680100) "negative offset normalization"
  assertOkEq (parseUtcIso8601 "2024-02-29T23:59:59.500000000Z")
    (Timestamp.ofNanosecondsSinceUnixEpoch 1709251199500000000) "leap-day nanosecond parse"

  for bad in ["", "not-a-timestamp", "2024-02-30T00:00:00Z", "2026-11-14T18:15:00"] do
    assertErrInvalidFormat (parseUtcIso8601 bad) s!"expected invalidFormat for {bad}"

private def testUtcDates : IO Unit := do
  let dateSamples : Array PlainDate := #[
    PlainDate.ofEpochDay 0,
    PlainDate.ofYearMonthDayClip 0 1 1,
    PlainDate.ofYearMonthDayClip 2024 2 29,
    PlainDate.ofYearMonthDayClip 2026 11 14,
    PlainDate.ofYearMonthDayClip 9999 12 31
  ]
  for d in dateSamples do
    let s := formatUtcDate d
    assertOkEq (parseUtcDate s) d s!"UTC date round-trip failed for {s}"
    let midnight := timestampOfUtcDate d
    assertTrue (utcDateOfTimestamp midnight == d) s!"utcDateOfTimestamp midnight mismatch for {s}"
    let justBefore := midnight - Duration.ofNanoseconds 1
    assertTrue (compare (utcDateOfTimestamp justBefore) d == .lt)
      s!"1ns before UTC midnight must map to earlier day for {s}"

  let negOneNs := Timestamp.ofNanosecondsSinceUnixEpoch (-1)
  assertTrue (formatUtcDate (utcDateOfTimestamp negOneNs) == "1969-12-31")
    "1ns before Unix epoch must map to 1969-12-31"

  for bad in ["", "2024-02-30", "2026/11/14", "2026-13-01"] do
    assertErrInvalidFormat (parseUtcDate bad) s!"expected invalidFormat date for {bad}"

private def testRealClockAndSleep : IO Unit := do
  let ts0 ← nowTimestamp
  assertTrue (ts0.toSecondsSinceUnixEpoch.val >= 1700000000)
    s!"real UTC clock unexpectedly old: {ts0.toSecondsSinceUnixEpoch.val}"

  let m0 ← monoNanosNow
  sleepMs 0
  let m1 ← monoNanosNow
  assertTrue (m0 ≤ m1) s!"monotonic clock regressed across sleepMs 0: {m0} -> {m1}"

  let ((), elapsed) ← measure (sleepMs 25)
  let elapsedMs := elapsed.toMilliseconds.val
  assertTrue (elapsedMs >= 20 && elapsedMs < 5000)
    s!"sleepMs 25 elapsed out of bounds: {elapsedMs}ms"

  let ((), elapsedDur) ← measure (sleepDuration (Duration.ofMillisecond 15))
  let elapsedDurMs := elapsedDur.toMilliseconds.val
  assertTrue (elapsedDurMs >= 10 && elapsedDurMs < 5000)
    s!"sleepDuration 15ms elapsed out of bounds: {elapsedDurMs}ms"

  let ((), elapsedNeg) ← measure (sleepDuration (Duration.ofSeconds (-5)))
  assertTrue (elapsedNeg.toMilliseconds.val < 1000)
    s!"sleepDuration (-5s) should be immediate, took {elapsedNeg.toMilliseconds.val}ms"

  let fakeInit : FakeClock := { wall := Timestamp.ofSecondsSinceUnixEpoch 100, monoNanos := 500 }
  let ((val, fElapsed), fakeEnd) :=
    (fakeApi.measure (do fakeApi.sleepMs 4294967297; pure 99)).run fakeInit
  assertTrue (val == 99) "fake measure returned wrong value"
  assertTrue (fElapsed == Duration.ofMillisecond (Millisecond.Offset.ofNat 4294967297))
    "fake measure elapsed mismatch across > UInt32.max"
  assertTrue (fakeEnd.sleepLog == #[UInt32.ofNat 4294967295, UInt32.ofNat 2])
    s!"unexpected fake sleepLog chunks: {repr fakeEnd.sleepLog}"

/-- Real error-forcing test proving `parseUtcIso8601` returns `.invalidFormat` on malformed timestamps. -/
def err_time_parseUtcIso8601_invalidFormat : IO Unit := do
  for bad in ["", "2024-02-30T00:00:00Z", "2026-11-14T18:15:00", "2026-11-14T25:00:00Z"] do
    assertErrInvalidFormat (parseUtcIso8601 bad) s!"expected invalidFormat ISO 8601 for {bad}"

/-- Real error-forcing test proving `parseUtcDate` returns `.invalidFormat` on malformed dates. -/
def err_time_parseUtcDate_invalidFormat : IO Unit := do
  for bad in ["", "2024-02-30", "2026-13-01", "2026/11/14", "2026-11-14Z"] do
    assertErrInvalidFormat (parseUtcDate bad) s!"expected invalidFormat date for {bad}"

/-- Runtime error-coverage obligations verified for `LeanSwe.Time`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Time.RuntimeTests.err_time_parseUtcIso8601_invalidFormat"
       mode := .real
       run := err_time_parseUtcIso8601_invalidFormat }
   , { testName := "LeanSwe.Time.RuntimeTests.err_time_parseUtcDate_invalidFormat"
       mode := .real
       run := err_time_parseUtcDate_invalidFormat } ]

private def seccompWorker : IO UInt32 := do
  let rc ← LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.installSeccompErrnoForTest
    LeanSwe.LinuxSyscall.Errno.EPERM 7
  if rc != 0 then
    IO.eprintln s!"time seccomp-worker: installSeccompErrnoForTest failed errno={rc}"
    return 1
  let ts ← nowTimestamp
  if ts != Timestamp.ofSecondsSinceUnixEpoch 0 then
    IO.eprintln s!"time seccomp-worker: expected epoch 0 fallback, got {repr ts}"
    return 2
  let mono ← monoNanosNow
  if mono != 0 then
    IO.eprintln s!"time seccomp-worker: expected monoNanosNow = 0 fallback, got {mono}"
    return 3
  sleepMs 1000
  sleepDuration (Duration.ofMillisecond 1000)
  return 0

/-- CLI entrypoint for `--time-probe`. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | ["--seccomp-worker", "EPERM"] => seccompWorker
  | _ =>
    IO.eprintln s!"unknown time-probe args: {args}"
    return 1

private def checkLiveSeccomp : IO Unit := do
  let exe ← IO.appPath
  let out ← IO.Process.output {
    cmd := exe.toString
    args := #["--time-probe", "--seccomp-worker", "EPERM"]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"LeanSwe.Time.RuntimeTests FAILED (live seccomp EPERM exit={out.exitCode}): {out.stderr}"

/-- Execute all runtime checks for `LeanSwe.Time`. -/
def runAll : IO Unit := do
  testUtcFormattingAndParsing
  testUtcDates
  testRealClockAndSleep
  Core.runRegisteredErrorTests registeredErrorTests
  checkLiveSeccomp
  IO.println "PASS: LeanSwe.Time runtime tests"

end LeanSwe.Time.RuntimeTests
