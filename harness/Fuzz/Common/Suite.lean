import Std.Data.HashSet

namespace Fuzz.Common

/-- Configuration passed to a `FuzzSuite` invocation. -/
structure FuzzConfig where
  /-- Number of fuzz steps to run in full fuzz mode. -/
  steps : Nat := 10000
  /-- Deterministic 64-bit SplitMix64 seed. -/
  seed : UInt64 := 0x517cc1b727220a95
  /-- Whether `--random-seed` requested OS entropy initialization. -/
  randomSeed : Bool := false
  /-- Whether `--self-test-shrink` was requested. -/
  selfTestShrink : Bool := false
  /-- Whether `--smoke` fast deterministic PR-check mode was requested. -/
  smoke : Bool := false
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Pluggable differential fuzzing suite descriptor registered in `Fuzz.Main`. -/
structure FuzzSuite where
  /-- Unique CLI suite identifier (for `--suite <name>` and `harness/Fuzz/suites.json`). -/
  name : String
  /-- Short human-readable summary of the boundary covered by this suite. -/
  description : String := ""
  /-- Fast deterministic smoke corpus plus coverage assertions for PR CI. -/
  runSmoke : FuzzConfig → IO Unit
  /-- Full randomized differential fuzzing pass for local/daily verification. -/
  runFuzz : FuzzConfig → IO Unit
  /-- Shrinker self-test verifying trace minimization on a synthetic injected failure. -/
  selfTestShrink : UInt64 → IO Unit

private structure FuzzCoverageSink where
  nonce : String
  handle : IO.FS.Handle

private initialize fuzzCoverageSinkRef : IO.Ref (Option FuzzCoverageSink) ← IO.mkRef none
private initialize emittedErrHitsRef : IO.Ref (Std.HashSet String) ← IO.mkRef {}
private initialize suiteBucketsRef : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)
private initialize suiteStepsRef : IO.Ref (Option Nat) ← IO.mkRef none

/-- Return `true` when a nonce-authenticated fuzz coverage log is currently active. -/
def isCoverageLogActive : IO Bool :=
  return (← fuzzCoverageSinkRef.get).isSome

/-- Open `logPath` for nonce-authenticated `ERR_HIT` and `FUZZ_EQUIV` emission and write `LOG_INIT`. -/
def initCoverageLog (logPath nonce : String) : IO Unit := do
  if logPath.isEmpty || nonce.isEmpty then
    throw (IO.userError "initCoverageLog requires non-empty path and nonce")
  let handle ← IO.FS.Handle.mk logPath .write
  handle.putStrLn s!"{nonce}|LOG_INIT"
  handle.flush
  emittedErrHitsRef.set {}
  suiteBucketsRef.set (0, 0)
  suiteStepsRef.set none
  fuzzCoverageSinkRef.set (some { nonce, handle })

/-- Emit a deduplicated nonce-authenticated `ERR_HIT` line when coverage logging is active. -/
def logErrHit (qualOp errorKindCtor mode : String) : IO Unit := do
  if let some sink ← fuzzCoverageSinkRef.get then
    let key := s!"{qualOp}|{errorKindCtor}|{mode}"
    let seen ← emittedErrHitsRef.get
    if !seen.contains key then
      emittedErrHitsRef.set (seen.insert key)
      sink.handle.putStrLn s!"{sink.nonce}|ERR_HIT|{key}"
      sink.handle.flush

/-- Emit a nonce-authenticated `FUZZ_EQUIV` summary line for `(pkg, suite)` when coverage logging is active. -/
def logFuzzEquiv (pkg suite : String) (steps bucketsHit bucketsTotal : Nat) (ok : Bool) : IO Unit := do
  if let some sink ← fuzzCoverageSinkRef.get then
    let okStr := if ok then "true" else "false"
    sink.handle.putStrLn s!"{sink.nonce}|FUZZ_EQUIV|{pkg}|{suite}|{steps}|{bucketsHit}/{bucketsTotal}|ok={okStr}"
    sink.handle.flush

/-- Reset the per-suite `(bucketsHit, bucketsTotal)` and executed-step accumulators before executing a suite. -/
def resetSuiteBuckets : IO Unit := do
  suiteBucketsRef.set (0, 0)
  suiteStepsRef.set none

/-- Record the actual executed step count for the active fuzz suite. -/
def recordSuiteSteps (steps : Nat) : IO Unit :=
  suiteStepsRef.set (some steps)

/-- Read the actual executed step count recorded for the active suite, falling back to `fallback`. -/
def getSuiteSteps (fallback : Nat) : IO Nat := do
  return (← suiteStepsRef.get).getD fallback

/-- Record the latest `(bucketsHit, bucketsTotal)` counts observed during the active suite. -/
def recordSuiteBuckets (bucketsHit bucketsTotal : Nat) : IO Unit :=
  suiteBucketsRef.modify fun (prevHit, prevTotal) =>
    if bucketsTotal >= prevTotal then (bucketsHit, bucketsTotal) else (prevHit, prevTotal)

/-- Read the `(bucketsHit, bucketsTotal)` counts accumulated for the current suite. -/
def getSuiteBuckets : IO (Nat × Nat) :=
  suiteBucketsRef.get

/-- Merge authenticated `ERR_HIT` and `FUZZ_EQUIV` step/bucket counts from a child worker log into the active parent coverage log and remove the temporary child file. -/
def mergeChildCoverageLog (childLogPath expectedNonce : String) : IO Unit := do
  let p : System.FilePath := childLogPath
  if !(← p.pathExists) then
    return ()
  try
    let txt ← IO.FS.readFile p
    for line in txt.splitOn "\n" do
      let trimmed := line.trimAscii.toString
      if trimmed.isEmpty then continue
      match trimmed.splitOn "|" with
      | [nonce, "ERR_HIT", qualOp, kindCtor, mode] =>
        if nonce == expectedNonce then
          logErrHit qualOp kindCtor mode
      | [nonce, "FUZZ_EQUIV", _, _, stepsStr, bucketsStr, _] =>
        if nonce == expectedNonce then
          if let some st := stepsStr.toNat? then
            if st > 0 then
              recordSuiteSteps st
          match bucketsStr.splitOn "/" with
          | [hStr, tStr] =>
            if let (some h, some t) := (hStr.toNat?, tStr.toNat?) then
              recordSuiteBuckets h t
          | _ => pure ()
      | _ => pure ()
  finally
    try IO.FS.removeFile p catch _ => pure ()

/-- Write the authenticated `LOG_CLOSE` trailer and flush the open fuzz coverage log handle. -/
def closeCoverageLog : IO Unit := do
  if let some sink ← fuzzCoverageSinkRef.get then
    sink.handle.putStrLn s!"{sink.nonce}|LOG_CLOSE"
    sink.handle.flush
    fuzzCoverageSinkRef.set none
    emittedErrHitsRef.set {}

end Fuzz.Common
