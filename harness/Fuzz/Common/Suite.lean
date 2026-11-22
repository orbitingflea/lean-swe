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

end Fuzz.Common
