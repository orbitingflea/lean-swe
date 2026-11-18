import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Coverage
import Fuzz.Common.Suite

namespace Fuzz.SelfTest

open Fuzz.Common

private inductive StackOp where
  | push (v : Nat)
  | pop
  | add
  | clear
  deriving Repr, DecidableEq, BEq

private inductive StackOutcome where
  | ok (top? : Option Nat)
  | err (code : String)
  deriving Repr, DecidableEq, BEq

private structure StackState where
  items : Array Nat := #[]
  cap : Nat := 3
  deriving Repr, DecidableEq, BEq

private def stepModel (s : StackState) (op : StackOp) : StackState × StackOutcome :=
  match op with
  | .push v =>
    if s.items.size >= s.cap then
      (s, .err "full")
    else
      ({ s with items := s.items.push v }, .ok (some v))
  | .pop =>
    if s.items.isEmpty then
      (s, .err "empty")
    else
      let top := s.items[s.items.size - 1]!
      ({ s with items := s.items.pop }, .ok (some top))
  | .add =>
    if s.items.size < 2 then
      (s, .err "underflow")
    else
      let a := s.items[s.items.size - 1]!
      let b := s.items[s.items.size - 2]!
      let sum := a + b
      let popped := s.items.pop.pop.push sum
      ({ s with items := popped }, .ok (some sum))
  | .clear =>
    ({ s with items := #[] }, .ok none)

private def stepImpl (s : StackState) (op : StackOp) : StackState × StackOutcome :=
  stepModel s op

private def genStackOp (r : Rng) : StackOp × Rng :=
  let (kind, r1) := r.nextNat 10
  if kind < 5 then
    let (v, r2) := r1.nextRange 0 15
    (.push v, r2)
  else if kind < 7 then
    (.pop, r1)
  else if kind < 9 then
    (.add, r1)
  else
    (.clear, r1)

private def opName : StackOp → String
  | .push _ => "push"
  | .pop => "pop"
  | .add => "add"
  | .clear => "clear"

private def outcomeBucket : StackOutcome → String
  | .ok _ => "ok"
  | .err code => s!"err.{code}"

private def requiredBuckets : Array CoverageBucket := #[
  bucket "push" "ok",
  bucket "push" "err.full",
  bucket "pop" "ok",
  bucket "pop" "err.empty",
  bucket "add" "ok",
  bucket "add" "err.underflow",
  bucket "clear" "ok"
]

private def checkTraceAgainstOracle (oracle : StackState → StackOp → StackState × StackOutcome)
    (trace : Array StackOp) : Bool := Id.run do
  let mut stModel : StackState := {}
  let mut stImpl : StackState := {}
  for op in trace do
    let (mNext, mOut) := oracle stModel op
    let (iNext, iOut) := stepImpl stImpl op
    if mNext != iNext || mOut != iOut then
      return false
    stModel := mNext
    stImpl := iNext
  return true

private def verifyRngInvariants (seedVal : UInt64) : IO Unit := do
  let mut rA := Rng.seed seedVal
  let mut rB := Rng.seed seedVal
  for _ in List.range 32 do
    let (x, rA') := rA.nextU64
    let (y, rB') := rB.nextU64
    if x != y then
      throw (IO.userError "RNG_DETERMINISM_FAILED")
    rA := rA'
    rB := rB'
  let mut seenRange : Array Nat := #[0, 0, 0, 0]
  let mut rng := rA
  for _ in List.range 256 do
    let (v, r') := rng.nextRange 0 3
    rng := r'
    if v > 3 then
      throw (IO.userError s!"RNG_RANGE_OUT_OF_BOUNDS: {v}")
    seenRange := seenRange.set! v (seenRange[v]! + 1)
  for i in List.range 4 do
    if seenRange[i]! == 0 then
      throw (IO.userError s!"RNG_RANGE_BUCKET_ZERO: {i}")
  let (bs, rBytes) := rng.nextBytes 19
  if bs.size != 19 then
    throw (IO.userError s!"RNG_NEXTBYTES_SIZE_MISMATCH: expected 19, got {bs.size}")
  let (picked, _) := rBytes.chooseWeighted #[(1, "a"), (3, "b")] "fallback"
  if picked != "a" && picked != "b" then
    throw (IO.userError s!"RNG_CHOOSE_WEIGHTED_INVALID: {picked}")

private def warmupCorpus : Array StackOp := #[
  .clear,
  .pop,
  .push 1,
  .push 2,
  .add,
  .add,
  .push 4,
  .push 5,
  .push 6,
  .pop
]

private def runTraceRecorded (tracker : CoverageTracker) (trace : Array StackOp) : IO CoverageTracker := do
  let mut tr := tracker
  let mut stModel : StackState := {}
  let mut stImpl : StackState := {}
  for op in trace do
    let (mNext, mOut) := stepModel stModel op
    let (iNext, iOut) := stepImpl stImpl op
    tr := tr.record (opName op) (outcomeBucket iOut)
    if mNext != iNext || mOut != iOut then
      let shrunk ← shrinkTrace (fun cand => pure (!checkTraceAgainstOracle stepModel cand)) trace
      throw (IO.userError s!"SELFTEST_MISMATCH shrunk={repr shrunk}")
    stModel := mNext
    stImpl := iNext
  return tr

private def runStackDiffFuzz (steps : Nat) (seedVal : UInt64) : IO Unit := do
  verifyRngInvariants seedVal
  let mut rng := Rng.seed seedVal
  let mut tracker ← runTraceRecorded CoverageTracker.empty warmupCorpus
  let mut done := 0
  while done < steps do
    let (epLenRaw, rEp) := rng.nextRange 8 24
    rng := rEp
    let epLen := min epLenRaw (steps - done)
    let mut trace : Array StackOp := Array.mkEmpty epLen
    for _ in List.range epLen do
      let (op, rOp) := genStackOp rng
      rng := rOp
      trace := trace.push op
    tracker ← runTraceRecorded tracker trace
    done := done + epLen
  assertCoverage "selftest" tracker requiredBuckets
  let missingEmpty := checkCoverage CoverageTracker.empty requiredBuckets
  if missingEmpty.size != requiredBuckets.size then
    throw (IO.userError s!"SELFTEST_COVERAGE_CHECK_FAILED: expected {requiredBuckets.size}, got {missingEmpty.size}")
  IO.println (tracker.formatReport "selftest")
  IO.println s!"FUZZ_SUMMARY suite=selftest steps={steps} seed={seedVal}"

/-- Verify both the generic shrinker and a stack-trace oracle shrinker on `seedVal`. -/
def runSelfTestShrink (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  let mut rng := Rng.seed (seedVal ^^^ 0x9e3779b97f4a7c15)
  let mut trace : Array StackOp := Array.mkEmpty 14
  for _ in List.range 12 do
    let (op, r') := genStackOp rng
    rng := r'
    trace := trace.push op
  let (insertAt, _) := rng.nextRange 0 11
  let prefixOps := trace.extract 0 insertAt
  let suffixOps := trace.extract insertAt trace.size
  let injected := ((prefixOps.push (.push 1)).push (.push 2)).push (.add) ++ suffixOps
  let buggyOracle (s : StackState) (op : StackOp) : StackState × StackOutcome :=
    match op with
    | .add =>
      if s.items.size >= 2 then
        let (s', _) := stepModel s op
        (s', .err "injected_bug")
      else
        stepModel s op
    | _ => stepModel s op
  let failsBuggy (cand : Array StackOp) : IO Bool :=
    pure (!checkTraceAgainstOracle buggyOracle cand)
  match ← verifyShrinker failsBuggy injected 3 with
  | .error msg => throw (IO.userError s!"SELFTEST_STACK_SHRINK_FAILED: {msg}")
  | .ok shrunk =>
    IO.println s!"SELFTEST_SHRINK_OK: original={injected.size} shrunk={shrunk.size}"

/-- Built-in `selftest` `FuzzSuite` validating PRNG, delta-shrinking, coverage assertions, and CLI wiring. -/
def suite : FuzzSuite := {
  name := "selftest"
  description := "Built-in Fuzz/Common end-to-end PRNG, shrinker, and coverage self-test suite"
  runSmoke := fun cfg =>
    let smokeSteps := min cfg.steps 300
    runStackDiffFuzz (max 200 smokeSteps) cfg.seed
  runFuzz := fun cfg =>
    runStackDiffFuzz cfg.steps cfg.seed
  selfTestShrink := runSelfTestShrink
}

end Fuzz.SelfTest
