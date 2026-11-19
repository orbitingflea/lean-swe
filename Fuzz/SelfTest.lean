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

private def referenceNextBytes (r : Rng) (len : Nat) : ByteArray := Id.run do
  let mut cur := r
  let mut out := ByteArray.emptyWithCapacity len
  let mut left := len
  while left > 0 do
    let (w, nxt) := cur.nextU64
    cur := nxt
    let take := min 8 left
    for shift in [:take] do
      out := out.push (UInt8.ofNat ((w >>> UInt64.ofNat (shift * 8)).toNat % 256))
    left := left - take
  return out

private def verifyRngInvariants (seedVal : UInt64) : IO Unit := do
  let mut rA := Rng.seed seedVal
  let mut rB := Rng.seed seedVal
  for _ in [:32] do
    let (x, rA') := rA.nextU64
    let (y, rB') := rB.nextU64
    if x != y then
      throw (IO.userError "RNG_DETERMINISM_FAILED")
    rA := rA'
    rB := rB'
  let mut seenRange : Array Nat := #[0, 0, 0, 0]
  let mut rng := rA
  for _ in [:256] do
    let (v, r') := rng.nextRange 0 3
    rng := r'
    if v > 3 then
      throw (IO.userError s!"RNG_RANGE_OUT_OF_BOUNDS: {v}")
    seenRange := seenRange.set! v (seenRange[v]! + 1)
  for i in [:4] do
    if seenRange[i]! == 0 then
      throw (IO.userError s!"RNG_RANGE_BUCKET_ZERO: {i}")
  let baseRng := Rng.seed 42
  let (_, rOne) := baseRng.nextU64
  let (_, rTwo) := rOne.nextU64
  let (v64, r64) := baseRng.nextNat UInt64.size
  if r64.state != rOne.state || v64 >= UInt64.size then
    throw (IO.userError "RNG_NEXTNAT_U64SIZE_FASTPATH_FAILED")
  let (_, rRngFull) := baseRng.nextRange 0 (UInt64.size - 1)
  if rRngFull.state != rOne.state then
    throw (IO.userError "RNG_NEXTRANGE_U64_FASTPATH_FAILED")
  let i63 : Int := Int.ofNat (1 <<< 63)
  let (iv, rIntFull) := baseRng.nextIntRange (-i63) (i63 - 1)
  if rIntFull.state != rOne.state || iv < -i63 || iv > i63 - 1 then
    throw (IO.userError "RNG_NEXTINTRANGE_I64_FASTPATH_FAILED")
  let pow128 := UInt64.size * UInt64.size
  let (v128, r128) := baseRng.nextNat pow128
  if r128.state != rTwo.state || v128 >= pow128 then
    throw (IO.userError "RNG_NEXTNAT_POW128_FASTPATH_FAILED")
  let (vBig, rBig) := baseRng.nextNat (pow128 + 1)
  if vBig >= pow128 + 1 || rBig.state == rTwo.state then
    throw (IO.userError "RNG_NEXTNAT_BIGNAT_FAILED")
  for len in #[0, 1, 7, 8, 9, 16, 19, 64] do
    let (bs, _) := rng.nextBytes len
    let exp := referenceNextBytes rng len
    if bs != exp then
      throw (IO.userError s!"RNG_NEXTBYTES_MISMATCH len={len}")
  let (bs, rBytes) := rng.nextBytes 19
  if bs.size != 19 then
    throw (IO.userError s!"RNG_NEXTBYTES_SIZE_MISMATCH: expected 19, got {bs.size}")
  let (picked, _) := rBytes.chooseWeighted #[(1, "a"), (3, "b")] "fallback"
  if picked != "a" && picked != "b" then
    throw (IO.userError s!"RNG_CHOOSE_WEIGHTED_INVALID: {picked}")

private def verifyCoverageInvariants : IO Unit := do
  let bZero := bucket "op" "zero"
  let bOk := bucket "op" "ok"
  let bExtra := bucket "op" "extra"
  let mapA : Std.HashMap CoverageBucket Nat :=
    ({} : Std.HashMap CoverageBucket Nat) |>.insert bZero 0 |>.insert bOk 2
  let mapB : Std.HashMap CoverageBucket Nat :=
    ({} : Std.HashMap CoverageBucket Nat) |>.insert bOk 3 |>.insert bExtra 0
  let trA : CoverageTracker := { hits := mapA, total := 999 }
  let trB : CoverageTracker := { hits := mapB, total := 777 }
  if trA.sortedEntries != #[(bOk, 2)] then
    throw (IO.userError s!"COVERAGE_SORTED_ZERO_LEAK: got {repr trA.sortedEntries}")
  let ab := trA.merge trB
  let ba := trB.merge trA
  if ab.sortedEntries != #[(bOk, 5)] || ba.sortedEntries != #[(bOk, 5)] then
    throw (IO.userError s!"COVERAGE_MERGE_ASYMMETRIC: ab={repr ab.sortedEntries} ba={repr ba.sortedEntries}")
  if ab.total != 5 || ba.total != 5 then
    throw (IO.userError s!"COVERAGE_MERGE_TOTAL_DRIFT: ab={ab.total} ba={ba.total}")
  let dupReq := #[bucket "push" "ok", bucket "push" "ok", bucket "pop" "empty", bucket "push" "ok"]
  let missingDup := checkCoverage CoverageTracker.empty dupReq
  if missingDup != #[bucket "push" "ok", bucket "pop" "empty"] then
    throw (IO.userError s!"COVERAGE_DEDUP_FAILED: got {repr missingDup}")

private def verifyShrinkRegressions : IO Unit := do
  let idShrink (n : Nat) : List Nat := [0, n / 2, n - 1]
  let callsId ← IO.mkRef (0 : Nat)
  let shrunkId ← shrinkElements idShrink (fun _ => do callsId.modify (· + 1); pure true) #[5]
  if shrunkId != #[0] then
    throw (IO.userError s!"SHRINK_IDENTITY_FAILED: got {repr shrunkId}")
  if (← callsId.get) > 4 then
    throw (IO.userError s!"SHRINK_IDENTITY_LOOPED: calls={← callsId.get}")
  let cycShrink (n : Nat) : List Nat :=
    if n == 1 then [2] else if n == 2 then [1] else []
  let callsCyc ← IO.mkRef (0 : Nat)
  let shrunkCyc ← shrinkElements cycShrink (fun _ => do callsCyc.modify (· + 1); pure true) #[1]
  if shrunkCyc != #[2] || (← callsCyc.get) > 2 then
    throw (IO.userError s!"SHRINK_CYCLE_FAILED: shrunk={repr shrunkCyc} calls={← callsCyc.get}")
  let divShrink (n : Nat) : List Nat := [n + 1]
  let shrunkDiv ← shrinkElements divShrink (fun _ => pure true) #[0] (maxSteps := 10)
  if shrunkDiv != #[10] then
    throw (IO.userError s!"SHRINK_FUEL_CAP_FAILED: got {repr shrunkDiv}")
  let natShrink (n : Nat) : List Nat := if n == 0 then [] else [0, n / 2, n - 1]
  let failsOrder (xs : Array Nat) : IO Bool :=
    pure (xs.size == 2 && xs[0]! >= xs[1]!)
  let shrunkFix ← shrinkElements natShrink failsOrder #[100, 100]
  if shrunkFix != #[0, 0] then
    throw (IO.userError s!"SHRINK_FIXPOINT_FAILED: got {repr shrunkFix}")
  let linTrace := Array.replicate 2000 (1 : Nat)
  let shrunkLin ← shrinkElements (fun n => if n == 0 then [] else [0]) (fun _ => pure false) linTrace
  if shrunkLin.size != 2000 || shrunkLin[0]! != 1 then
    throw (IO.userError "SHRINK_LINEAR_RESTORE_FAILED")
  let isBalanced (xs : Array String) : IO Bool := Id.run do
    let mut depth : Int := 0
    let mut hasReq := false
    let mut hasTrig := false
    for x in xs do
      if x == "req" then hasReq := true
      else if x == "trigger" then hasTrig := true
      else if x == "open" then depth := depth + 1
      else if x == "close" then
        depth := depth - 1
        if depth < 0 then return pure false
    return pure (hasReq && hasTrig && depth == 0)
  let pairTrace := #["req", "open", "close", "open", "close", "trigger"]
  let shrunkPair ← shrinkTrace isBalanced pairTrace
  if shrunkPair != #["req", "trigger"] then
    throw (IO.userError s!"SHRINK_BALANCED_PAIR_FAILED: got {repr shrunkPair}")
  let nonAdjTrace := #["req", "open", "mid", "close", "trigger"]
  let failsNonAdj (xs : Array String) : IO Bool := do
    if !xs.contains "mid" then return false
    isBalanced xs
  let shrunkNonAdj ← shrinkTrace failsNonAdj nonAdjTrace
  if shrunkNonAdj != #["req", "mid", "trigger"] then
    throw (IO.userError s!"SHRINK_NONADJ_PAIR_FAILED: got {repr shrunkNonAdj}")
  let parityTrace : Array Nat := #[99, 1, 2, 3, 4, 5]
  let shrunkParity ← shrinkTrace (fun xs => pure (xs.contains 99 && xs.size % 2 == 0)) parityTrace
  if shrunkParity.size != 2 || !shrunkParity.contains 99 then
    throw (IO.userError s!"SHRINK_PARITY_FAILED: got {repr shrunkParity}")
  let emptyCalls ← IO.mkRef (0 : Nat)
  let failsZero (xs : Array Nat) : IO Bool := do
    if xs.isEmpty then emptyCalls.modify (· + 1)
    return xs.contains 0
  let bigTrace := Array.range 1024
  let shrunkBig ← shrinkTrace failsZero bigTrace (allowEmpty := true)
  if shrunkBig != #[0] || (← emptyCalls.get) != 1 then
    throw (IO.userError s!"SHRINK_EMPTY_RECALL_FAILED: shrunk={repr shrunkBig} emptyCalls={← emptyCalls.get}")
  match ← verifyShrinker (fun _ => pure true) #[1, 2, 3] 0 with
  | .ok shrunk0 =>
    if !shrunk0.isEmpty then
      throw (IO.userError s!"VERIFY_SHRINKER_ZERO_FAILED: got {repr shrunk0}")
  | .error msg =>
    throw (IO.userError s!"VERIFY_SHRINKER_ZERO_FAILED: {msg}")
  match ← verifyShrinker (fun _ => pure true) #[1, 2, 3] 1 (allowEmpty := true) with
  | .ok shrunk0 =>
    if !shrunk0.isEmpty then
      throw (IO.userError s!"VERIFY_SHRINKER_ALLOWEMPTY_FAILED: got {repr shrunk0}")
  | .error msg =>
    throw (IO.userError s!"VERIFY_SHRINKER_ALLOWEMPTY_FAILED: {msg}")
  match ← verifyShrinker (fun _ => pure true) #[1, 2, 3] 0 (allowEmpty := false) with
  | .ok shrunkBad =>
    throw (IO.userError s!"VERIFY_SHRINKER_DISALLOWEMPTY_FAILED: expected error, got {repr shrunkBad}")
  | .error _ => pure ()
  let calls258 ← IO.mkRef (0 : Nat)
  let shrink258 : Nat × Nat → List (Nat × Nat)
    | (0, v) => [(0, (v + 1) % 258)]
    | (1, v) => if v == 0 then [] else [(1, 0)]
    | _ => []
  let shrunk258 ← shrinkElements shrink258 (fun _ => do calls258.modify (· + 1); pure true) #[(0, 0), (1, 1000)]
  if shrunk258[1]! != (1, 0) || (← calls258.get) >= 1000 then
    throw (IO.userError s!"SHRINK_BRENT_258_FAILED: got={repr shrunk258} calls={← calls258.get}")
  let callsLasso ← IO.mkRef (0 : Nat)
  let shrinkLasso (n : Nat) : List Nat := [if n < 307 then n + 1 else 50]
  let _ ← shrinkElements shrinkLasso (fun _ => do callsLasso.modify (· + 1); pure true) #[0]
  if (← callsLasso.get) >= 1000 then
    throw (IO.userError s!"SHRINK_BRENT_LASSO_FAILED: calls={← callsLasso.get}")
  let calls2Cand ← IO.mkRef (0 : Nat)
  let shrink2Cand : Nat × Nat → List (Nat × Nat)
    | (0, v) => [(0, (v + 1) % 259), (0, (v + 2) % 259)]
    | (1, v) => if v == 0 then [] else [(1, 0)]
    | _ => []
  let shrunk2Cand ← shrinkElements shrink2Cand (fun _ => do calls2Cand.modify (· + 1); pure true) #[(0, 0), (1, 1000)]
  if shrunk2Cand[1]! != (1, 0) || (← calls2Cand.get) > 265 then
    throw (IO.userError s!"SHRINK_2CAND_259_FAILED: got={repr shrunk2Cand} calls={← calls2Cand.get}")
  let callsProd ← IO.mkRef (0 : Nat)
  let shrinkProd : Nat × Nat → List (Nat × Nat)
    | (0, v) =>
      let a := v / 17
      let b := v % 17
      [(0, ((a + 1) % 23) * 17 + b), (0, a * 17 + ((b + 1) % 17))]
    | (1, v) => if v == 0 then [] else [(1, 0)]
    | _ => []
  let shrunkProd ← shrinkElements shrinkProd (fun _ => do callsProd.modify (· + 1); pure true) #[(0, 0), (1, 1000)]
  if shrunkProd[1]! != (1, 0) || (← callsProd.get) > 400 then
    throw (IO.userError s!"SHRINK_PROD_CYCLE_FAILED: got={repr shrunkProd} calls={← callsProd.get}")
  let shrinkDivFair : Nat × Nat → List (Nat × Nat)
    | (0, v) => [(0, v + 1)]
    | (1, v) => if v == 0 then [] else [(1, 0)]
    | _ => []
  let shrunkFair ← shrinkElements shrinkDivFair (fun _ => pure true) #[(0, 0), (1, 1000)] (maxSteps := 300)
  if shrunkFair[1]! != (1, 0) then
    throw (IO.userError s!"SHRINK_DIV_FAIRNESS_FAILED: got={repr shrunkFair}")

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
  verifyCoverageInvariants
  let mut rng := Rng.seed seedVal
  let mut tracker ← runTraceRecorded CoverageTracker.empty warmupCorpus
  let mut done := 0
  while done < steps do
    let (epLenRaw, rEp) := rng.nextRange 8 24
    rng := rEp
    let epLen := min epLenRaw (steps - done)
    let mut trace : Array StackOp := Array.mkEmpty epLen
    for _ in [:epLen] do
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

/-- Verify both the generic shrinker, regression suite, and a stack-trace oracle shrinker on `seedVal`. -/
def runSelfTestShrink (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  verifyShrinkRegressions
  let mut rng := Rng.seed (seedVal ^^^ 0x9e3779b97f4a7c15)
  let mut trace : Array StackOp := Array.mkEmpty 14
  for _ in [:12] do
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
    runStackDiffFuzz (min cfg.steps 300) cfg.seed
  runFuzz := fun cfg =>
    runStackDiffFuzz cfg.steps cfg.seed
  selfTestShrink := runSelfTestShrink
}

end Fuzz.SelfTest
