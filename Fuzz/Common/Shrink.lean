import Fuzz.Common.Rng

namespace Fuzz.Common

/-- Greedy delta-minimization shrinker reducing a failing trace toward a minimal reproducing subtrace. -/
partial def shrinkTrace {m : Type → Type} [Monad m] {α : Type}
    (fails : Array α → m Bool) (trace : Array α) (allowEmpty : Bool := false) : m (Array α) := do
  if allowEmpty then
    if ← fails #[] then
      return #[]
  if trace.size <= 1 then
    return trace
  let mut cur := trace
  let mut chunk := max 1 (cur.size / 2)
  while chunk >= 1 && cur.size > 1 do
    let mut improved := false
    let mut start := 0
    while start < cur.size && cur.size > 1 do
      let stop := min cur.size (start + chunk)
      let cand := cur.extract 0 start ++ cur.extract stop cur.size
      if (allowEmpty || !cand.isEmpty) && (← fails cand) then
        cur := cand
        improved := true
        if cur.size == 0 then
          return cur
      else
        start := start + chunk
    if !improved then
      if chunk == 1 then
        break
      chunk := max 1 (chunk / 2)
  return cur

/-- Greedily shrink individual trace elements in-place using `shrinkItem` while preserving failure. -/
def shrinkElements {m : Type → Type} [Monad m] {α : Type}
    (shrinkItem : α → List α) (fails : Array α → m Bool) (trace : Array α) : m (Array α) := do
  let mut cur := trace
  let mut idx := 0
  while idx < cur.size do
    match cur[idx]? with
    | none => break
    | some orig =>
      let mut replaced := false
      for candItem in shrinkItem orig do
        let cand := cur.setIfInBounds idx candItem
        if ← fails cand then
          cur := cand
          replaced := true
          break
      if !replaced then
        idx := idx + 1
  return cur

/-- Verify that `shrinkTrace` preserves `fails` and reduces `trace` to at most `maxExpectedSize` elements. -/
def verifyShrinker {m : Type → Type} [Monad m] {α : Type}
    (fails : Array α → m Bool) (trace : Array α) (maxExpectedSize : Nat := 1) : m (Except String (Array α)) := do
  unless ← fails trace do
    return .error s!"verifyShrinker: initial trace (size={trace.size}) did not trigger failure"
  let shrunk ← shrinkTrace fails trace
  unless ← fails shrunk do
    return .error s!"verifyShrinker: shrunk trace (size={shrunk.size}) no longer triggers failure"
  if shrunk.size > maxExpectedSize then
    return .error s!"verifyShrinker: expected shrunk size <= {maxExpectedSize}, got {shrunk.size}"
  return .ok shrunk

/-- Self-test `shrinkTrace` on both a single-step fault and an ordered two-step fault embedded in random traces. -/
def runGenericShrinkSelfTest (seedVal : UInt64 := 0x123456789abcdef0) : IO Unit := do
  let mut rng := Rng.seed (seedVal ^^^ 0x517cc1b727220a95)
  let mut trace1 : Array Nat := Array.mkEmpty 24
  for _ in List.range 24 do
    let (v, r') := rng.nextRange 1 999
    rng := r'
    trace1 := trace1.push v
  let (badIdx1, r2) := rng.nextNat trace1.size
  rng := r2
  trace1 := trace1.set! badIdx1 1000001
  let isSingleFault (xs : Array Nat) : IO Bool :=
    return xs.any (· == 1000001)
  match ← verifyShrinker isSingleFault trace1 1 with
  | .error msg => throw (IO.userError s!"GENERIC_SHRINK_SELFTEST_SINGLE_FAILED: {msg}")
  | .ok shrunk1 =>
    if shrunk1 != #[1000001] then
      throw (IO.userError s!"GENERIC_SHRINK_SELFTEST_SINGLE_MISMATCH: got {repr shrunk1}")
  let mut trace2 : Array Nat := Array.mkEmpty 24
  for _ in List.range 24 do
    let (v, r') := rng.nextRange 1 999
    rng := r'
    trace2 := trace2.push v
  let (idxA, r3) := rng.nextRange 0 11
  let (idxB, _) := r3.nextRange 12 23
  trace2 := trace2.set! idxA 2000001
  trace2 := trace2.set! idxB 2000002
  let isOrderedPairFault (xs : Array Nat) : IO Bool := do
    let mut seenFirst := false
    for x in xs do
      if x == 2000001 then
        seenFirst := true
      else if x == 2000002 && seenFirst then
        return true
    return false
  match ← verifyShrinker isOrderedPairFault trace2 2 with
  | .error msg => throw (IO.userError s!"GENERIC_SHRINK_SELFTEST_PAIR_FAILED: {msg}")
  | .ok shrunk2 =>
    if shrunk2 != #[2000001, 2000002] then
      throw (IO.userError s!"GENERIC_SHRINK_SELFTEST_PAIR_MISMATCH: got {repr shrunk2}")

end Fuzz.Common
