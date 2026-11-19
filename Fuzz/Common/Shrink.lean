import Std.Data.HashMap
import Fuzz.Common.Rng

namespace Fuzz.Common

private def shrinkTraceDdmin {m : Type → Type} [Monad m] {α : Type}
    (fails : Array α → m Bool) (initial : Array α) : m (Array α) := do
  let mut cur := initial
  let mut n := min 2 cur.size
  let mut compStart := 0
  let mut trySubsets := true
  while cur.size > 1 do
    let m := cur.size
    if n > m then
      n := m
    if n < 2 then
      n := min 2 m
    let base := m / n
    let rem := m % n
    let chunkRange (i : Nat) : Nat × Nat :=
      let start := i * base + min i rem
      let len := base + (if i < rem then 1 else 0)
      (start, start + len)
    let mut reduced := false
    if trySubsets then
      for i in [:n] do
        let (start, stop) := chunkRange i
        let len := stop - start
        if len > 0 && len < m then
          let sub := cur.extract start stop
          if ← fails sub then
            cur := sub
            n := min 2 cur.size
            compStart := 0
            trySubsets := true
            reduced := true
            break
    if reduced then
      continue
    if n > 2 then
      let offset := compStart % n
      for k in [:n] do
        let i := (offset + k) % n
        let (start, stop) := chunkRange i
        let len := stop - start
        if len > 0 && len < m then
          let comp := cur.extract 0 start ++ cur.extract stop m
          if !comp.isEmpty then
            if ← fails comp then
              cur := comp
              if cur.size <= 1 then
                return cur
              let nextN := max 2 (min (n - 1) cur.size)
              compStart := i % nextN
              trySubsets := nextN == 2 || cur.size <= 32
              n := nextN
              reduced := true
              break
    if reduced then
      continue
    if n >= cur.size then
      if !trySubsets then
        trySubsets := true
        continue
      break
    n := min cur.size (n * 2)
    compStart := 0
    trySubsets := true
  return cur

private def shrinkTraceWindows {m : Type → Type} [Monad m] {α : Type}
    (fails : Array α → m Bool) (cur : Array α) : m (Option (Array α)) := do
  if cur.size <= 256 then
    for winSize in #[2, 3, 4] do
      if winSize < cur.size then
        let maxStart := cur.size - winSize
        for start in [:maxStart + 1] do
          let cand := cur.extract 0 start ++ cur.extract (start + winSize) cur.size
          if !cand.isEmpty then
            if ← fails cand then
              return some cand
  if cur.size >= 3 && cur.size <= 32 then
    for i in [:cur.size] do
      if i + 2 < cur.size then
        for j in [i + 2 : cur.size] do
          let cand := cur.extract 0 i ++ cur.extract (i + 1) j ++ cur.extract (j + 1) cur.size
          if !cand.isEmpty then
            if ← fails cand then
              return some cand
  return none

/-- Zeller `ddmin` delta-minimization shrinker with sliding-window and coupled-pair reduction. -/
partial def shrinkTrace {m : Type → Type} [Monad m] {α : Type}
    (fails : Array α → m Bool) (trace : Array α) (allowEmpty : Bool := false) : m (Array α) := do
  if allowEmpty then
    if ← fails #[] then
      return #[]
  if trace.size <= 1 then
    return trace
  let mut cur := trace
  while cur.size > 1 do
    cur ← shrinkTraceDdmin fails cur
    if cur.size <= 1 then
      break
    match ← shrinkTraceWindows fails cur with
    | some smaller =>
      cur := smaller
    | none =>
      break
  return cur

private def seenContains {α : Type} [BEq α] (seen : Array α) (x : α) : Bool :=
  seen.any (· == x)

private def recordSeen {α : Type} (map : Std.HashMap Nat (Array α × Nat)) (idx : Nat) (val : α) :
    Std.HashMap Nat (Array α × Nat) :=
  let cap := 256
  match map.get? idx with
  | none => map.insert idx (#[val], 1)
  | some (arr, pos) =>
    if arr.size < cap then
      map.insert idx (arr.push val, (pos + 1) % cap)
    else
      map.insert idx (arr.setIfInBounds (pos % cap) val, (pos + 1) % cap)

private def tryCandidatesAt {m : Type → Type} [Monad m] {α : Type} [BEq α]
    (fails : Array α → m Bool) (idx : Nat) (orig : α) (seen : Array α) :
    List α → (cur : Array α) → idx < cur.size → m (Array α × Bool)
  | [], cur, _ => pure (cur, false)
  | cand :: rest, cur, h => do
    if cand == orig || seenContains seen cand then
      tryCandidatesAt fails idx orig seen rest cur h
    else
      let cur' := cur.set idx cand h
      have h' : idx < cur'.size := by simpa [cur'] using h
      if ← fails cur' then
        pure (cur', true)
      else
        let restored := cur'.set idx orig h'
        have hRest : idx < restored.size := by simpa [restored] using h'
        tryCandidatesAt fails idx orig seen rest restored hRest

private def getSeenAt {α : Type} (map : Std.HashMap Nat (Array α × Nat)) (idx : Nat) : Array α :=
  match map.get? idx with
  | none => #[]
  | some (arr, _) => arr

/-- Greedily shrink individual trace elements in-place to a fixed point with cycle protection and step budget. -/
@[specialize] def shrinkElements {m : Type → Type} [Monad m] {α : Type} [BEq α]
    (shrinkItem : α → List α) (fails : Array α → m Bool) (trace : Array α)
    (maxSteps : Nat := 10000) : m (Array α) := do
  let mut cur := trace
  let mut seenMap : Std.HashMap Nat (Array α × Nat) := {}
  let mut steps : Nat := 0
  let mut outerChanged := true
  while outerChanged && steps < maxSteps do
    outerChanged := false
    let mut idx : Nat := 0
    while idx < cur.size && steps < maxSteps do
      if h : idx < cur.size then
        let orig := cur[idx]
        let seen := getSeenAt seenMap idx
        let cands := shrinkItem orig
        let (nextCur, replaced) ← tryCandidatesAt fails idx orig seen cands cur h
        cur := nextCur
        if replaced then
          seenMap := recordSeen seenMap idx orig
          steps := steps + 1
          outerChanged := true
        else
          idx := idx + 1
      else
        break
  return cur

/-- Verify that `shrinkTrace` preserves `fails` and reduces `trace` to at most `maxExpectedSize` elements. -/
def verifyShrinker {m : Type → Type} [Monad m] {α : Type}
    (fails : Array α → m Bool) (trace : Array α) (maxExpectedSize : Nat := 1)
    (allowEmpty : Bool := (maxExpectedSize == 0)) : m (Except String (Array α)) := do
  unless ← fails trace do
    return .error s!"verifyShrinker: initial trace (size={trace.size}) did not trigger failure"
  let shrunk ← shrinkTrace fails trace allowEmpty
  unless ← fails shrunk do
    return .error s!"verifyShrinker: shrunk trace (size={shrunk.size}) no longer triggers failure"
  if shrunk.size > maxExpectedSize then
    return .error s!"verifyShrinker: expected shrunk size <= {maxExpectedSize}, got {shrunk.size}"
  return .ok shrunk

/-- Self-test `shrinkTrace` on both a single-step fault and an ordered two-step fault embedded in random traces. -/
def runGenericShrinkSelfTest (seedVal : UInt64 := 0x123456789abcdef0) : IO Unit := do
  let mut rng := Rng.seed (seedVal ^^^ 0x6a09e667f3bcc908)
  let mut trace1 : Array Nat := Array.mkEmpty 24
  for _ in [:24] do
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
  for _ in [:24] do
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
