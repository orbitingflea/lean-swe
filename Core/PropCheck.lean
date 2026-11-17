import Core.NondetTest

namespace Core.PropCheck

/-- Simple deterministic pseudo-RNG (LCG) for reproducible runtime property testing. -/
structure Rng where
  /-- Current 64-bit LCG state. -/
  state : UInt64 := 0x9e3779b97f4a7c15

/-- Advance `Rng` by one step returning `(nextUInt64, updatedRng)`. -/
def Rng.next (r : Rng) : UInt64 × Rng :=
  let s' := r.state * 6364136223846793005 + 1442695040888963407
  (s', { state := s' })

/-- Outcome of running a property check across `trials` random or curated draws. -/
structure PropCheckStats where
  /-- Number of trials passing all `assume` guards and executing `assert`. -/
  passed : Nat := 0
  /-- Number of trials discarded by an `assume` guard. -/
  discarded : Nat := 0

/-- Enforce an `assume` guard returning `.error "__DISCARD__"` when `cond = false`. -/
def assumeB (cond : Bool) : Except String Unit :=
  if cond then .ok () else .error "__DISCARD__"

/-- Enforce an `assert` check returning `.error` when `cond = false`. -/
def assertB (label : String) (cond : Bool) : Except String Unit :=
  if cond then .ok () else .error s!"ASSERT_FAILED: {label}"

/-- Run `prop` for `trials` draws, failing if any `assertB` fails or if zero trials pass `assumeB`. -/
def checkFor (name : String) (trials : Nat := 60)
    (prop : Rng → Rng × Except String Unit) : IO PropCheckStats := do
  let mut rng : Rng := {}
  let mut stats : PropCheckStats := {}
  for i in [:trials] do
    let (rng', res) := prop { state := rng.state + UInt64.ofNat (i * 1315423911 + 1) }
    rng := rng'
    match res with
    | .ok () => stats := { stats with passed := stats.passed + 1 }
    | .error "__DISCARD__" => stats := { stats with discarded := stats.discarded + 1 }
    | .error msg =>
      throw (IO.userError s!"PropCheck `{name}` failed at trial {i}: {msg}")
  if stats.passed == 0 then
    throw (IO.userError s!"PropCheck `{name}` had 0 passing trials (all {stats.discarded} discarded by assume)")
  return stats

end Core.PropCheck
