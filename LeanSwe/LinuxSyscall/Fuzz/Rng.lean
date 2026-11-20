namespace LeanSwe.LinuxSyscall.Fuzz

/-- Deterministic 64-bit SplitMix64 pseudo-random generator state. -/
structure Rng where
  /-- Current 64-bit internal seed state. -/
  state : UInt64
  deriving Repr, DecidableEq, BEq

/-- Construct a deterministic `Rng` from a 64-bit seed. -/
def Rng.seed (s : UInt64) : Rng := { state := s }

/-- Advance `Rng` by one SplitMix64 step and return the mixed 64-bit value. -/
def Rng.nextU64 (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9e3779b97f4a7c15
  let z1 := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  let z3 := z2 ^^^ (z2 >>> 31)
  (z3, { state := s })

/-- Return a pseudo-random `Nat` in `[0, bound)` (or `0` when `bound = 0`). -/
def Rng.nextNat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r') := r.nextU64
  if bound == 0 then (0, r') else (v.toNat % bound, r')

/-- Return a pseudo-random `Nat` in `[lo, hi]` inclusive. -/
def Rng.nextRange (r : Rng) (lo hi : Nat) : Nat × Rng :=
  if hi <= lo then (lo, r)
  else
    let (off, r') := r.nextNat (hi - lo + 1)
    (lo + off, r')

/-- Return a pseudo-random `Bool` with `num / den` true probability. -/
def Rng.chance (r : Rng) (num den : Nat) : Bool × Rng :=
  if den == 0 then (false, r)
  else
    let (v, r') := r.nextNat den
    (v < num, r')

/-- Pick an element uniformly from a non-empty `Array α`, returning `fallback` if empty. -/
def Rng.pickArray {α : Type} (r : Rng) (xs : Array α) (fallback : α) : α × Rng :=
  if xs.isEmpty then (fallback, r)
  else
    let (idx, r') := r.nextNat xs.size
    (xs.getD idx fallback, r')

/-- Greedy delta-minimization loop reducing a normalized trace via chunked deletion passes down to `chunk = 1`. -/
def deltaShrink {α : Type} (init : α) (sizeOf : α → Nat) (dropRange : α → Nat → Nat → α)
    (reproduces : α → IO Bool) : IO α := do
  let mut cur := init
  let mut chunk := max 1 (sizeOf cur / 2)
  while true do
    let mut progress := false
    let mut i := 0
    while i < sizeOf cur do
      let n := sizeOf cur
      let hi := min n (i + chunk)
      let cand := dropRange cur i hi
      if sizeOf cand < n then
        if ← reproduces cand then
          cur := cand
          progress := true
        else
          i := i + chunk
      else
        i := i + chunk
    if !progress then
      if chunk <= 1 then
        break
      chunk := max 1 (chunk / 2)
  return cur
end LeanSwe.LinuxSyscall.Fuzz
