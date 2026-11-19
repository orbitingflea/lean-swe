namespace Fuzz.Common

/-- Deterministic 64-bit SplitMix64 pseudo-random generator state. -/
structure Rng where
  /-- Current 64-bit internal seed state. -/
  state : UInt64
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Construct a deterministic `Rng` from a 64-bit seed. -/
def Rng.seed (s : UInt64) : Rng := { state := s }

/-- Advance `Rng` by one SplitMix64 step and return the mixed 64-bit value. -/
def Rng.nextU64 (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9e3779b97f4a7c15
  let z1 := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  let z3 := z2 ^^^ (z2 >>> 31)
  (z3, { state := s })

/-- Derive an independent child `Rng` while advancing the parent generator. -/
def Rng.split (r : Rng) : Rng × Rng :=
  let (childSeed, r') := r.nextU64
  (Rng.seed childSeed, r')

private partial def nextBigNatLoop (r : Rng) (words : Nat) (space : Nat) (bound : Nat) : Nat × Rng :=
  Id.run do
    let mut cur := r
    let mut acc : Nat := 0
    for _ in [:words] do
      let (v, nxt) := cur.nextU64
      cur := nxt
      acc := acc * UInt64.size + v.toNat
    let threshold := space % bound
    if acc >= threshold then
      return (acc % bound, cur)
    else
      return nextBigNatLoop cur words space bound

private partial def nextSmallNatLoop (r : Rng) (bound threshold : Nat) : Nat × Rng :=
  let (v, r') := r.nextU64
  if v.toNat >= threshold then
    (v.toNat % bound, r')
  else
    nextSmallNatLoop r' bound threshold

/-- Return an unbiased pseudo-random `Nat` in `[0, bound)` (or `0` when `bound <= 1`). -/
def Rng.nextNat (r : Rng) (bound : Nat) : Nat × Rng :=
  if bound <= 1 then
    (0, r)
  else if bound == UInt64.size then
    let (v, r') := r.nextU64
    (v.toNat, r')
  else if bound < UInt64.size then
    nextSmallNatLoop r bound (UInt64.size % bound)
  else
    let (words, space) := Id.run do
      let mut w : Nat := 2
      let mut sp : Nat := UInt64.size * UInt64.size
      while sp < bound do
        w := w + 1
        sp := sp * UInt64.size
      return (w, sp)
    nextBigNatLoop r words space bound

/-- Return an unbiased pseudo-random `Nat` in `[lo, hi]` inclusive (`lo` when `hi <= lo`). -/
def Rng.nextRange (r : Rng) (lo hi : Nat) : Nat × Rng :=
  if hi <= lo then
    (lo, r)
  else
    let (off, r') := r.nextNat (hi - lo + 1)
    (lo + off, r')

/-- Return an unbiased pseudo-random `Int` in `[lo, hi]` inclusive (`lo` when `hi <= lo`). -/
def Rng.nextIntRange (r : Rng) (lo hi : Int) : Int × Rng :=
  if hi <= lo then
    (lo, r)
  else
    let span := (hi - lo).toNat + 1
    let (off, r') := r.nextNat span
    (lo + Int.ofNat off, r')

/-- Return an unbiased pseudo-random `Bool`. -/
def Rng.nextBool (r : Rng) : Bool × Rng :=
  let (v, r') := r.nextU64
  ((v >>> 63) == 1, r')

/-- Return a `Bool` with exact `num / den` true probability (`false` when `den == 0` or `num == 0`). -/
def Rng.chance (r : Rng) (num den : Nat) : Bool × Rng :=
  if den == 0 || num == 0 then
    (false, r)
  else if num >= den then
    (true, r)
  else
    let (v, r') := r.nextNat den
    (v < num, r')

/-- Return a pseudo-random `UInt8`. -/
def Rng.nextU8 (r : Rng) : UInt8 × Rng :=
  let (v, r') := r.nextU64
  (UInt8.ofNat (v >>> 56).toNat, r')

/-- Return a pseudo-random `UInt32`. -/
def Rng.nextU32 (r : Rng) : UInt32 × Rng :=
  let (v, r') := r.nextU64
  (UInt32.ofNat (v >>> 32).toNat, r')

/-- Return `len` pseudo-random bytes as a `ByteArray`. -/
def Rng.nextBytes (r : Rng) (len : Nat) : ByteArray × Rng := Id.run do
  let mut cur := r
  let mut out := ByteArray.emptyWithCapacity len
  let fullWords := len / 8
  let remBytes := len % 8
  for _ in [:fullWords] do
    let (w, nxt) := cur.nextU64
    cur := nxt
    out := out.push w.toUInt8
    out := out.push (w >>> 8).toUInt8
    out := out.push (w >>> 16).toUInt8
    out := out.push (w >>> 24).toUInt8
    out := out.push (w >>> 32).toUInt8
    out := out.push (w >>> 40).toUInt8
    out := out.push (w >>> 48).toUInt8
    out := out.push (w >>> 56).toUInt8
  if remBytes > 0 then
    let (w, nxt) := cur.nextU64
    cur := nxt
    for shift in [:remBytes] do
      out := out.push (w >>> UInt64.ofNat (shift * 8)).toUInt8
  return (out, cur)

/-- Return a `ByteArray` of unbiased random length in `[minLen, maxLen]` filled with random bytes. -/
def Rng.nextBytesRange (r : Rng) (minLen maxLen : Nat) : ByteArray × Rng :=
  let (len, r1) := r.nextRange minLen maxLen
  r1.nextBytes len

/-- Pick an element uniformly from `xs`, returning `none` if empty. -/
def Rng.choose? {α : Type} (r : Rng) (xs : Array α) : Option α × Rng :=
  if xs.isEmpty then
    (none, r)
  else
    let (idx, r') := r.nextNat xs.size
    (xs[idx]?, r')

/-- Pick an element uniformly from `xs`, returning `fallback` if empty. -/
def Rng.choose {α : Type} (r : Rng) (xs : Array α) (fallback : α) : α × Rng :=
  if xs.isEmpty then
    (fallback, r)
  else
    let (idx, r') := r.nextNat xs.size
    (xs.getD idx fallback, r')

/-- Pick an element uniformly from a `List`, returning `fallback` if empty. -/
def Rng.chooseList {α : Type} (r : Rng) (xs : List α) (fallback : α) : α × Rng :=
  r.choose xs.toArray fallback

/-- Pick an element according to positive integer weights `(weight, value)`, returning `fallback` if total weight is 0. -/
def Rng.chooseWeighted {α : Type} (r : Rng) (items : Array (Nat × α)) (fallback : α) : α × Rng := Id.run do
  let total := items.foldl (fun acc (w, _) => acc + w) 0
  if total == 0 then
    return (fallback, r)
  let (pick, r') := r.nextNat total
  let mut running := 0
  for (w, val) in items do
    running := running + w
    if pick < running then
      return (val, r')
  return (fallback, r')

end Fuzz.Common
