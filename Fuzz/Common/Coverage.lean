import Std.Data.HashMap

namespace Fuzz.Common

/-- Key identifying one `(operation × error/outcome bucket)` coverage cell. -/
structure CoverageBucket where
  /-- Operation or syscall name. -/
  op : String
  /-- Outcome or error bucket label (e.g. `ok`, `err.EINVAL`, `err.empty`). -/
  bucket : String
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited, Ord

/-- Human-readable label `"<op> -> <bucket>"` for a `CoverageBucket`. -/
def CoverageBucket.label (b : CoverageBucket) : String :=
  s!"{b.op} -> {b.bucket}"

/-- Construct a `CoverageBucket` from an operation name and outcome/error bucket name. -/
def bucket (op name : String) : CoverageBucket :=
  { op := op, bucket := name }

/-- Operation × error-bucket hit counter for fuzzing coverage tracking. -/
structure CoverageTracker where
  /-- Per-bucket observed hit counts. -/
  hits : Std.HashMap CoverageBucket Nat := {}
  /-- Total recorded hits across all buckets. -/
  total : Nat := 0
  deriving Inhabited

/-- Empty `CoverageTracker` with zero recorded hits. -/
def CoverageTracker.empty : CoverageTracker := {}

/-- Increment the hit count for `(op, outcomeBucket)` by `count` (default `1`). -/
def CoverageTracker.record (t : CoverageTracker) (op outcomeBucket : String) (count : Nat := 1) : CoverageTracker :=
  if count == 0 then
    t
  else
    let key : CoverageBucket := { op := op, bucket := outcomeBucket }
    let prev := t.hits.getD key 0
    { hits := t.hits.insert key (prev + count)
      total := t.total + count }

/-- Merge two `CoverageTracker` maps by summing counts per bucket. -/
def CoverageTracker.merge (a b : CoverageTracker) : CoverageTracker :=
  let mergedHits := b.hits.fold (init := a.hits) fun acc k n =>
    if n == 0 then acc else acc.insert k (acc.getD k 0 + n)
  { hits := mergedHits
    total := a.total + b.total }

/-- Return the hit count for `(op, outcomeBucket)`, or `0` if unseen. -/
def CoverageTracker.get (t : CoverageTracker) (op outcomeBucket : String) : Nat :=
  t.hits.getD { op := op, bucket := outcomeBucket } 0

/-- Return all non-zero buckets sorted deterministically by `(op, bucket)`. -/
def CoverageTracker.sortedEntries (t : CoverageTracker) : Array (CoverageBucket × Nat) :=
  let arr := t.hits.fold (init := #[]) fun acc k v => acc.push (k, v)
  arr.qsort fun a b =>
    if a.1.op != b.1.op then a.1.op < b.1.op
    else a.1.bucket < b.1.bucket

/-- Format a deterministic multi-line summary of observed `(op -> bucket): count` entries. -/
def CoverageTracker.formatReport (t : CoverageTracker) (suiteName : String) : String := Id.run do
  let mut lines : Array String := #[s!"COVERAGE_MATRIX_BEGIN suite={suiteName} total={t.total}"]
  for (k, n) in t.sortedEntries do
    lines := lines.push s!"  {k.label}: {n}"
  lines := lines.push s!"COVERAGE_MATRIX_END suite={suiteName}"
  return "\n".intercalate lines.toList

/-- Return every `CoverageBucket` in `required` with `0` hits in `tracker`. -/
def checkCoverage (tracker : CoverageTracker) (required : Array CoverageBucket) : Array CoverageBucket := Id.run do
  let mut missing : Array CoverageBucket := #[]
  for req in required do
    if tracker.get req.op req.bucket == 0 then
      missing := missing.push req
  return missing

/-- Fail loudly with `IO.userError` if any bucket in `required` has `0` hits in `tracker`. -/
def assertCoverage (suiteName : String) (tracker : CoverageTracker) (required : Array CoverageBucket) : IO Unit := do
  let missing := checkCoverage tracker required
  unless missing.isEmpty do
    let labels := missing.toList.map CoverageBucket.label
    throw (IO.userError s!"COVERAGE_GAP suite={suiteName} missing={missing.size}: {", ".intercalate labels}")

end Fuzz.Common
