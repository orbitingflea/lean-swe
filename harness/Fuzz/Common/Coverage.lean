import Std.Data.HashMap
import Std.Data.HashSet
import Fuzz.Common.Suite

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

/-- Merge two `CoverageTracker` maps symmetrically, dropping zero-count buckets and recomputing `total`. -/
def CoverageTracker.merge (a b : CoverageTracker) : CoverageTracker :=
  let addNonZero (init : Std.HashMap CoverageBucket Nat) (m : Std.HashMap CoverageBucket Nat) :=
    m.fold (init := init) fun acc k n =>
      if n == 0 then acc else acc.insert k (acc.getD k 0 + n)
  let mergedHits := addNonZero (addNonZero {} a.hits) b.hits
  let totalHits := mergedHits.fold (init := 0) fun acc _ n => acc + n
  { hits := mergedHits
    total := totalHits }

/-- Return the hit count for `(op, outcomeBucket)`, or `0` if unseen. -/
def CoverageTracker.get (t : CoverageTracker) (op outcomeBucket : String) : Nat :=
  t.hits.getD { op := op, bucket := outcomeBucket } 0

/-- Return all non-zero buckets sorted deterministically by `(op, bucket)`. -/
def CoverageTracker.sortedEntries (t : CoverageTracker) : Array (CoverageBucket × Nat) :=
  let arr := t.hits.fold (init := #[]) fun acc k v =>
    if v > 0 then acc.push (k, v) else acc
  arr.qsort fun a b =>
    if a.1.op != b.1.op then a.1.op < b.1.op
    else a.1.bucket < b.1.bucket

/-- Format a deterministic multi-line summary of observed `(op -> bucket): count` entries. -/
def CoverageTracker.formatReport (t : CoverageTracker) (suiteName : String) : String := Id.run do
  let entries := t.sortedEntries
  let sumTotal := entries.foldl (fun acc (_, n) => acc + n) 0
  let mut lines : Array String := #[s!"COVERAGE_MATRIX_BEGIN suite={suiteName} total={sumTotal}"]
  for (k, n) in entries do
    lines := lines.push s!"  {k.label}: {n}"
  lines := lines.push s!"COVERAGE_MATRIX_END suite={suiteName}"
  return "\n".intercalate lines.toList

/-- Return every unique `CoverageBucket` in `required` with `0` hits in `tracker` (preserving first-seen order). -/
def checkCoverage (tracker : CoverageTracker) (required : Array CoverageBucket) : Array CoverageBucket := Id.run do
  let mut missing : Array CoverageBucket := #[]
  let mut seen : Std.HashSet CoverageBucket := {}
  for req in required do
    if seen.contains req then
      continue
    seen := seen.insert req
    if tracker.get req.op req.bucket == 0 then
      missing := missing.push req
  return missing

/-- Fail loudly with `IO.userError` if any bucket in `required` has `0` hits in `tracker`. -/
def assertCoverage (suiteName : String) (tracker : CoverageTracker) (required : Array CoverageBucket) : IO Unit := do
  let mut uniqueCount : Nat := 0
  let mut seen : Std.HashSet CoverageBucket := {}
  for req in required do
    if !seen.contains req then
      seen := seen.insert req
      uniqueCount := uniqueCount + 1
  let missing := checkCoverage tracker required
  let hitCount := uniqueCount - missing.size
  recordSuiteBuckets hitCount uniqueCount
  unless missing.isEmpty do
    let labels := missing.toList.map CoverageBucket.label
    throw (IO.userError s!"COVERAGE_GAP suite={suiteName} missing={missing.size}: {", ".intercalate labels}")

end Fuzz.Common
