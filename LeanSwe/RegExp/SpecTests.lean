import Core.NondetTest
import LeanSwe.RegExp.Types

/-!
# Regex SpecTests

Human-audited behavioral specifications for `LeanSwe.RegExp.RegexApi` written in
`Core.NondetTest`. Notice zero raw `∀`, `→`, or proof scripts appear in the
spec definitions below.
-/

namespace LeanSwe.RegExp

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `api.testPattern` must carry a non-empty diagnostic message. -/
def test_regex_onError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : RegexApi) : runner Unit := do
  let pat ← nondet String
  let hay ← nondet String
  match api.testPattern pat hay with
  | .ok _ => assume False
  | .error e => assert (e.message ≠ "")

/-- On valid patterns, `testPattern` returns `true` iff `findFirst` returns `some span`. -/
def test_regex_testPattern_iff_findFirstSome
    {runner} [NondetTest runner] (api : RegexApi) : runner Unit := do
  let pat ← nondet String
  let hay ← nondet String
  match api.testPattern pat hay with
  | .error _ => assume False
  | .ok b =>
    match api.findFirst pat hay with
    | .error _ => assert False
    | .ok span? => assert (b = true ↔ span?.isSome)

/-- On valid patterns, `countMatches` equals `(findAll).size`. -/
def test_regex_countMatches_eq_findAllSize
    {runner} [NondetTest runner] (api : RegexApi) : runner Unit := do
  let pat ← nondet String
  let hay ← nondet String
  match api.countMatches pat hay with
  | .error _ => assume False
  | .ok c =>
    match api.findAll pat hay with
    | .error _ => assert False
    | .ok xs => assert (c = xs.size)

/-- Every `MatchSpan` returned by `findAll` satisfies `startByte ≤ stopByte ≤ hay.utf8ByteSize`. -/
def test_regex_findAll_spansValid
    {runner} [NondetTest runner] (api : RegexApi) : runner Unit := do
  let pat ← nondet String
  let hay ← nondet String
  match api.findAll pat hay with
  | .error _ => assume False
  | .ok xs =>
    let i ← nondet Nat
    assume (i < xs.size)
    let span := xs[i]!
    assert (span.startByte ≤ span.stopByte ∧ span.stopByte ≤ hay.utf8ByteSize)

/-- On valid patterns, `splitBy` always returns at least one substring piece. -/
def test_regex_splitBy_nonEmpty
    {runner} [NondetTest runner] (api : RegexApi) : runner Unit := do
  let pat ← nondet String
  let hay ← nondet String
  match api.splitBy pat hay with
  | .error _ => assume False
  | .ok parts => assert (1 ≤ parts.size)

/-- The empty regex pattern `""` matches every haystack string. -/
def test_regex_emptyPattern_matchesAnyHaystack
    {runner} [NondetTest runner] (api : RegexApi) : runner Unit := do
  let hay ← nondet String
  match api.testPattern "" hay with
  | .error _ => assume False
  | .ok b => assert (b = true)

/-- Replacing matches of `""` in `""` with `rep` returns `rep`. -/
def test_regex_replaceAll_emptyOnEmpty_eqReplacement
    {runner} [NondetTest runner] (api : RegexApi) : runner Unit := do
  let rep ← nondet String
  match api.replaceAll "" "" rep with
  | .error _ => assume False
  | .ok out => assert (out = rep)

/-- Compile-time negative mutation check: a broken `countMatches` must fail `SpecTests`. -/
private def buggyCountApi : RegexApi :=
  { testPattern := fun _ _ => .ok false
    findFirst := fun _ _ => .ok none
    findAll := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 99
    replaceAll := fun _ h _ => .ok h
    splitBy := fun _ h => .ok #[h] }

example : ¬ Core.AllPass (test_regex_countMatches_eq_findAllSize buggyCountApi) := by
  intro h
  have h0 := h "a" "a"
  simp [buggyCountApi, assert] at h0

example : ¬ Core.AllPass (test_regex_replaceAll_emptyOnEmpty_eqReplacement buggyCountApi) := by
  intro h
  have h0 := h "x"
  simp [buggyCountApi, assert] at h0

/-- Compile-time negative mutation check: a stub that never matches must fail semantic `SpecTests`. -/
private def buggyNeverMatchApi : RegexApi :=
  { testPattern := fun _ _ => .ok false
    findFirst := fun _ _ => .ok none
    findAll := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 0
    replaceAll := fun _ h _ => .ok h
    splitBy := fun _ h => .ok #[h] }

example : ¬ Core.AllPass (test_regex_emptyPattern_matchesAnyHaystack buggyNeverMatchApi) := by
  intro h
  have h0 := h "abc"
  simp [buggyNeverMatchApi, assert] at h0

/-- Compile-time negative mutation check: a `testPattern` always returning `true` must fail `SpecTests`. -/
private def buggyTestApi : RegexApi :=
  { testPattern := fun _ _ => .ok true
    findFirst := fun _ _ => .ok none
    findAll := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 0
    replaceAll := fun _ h _ => .ok h
    splitBy := fun _ h => .ok #[h] }

example : ¬ Core.AllPass (test_regex_testPattern_iff_findFirstSome buggyTestApi) := by
  intro h
  have h0 := h "a" "a"
  simp [buggyTestApi, assert] at h0

end LeanSwe.RegExp
