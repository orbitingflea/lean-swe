import Core.NondetTest
import LeanSwe.Glob.Types

/-!
# Glob SpecTests

Human-audited behavioral specifications for `LeanSwe.Glob.GlobApi` written in
`Core.NondetTest`. Notice zero raw `∀`, `→`, or proof scripts appear in the
spec definitions below.
-/

namespace LeanSwe.Glob

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `api.isMatch` must carry a non-empty diagnostic message. -/
def test_glob_onError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let path ← nondet String
  match api.isMatch pat path with
  | .ok _ => assume False
  | .error e => assert (e.message ≠ "")

/-- `api.isMatch pat path` succeeds iff `api.validate pat` succeeds (independent of `path`). -/
def test_glob_isMatch_iff_validateOk
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let path ← nondet String
  match api.validate pat with
  | .error e1 =>
    match api.isMatch pat path with
    | .ok _ => assert False
    | .error e2 => assert (e1 = e2)
  | .ok () =>
    match api.isMatch pat path with
    | .error _ => assert False
    | .ok _ => assert True

/-- On valid patterns, `api.filter` shrinks or keeps size and only emits matching paths. -/
def test_glob_filter_preservesValidity
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let paths ← nondet (Array String)
  match api.validate pat with
  | .error _ => assume False
  | .ok () =>
    match api.filter pat paths with
    | .error _ => assert False
    | .ok kept =>
      assert (kept.size ≤ paths.size)
      let i ← nondet Nat
      assume (i < kept.size)
      match api.isMatch pat kept[i]! with
      | .ok b => assert (b = true)
      | .error _ => assert False

/-- `api.countMatches pat paths` equals `(api.filter pat paths).map Array.size`. -/
def test_glob_countMatches_eq_filterSize
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let paths ← nondet (Array String)
  match api.filter pat paths with
  | .error e1 =>
    match api.countMatches pat paths with
    | .ok _ => assert False
    | .error e2 => assert (e1 = e2)
  | .ok kept =>
    match api.countMatches pat paths with
    | .error _ => assert False
    | .ok c => assert (c = kept.size)

/-- The recursive globstar pattern `"**"` matches every path. -/
def test_glob_globStar_matchesAll
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let path ← nondet String
  match api.isMatch "**" path with
  | .error _ => assume False
  | .ok b => assert (b = true)

/-- Escaping any literal path produces a valid glob pattern that matches the original path. -/
def test_glob_escape_matchesSelf
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let path ← nondet String
  match api.isMatch (api.escape path) path with
  | .error _ => assert False
  | .ok b => assert (b = true)

/-- Negative mutation check: a stub returning `countMatches = 99` must fail `SpecTests`. -/
private def buggyCountApi : GlobApi :=
  { validate := fun _ => .ok ()
    isMatch := fun _ _ => .ok false
    filter := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 99
    escape := id }

example : ¬ Core.AllPass (test_glob_countMatches_eq_filterSize buggyCountApi) := by
  intro h
  have h0 := h "*.lean" #[]
  simp [buggyCountApi, assert] at h0

/-- Negative mutation check: a stub whose `isMatch` always fails to match must fail `SpecTests`. -/
private def buggyNeverMatchApi : GlobApi :=
  { validate := fun _ => .ok ()
    isMatch := fun _ _ => .ok false
    filter := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 0
    escape := id }

example : ¬ Core.AllPass (test_glob_globStar_matchesAll buggyNeverMatchApi) := by
  intro h
  have h0 := h "src/Main.lean"
  simp [buggyNeverMatchApi, assert] at h0

example : ¬ Core.AllPass (test_glob_escape_matchesSelf buggyNeverMatchApi) := by
  intro h
  have h0 := h "a.lean"
  simp [buggyNeverMatchApi, assert] at h0

/-- Negative mutation check: a `filter` dropping validation errors must fail `SpecTests` consistency. -/
private def buggySilentValidateApi : GlobApi :=
  { validate := fun _ => .error { kind := .unclosedClass, message := "err" }
    isMatch := fun _ _ => .ok true
    filter := fun _ xs => .ok xs
    countMatches := fun _ xs => .ok xs.size
    escape := id }

example : ¬ Core.AllPass (test_glob_isMatch_iff_validateOk buggySilentValidateApi) := by
  intro h
  have h0 := h "[" "a"
  simp [buggySilentValidateApi, assert] at h0

end LeanSwe.Glob
