import Core.NondetTest
import Core.Assumptions
import LeanSwe.Glob.Types

namespace LeanSwe.Glob

open Core (NondetTest ErrorObligation)
open Core.NondetTest

/-- Every error returned by `api.isMatch` must carry a non-empty diagnostic message. -/
def test_glob_onError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let path ← nondet String
  match api.isMatch pat path with
  | .ok _ => assume False
  | .error e => NondetTest.assert (e.message ≠ "")

/-- `api.isMatch pat path` succeeds iff `api.validate pat` succeeds (independent of `path`). -/
def test_glob_isMatch_iff_validateOk
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let path ← nondet String
  match api.validate pat with
  | .error e1 =>
    match api.isMatch pat path with
    | .ok _ => NondetTest.assert False
    | .error e2 => NondetTest.assert (e1 = e2)
  | .ok () =>
    match api.isMatch pat path with
    | .error _ => NondetTest.assert False
    | .ok _ => NondetTest.assert True

/-- On valid patterns, `api.filter` shrinks or keeps size and only emits matching paths. -/
def test_glob_filter_preservesValidity
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let paths ← nondet (Array String)
  match api.validate pat with
  | .error _ => assume False
  | .ok () =>
    match api.filter pat paths with
    | .error _ => NondetTest.assert False
    | .ok kept =>
      NondetTest.assert (kept.size ≤ paths.size)
      let i ← nondet Nat
      assume (i < kept.size)
      match api.isMatch pat kept[i]! with
      | .ok b => NondetTest.assert (b = true)
      | .error _ => NondetTest.assert False

/-- `api.countMatches pat paths` equals `(api.filter pat paths).map Array.size`. -/
def test_glob_countMatches_eq_filterSize
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let paths ← nondet (Array String)
  match api.filter pat paths with
  | .error e1 =>
    match api.countMatches pat paths with
    | .ok _ => NondetTest.assert False
    | .error e2 => NondetTest.assert (e1 = e2)
  | .ok kept =>
    match api.countMatches pat paths with
    | .error _ => NondetTest.assert False
    | .ok c => NondetTest.assert (c = kept.size)

/-- The recursive globstar pattern `"**"` matches every path. -/
def test_glob_globStar_matchesAll
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let path ← nondet String
  match api.isMatch "**" path with
  | .error _ => assume False
  | .ok b => NondetTest.assert (b = true)

/-- Escaping any literal path produces a valid glob pattern that matches the original path. -/
def test_glob_escape_matchesSelf
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let path ← nondet String
  match api.isMatch (api.escape path) path with
  | .error _ => NondetTest.assert False
  | .ok b => NondetTest.assert (b = true)

/-- Declared error-coverage matrix for `LeanSwe.Glob` fallible requests (`GlobErrorKind`). -/
def errorCoverage : List (ErrorObligation GlobErrorKind) :=
  [ { request := "LeanSwe.Glob.validate"
      errorKind := .unclosedClass
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_validate_unclosedClass" .real }
  , { request := "LeanSwe.Glob.validate"
      errorKind := .emptyClass
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_validate_emptyClass" .real }
  , { request := "LeanSwe.Glob.validate"
      errorKind := .invalidRange
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_validate_invalidRange" .real }
  , { request := "LeanSwe.Glob.validate"
      errorKind := .trailingEscape
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_validate_trailingEscape" .real }
  , { request := "LeanSwe.Glob.isMatch"
      errorKind := .unclosedClass
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_isMatch_unclosedClass" .real }
  , { request := "LeanSwe.Glob.isMatch"
      errorKind := .emptyClass
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_isMatch_emptyClass" .real }
  , { request := "LeanSwe.Glob.isMatch"
      errorKind := .invalidRange
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_isMatch_invalidRange" .real }
  , { request := "LeanSwe.Glob.isMatch"
      errorKind := .trailingEscape
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_isMatch_trailingEscape" .real }
  , { request := "LeanSwe.Glob.filter"
      errorKind := .unclosedClass
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_filter_unclosedClass" .real }
  , { request := "LeanSwe.Glob.filter"
      errorKind := .emptyClass
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_filter_emptyClass" .real }
  , { request := "LeanSwe.Glob.filter"
      errorKind := .invalidRange
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_filter_invalidRange" .real }
  , { request := "LeanSwe.Glob.filter"
      errorKind := .trailingEscape
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_filter_trailingEscape" .real }
  , { request := "LeanSwe.Glob.countMatches"
      errorKind := .unclosedClass
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_countMatches_unclosedClass" .real }
  , { request := "LeanSwe.Glob.countMatches"
      errorKind := .emptyClass
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_countMatches_emptyClass" .real }
  , { request := "LeanSwe.Glob.countMatches"
      errorKind := .invalidRange
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_countMatches_invalidRange" .real }
  , { request := "LeanSwe.Glob.countMatches"
      errorKind := .trailingEscape
      justification := .tested "LeanSwe.Glob.RuntimeTests.err_glob_countMatches_trailingEscape" .real } ]

end LeanSwe.Glob
