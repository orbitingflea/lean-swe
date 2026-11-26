import Core.NondetTest
import LeanSwe.Glob.Types
import LeanSwe.Glob.Model

namespace LeanSwe.Glob

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Glob.Model

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

/-- `api.validate` agrees unconditionally with `validateModel` on success, error kind, and non-empty message. -/
def test_glob_validate_matchesModel
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  match api.validate pat, validateModel pat with
  | .ok (), .ok () => NondetTest.assert True
  | .error e, .error expectedKind =>
    NondetTest.assert (e.kind = expectedKind ∧ e.message ≠ "")
  | _, _ => NondetTest.assert False

/-- `api.isMatch` agrees unconditionally with `isMatchModel` across all operators (`*`, `?`, `[...]`, `[!...]`, `\`, `**`, `/`) and syntax errors. -/
def test_glob_isMatch_matchesModel
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let path ← nondet String
  match api.isMatch pat path, isMatchModel pat path with
  | .ok actual, .ok expected => NondetTest.assert (actual = expected)
  | .error e, .error expectedKind =>
    NondetTest.assert (e.kind = expectedKind ∧ e.message ≠ "")
  | _, _ => NondetTest.assert False

/-- `api.filter` agrees unconditionally with `filterModel` in both membership, ordering, and error kind. -/
def test_glob_filter_matchesModel
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let paths ← nondet (Array String)
  match api.filter pat paths, filterModel pat paths with
  | .ok actual, .ok expected => NondetTest.assert (actual = expected)
  | .error e, .error expectedKind =>
    NondetTest.assert (e.kind = expectedKind ∧ e.message ≠ "")
  | _, _ => NondetTest.assert False

/-- `api.countMatches` agrees unconditionally with `countMatchesModel` on count and error kind. -/
def test_glob_countMatches_matchesModel
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let pat ← nondet String
  let paths ← nondet (Array String)
  match api.countMatches pat paths, countMatchesModel pat paths with
  | .ok actual, .ok expected => NondetTest.assert (actual = expected)
  | .error e, .error expectedKind =>
    NondetTest.assert (e.kind = expectedKind ∧ e.message ≠ "")
  | _, _ => NondetTest.assert False

/-- `api.escape` agrees unconditionally with `escapeModel` for every string. -/
def test_glob_escape_matchesModel
    {runner} [NondetTest runner] (api : GlobApi) : runner Unit := do
  let literal ← nondet String
  NondetTest.assert (api.escape literal = escapeModel literal)

end LeanSwe.Glob
