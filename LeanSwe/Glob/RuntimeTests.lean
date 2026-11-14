import LeanSwe.Glob.Interface

namespace LeanSwe.Glob.RuntimeTests

open LeanSwe

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOkEq {α : Type} [BEq α] [Repr α]
    (actual : Except GlobError α) (expected : α) (msg : String) : IO Unit := do
  match actual with
  | .ok v =>
    if !(v == expected) then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr v}, expected {repr expected})")
  | .error e =>
    throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {e.message})")

private def assertErrKind (actual : Except GlobError Unit) (expected : GlobErrorKind)
    (msg : String) : IO Unit := do
  match actual with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected kind {repr expected})")

/-- Execute all runtime sanity checks for `LeanSwe.Glob`. -/
def runAll : IO Unit := do
  assertOkEq (Glob.isMatch "*.lean" "Main.lean") true "star extension match"
  assertOkEq (Glob.isMatch "*.lean" "src/Main.lean") false "star must not cross /"
  assertOkEq (Glob.isMatch "**/*.lean" "Main.lean") true "globstar matches zero dirs"
  assertOkEq (Glob.isMatch "**/*.lean" "a/b/Main.lean") true "globstar matches nested dirs"
  assertOkEq (Glob.isMatch "a/**/z" "a/z") true "middle globstar zero dirs"
  assertOkEq (Glob.isMatch "a/**/z" "a/x/y/z") true "middle globstar multi dirs"
  assertOkEq (Glob.isMatch "f?o" "foo") true "? matches one char"
  assertOkEq (Glob.isMatch "f?o" "f/o") false "? matches within one segment only"
  assertOkEq (Glob.isMatch "[a-c][0-9]" "b7") true "character ranges"
  assertOkEq (Glob.isMatch "[!0-9].txt" "a.txt") true "negated class matches alpha"
  assertOkEq (Glob.isMatch "[!0-9].txt" "5.txt") false "negated class rejects digit"
  assertOkEq (Glob.isMatch "[a-]" "-") true "trailing dash in class is literal"
  assertOkEq (Glob.isMatch "a\\*b" "a*b") true "escaped star is literal"
  assertOkEq (Glob.isMatch "a\\*b" "axb") false "escaped star does not wildcard"
  assertOkEq (Glob.isMatch (Glob.escape "src/**/a[0]*.lean") "src/**/a[0]*.lean")
    true "escape roundtrip with ** and brackets"
  assertOkEq
    (Glob.filter "LeanSwe/**/*.lean"
      #["LeanSwe/RegExp/Types.lean", "Tests/Main.lean", "LeanSwe/Glob/Impl.lean"])
    #["LeanSwe/RegExp/Types.lean", "LeanSwe/Glob/Impl.lean"]
    "filter preserves matching paths in order"
  assertOkEq
    (Glob.countMatches "LeanSwe/**/*.lean"
      #["LeanSwe/RegExp/Types.lean", "Tests/Main.lean", "LeanSwe/Glob/Impl.lean"])
    2
    "countMatches matches filter size"
  assertErrKind (Glob.validate "[abc") .unclosedClass "unclosed bracket"
  assertErrKind (Glob.validate "[]") .emptyClass "empty bracket"
  assertErrKind (Glob.validate "[!]") .emptyClass "empty negated bracket"
  assertErrKind (Glob.validate "[z-a]") .invalidRange "reversed range"
  assertErrKind (Glob.validate "abc\\") .trailingEscape "trailing backslash"
  assertTrue (Glob.escape "a*b/c?[0]\\d" == "a\\*b/c\\?\\[0\\]\\\\d")
    "escape leaves / untouched and escapes metachars"
  IO.println "PASS: LeanSwe.Glob runtime tests"

end LeanSwe.Glob.RuntimeTests
