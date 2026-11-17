import Core.Assumptions
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

private def assertErrKind {α : Type} [Repr α] (actual : Except GlobError α) (expected : GlobErrorKind)
    (msg : String) : IO Unit := do
  match actual with
  | .ok v => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error, got {repr v})")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected kind {repr expected})")

/-- Error test for `Glob.validate` returning `.unclosedClass`. -/
def err_glob_validate_unclosedClass : IO Unit :=
  assertErrKind (Glob.validate "[abc") .unclosedClass "validate unclosed class"

/-- Error test for `Glob.validate` returning `.emptyClass`. -/
def err_glob_validate_emptyClass : IO Unit :=
  assertErrKind (Glob.validate "[]") .emptyClass "validate empty class"

/-- Error test for `Glob.validate` returning `.invalidRange`. -/
def err_glob_validate_invalidRange : IO Unit :=
  assertErrKind (Glob.validate "[z-a]") .invalidRange "validate reversed range"

/-- Error test for `Glob.validate` returning `.trailingEscape`. -/
def err_glob_validate_trailingEscape : IO Unit :=
  assertErrKind (Glob.validate "abc\\") .trailingEscape "validate trailing escape"

/-- Error test for `Glob.isMatch` returning `.unclosedClass`. -/
def err_glob_isMatch_unclosedClass : IO Unit :=
  assertErrKind (Glob.isMatch "[abc" "a") .unclosedClass "isMatch unclosed class"

/-- Error test for `Glob.isMatch` returning `.emptyClass`. -/
def err_glob_isMatch_emptyClass : IO Unit :=
  assertErrKind (Glob.isMatch "[]" "a") .emptyClass "isMatch empty class"

/-- Error test for `Glob.isMatch` returning `.invalidRange`. -/
def err_glob_isMatch_invalidRange : IO Unit :=
  assertErrKind (Glob.isMatch "[z-a]" "a") .invalidRange "isMatch reversed range"

/-- Error test for `Glob.isMatch` returning `.trailingEscape`. -/
def err_glob_isMatch_trailingEscape : IO Unit :=
  assertErrKind (Glob.isMatch "abc\\" "abc") .trailingEscape "isMatch trailing escape"

/-- Error test for `Glob.filter` returning `.unclosedClass`. -/
def err_glob_filter_unclosedClass : IO Unit :=
  assertErrKind (Glob.filter "[abc" #["a"]) .unclosedClass "filter unclosed class"

/-- Error test for `Glob.filter` returning `.emptyClass`. -/
def err_glob_filter_emptyClass : IO Unit :=
  assertErrKind (Glob.filter "[]" #["a"]) .emptyClass "filter empty class"

/-- Error test for `Glob.filter` returning `.invalidRange`. -/
def err_glob_filter_invalidRange : IO Unit :=
  assertErrKind (Glob.filter "[z-a]" #["a"]) .invalidRange "filter reversed range"

/-- Error test for `Glob.filter` returning `.trailingEscape`. -/
def err_glob_filter_trailingEscape : IO Unit :=
  assertErrKind (Glob.filter "abc\\" #["abc"]) .trailingEscape "filter trailing escape"

/-- Error test for `Glob.countMatches` returning `.unclosedClass`. -/
def err_glob_countMatches_unclosedClass : IO Unit :=
  assertErrKind (Glob.countMatches "[abc" #["a"]) .unclosedClass "countMatches unclosed class"

/-- Error test for `Glob.countMatches` returning `.emptyClass`. -/
def err_glob_countMatches_emptyClass : IO Unit :=
  assertErrKind (Glob.countMatches "[]" #["a"]) .emptyClass "countMatches empty class"

/-- Error test for `Glob.countMatches` returning `.invalidRange`. -/
def err_glob_countMatches_invalidRange : IO Unit :=
  assertErrKind (Glob.countMatches "[z-a]" #["a"]) .invalidRange "countMatches reversed range"

/-- Error test for `Glob.countMatches` returning `.trailingEscape`. -/
def err_glob_countMatches_trailingEscape : IO Unit :=
  assertErrKind (Glob.countMatches "abc\\" #["abc"]) .trailingEscape "countMatches trailing escape"

/-- Registered error-coverage tests for `LeanSwe.Glob`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Glob.RuntimeTests.err_glob_validate_unclosedClass"
     , mode := .real
     , run := err_glob_validate_unclosedClass }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_validate_emptyClass"
     , mode := .real
     , run := err_glob_validate_emptyClass }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_validate_invalidRange"
     , mode := .real
     , run := err_glob_validate_invalidRange }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_validate_trailingEscape"
     , mode := .real
     , run := err_glob_validate_trailingEscape }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_isMatch_unclosedClass"
     , mode := .real
     , run := err_glob_isMatch_unclosedClass }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_isMatch_emptyClass"
     , mode := .real
     , run := err_glob_isMatch_emptyClass }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_isMatch_invalidRange"
     , mode := .real
     , run := err_glob_isMatch_invalidRange }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_isMatch_trailingEscape"
     , mode := .real
     , run := err_glob_isMatch_trailingEscape }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_filter_unclosedClass"
     , mode := .real
     , run := err_glob_filter_unclosedClass }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_filter_emptyClass"
     , mode := .real
     , run := err_glob_filter_emptyClass }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_filter_invalidRange"
     , mode := .real
     , run := err_glob_filter_invalidRange }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_filter_trailingEscape"
     , mode := .real
     , run := err_glob_filter_trailingEscape }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_countMatches_unclosedClass"
     , mode := .real
     , run := err_glob_countMatches_unclosedClass }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_countMatches_emptyClass"
     , mode := .real
     , run := err_glob_countMatches_emptyClass }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_countMatches_invalidRange"
     , mode := .real
     , run := err_glob_countMatches_invalidRange }
   , { testName := "LeanSwe.Glob.RuntimeTests.err_glob_countMatches_trailingEscape"
     , mode := .real
     , run := err_glob_countMatches_trailingEscape }
   ]

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
  assertOkEq (Glob.isMatch "[ab]" "a") true "single char class matches first entry"
  assertOkEq (Glob.isMatch "[ab]" "c") false "single char class rejects non-member"
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
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.Glob runtime tests"

end LeanSwe.Glob.RuntimeTests
