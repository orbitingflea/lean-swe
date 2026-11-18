import Core.Assumptions
import LeanSwe.RegExp.Interface

namespace LeanSwe.RegExp.RuntimeTests

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOkEq {α : Type} [BEq α] [Repr α]
    (actual : Except RegexError α) (expected : α) (msg : String) : IO Unit := do
  match actual with
  | .ok v =>
    if !(v == expected) then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr v}, expected {repr expected})")
  | .error e =>
    throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {e.message})")

private def assertErrKind {α : Type} [Repr α] (actual : Except RegexError α) (expected : RegexErrorKind)
    (msg : String) : IO Unit := do
  match actual with
  | .ok v => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error, got {repr v})")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected kind {repr expected})")

/-- Error test for `testPattern` returning `.invalidSyntax`. -/
def err_regexp_testPattern_invalidSyntax : IO Unit :=
  assertErrKind (testPattern "*bad" "abc") .invalidSyntax "testPattern invalid syntax"

/-- Error test for `testPattern` returning `.unexpectedEof`. -/
def err_regexp_testPattern_unexpectedEof : IO Unit :=
  assertErrKind (testPattern "[unclosed" "abc") .unexpectedEof "testPattern unexpected EOF"

/-- Error test for `findFirst` returning `.invalidSyntax`. -/
def err_regexp_findFirst_invalidSyntax : IO Unit :=
  assertErrKind (findFirst "*bad" "abc") .invalidSyntax "findFirst invalid syntax"

/-- Error test for `findFirst` returning `.unexpectedEof`. -/
def err_regexp_findFirst_unexpectedEof : IO Unit :=
  assertErrKind (findFirst "[unclosed" "abc") .unexpectedEof "findFirst unexpected EOF"

/-- Error test for `findAll` returning `.invalidSyntax`. -/
def err_regexp_findAll_invalidSyntax : IO Unit :=
  assertErrKind (findAll "*bad" "abc") .invalidSyntax "findAll invalid syntax"

/-- Error test for `findAll` returning `.unexpectedEof`. -/
def err_regexp_findAll_unexpectedEof : IO Unit :=
  assertErrKind (findAll "[unclosed" "abc") .unexpectedEof "findAll unexpected EOF"

/-- Error test for `countMatches` returning `.invalidSyntax`. -/
def err_regexp_countMatches_invalidSyntax : IO Unit :=
  assertErrKind (countMatches "*bad" "abc") .invalidSyntax "countMatches invalid syntax"

/-- Error test for `countMatches` returning `.unexpectedEof`. -/
def err_regexp_countMatches_unexpectedEof : IO Unit :=
  assertErrKind (countMatches "[unclosed" "abc") .unexpectedEof "countMatches unexpected EOF"

/-- Error test for `replaceAll` returning `.invalidSyntax`. -/
def err_regexp_replaceAll_invalidSyntax : IO Unit :=
  assertErrKind (replaceAll "*bad" "abc" "x") .invalidSyntax "replaceAll invalid syntax"

/-- Error test for `replaceAll` returning `.unexpectedEof`. -/
def err_regexp_replaceAll_unexpectedEof : IO Unit :=
  assertErrKind (replaceAll "[unclosed" "abc" "x") .unexpectedEof "replaceAll unexpected EOF"

/-- Error test for `splitBy` returning `.invalidSyntax`. -/
def err_regexp_splitBy_invalidSyntax : IO Unit :=
  assertErrKind (splitBy "*bad" "abc") .invalidSyntax "splitBy invalid syntax"

/-- Error test for `splitBy` returning `.unexpectedEof`. -/
def err_regexp_splitBy_unexpectedEof : IO Unit :=
  assertErrKind (splitBy "[unclosed" "abc") .unexpectedEof "splitBy unexpected EOF"

/-- Registered error-coverage tests for `LeanSwe.RegExp`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_testPattern_invalidSyntax"
     , mode := .real
     , run := err_regexp_testPattern_invalidSyntax }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_testPattern_unexpectedEof"
     , mode := .real
     , run := err_regexp_testPattern_unexpectedEof }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_findFirst_invalidSyntax"
     , mode := .real
     , run := err_regexp_findFirst_invalidSyntax }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_findFirst_unexpectedEof"
     , mode := .real
     , run := err_regexp_findFirst_unexpectedEof }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_findAll_invalidSyntax"
     , mode := .real
     , run := err_regexp_findAll_invalidSyntax }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_findAll_unexpectedEof"
     , mode := .real
     , run := err_regexp_findAll_unexpectedEof }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_countMatches_invalidSyntax"
     , mode := .real
     , run := err_regexp_countMatches_invalidSyntax }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_countMatches_unexpectedEof"
     , mode := .real
     , run := err_regexp_countMatches_unexpectedEof }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_replaceAll_invalidSyntax"
     , mode := .real
     , run := err_regexp_replaceAll_invalidSyntax }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_replaceAll_unexpectedEof"
     , mode := .real
     , run := err_regexp_replaceAll_unexpectedEof }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_splitBy_invalidSyntax"
     , mode := .real
     , run := err_regexp_splitBy_invalidSyntax }
   , { testName := "LeanSwe.RegExp.RuntimeTests.err_regexp_splitBy_unexpectedEof"
     , mode := .real
     , run := err_regexp_splitBy_unexpectedEof }
   ]

/-- Execute all runtime sanity checks for `LeanSwe.RegExp`. -/
def runAll : IO Unit := do
  assertOkEq (testPattern "[0-9]+" "id=42") true "digit match expected"
  assertOkEq (testPattern "[0-9]+" "abc") false "non-match expected"
  match findFirst "a+" "xaaay" with
  | .ok (some sp) =>
    assertTrue (sp.matched == "aaa" && sp.startByte == 1 && sp.stopByte == 4)
      s!"unexpected findFirst span: {repr sp}"
  | other => throw (IO.userError s!"unexpected findFirst result: {repr other}")
  match findAll "[0-9]+" "10,200,3" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["10", "200", "3"])
      s!"unexpected findAll: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected findAll error: {e.message}")
  assertOkEq (countMatches "a+" "baaaaca") 2 "expected 2 matches"
  assertOkEq (replaceAll "[0-9]+" "v1.2" "X") "vX.X" "expected replaceAll"
  assertOkEq (splitBy "," "a,,b") #["a", "", "b"] "expected 3 split parts"
  match findFirst "b+" "αbbbβ" with
  | .ok (some sp) =>
    assertTrue (sp.matched == "bbb" && sp.startByte == 2 && sp.stopByte == 5)
      s!"unexpected UTF-8 span: {repr sp}"
  | other => throw (IO.userError s!"unexpected UTF-8 findFirst: {repr other}")
  assertOkEq (testPattern "$" "a") true "end anchor should match after scanning past index 0"
  assertOkEq (testPattern "\\ba" " a") true "word boundary pattern should match at index 1"
  assertOkEq (testPattern "\\Ba" "ba") true "non-word boundary pattern should match at index 1"
  assertOkEq (countMatches "$" "a") 1 "zero-width end anchor should match once"
  match findAll "\\b" " a" with
  | .ok xs =>
    assertTrue (xs.map (fun s => (s.startByte, s.stopByte)) == #[(1, 1), (2, 2)])
      s!"unexpected word boundary spans: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected word boundary findAll error: {e.message}")
  for bad in ["[unclosed", "(abc", "*bad"] do
    match testPattern bad "hello" with
    | .error e => assertTrue (e.message != "") s!"empty error message for {bad}"
    | .ok b => throw (IO.userError s!"expected parse error for {bad}, got {b}")
  assertOkEq (testPattern "" "abc") true "empty pattern matches"
  assertOkEq (testPattern "^ab" "ab") true "start anchor matches start"
  assertOkEq (testPattern "^ab" "xab") false "start anchor rejects non-start"
  assertOkEq (testPattern "(?:ab)|cd" "ab") true "non-capturing group matches first branch"
  assertOkEq (testPattern "(?:ab)|cd" "cd") true "non-capturing group and alternation"
  assertOkEq (testPattern "a\\sb" "a\tb") true "whitespace escape matches tab"
  assertOkEq (testPattern "a\\sb" "a b") true "whitespace escape matches space"
  assertOkEq (testPattern "a\\sb" "axb") false "whitespace escape rejects letter"
  assertOkEq (testPattern "[a-z]+" "xyz") true "char range matches"
  assertOkEq (testPattern "[^0-9]+" "abc") true "negated char class matches"
  assertOkEq (testPattern "a{2,3}" "aa") true "bounded repetition matches"
  assertOkEq (testPattern "^a{2,3}$" "aaaa") false "bounded repetition respects upper bound"
  assertOkEq (testPattern "a?" "") true "optional quantifier matches empty"
  assertOkEq (testPattern "a*" "") true "star quantifier matches empty"
  match findFirst "a+?" "aaa" with
  | .ok (some sp) =>
    assertTrue (sp.matched == "a") s!"lazy plus should match minimal 'a', got {sp.matched}"
  | other => throw (IO.userError s!"unexpected lazy findFirst: {repr other}")
  assertErrKind (testPattern "(((((((*" "a") .invalidSyntax "deep parens leading quantifier invalidSyntax"
  assertErrKind (testPattern "(((((([]" "a") .invalidSyntax "deep parens empty class invalidSyntax"
  assertErrKind (testPattern "((((((a**" "a") .invalidSyntax "deep parens extra quantifier invalidSyntax"
  assertErrKind (testPattern "((((((a" "a") .unexpectedEof "deep parens unclosed unexpectedEof"
  assertOkEq (testPattern "((((((a))))))" "a") true "deep valid parens match"
  match findAll "(a*?)*" "ab" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["a", "", ""]) s!"unexpected (a*?)* on ab: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected (a*?)* error: {e.message}")
  match findAll "(a*?)+" "baab" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["", "aa", "", ""]) s!"unexpected (a*?)+ on baab: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected (a*?)+ error: {e.message}")
  match findAll "(a*?){1,}" "ab" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["a", "", ""]) s!"unexpected (a*?)\{1,} on ab: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected (a*?)\{1,} error: {e.message}")
  match findAll "((a*?)*)*" "ab" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["a", "", ""]) s!"unexpected ((a*?)*)* on ab: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected ((a*?)*)* error: {e.message}")
  match findAll "(?:|a*?)*" "ab" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["a", "", ""]) s!"unexpected (?:|a*?)* on ab: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected (?:|a*?)* error: {e.message}")
  match findAll "(a*?b?)*" "baab" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["baab", ""]) s!"unexpected (a*?b?)* on baab: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected (a*?b?)* error: {e.message}")
  match findAll "(b?a*?)*" "baab" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["baab", ""]) s!"unexpected (b?a*?)* on baab: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected (b?a*?)* error: {e.message}")
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.RegExp runtime tests"

end LeanSwe.RegExp.RuntimeTests
