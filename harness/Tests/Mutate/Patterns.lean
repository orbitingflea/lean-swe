import Tests.Common
import LeanSwe.RegExp.RuntimeTests
import LeanSwe.Glob.RuntimeTests

namespace Tests.Mutate.Patterns

open LeanSwe
open Tests.Common

/-- Mutation test suite for `LeanSwe.RegExp`. -/
def regExpSuite : MutateSuite :=
  { name := "RegExp", runBase := do RegExp.RuntimeTests.runAll; smokeRegExp; return none }

/-- Mutation test suite for `LeanSwe.Glob`. -/
def globSuite : MutateSuite :=
  { name := "Glob", runBase := do Glob.RuntimeTests.runAll; return none }

end Tests.Mutate.Patterns
