import Tests.Common
import LeanSwe.NumParse.RuntimeTests

namespace Tests.Mutate.NumParse

open LeanSwe
open Tests.Common

/-- Mutation test suite for `LeanSwe.NumParse`. -/
def numParseSuite : MutateSuite :=
  { name := "NumParse", runBase := do NumParse.RuntimeTests.runAll; return none }

end Tests.Mutate.NumParse
