import Tests.Common
import LeanSwe.Time.RuntimeTests
import LeanSwe.Uuid.RuntimeTests

namespace Tests.Mutate.TimeAndIds

open LeanSwe
open Tests.Common

/-- Mutation test suite for `LeanSwe.Time`. -/
def timeSuite : MutateSuite :=
  { name := "Time", runBase := do Time.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Uuid`. -/
def uuidSuite : MutateSuite :=
  { name := "Uuid", runBase := do Uuid.RuntimeTests.runAll; return none }

end Tests.Mutate.TimeAndIds
