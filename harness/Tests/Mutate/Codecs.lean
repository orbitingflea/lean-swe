import Tests.Common
import LeanSwe.Json.RuntimeTests
import LeanSwe.Toml.RuntimeTests
import LeanSwe.Base64.RuntimeTests
import LeanSwe.Tar.RuntimeTests

namespace Tests.Mutate.Codecs

open LeanSwe
open Tests.Common

/-- Mutation test suite for `LeanSwe.Json`. -/
def jsonSuite : MutateSuite :=
  { name := "Json", runBase := do Json.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Toml`. -/
def tomlSuite : MutateSuite :=
  { name := "Toml", runBase := do Toml.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Base64`. -/
def base64Suite : MutateSuite :=
  { name := "Base64", runBase := do Base64.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Tar`. -/
def tarSuite : MutateSuite :=
  { name := "Tar", runBase := do Tar.RuntimeTests.runAll; return none }

end Tests.Mutate.Codecs
