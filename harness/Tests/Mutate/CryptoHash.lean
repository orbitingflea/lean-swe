import Tests.Common
import LeanSwe.CryptoHash.Raw.RuntimeTests
import LeanSwe.CryptoHash.RuntimeTests

namespace Tests.Mutate.CryptoHash

open LeanSwe
open Tests.Common

/-- Mutation test suite for `LeanSwe.CryptoHash.Raw`. -/
def cryptoHashRawSuite : MutateSuite :=
  { name := "CryptoHash.Raw", runBase := do CryptoHash.Raw.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.CryptoHash`. -/
def cryptoHashSuite : MutateSuite :=
  { name := "CryptoHash", runBase := do CryptoHash.RuntimeTests.runAll; return none }

end Tests.Mutate.CryptoHash
