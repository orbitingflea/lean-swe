import LeanSwe.CryptoHash.Raw.Types
import LeanSwe.CryptoHash.Raw.Interface

namespace LeanSwe.CryptoHash.Raw.RuntimeTests

open LeanSwe.CryptoHash.Raw

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"CryptoHash.Raw runtime test failed: {msg}")

/-- Run all runtime verification tests for `LeanSwe.CryptoHash.Raw`. -/
def runAll : IO Unit := do
  let err1 := mapRawError (.invalidArgument "")
  assertTrue (err1.kind == .invalidInput && !err1.message.isEmpty && err1.opensslCode == none)
    "mapRawError invalidArgument"
  let err2 := mapRawError (.opensslError (some 123) "")
  assertTrue (err2.kind == .cryptoError && !err2.message.isEmpty && err2.opensslCode == some 123)
    "mapRawError opensslError"

  match ← digestRaw .sha256 ByteArray.empty with
  | .error e => throw (IO.userError s!"digestRaw sha256 empty failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 32) "digestRaw sha256 empty size 32"

  match ← digestRaw .sha512 ByteArray.empty with
  | .error e => throw (IO.userError s!"digestRaw sha512 empty failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 64) "digestRaw sha512 empty size 64"

  let nulMsg := ByteArray.mk #[0x00, 0x61, 0x00]
  match ← digestRaw .sha256 nulMsg with
  | .error e => throw (IO.userError s!"digestRaw sha256 nul failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 32) "digestRaw sha256 embedded NUL size 32"

  match ← hmacSha256Raw ByteArray.empty "abc".toUTF8 with
  | .error e => throw (IO.userError s!"hmacSha256Raw empty key failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 32) "hmacSha256Raw empty key size 32"

  let longKey := ByteArray.mk (Array.replicate 131 0xAA)
  match ← hmacSha256Raw longKey "msg".toUTF8 with
  | .error e => throw (IO.userError s!"hmacSha256Raw long key failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 32) "hmacSha256Raw 131-byte key size 32"

  match ← ctEqualRaw ByteArray.empty ByteArray.empty with
  | .error e => throw (IO.userError s!"ctEqualRaw empty failed: {e.message}")
  | .ok eq => assertTrue eq "ctEqualRaw empty == empty"

  match ← ctEqualRaw nulMsg nulMsg with
  | .error e => throw (IO.userError s!"ctEqualRaw equal failed: {e.message}")
  | .ok eq => assertTrue eq "ctEqualRaw equal arrays"

  match ← ctEqualRaw nulMsg (ByteArray.mk #[0x00, 0x62, 0x00]) with
  | .error e => throw (IO.userError s!"ctEqualRaw unequal bytes failed: {e.message}")
  | .ok eq => assertTrue (!eq) "ctEqualRaw unequal bytes"

  match ← ctEqualRaw nulMsg (ByteArray.mk #[0x00, 0x61]) with
  | .ok _ => throw (IO.userError "ctEqualRaw should reject unequal length")
  | .error e =>
    assertTrue (e.kind == .lengthMismatch && !e.message.isEmpty)
      "ctEqualRaw unequal length rejects with .lengthMismatch"
  IO.println "PASS: LeanSwe.CryptoHash.Raw runtime tests"

end LeanSwe.CryptoHash.Raw.RuntimeTests
