import LeanSwe.Uuid.Raw.Interface

namespace LeanSwe.Uuid.Raw.RuntimeTests

private def check (name : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"LeanSwe.Uuid.Raw runtime test failed: {name}")

/-- Run executable runtime tests grounding `LeanSwe.Uuid.Raw` against OS entropy (`getrandom`/`/dev/urandom`). -/
def runAll : IO Unit := do
  let mut samples : Array ByteArray := #[]
  for _ in [0:64] do
    match ← randomBytes16 with
    | .error e =>
      throw (IO.userError s!"randomBytes16 failed: {e.message}")
    | .ok bs =>
      check "randomBytes16 returns 16 bytes" (bs.size == 16)
      samples := samples.push bs
  let first := samples[0]!
  check "randomBytes16 does not return constant bytes" (samples.any (fun b => b != first))
  let e1 := mapRawError (.osError 13 "")
  check "mapRawError osError preserves errno and non-empty message"
    (e1.kind == .entropyFailed && e1.errnoCode == some 13 && !e1.message.isEmpty)
  let e2 := mapRawError (.shortRead 4 "")
  check "mapRawError shortRead sets entropyFailed and non-empty message"
    (e2.kind == .entropyFailed && !e2.message.isEmpty)
  let e3 := mapRawError (.userError "")
  check "mapRawError userError sets entropyFailed and non-empty message"
    (e3.kind == .entropyFailed && !e3.message.isEmpty)
  IO.println "PASS: LeanSwe.Uuid.Raw runtime tests"

end LeanSwe.Uuid.Raw.RuntimeTests
