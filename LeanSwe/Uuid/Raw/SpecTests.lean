import Core.NondetTest
import LeanSwe.Uuid.Raw.Types

namespace LeanSwe.Uuid.Raw

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `ops.mapRawError` has kind `.entropyFailed` and a non-empty diagnostic message, preserving `errno` on `.osError`. -/
def test_uuidraw_mapRawError_normalizesError
    {runner} [NondetTest runner] (ops : RawUuidOps) : runner Unit := do
  let raw ← nondet UuidRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.kind = .entropyFailed ∧ err.message ≠ "")
  match raw with
  | .osError code _ => NondetTest.assert (err.errnoCode = some code)
  | .shortRead _ _ => NondetTest.assert True
  | .userError _ => NondetTest.assert True

/-- Successful `ops.randomBytes16` calls return exactly 16 bytes, and failures carry `.entropyFailed` with a non-empty message. -/
def test_uuidraw_randomBytes16_returns16BytesOrError
    {S : Type} {runner} [NondetTest runner] (ops : RawUuidOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  match (ops.randomBytes16.run s₀).1 with
  | .ok bs => NondetTest.assert (bs.size = 16)
  | .error e => NondetTest.assert (e.kind = .entropyFailed ∧ e.message ≠ "")

end LeanSwe.Uuid.Raw
