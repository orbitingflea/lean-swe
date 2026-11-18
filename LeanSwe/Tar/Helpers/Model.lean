import Core.NondetTest
import LeanSwe.Tar.Types
import LeanSwe.Tar.Model

namespace LeanSwe.Tar

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Tar.Model

/-- Assert that `api.packWith opts entries` succeeds and `api.unpackWith unpackOpts` returns a `TarEquiv` list. -/
def checkRoundTripCase {runner} [NondetTest runner] (api : TarApi)
    (packOpts : PackOptions) (unpackOpts : UnpackOptions) (entries : List TarEntry) :
    runner Unit :=
  match api.packWith packOpts entries with
  | .error _ => NondetTest.assert False
  | .ok bytes =>
    match api.unpackWith unpackOpts bytes with
    | .error _ => NondetTest.assert False
    | .ok decoded =>
      let expected := if packOpts.deterministic then entries.map zeroDeterministicMeta else entries
      NondetTest.assert (TarEquiv expected decoded)

/-- Assert that `api.packWith opts entries` fails with exact `expectedKind` and non-empty message. -/
def checkPackError {runner} [NondetTest runner] (api : TarApi)
    (opts : PackOptions) (entries : List TarEntry) (expectedKind : TarErrorKind) :
    runner Unit :=
  match api.packWith opts entries with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = expectedKind ∧ !e.message.isEmpty = true)

/-- Assert that `api.unpackWith opts bytes` fails with exact `expectedKind` and non-empty message. -/
def checkUnpackError {runner} [NondetTest runner] (api : TarApi)
    (opts : UnpackOptions) (bytes : ByteArray) (expectedKind : TarErrorKind) :
    runner Unit :=
  match api.unpackWith opts bytes with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = expectedKind ∧ !e.message.isEmpty = true)

end LeanSwe.Tar
