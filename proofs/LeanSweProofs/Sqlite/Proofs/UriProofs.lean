import LeanSweProofs.Sqlite.Proofs.UriNoWalProofs
import LeanSweProofs.Sqlite.Proofs.UriHasWalProofs

namespace LeanSwe.Sqlite.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite

/-- Proof of `test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets` for `Internal.mkRawOps`. -/
theorem proof_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets :
    AllPass (test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets Internal.mkRawOps) := by
  dsimp only [test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets, assert]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact uriNoWal_1
  · exact uriNoWal_2
  · exact uriNoWal_3
  · exact uriNoWal_4
  · exact uriNoWal_5
  · exact uriHasWal_1
  · exact uriHasWal_2
  · exact uriHasWal_3
  · exact uriHasWal_4
  · exact uriHasWal_5

/-- Non-vacuity `CanReach` witness for `test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets`. -/
theorem reach_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets :
    CanReach (test_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets Internal.mkRawOps) :=
  proof_sqliteraw_openDb_uriAuthorityNullEscapeAndWalTargets

end LeanSwe.Sqlite.Proofs
