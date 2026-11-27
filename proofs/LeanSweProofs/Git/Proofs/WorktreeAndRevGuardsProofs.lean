import LeanSweProofs.Git.Proofs.RevSecondaryGuardsProofs

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git

/-- Proof of `test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards` for `Impl.mkApiM`. -/
theorem proof_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards :
    AllPass (test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards (fun ops => Impl.mkApiM ops)) := by
  dsimp only [test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards, AllPass, assert]
  exact ⟨secGuard_wa40Direct, secGuard_dfRevBShort, secGuard_sfShort, trivial⟩

end LeanSwe.Git.Proofs
