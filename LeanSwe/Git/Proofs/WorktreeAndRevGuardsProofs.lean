import LeanSwe.Git.Proofs.RevSecondaryGuardsProofs
import LeanSwe.Git.Proofs.WorktreeHexAttachProofs
import LeanSwe.Git.Proofs.WorktreeHexSymFailProofs

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private def secBranchInUseErr : GitError :=
  { kind := .branchInUse, command := some "worktree", message := "'" ++ secBr40Const ++ "' is already used by worktree" }

private theorem secGuard_wa40Used :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeAdd "/repo" { path := "/wt40", target? := some secBr40Const }).run (mkSecGuardState true false))
    ∃ e, res = .error e ∧ e.kind = .branchInUse ∧
      !st.recordedRequests.any (fun r => r.args.toList.contains "add" || r.args.toList.contains "remove") :=
  ⟨secBranchInUseErr, by cbv, rfl, by cbv⟩

/-- Proof of `test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards` for `Impl.mkApiM`. -/
theorem proof_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards :
    AllPass (test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards (fun ops => Impl.mkApiM ops)) := by
  dsimp only [test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards, AllPass, assert]
  exact ⟨secGuard_wa40Used, secGuard_wa40Ok, secGuard_wa40SymFail, secGuard_dfRevBShort, secGuard_sfShort, trivial⟩

end LeanSwe.Git.Proofs
