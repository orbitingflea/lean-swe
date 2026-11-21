import LeanSwe.Git.Proofs.RevSecondaryGuardsProofs

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

/-- `worktreeAdd` attaches an unused 40-hex local branch via `symbolic-ref`. -/
theorem secGuard_wa40Ok :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeAdd "/repo" { path := "/wt40", target? := some secBr40Const }).run (mkSecGuardState false false))
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/wt40", args := #["symbolic-ref", "HEAD", "refs/heads/" ++ secBr40Const] } := by
  constructor <;> cbv

end LeanSwe.Git.Proofs
