import LeanSwe.Git.Types
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.SpecTests

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private def guardSha1Const : String := String.ofList (List.replicate 40 '1')

private def mkGuardDelegationState : GitCliMockState :=
  { handler := fun req _ =>
      if req.args.toList.contains "--verify" && !req.args.toList.contains "show-ref" then
        .ok { exitCode := 0, stdout := (guardSha1Const ++ "\n").toUTF8, stderr := ByteArray.empty }
      else
        .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }

private theorem guard_swEF :
    let (res, st) := (((Impl.mkApiM mockRawOps).switch "/repo" { raw := "feat" } false none true).run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["switch", "--force", "feat"] } := by
  constructor <;> cbv

private theorem guard_coRF :
    let (res, st) := (((Impl.mkApiM mockRawOps).checkout "/repo" (.ref "HEAD~1") true).run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["checkout", "--force", "HEAD~1", "--"] } := by
  constructor <;> cbv

private theorem guard_waDF :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeAdd "/repo" { path := "/wt3", detach := true, force := true }).run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["worktree", "add", "--force", "--detach", "--", "/wt3"] } := by
  constructor <;> cbv

private theorem guard_waDef :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeAdd "/repo" { path := "/wt_def" }).run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["worktree", "add", "--", "/wt_def"] } := by
  constructor <;> cbv

private theorem guard_rsRefOk :
    let (res, st) := (((Impl.mkApiM mockRawOps).reset "/repo" .hard "feat~1").run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["reset", "--hard", "feat~1", "--"] } := by
  constructor <;> cbv

private theorem guard_rpShort :
    (((Impl.mkApiM mockRawOps).revParseCommit "/repo" "1111111").run mkGuardDelegationState).1 = .ok { hex := guardSha1Const } ∧
    (((Impl.mkApiM mockRawOps).revParseCommit "/repo" "HEAD@{0}").run mkGuardDelegationState).1 = .ok { hex := guardSha1Const } := by
  constructor <;> cbv

private theorem guard_rsShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).reset "/repo" .hard "1111111").run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["reset", "--hard", "1111111", "--"] } := by
  constructor <;> cbv

private theorem guard_coShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).checkout "/repo" (.ref "1111111") false).run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["checkout", "1111111", "--"] } := by
  constructor <;> cbv

private theorem guard_swShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).switch "/repo" { raw := "newbr" } true (some "1111111") false).run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["switch", "-c", "newbr", "1111111"] } := by
  constructor <;> cbv

private theorem guard_cbShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).createBranch "/repo" { raw := "newbr" } (some "1111111") false).run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["branch", "--", "newbr", "1111111"] } := by
  constructor <;> cbv

private theorem guard_dfShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).diffNameStatus "/repo" "1111111" none #[]).run mkGuardDelegationState)
    res = .ok #[] ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["diff", "--name-status", "--find-renames=100%", "-z", "1111111", "--"] } := by
  constructor <;> cbv

private theorem guard_waShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeAdd "/repo" { path := "/wt4", newBranch? := some { raw := "wtb" }, target? := some "1111111" }).run mkGuardDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["worktree", "add", "-b", "wtb", "--", "/wt4", "1111111"] } := by
  constructor <;> cbv

/-- Proof of `test_git_raw_mkApi_forceAndShortShaGuards` for `Impl.mkApiM`. -/
theorem proof_git_raw_mkApi_forceAndShortShaGuards :
    AllPass (test_git_raw_mkApi_forceAndShortShaGuards (fun ops => Impl.mkApiM ops)) := by
  dsimp only [test_git_raw_mkApi_forceAndShortShaGuards, AllPass, assert]
  exact ⟨guard_swEF, guard_coRF, guard_waDF, guard_waDef, guard_rsRefOk,
    guard_rpShort, guard_rsShort, guard_coShort, guard_swShort, guard_cbShort, guard_dfShort, guard_waShort, trivial⟩

end LeanSwe.Git.Proofs
