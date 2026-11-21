import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.SpecTests
import LeanSwe.Git.Proofs.ParserProofs

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private def extSha1Const : String := String.ofList (List.replicate 40 '1')

private def mkExtDelegationState : GitCliMockState :=
  { handler := fun req _ =>
      if req.args.toList.contains "--verify" && !req.args.toList.contains "show-ref" then
        .ok { exitCode := 0, stdout := (extSha1Const ++ "\n").toUTF8, stderr := ByteArray.empty }
      else
        .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }

private theorem extDel_commitFull :
    let (res, st) := (((Impl.mkApiM mockRawOps).commit "/repo"
      { message := "msg\nbody"
        allowEmpty := true
        authorName := some "Alice"
        authorEmail := some "alice@example.com" }).run mkExtDelegationState)
    res = .ok { hex := extSha1Const } ∧ st.recordedRequests[0]? = some
      { cwd := some "/repo"
        args := #["commit", "--no-gpg-sign", "-m", "msg\nbody", "--allow-empty"]
        extraEnv := #[
          ("GIT_AUTHOR_NAME", some "Alice"),
          ("GIT_COMMITTER_NAME", some "Alice"),
          ("GIT_AUTHOR_EMAIL", some "alice@example.com"),
          ("GIT_COMMITTER_EMAIL", some "alice@example.com")
        ] } := by
  constructor <;> cbv

private theorem extDel_commitPlain :
    let (res, st) := (((Impl.mkApiM mockRawOps).commit "/repo"
      { message := "plain", allowEmpty := false }).run mkExtDelegationState)
    res = .ok { hex := extSha1Const } ∧ st.recordedRequests[0]? = some
      { cwd := some "/repo"
        args := #["commit", "--no-gpg-sign", "-m", "plain"]
        extraEnv := #[] } := by
  constructor <;> cbv

private theorem extDel_resetS :
    let (res, st) := (((Impl.mkApiM mockRawOps).reset "/repo" .soft "HEAD").run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["reset", "--soft", "HEAD", "--"] } := by
  constructor <;> cbv

private theorem extDel_diff2 :
    let (res, st) := (((Impl.mkApiM mockRawOps).diffNameStatus "/repo" "HEAD" (some "HEAD~1") #["a.txt", "sub/b.txt"]).run mkExtDelegationState)
    res = .ok #[] ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["diff", "--name-status", "--find-renames=100%", "-z", "HEAD", "HEAD~1", "--", "a.txt", "sub/b.txt"] } := by
  constructor <;> cbv

private theorem extDel_diff1 :
    let (res, st) := (((Impl.mkApiM mockRawOps).diffNameStatus "/repo" "HEAD" none #[]).run mkExtDelegationState)
    res = .ok #[] ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["diff", "--name-status", "--find-renames=100%", "-z", "HEAD", "--"] } := by
  constructor <;> cbv

private theorem extDel_worktreeAddF :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeAdd "/repo"
      { path := "/wt1", newBranch? := some { raw := "wtbr" }, target? := some "HEAD", force := true }).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["worktree", "add", "--force", "-b", "wtbr", "--", "/wt1", "HEAD"] } := by
  constructor <;> cbv

private theorem extDel_worktreeAddD :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeAdd "/repo"
      { path := "/wt2", detach := true }).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["worktree", "add", "--detach", "--", "/wt2"] } := by
  constructor <;> cbv

private theorem extDel_worktreeRemoveF :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeRemove "/repo" "/wt1" true).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["worktree", "remove", "--force", "--", "/wt1"] } := by
  constructor <;> cbv

private theorem extDel_worktreeRemoveS :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeRemove "/repo" "/wt1" false).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["worktree", "remove", "--", "/wt1"] } := by
  constructor <;> cbv

private theorem extDel_checkoutC0 :
    let (res, st) := (((Impl.mkApiM mockRawOps).checkout "/repo" (.commit { hex := extSha1Const }) false).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["checkout", "--detach", extSha1Const, "--"] } := by
  constructor <;> cbv

private theorem extDel_checkoutC1 :
    let (res, st) := (((Impl.mkApiM mockRawOps).checkout "/repo" (.commit { hex := extSha1Const }) true).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["checkout", "--force", "--detach", extSha1Const, "--"] } := by
  constructor <;> cbv

private theorem extDel_checkoutR :
    let (res, st) := (((Impl.mkApiM mockRawOps).checkout "/repo" (.ref "HEAD~1") false).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["checkout", "HEAD~1", "--"] } := by
  constructor <;> cbv

private theorem extDel_checkoutB :
    let (res, st) := (((Impl.mkApiM mockRawOps).checkout "/repo" (.branch { raw := "feat" }) false).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["checkout", "feat", "--"] } := by
  constructor <;> cbv

private theorem extDel_switchC :
    let (res, st) := (((Impl.mkApiM mockRawOps).switch "/repo" { raw := "feat" } true none false).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["switch", "-c", "feat"] } := by
  constructor <;> cbv

private theorem extDel_switchE :
    let (res, st) := (((Impl.mkApiM mockRawOps).switch "/repo" { raw := "feat" } false none false).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["switch", "feat"] } := by
  constructor <;> cbv

private theorem extDel_addP :
    let (res, st) := (((Impl.mkApiM mockRawOps).add "/repo" #["a.txt"] false).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["add", "--", "a.txt"] } := by
  constructor <;> cbv

private theorem extDel_addA :
    let (res, st) := (((Impl.mkApiM mockRawOps).add "/repo" #[] true).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["add", "--all"] } := by
  constructor <;> cbv

private theorem extDel_initP :
    let (res, st) := (((Impl.mkApiM mockRawOps).init "/newrepo" false none).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := none, args := #["init", "--", "/newrepo"] } := by
  constructor <;> cbv

private theorem extDel_cloneP :
    let (res, st) := (((Impl.mkApiM mockRawOps).clone "/src" "/dst" {}).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := none, args := #["clone", "--", "/src", "/dst"] } := by
  constructor <;> cbv

private theorem extDel_createBranchP :
    let (res, st) := (((Impl.mkApiM mockRawOps).createBranch "/repo" { raw := "feat" } none false).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["branch", "--", "feat"] } := by
  constructor <;> cbv

private theorem extDel_fetchP :
    let (res, st) := (((Impl.mkApiM mockRawOps).fetch "/repo" "origin" none false).run mkExtDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["fetch", "origin"] } := by
  constructor <;> cbv

/-- Proof of `test_git_raw_mkApi_extendedFlagAndCommitDelegation` for `Impl.mkApiM`. -/
theorem proof_git_raw_mkApi_extendedFlagAndCommitDelegation :
    AllPass (test_git_raw_mkApi_extendedFlagAndCommitDelegation (fun ops => Impl.mkApiM ops)) := by
  dsimp only [test_git_raw_mkApi_extendedFlagAndCommitDelegation, AllPass, assert]
  exact ⟨extDel_commitFull, extDel_commitPlain, extDel_resetS, extDel_diff2, extDel_diff1,
    extDel_worktreeAddF, extDel_worktreeAddD, extDel_worktreeRemoveF, extDel_worktreeRemoveS,
    extDel_checkoutC0, extDel_checkoutC1, extDel_checkoutR, extDel_checkoutB,
    extDel_switchC, extDel_switchE, extDel_addP, extDel_addA,
    extDel_initP, extDel_cloneP, extDel_createBranchP, extDel_fetchP, trivial⟩

end LeanSwe.Git.Proofs
