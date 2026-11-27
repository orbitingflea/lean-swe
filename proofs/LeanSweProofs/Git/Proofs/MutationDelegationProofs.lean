import LeanSwe.Git.Types
import LeanSweProofs.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSweProofs.Git.SpecTests
import LeanSweProofs.Git.Proofs.ParserProofs

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private def sha1Const : String := String.ofList (List.replicate 40 '1')
private def sha2Const : String := String.ofList (List.replicate 40 '2')

private def mkMutDelegationState : GitCliMockState :=
  { handler := fun req _ =>
      if req.args == #["cat-file", "-t", sha1Const ++ ":f.txt"] then
        .ok { exitCode := 0, stdout := "blob\n".toUTF8, stderr := ByteArray.empty }
      else if req.args == #["cat-file", "blob", sha1Const ++ ":f.txt"] then
        .ok { exitCode := 0, stdout := "hello".toUTF8, stderr := ByteArray.empty }
      else if req.args.toList.contains "--verify" && !req.args.toList.contains "show-ref" then
        .ok { exitCode := 0, stdout := (sha1Const ++ "\n").toUTF8, stderr := ByteArray.empty }
      else
        .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }

private def mkExit1State : GitCliMockState :=
  { handler := fun _ _ =>
      .ok { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty } }

private theorem mutDel_isRepo :
    let (res, st) := (((Impl.mkApiM mockRawOps).isRepo "/repo").run mkMutDelegationState)
    res = .ok true ∧ st.callCount = 1 := by
  constructor <;> cbv

private theorem mutDel_headCommit :
    let (res, st) := (((Impl.mkApiM mockRawOps).headCommit? "/repo").run mkMutDelegationState)
    res = .ok (some { hex := sha1Const }) ∧ st.callCount = 1 := by
  constructor <;> cbv

private theorem mutDel_revParseCommit :
    let (res, st) := (((Impl.mkApiM mockRawOps).revParseCommit "/repo" "HEAD").run mkMutDelegationState)
    res = .ok { hex := sha1Const } ∧ st.callCount = 1 := by
  constructor <;> cbv

private theorem mutDel_isAncestor :
    (((Impl.mkApiM mockRawOps).isAncestor "/repo" { hex := sha1Const } { hex := sha2Const }).run mkMutDelegationState).1 = .ok true ∧
    (((Impl.mkApiM mockRawOps).isAncestor "/repo" { hex := sha1Const } { hex := sha2Const }).run mkExit1State).1 = .ok false := by
  constructor <;> cbv

private theorem mutDel_showFile :
    let (res, st) := (((Impl.mkApiM mockRawOps).showFile? "/repo" "HEAD" "f.txt").run mkMutDelegationState)
    res = .ok (some "hello".toUTF8) ∧ st.callCount = 3 := by
  constructor <;> cbv

private theorem mutDel_init :
    let (res, st) := (((Impl.mkApiM mockRawOps).init "/newrepo" true (some { raw := "dev" })).run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := none, args := #["init", "--bare", "-b", "dev", "--", "/newrepo"] } := by
  constructor <;> cbv

private theorem mutDel_clone :
    let (res, st) := (((Impl.mkApiM mockRawOps).clone "/src" "/dst"
      { bare := true, singleBranch := true, depth? := some 1, branch? := some "dev" }).run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? =
      some { cwd := none, args := #["clone", "--bare", "--single-branch", "--depth", "1", "--branch", "dev", "--", "/src", "/dst"] } := by
  constructor <;> cbv

private theorem mutDel_add :
    let (res, st) := (((Impl.mkApiM mockRawOps).add "/repo" #["a.txt"] true).run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := some "/repo", args := #["add", "--all", "--", "a.txt"] } := by
  constructor <;> cbv

private theorem mutDel_createBranch :
    let (res, st) := (((Impl.mkApiM mockRawOps).createBranch "/repo" { raw := "feat" } (some "HEAD") true).run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := some "/repo", args := #["branch", "-f", "--", "feat", "HEAD"] } := by
  constructor <;> cbv

private theorem mutDel_deleteBranchF :
    let (res, st) := (((Impl.mkApiM mockRawOps).deleteBranch "/repo" { raw := "feat" } true).run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := some "/repo", args := #["branch", "-D", "--", "feat"] } := by
  constructor <;> cbv

private theorem mutDel_deleteBranchS :
    let (res, st) := (((Impl.mkApiM mockRawOps).deleteBranch "/repo" { raw := "feat" } false).run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := some "/repo", args := #["branch", "-d", "--", "feat"] } := by
  constructor <;> cbv

private theorem mutDel_checkout :
    let (res, st) := (((Impl.mkApiM mockRawOps).checkout "/repo" (.branch { raw := "feat" }) true).run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := some "/repo", args := #["checkout", "--force", "feat", "--"] } := by
  constructor <;> cbv

private theorem mutDel_switch :
    let (res, st) := (((Impl.mkApiM mockRawOps).switch "/repo" { raw := "feat" } true (some "HEAD") true).run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := some "/repo", args := #["switch", "--force", "-C", "feat", "HEAD"] } := by
  constructor <;> cbv

private theorem mutDel_resetM :
    let (res, st) := (((Impl.mkApiM mockRawOps).reset "/repo" .mixed "HEAD").run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := some "/repo", args := #["reset", "--mixed", "HEAD", "--"] } := by
  constructor <;> cbv

private theorem mutDel_resetH :
    let (res, st) := (((Impl.mkApiM mockRawOps).reset "/repo" .hard "HEAD").run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := some "/repo", args := #["reset", "--hard", "HEAD", "--"] } := by
  constructor <;> cbv

private theorem mutDel_fetch :
    let (res, st) := (((Impl.mkApiM mockRawOps).fetch "/repo" "origin" (some "HEAD") true).run mkMutDelegationState)
    res = .ok () ∧ st.recordedRequests.getLast? = some { cwd := some "/repo", args := #["fetch", "--prune", "origin", "HEAD"] } := by
  constructor <;> cbv

/-- Proof of `test_git_raw_mkApi_mutationAndFlagDelegation` for `Impl.mkApiM`. -/
theorem proof_git_raw_mkApi_mutationAndFlagDelegation :
    AllPass (test_git_raw_mkApi_mutationAndFlagDelegation (fun ops => Impl.mkApiM ops)) := by
  dsimp only [test_git_raw_mkApi_mutationAndFlagDelegation, AllPass, assert]
  exact ⟨mutDel_isRepo, mutDel_headCommit, mutDel_revParseCommit, mutDel_isAncestor,
    mutDel_showFile, mutDel_init, mutDel_clone, mutDel_add, mutDel_createBranch,
    mutDel_deleteBranchF, mutDel_deleteBranchS, mutDel_checkout, mutDel_switch,
    mutDel_resetM, mutDel_resetH, mutDel_fetch, trivial⟩

end LeanSwe.Git.Proofs
