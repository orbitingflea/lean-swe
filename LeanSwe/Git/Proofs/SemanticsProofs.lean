import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Interface
import LeanSwe.Git.SpecTests

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private def c0Const : CommitId := { hex := String.ofList (List.replicate 40 '0') }
private def c1Const : CommitId := { hex := String.ofList (List.replicate 40 '1') }
private def eA0Const : GitTreeEntry := { kind := .regular false, bytes := "v0".toUTF8 }
private def eA1Const : GitTreeEntry := { kind := .regular false, bytes := "v1".toUTF8 }
private def eSubConst : GitTreeEntry := { kind := .regular false, bytes := "sub1".toUTF8 }
private def tree0Const : List (ByteArray × GitTreeEntry) := [("a.txt".toUTF8, eA0Const)]
private def tree1Const : List (ByteArray × GitTreeEntry) := [("a.txt".toUTF8, eA1Const), ("sub/b.txt".toUTF8, eSubConst)]

private def sResetDiffConst : GitRepoState :=
  { vfs := .dir true true [("repo".toUTF8, .dir true true [
      (".git".toUTF8, .dir true true []),
      ("a.txt".toUTF8, .file false "v1".toUTF8),
      ("sub".toUTF8, .dir true true [("b.txt".toUTF8, .file false "sub1".toUTF8)])
    ])]
    repos := [{
      commonDir := "/repo/.git".toUTF8
      commits := [
        { id := c0Const, parents := [], tree := tree0Const },
        { id := c1Const, parents := [c0Const], tree := tree1Const }
      ]
      refs := [("refs/heads/main", c1Const)]
      worktrees := [{ rootPath := "/repo".toUTF8, head := .symbolic { raw := "main" }, index := { entries := tree1Const } }]
    }] }

private def sFetchConst : GitRepoState :=
  { vfs := .dir true true [
      ("origin".toUTF8, .dir true true [(".git".toUTF8, .dir true true [])]),
      ("clone".toUTF8, .dir true true [(".git".toUTF8, .dir true true [])])
    ]
    repos := [
      { commonDir := "/origin/.git".toUTF8
        commits := [{ id := c0Const, parents := [], tree := tree0Const }]
        refs := [("refs/heads/main", c0Const)]
        worktrees := [{ rootPath := "/origin".toUTF8, head := .symbolic { raw := "main" }, index := { entries := tree0Const } }] },
      { commonDir := "/clone/.git".toUTF8
        commits := [{ id := c0Const, parents := [], tree := tree0Const }]
        refs := [("refs/heads/main", c0Const), ("refs/remotes/origin/main", c0Const), ("refs/remotes/origin/stale", c0Const)]
        remotes := [{ name := "origin", url := "/origin", fetchSpecs := ["+refs/heads/*:refs/remotes/origin/*"] }]
        worktrees := [{ rootPath := "/clone".toUTF8, head := .symbolic { raw := "main" }, index := { entries := tree0Const } }] }
    ] }

private def sBranchConst : GitRepoState :=
  { vfs := .dir true true [("repo".toUTF8, .dir true true [
      (".git".toUTF8, .dir true true []),
      ("a.txt".toUTF8, .file false "v0".toUTF8)
    ])]
    repos := [{
      commonDir := "/repo/.git".toUTF8
      commits := [
        { id := c0Const, parents := [], tree := tree0Const },
        { id := c1Const, parents := [c0Const], tree := tree0Const }
      ]
      refs := [("refs/heads/main", c0Const), ("refs/heads/topic", c1Const)]
      worktrees := [{ rootPath := "/repo".toUTF8, head := .symbolic { raw := "main" }, index := { entries := tree0Const } }]
    }] }

private theorem sem_resetSoft :
    let (softRes, sAfterSoft) := (evalGitApi.reset "/repo" .soft c0Const.hex).run sResetDiffConst
    let (softHc, _) := (evalGitApi.headCommit? "/repo").run sAfterSoft
    let (softSt, _) := (evalGitApi.status "/repo").run sAfterSoft
    softRes = .ok () ∧ softHc = .ok (some c0Const) ∧ softSt = .ok #[
      { indexStatus := some .modified, worktreeStatus := none, path := "a.txt" },
      { indexStatus := some .added, worktreeStatus := none, path := "sub/b.txt" }
    ] := by
  refine ⟨by cbv, by cbv, by cbv⟩

private theorem sem_resetMixed :
    let (mixRes, sAfterMix) := (evalGitApi.reset "/repo" .mixed c0Const.hex).run sResetDiffConst
    let (mixHc, _) := (evalGitApi.headCommit? "/repo").run sAfterMix
    let (mixSt, _) := (evalGitApi.status "/repo").run sAfterMix
    mixRes = .ok () ∧ mixHc = .ok (some c0Const) ∧ mixSt = .ok #[
      { indexStatus := none, worktreeStatus := some .modified, path := "a.txt" },
      { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "sub/" }
    ] := by
  refine ⟨by cbv, by cbv, by cbv⟩

private theorem sem_diffSub :
    ((evalGitApi.diffNameStatus "/repo" c0Const.hex (some c1Const.hex) #["sub"]).run sResetDiffConst).1 =
      .ok #[{ kind := .added, path := "sub/b.txt", origPath := none }] := by
  cbv

private theorem sem_fetchNoPrune :
    let (fNoPrune, sNoPrune) := (evalGitApi.fetch "/clone" "origin" none false).run sFetchConst
    let (rpKept, _) := (evalGitApi.revParseCommit "/clone" "origin/stale").run sNoPrune
    fNoPrune = .ok () ∧ rpKept = .ok c0Const := by
  exact ⟨by cbv, by cbv; simp +decide; cbv⟩

private theorem sem_fetchPrune :
    let (fPrune, sPruned) := (evalGitApi.fetch "/clone" "origin" none true).run sFetchConst
    let (rpGone, _) := (evalGitApi.revParseCommit "/clone" "origin/stale").run sPruned
    let (rpMain, _) := (evalGitApi.revParseCommit "/clone" "origin/main").run sPruned
    fPrune = .ok () ∧ rpMain = .ok c0Const ∧ ∃ e, rpGone = .error e ∧ e.kind = .invalidRef := by
  refine ⟨by cbv, by cbv; simp +decide; cbv,
    ⟨{ kind := .invalidRef, message := "unknown revision 'origin/stale'" },
      by cbv; simp +decide; cbv, rfl⟩⟩

private theorem sem_deleteBranchSafe :
    let (delSafe, sDelSafe) := (evalGitApi.deleteBranch "/repo" { raw := "topic" } false).run sBranchConst
    ∃ e, delSafe = .error e ∧ e.kind = .dirtyWorktree ∧ sDelSafe = sBranchConst := by
  exact ⟨{ kind := .dirtyWorktree, message := "the branch 'topic' is not fully merged" }, by cbv, rfl, by cbv⟩

private theorem sem_deleteBranchForce :
    let (delForce, sDelForce) := (evalGitApi.deleteBranch "/repo" { raw := "topic" } true).run sBranchConst
    let (rpDelTopic, _) := (evalGitApi.revParseCommit "/repo" "topic").run sDelForce
    delForce = .ok () ∧ ∃ e, rpDelTopic = .error e ∧ e.kind = .invalidRef := by
  refine ⟨by cbv,
    ⟨{ kind := .invalidRef, message := "unknown revision 'topic'" },
      by cbv; simp +decide; cbv, rfl⟩⟩

private theorem sem_switchCreateDup :
    let (swCreateDup, sSwDup) := (evalGitApi.switch "/repo" { raw := "topic" } true none false).run sBranchConst
    ∃ e, swCreateDup = .error e ∧ e.kind = .alreadyExists ∧ sSwDup = sBranchConst := by
  exact ⟨{ kind := .alreadyExists, message := "a branch named 'topic' already exists" }, by cbv, rfl, by cbv⟩

private theorem sem_switchCreateForce :
    let (swCreateForce, sSwForce) := (evalGitApi.switch "/repo" { raw := "topic" } true none true).run sBranchConst
    let (hsAfterSwF, _) := (evalGitApi.headState "/repo").run sSwForce
    swCreateForce = .ok () ∧ hsAfterSwF = .ok (.attached { raw := "topic" } (some c0Const)) := by
  exact ⟨by cbv, by cbv⟩

/-- Proof of `test_git_api_resetDiffFetchDeleteAndSwitch_semantics` for `evalGitApi`. -/
theorem proof_git_api_resetDiffFetchDeleteAndSwitch_semantics :
    AllPass (test_git_api_resetDiffFetchDeleteAndSwitch_semantics evalGitApi) := by
  dsimp only [test_git_api_resetDiffFetchDeleteAndSwitch_semantics, AllPass, assert]
  exact ⟨sem_resetSoft, sem_resetMixed, sem_diffSub, sem_fetchNoPrune, sem_fetchPrune,
    sem_deleteBranchSafe, sem_deleteBranchForce, sem_switchCreateDup, sem_switchCreateForce, trivial⟩

end LeanSwe.Git.Proofs
